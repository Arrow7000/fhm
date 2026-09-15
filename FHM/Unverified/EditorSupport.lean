import FHM.Unverified.Surface.Parse
import FHM.Surface.Span
import FHM.Unverified.Surface.Lex
import FHM.SurfaceBridge
import FHM.Unverified.HMArtifacts
import FHM.Unverified.HMDisplay
import FHM.Unverified.PipelineShared
import FHM.InferW
import FHM.Pretty
import FHM.Decls
import FHM.Bounds.Erase
import FHM.Bounds.Report
import FHM.Bounds.Pipeline
import FHM.Bounds.RecursiveFound
import FHM.Bounds.Check
import Lean.Data.Json

/-!
# Editor support helpers

`fhm diagnose` consumes found-producing inference and separate provenance.
HM mode displays found payloads with bounds erased; canonical Bounds mode joins
proof-producing per-node reports back to the same source IDs. Binding definitions
use inferred schemes or validated declarations. Source locations, name recovery,
and JSON presentation remain unverified.

The old structural guesses are retained only for `collectHoverLegacyBL`; they
are not used by either current editor mode. The v3 span/scope JSON contract
remains compatible with the existing VS Code and web consumers.
-/

open Surface.Parse
open Surface.Span
open Surface.Lex (BinOpToken Punct Token)
open SurfaceBridge
open FHM.Bounds (BoundBinding BoundsTy ProgramBoundsAnns BoundsAnnTy)
open FHM.Bounds.Report
open FHM.Bounds.Pipeline

/-- Hover typing environment: let schemes + λ/pattern locals (prepend = shadow). -/
structure HoverEnv where
  lets : List (ValName × PolyTy)
  locals : List (ValName × Ty)

def HoverEnv.empty : HoverEnv := ⟨[], []⟩

def HoverEnv.lookupTy (e : HoverEnv) (n : ValName) : Option Ty :=
  match e.locals.find? (fun p => p.1 == n) with
  | some ⟨_, τ⟩ => some τ
  | none =>
    match e.lets.find? (fun p => p.1 == n) with
    | some ⟨_, σ⟩ => some σ.body
    | none => none

def HoverEnv.extendLocal (e : HoverEnv) (n : ValName) (τ : Ty) : HoverEnv :=
  { e with locals := (n, τ) :: e.locals }

def HoverEnv.extendLocals (e : HoverEnv) (ps : List (ValName × Ty)) : HoverEnv :=
  { e with locals := ps ++ e.locals }

def HoverEnv.extendLets (e : HoverEnv) (ps : List (ValName × PolyTy)) : HoverEnv :=
  { e with lets := ps ++ e.lets }

/-- Best-effort surface expression type (vars, lits, ctors, apps, pairs, …). -/
partial def hoverExprTy (ctors : CtorEnv) (env : HoverEnv) : Surface.Expr → Option Ty
  | .var n => env.lookupTy n
  | .primLit (.int n) => some (PrimLitExpr.ty (.int n))
  | .primLit (.nat n) => some (PrimLitExpr.ty (.nat n))
  | .primLit (.bool _) => some (.customTy nBool [])
  | .primLit (.char c) => some (PrimLitExpr.ty (.char c))
  | .primLit .unit => some (PrimLitExpr.ty .unit)
  | .ctor n =>
      match LookupList.get? ctors n with
      | some ctor => some ctor.toTy.body
      | none => none
  | .pair a b =>
      match hoverExprTy ctors env a, hoverExprTy ctors env b with
      | some ta, some tb => some (.customTy nPair [ta, tb])
      | _, _ => none
  | .cons h _ =>
      match hoverExprTy ctors env h with
      | some th => some (.customTy nList [th])
      | none => none
  | .list (h :: _) =>
      match hoverExprTy ctors env h with
      | some th => some (.customTy nList [th])
      | none => none
  | .list [] => none
  | .ife _ t f =>
      match hoverExprTy ctors env t with
      | some τ => some τ
      | none => hoverExprTy ctors env f
  | .app f x =>
      match f, hoverExprTy ctors env x with
      | .ctor n, some τarg =>
          match LookupList.get? ctors n with
          | some ctor =>
              if ctor.paramCount == 1 && ctor.contents.length == 1 then
                some (.customTy ctor.tyName [τarg])
              else if ctor.paramCount == 0 && ctor.contents.isEmpty then
                some (.customTy ctor.tyName [])
              else
                match hoverExprTy ctors env f with
                | some (.arrow _ b) => some b
                | _ => none
          | none => none
      | _, _ =>
          match hoverExprTy ctors env f with
          | some (.arrow _ b) => some b
          | _ => none
  | .lambda .. => none
  | .letIn .. => none
  | .letRecIn .. => none
  | .match_ .. => none
  | .primBinOp op => PrimBinOp.ty ctors op

/-- Slot types for one pattern's binders in `patVars` order (pad with `none`). -/
def patSlots (ctors : CtorEnv) (pat : Surface.Pattern) (τ? : Option Ty) :
    List (Option Ty) :=
  let ns := patVars pat
  match τ? with
  | none => ns.map fun _ => none
  | some τ =>
      let tys := patBindTys ctors pat τ
      ns.mapIdx fun i _ => tys[i]?

/-- Locals to prepend for a pattern arm when scrutinee type is known. -/
def patLocalPairs (ctors : CtorEnv) (pat : Surface.Pattern) (τ : Ty) :
    List (ValName × Ty) :=
  (patVars pat).zip (patBindTys ctors pat τ)

/-- Residual mono type of a binding RHS after `n` head value-params (arrow peel). -/
def rhsExpectedAfterHead (σ : PolyTy) (nHead : Nat) : Option Ty :=
  let rec go (n : Nat) (τ : Ty) : Option Ty :=
    match n, τ with
    | 0, τ => some τ
    | n + 1, .arrow _ r => go n r
    | _ + 1, _ => none
  go nHead σ.body

/-- First `n` arrow domains of a mono type (scheme body after quantifiers). -/
def peelArrowDoms : Nat → Ty → List Ty
  | 0, _ => []
  | n + 1, .arrow d r => d :: peelArrowDoms n r
  | _ + 1, _ => []

/-- Scheme for a surface let: lowered annotation, else synth RHS, else `none`. -/
def surfaceLetScheme (ctors : CtorEnv) (ke : KindEnv) (env : HoverEnv)
    (ann : Option Surface.PolyTy) (rhs : Surface.Expr) : Option PolyTy :=
  match ann with
  | some σs => lowerPoly ke σs
  | none => (hoverExprTy ctors env rhs).map PolyTy.mkTrivial

def prettyTyName : TyName → String
  | .mk s => s

def prettyCtorName : CtorName → String
  | .mk s => s

/-- Surface `type T a = C … | D …` rendering for hover. -/
def prettySurfaceDataDecl (d : Surface.DataDecl) : String :=
  let params := String.intercalate " " (d.params.map prettyValName)
  let header :=
    if d.params.isEmpty then s!"type {prettyTyName d.name}"
    else s!"type {prettyTyName d.name} {params}"
  let ctorStr (c : CtorName × List Surface.Ty) : String :=
    let ⟨cname, fields⟩ := c
    if fields.isEmpty then prettyCtorName cname
    else prettyCtorName cname ++ " " ++
      String.intercalate " " (fields.map (Surface.Ty.prettyAux 2))
  header ++ " = " ++ String.intercalate " | " (d.ctors.map ctorStr)

/-- Spanned hover symbol (v3): def `span` + lexical `scope`. -/
structure RangedSymbol where
  name : String
  kind : String
  type_ : String
  span : Span
  scope : Span
  deriving Repr, BEq

def RangedSymbol.toJson (s : RangedSymbol) : Lean.Json :=
  Lean.Json.mkObj [
    ("name", Lean.Json.str s.name),
    ("kind", Lean.Json.str s.kind),
    ("type", Lean.Json.str s.type_),
    ("startLine", Lean.Json.num s.span.startLine),
    ("startCol", Lean.Json.num s.span.startCol),
    ("endLine", Lean.Json.num s.span.endLine),
    ("endCol", Lean.Json.num s.span.endCol),
    ("scopeStartLine", Lean.Json.num s.scope.startLine),
    ("scopeStartCol", Lean.Json.num s.scope.startCol),
    ("scopeEndLine", Lean.Json.num s.scope.endLine),
    ("scopeEndCol", Lean.Json.num s.scope.endCol)
  ]

def mkSym (name kind type_ : String) (span scope : Span) : RangedSymbol :=
  { name, kind, type_, span, scope }

/-- Among symbols whose span contains `(line, col)`, pick the **smallest** area;
    tie-break: later (inner) entry wins. -/
def symbolAt (syms : List RangedSymbol) (line col : Nat) : Option RangedSymbol :=
  let hits := syms.filter (fun s => s.span.contains line col)
  match hits with
  | [] => none
  | h :: rest =>
    some <| rest.foldl (fun best s =>
      let aBest := best.span.area
      let aS := s.span.area
      if aS < aBest then s
      else if aS == aBest then s
      else best) h

/-- Use-site: name match + `scope.contains` + non-empty type; smallest scope wins. -/
def symbolAtUseSite (syms : List RangedSymbol) (line col : Nat) (name : String) :
    Option RangedSymbol :=
  let hits := syms.filter fun s =>
    s.name == name && !s.type_.isEmpty && s.scope.contains line col
  match hits with
  | [] => none
  | h :: rest =>
    some <| rest.foldl (fun best s =>
      let aBest := best.scope.area
      let aS := s.scope.area
      if aS < aBest then s
      else if aS == aBest then s
      else best) h

/-! ## Structural hover walk (correct by construction)

One walk of the surface AST + spanned sidecar emits a complete `RangedSymbol`
per binder site (span + type + scope together). Binder spans are consumed in the
**same order the parser emitted them for that AST**, so there is no parallel-stream
zip. Top-level schemes are a name map from inference (SCC order is irrelevant).
-/

/-- Pop the next binder if it has the expected kind. -/
def takeKind (bs : List BinderSpan) (k : BinderKind) :
    Option (BinderSpan × List BinderSpan) :=
  match bs with
  | b :: rest => if b.kind == k then some (b, rest) else none
  | [] => none

/-- Top-level val scopes: each SCC group scopes over its RHSs + remaining program. -/
def collectTopValScopes (p : Surface.Program) (sp : SpannedProgram) : List (ValName × Span) :=
  let bodySpan := sp.body.span
  let rec go (gs : List (List Surface.Binding)) (rss : List (List SpannedExpr)) :
      List (ValName × Span) :=
    match gs, rss with
    | [], _ => []
    | g :: gs', rhss :: rss' =>
        let restSpan :=
          match Span.hull (rss'.flatMap (·.map SpannedExpr.span) ++ [bodySpan]) with
          | some s => s
          | none => bodySpan
        let groupScope :=
          match Span.hull (rhss.map SpannedExpr.span ++ [restSpan]) with
          | some s => s
          | none => restSpan
        g.map (fun b => (b.name, groupScope)) ++ go gs' rss'
    | _, _ => []
  go p.groups sp.groups

def lookupSpan (xs : List (ValName × Span)) (n : ValName) : Option Span :=
  (xs.find? (fun p => p.1 == n)).map (·.2)

def lookupScheme (xs : List (ValName × PolyTy)) (n : ValName) : Option PolyTy :=
  (xs.find? (fun p => p.1 == n)).map (·.2)

def lookupBinding (xs : List Surface.Binding) (n : ValName) : Option Surface.Binding :=
  xs.find? (fun b => b.name == n)

/-- RHS span for a top binding name (SCC-aligned `sp.groups` remapped by name). -/
def topRhsSpan (p : Surface.Program) (sp : SpannedProgram) (n : ValName) : Option SpannedExpr :=
  let flatB := p.groups.flatMap id
  let flatS := sp.groups.flatMap id
  (flatB.zip flatS).find? (fun pair => pair.1.name == n) |>.map (·.2)

def optTyStr : Option Ty → String
  | some τ => τ.pretty
  | none => ""

def optPolyStr : Option PolyTy → String
  | some σ => σ.pretty
  | none => ""

/-- Emit `n` leading binders of kind `k` with a fixed hover label. -/
def takeLabeledBinders (k : BinderKind) (n : Nat) (scope : Span) (label : String)
    (bs : List BinderSpan) : List BinderSpan × List RangedSymbol :=
  let rec go (m : Nat) (bs : List BinderSpan) (acc : List RangedSymbol) :
      List BinderSpan × List RangedSymbol :=
    match m, bs with
    | 0, _ => (bs, acc)
    | m' + 1, _ =>
      match takeKind bs k with
      | some (b, rest) =>
          let sc := b.scope?.getD scope
          go m' rest (acc ++ [mkSym b.name k.toString label b.span sc])
      | none => (bs, acc)
  go n bs []

/-- Emit `n` leading `.param` binders as scheme tyvars. -/
def takeTyVarParams (n : Nat) (scope : Span) (label : String) (bs : List BinderSpan) :
    List BinderSpan × List RangedSymbol :=
  takeLabeledBinders .param n scope label bs

/-- Emit `n` leading `.count` binders from `{n : Nat,…}`. -/
def takeCountParams (n : Nat) (scope : Span) (bs : List BinderSpan) :
    List BinderSpan × List RangedSymbol :=
  takeLabeledBinders .count n scope "count variable (Nat)" bs

/-- Emit head value-params with already-pretty domain strings. -/
def takeHeadValueParamsStr (domStrs : List String) (scope : Span) (bs : List BinderSpan) :
    List BinderSpan × List RangedSymbol :=
  let rec go (ds : List String) (bs : List BinderSpan) (acc : List RangedSymbol) :
      List BinderSpan × List RangedSymbol :=
    match ds, bs with
    | [], _ => (bs, acc)
    | tyStr :: rest, _ =>
      match takeKind bs .param with
      | some (b, bs') =>
          go rest bs' (acc ++ [mkSym b.name "param" tyStr b.span scope])
      | none => (bs, acc)
  go domStrs bs []

/-- Emit head value-params with types from arrow domains (pad short peels). -/
def takeHeadValueParams (doms : List Ty) (scope : Span) (bs : List BinderSpan) :
    List BinderSpan × List RangedSymbol :=
  takeHeadValueParamsStr (doms.map (·.pretty)) scope bs

/-- Head binders of one `Binding` + val def.

`br?` is the assembled `BindingReport` for top-level binders (display + HM).
Nested lets pass `none` and supply `σ?` from surface/Infer synthesis. -/
def hoverBindingHead (env : HoverEnv) (b : Surface.Binding)
    (br? : Option BindingReport) (σ? : Option PolyTy)
    (valScope : Span) (bs : List BinderSpan) :
    List BinderSpan × List RangedSymbol × HoverEnv :=
  match takeKind bs .val with
  | none => (bs, [], env)
  | some (vb, bs1) =>
      let σ? := match br? with | some br => some br.hm | none => σ?
      let valTy :=
        match br? with
        | some br => br.pretty
        | none => optPolyStr σ?
      let valSym := mkSym vb.name "val" valTy vb.span valScope
      let nAnn := match b.ann with | some σ => σ.foralls.length | none => 0
      -- Parse order: val, tyParams, header value-params, scheme ann (count then type
      -- foralls), then RHS binders — see `letBinding` in Surface/Parse.
      let (bs2, tySyms) :=
        takeTyVarParams b.tyParams.length valScope "type variable (scheme binder)" bs1
      -- Display domains from report when present; HM peel for env locals always.
      let domStrs :=
        match br? with
        | some br => br.headParamDoms b.params.length
        | none =>
            let doms :=
              match σ? with
              | some σ => peelArrowDoms b.params.length σ.body
              | none => []
            let doms' :=
              if doms.length < b.params.length then
                doms ++ List.replicate (b.params.length - doms.length) (.prim .unit)
              else
                doms.take b.params.length
            doms'.map (·.pretty)
      let domsTy : List Ty :=
        let doms :=
          match σ? with
          | some σ => peelArrowDoms b.params.length σ.body
          | none => []
        if doms.length < b.params.length then
          doms ++ List.replicate (b.params.length - doms.length) (.prim .unit)
        else
          doms.take b.params.length
      let (bs3, headSyms) := takeHeadValueParamsStr domStrs valScope bs2
      let (bs3c, countSyms) := takeCountParams b.natBinders.length valScope bs3
      let (bs4, annSyms) :=
        takeTyVarParams nAnn valScope "type variable (scheme binder)" bs3c
      let headLocals : List (ValName × Ty) :=
        b.params.map (·.1) |>.zip domsTy
      let env' := env.extendLocals headLocals
      let env'' :=
        match σ? with
        | some σ => env'.extendLets [(b.name, σ)]
        | none => env'
      (bs4, valSym :: countSyms ++ tySyms ++ headSyms ++ annSyms, env'')

/-- Structural walk: each binder site emits a full symbol. Consumes `bs` in parse order.

`expectedβ`: optional bounds ascription residual (after head-param peel). When set,
λ params prefer `BL …` display over HM `List …` (T1 / colon-form `\xs ->`). -/
partial def hoverWalkExpr (ctors : CtorEnv) (ke : KindEnv) (env : HoverEnv)
    (expected : Option Ty) (expectedβ : Option BoundsAnnTy) :
    Surface.Expr → SpannedExpr → List BinderSpan → List BinderSpan × List RangedSymbol
  | .lambda (.name n) _ body, .lambda _ bodyS, bs =>
      let τDom := match expected with | some (.arrow a _) => some a | _ => none
      let τCod := match expected with | some (.arrow _ b) => some b | _ => none
      let βDomPretty :=
        match expectedβ with
        | some (.arrow d _) => some (BoundsAnnTy.pretty d)
        | _ => none
      let βCod :=
        match expectedβ with
        | some (.arrow _ c) => some c
        | _ => none
      match takeKind bs .param with
      | some (b, rest) =>
          let tyStr :=
            match βDomPretty with
            | some s => s
            | none => optTyStr τDom
          let sym := mkSym b.name "param" tyStr b.span bodyS.span
          let env' :=
            match τDom with
            | some τ => env.extendLocal n τ
            | none => env
          let (rest', syms) := hoverWalkExpr ctors ke env' τCod βCod body bodyS rest
          (rest', sym :: syms)
      | none => hoverWalkExpr ctors ke env none none body bodyS bs
  | .lambda .wildcard _ body, .lambda _ bodyS, bs =>
      let τCod := match expected with | some (.arrow _ b) => some b | _ => none
      let βCod :=
        match expectedβ with
        | some (.arrow _ c) => some c
        | _ => none
      hoverWalkExpr ctors ke env τCod βCod body bodyS bs
  | .lambda _ _ body, .lambda _ bodyS, bs =>
      hoverWalkExpr ctors ke env none none body bodyS bs
  | .letIn name tyParams params ann rhs body, .letIn _ rhsS bodyS, bs =>
      -- Always synth this binding (ann / RHS). Do **not** look up `name` in
      -- `env.lets` — an outer same-named let would steal the scheme (shadowing).
      let σ? := surfaceLetScheme ctors ke env ann rhs
      let bind : Surface.Binding := { name, tyParams, params, ann, rhs }
      let (bs1, headSyms, envRhs) :=
        hoverBindingHead env bind none σ? bodyS.span bs
      let rhsExp :=
        match σ? with
        | some σ => rhsExpectedAfterHead σ params.length
        | none => none
      let (bs2, rhsSyms) := hoverWalkExpr ctors ke envRhs rhsExp none rhs rhsS bs1
      let envBody :=
        match σ? with
        | some σ => env.extendLets [(name, σ)]
        | none => env
      let (bs3, bodySyms) :=
        hoverWalkExpr ctors ke envBody expected expectedβ body bodyS bs2
      (bs3, headSyms ++ rhsSyms ++ bodySyms)
  | .letRecIn binds body, .letRecIn _ rhss bodyS, bs =>
      -- Synthesize schemes for the group, extend env, then each binding head+RHS.
      let pairs : List (ValName × Option PolyTy) :=
        binds.map fun b => (b.name, surfaceLetScheme ctors ke env b.ann b.rhs)
      let envBinds :=
        env.extendLets (pairs.filterMap fun ⟨n, σ?⟩ => σ?.map fun σ => (n, σ))
      let groupScope :=
        match Span.hull (rhss.map SpannedExpr.span ++ [bodyS.span]) with
        | some s => s
        | none => bodyS.span
      let rec goBinds
          (bsLeft : List BinderSpan)
          (bspecs : List Surface.Binding)
          (rss : List SpannedExpr)
          (acc : List RangedSymbol) :
          List BinderSpan × List RangedSymbol :=
        match bspecs, rss with
        | b :: bs', sRhs :: rss' =>
            let σ? := (pairs.find? (fun p => p.1 == b.name)).bind (·.2)
            let (bs1, headSyms, envRhs) :=
              hoverBindingHead envBinds b none σ? groupScope bsLeft
            let rhsExp :=
              match σ? with
              | some σ => rhsExpectedAfterHead σ b.params.length
              | none => none
            let (bs2, rhsSyms) :=
              hoverWalkExpr ctors ke envRhs rhsExp none b.rhs sRhs bs1
            goBinds bs2 bs' rss' (acc ++ headSyms ++ rhsSyms)
        | _, _ => (bsLeft, acc)
      let (bs1, bindSyms) := goBinds bs binds rhss []
      let (bs2, bodySyms) :=
        hoverWalkExpr ctors ke envBinds expected expectedβ body bodyS bs1
      (bs2, bindSyms ++ bodySyms)
  | .app f x, .app _ fS xS, bs =>
      let (bs1, fSyms) := hoverWalkExpr ctors ke env none none f fS bs
      let xExp :=
        match hoverExprTy ctors env f with
        | some (.arrow a _) => some a
        | _ => none
      let (bs2, xSyms) := hoverWalkExpr ctors ke env xExp none x xS bs1
      (bs2, fSyms ++ xSyms)
  | .pair a b, .pair _ aS bS, bs =>
      let (bs1, aSyms) := hoverWalkExpr ctors ke env none none a aS bs
      let (bs2, bSyms) := hoverWalkExpr ctors ke env none none b bS bs1
      (bs2, aSyms ++ bSyms)
  | .cons h t, .cons _ hS tS, bs =>
      let (bs1, hSyms) := hoverWalkExpr ctors ke env none none h hS bs
      let (bs2, tSyms) := hoverWalkExpr ctors ke env none none t tS bs1
      (bs2, hSyms ++ tSyms)
  | .list items, .list _ itemSs, bs =>
      let rec go (bs : List BinderSpan) (es : List Surface.Expr)
          (ss : List SpannedExpr) (acc : List RangedSymbol) :
          List BinderSpan × List RangedSymbol :=
        match es, ss with
        | e :: es', s :: ss' =>
            let (bs', syms) := hoverWalkExpr ctors ke env none none e s bs
            go bs' es' ss' (acc ++ syms)
        | _, _ => (bs, acc)
      go bs items itemSs []
  | .match_ scrut arms, .match_ _ scrutS armSs, bs =>
      let (bs1, scrutSyms) := hoverWalkExpr ctors ke env none none scrut scrutS bs
      let τScrut := hoverExprTy ctors env scrut
      let rec goArms (bs : List BinderSpan)
          (as : List (Surface.Pattern × Surface.Expr))
          (ss : List SpannedExpr) (acc : List RangedSymbol) :
          List BinderSpan × List RangedSymbol :=
        match as, ss with
        | ⟨pat, body⟩ :: as', bodyS :: ss' =>
            let ns := patVars pat
            let slots := patSlots ctors pat τScrut
            let rec takePats (bs : List BinderSpan) (ns : List ValName)
                (slots : List (Option Ty)) (acc : List RangedSymbol) :
                List BinderSpan × List RangedSymbol :=
              match ns, slots with
              | _ :: ns', τ? :: slots' =>
                  match takeKind bs .pat with
                  | some (b, rest) =>
                      takePats rest ns' slots'
                        (acc ++ [mkSym b.name "pat" (optTyStr τ?) b.span bodyS.span])
                  | none => (bs, acc)
              | _ :: ns', [] =>
                  match takeKind bs .pat with
                  | some (b, rest) =>
                      takePats rest ns' []
                        (acc ++ [mkSym b.name "pat" "" b.span bodyS.span])
                  | none => (bs, acc)
              | _, _ => (bs, acc)
            let (bs2, patSyms) := takePats bs ns slots []
            let envArm :=
              match τScrut with
              | some τ => env.extendLocals (patLocalPairs ctors pat τ)
              | none => env
            let (bs3, bodySyms) :=
              hoverWalkExpr ctors ke envArm none none body bodyS bs2
            goArms bs3 as' ss' (acc ++ patSyms ++ bodySyms)
        | _, _ => (bs, acc)
      let (bs2, armSyms) := goArms bs1 arms armSs []
      (bs2, scrutSyms ++ armSyms)
  | .ife c t f, .ife _ cS tS fS, bs =>
      let (bs1, cSyms) := hoverWalkExpr ctors ke env none none c cS bs
      let (bs2, tSyms) := hoverWalkExpr ctors ke env none none t tS bs1
      let (bs3, fSyms) := hoverWalkExpr ctors ke env none none f fS bs2
      (bs3, cSyms ++ tSyms ++ fSyms)
  | _, _, bs => (bs, [])

/-- Type / ctor / typaram symbols from surface data decls (parse order). -/
def hoverDecls (ctors : CtorEnv) (decls : List Surface.DataDecl)
    (declScopes : List Span) (programScope : Span) (bs : List BinderSpan) :
    List BinderSpan × List RangedSymbol :=
  Id.run do
    let mut bs := bs
    let mut out : List RangedSymbol := []
    let mut di : Nat := 0
    for d in decls do
      let typeStr := prettySurfaceDataDecl d
      let typeName := prettyTyName d.name
      let declScope := declScopes[di]?.getD programScope
      di := di + 1
      match takeKind bs .type with
      | some (b, rest) =>
        bs := rest
        out := out ++ [mkSym b.name "type" typeStr b.span programScope]
      | none => pure ()
      for _ in d.params do
        match takeKind bs .param with
        | some (b, rest) =>
          bs := rest
          out := out ++ [
            mkSym b.name "param" s!"type variable (of {typeName})" b.span declScope
          ]
        | none => pure ()
      for ⟨cname, _⟩ in d.ctors do
        let ctorTy :=
          match LookupList.get? ctors cname with
          | some ctor => ctor.toTy.pretty
          | none => prettyCtorName cname
        match takeKind bs .ctor with
        | some (b, rest) =>
          bs := rest
          out := out ++ [mkSym b.name "ctor" ctorTy b.span programScope]
        | none => pure ()
    return (bs, out)

/-- Leftover binders (parse/walk mismatch): emit with def-only scope, empty type. -/
def hoverLeftoverBinders (bs : List BinderSpan) : List RangedSymbol :=
  bs.map fun b =>
    let sc := b.scope?.getD b.span
    let typeStr :=
      if b.kind == .param && b.scope?.isSome then "type variable (scheme binder)"
      else if b.kind == .count && b.scope?.isSome then "count variable (Nat)"
      else ""
    mkSym b.name b.kind.toString typeStr b.span sc

/-- Build all binder hover symbols by walking decls + **source-order** tops + body. -/
def buildHoverSymbols (ctors : CtorEnv) (ke : KindEnv) (p : Surface.Program)
    (sp : SpannedProgram) (binders : List BinderSpan)
    (report : ProgramReport) (programScope : Span) :
    List RangedSymbol :=
  let flatBinds := p.groups.flatMap id
  let topScopes := collectTopValScopes p sp
  let env0 : HoverEnv := {
    lets := report.bindings.map fun b => (b.name, b.hm)
    locals := []
  }
  let (bs1, declSyms) := hoverDecls ctors p.decls sp.declSpans programScope binders
  -- Source-order top bindings (pre-SCC). Fall back to group flatten if missing.
  let sourceNames :=
    if sp.sourceNames.isEmpty then
      flatBinds.map fun b => match b.name with | .mk s => s
    else
      sp.sourceNames
  let rec goTops (names : List String) (bs : List BinderSpan)
      (acc : List RangedSymbol) : List BinderSpan × List RangedSymbol :=
    match names with
    | [] =>
        let (bs', bodySyms) :=
          hoverWalkExpr ctors ke env0 none none p.body sp.body bs
        (bs', acc ++ bodySyms)
    | nm :: nms =>
        let n : ValName := .mk nm
        match lookupBinding flatBinds n with
        | none => goTops nms bs acc
        | some b =>
            let br? := report.find? n
            let σ? := br?.map (·.hm)
            let valScope := (lookupSpan topScopes n).getD programScope
            let sRhs := (topRhsSpan p sp n).getD (.leaf Span.empty)
            let (bsH, headSyms, envRhs) :=
              hoverBindingHead env0 b br? σ? valScope bs
            let rhsExp :=
              match σ? with
              | some σ => rhsExpectedAfterHead σ b.params.length
              | none => none
            let rhsβ := br?.bind fun br => br.rhsBoundsAfterHead b.params.length
            let (bsR, rhsSyms) :=
              hoverWalkExpr ctors ke envRhs rhsExp rhsβ b.rhs sRhs bsH
            goTops nms bsR (acc ++ headSyms ++ rhsSyms)
  let (bs2, restSyms) := goTops sourceNames bs1 []
  declSyms ++ restSyms ++ hoverLeftoverBinders bs2

/-- Hull covering decls, binders, and the program body (global type/ctor scope). -/
def programWideScope (binders : List BinderSpan) (sp : SpannedProgram) : Span :=
  let spans :=
    binders.map (·.span) ++
      sp.groups.flatMap (·.map SpannedExpr.span) ++ [sp.body.span]
  (Span.hull spans).getD sp.body.span

/-- Pretty-print a Core `DataDecl` (prelude types have no surface binder spans). -/
def prettyCoreDataDecl (d : DataDecl) : String :=
  let params := String.intercalate " " ((List.range d.paramCount).map prettyTyVarName)
  let header :=
    if d.paramCount == 0 then s!"type {prettyTyName d.name}"
    else s!"type {prettyTyName d.name} {params}"
  let ctorStr (c : CtorName × List Ty) : String :=
    let ⟨cname, fields⟩ := c
    if fields.isEmpty then prettyCtorName cname
    else prettyCtorName cname ++ " " ++
      String.intercalate " " (fields.map (fun τ => Ty.prettyAux 2 τ))
  header ++ " = " ++ String.intercalate " | " (d.ctors.map ctorStr)

/-- Prelude type/ctor symbols for use-site only (`span` empty so they never
    steal def-site hits; `scope` is program-wide). -/
def preludeTypeCtorSymbols (ctors : CtorEnv) (scope : Span) : List RangedSymbol :=
  preludeDecls.flatMap fun d =>
    let typeSym : RangedSymbol := {
      name := prettyTyName d.name, kind := "type",
      type_ := prettyCoreDataDecl d,
      span := Span.empty, scope := scope
    }
    let ctorSyms := d.ctors.map fun ⟨cname, _⟩ =>
      let tyStr :=
        match LookupList.get? ctors cname with
        | some ctor => ctor.toTy.pretty
        | none => prettyCtorName cname
      ({
        name := prettyCtorName cname, kind := "ctor", type_ := tyStr,
        span := Span.empty, scope := scope
      } : RangedSymbol)
    typeSym :: ctorSyms

/-- Map surface binop token to Core primop (same table as `Parse.applyBinOp`). -/
def binOpPrimTy (ctors : CtorEnv) : BinOpToken → Option (String × String)
  | .plus =>
      (PrimBinOp.ty ctors .intAdd).map fun τ => ("+", τ.pretty)
  | .minus =>
      (PrimBinOp.ty ctors .intSub).map fun τ => ("-", τ.pretty)
  | .lt =>
      (PrimBinOp.ty ctors .intLt).map fun τ => ("<", τ.pretty)
  | .cons =>
      match LookupList.get? ctors cCons with
      | some ctor => some ("::", ctor.toTy.pretty)
      | none => none

/-- Lit / op hover symbols from a re-lex of `src` (token spans; Core types).
    Adjacent `(` `)` tokens become one unit lit (lexer emits two puncts). -/
def collectLitOpSymbols (src : String) (ctors : CtorEnv) : List RangedSymbol :=
  match Surface.Lex.lex src with
  | .error _ => []
  | .ok toks =>
    Id.run do
      let mut out : List RangedSymbol := []
      let mut i : Nat := 0
      while h : i < toks.size do
        let t := toks[i]
        match t.token with
        | .punct .lparen =>
          if h2 : i + 1 < toks.size then
            let t2 := toks[i + 1]
            if t2.token == .punct .rparen then
              let sp := Span.union (Span.ofTok t) (Span.ofTok t2)
              out := out ++ [{
                name := "()", kind := "lit",
                type_ := (PrimLitExpr.ty .unit).pretty,
                span := sp, scope := sp
              }]
              i := i + 2
            else
              i := i + 1
          else
            i := i + 1
        | .intLit n =>
          let sp := Span.ofTok t
          out := out ++ [{
            name := toString n, kind := "lit",
            type_ := (PrimLitExpr.ty (.int n)).pretty,
            span := sp, scope := sp
          }]
          i := i + 1
        | .charLit c =>
          let sp := Span.ofTok t
          out := out ++ [{
            name := prettyPrimLit (.char c), kind := "lit",
            type_ := (PrimLitExpr.ty (.char c)).pretty,
            span := sp, scope := sp
          }]
          i := i + 1
        | .boolLit b =>
          let sp := Span.ofTok t
          out := out ++ [{
            name := if b then "True" else "False", kind := "lit",
            type_ := (Ty.customTy nBool []).pretty,
            span := sp, scope := sp
          }]
          i := i + 1
        | .op o =>
          let sp := Span.ofTok t
          match binOpPrimTy ctors o with
          | some (nm, tyStr) =>
            out := out ++ [{ name := nm, kind := "op", type_ := tyStr, span := sp, scope := sp }]
          | none => pure ()
          i := i + 1
        | _ =>
          i := i + 1
      return out

/-- One editor diagnostic (1-based half-open span, same as parse / hover symbols). -/
structure HoverDiag where
  message : String
  line : Nat := 1
  col : Nat := 1
  endLine : Nat := 1
  endCol : Nat := 2
  deriving Repr

def HoverDiag.toJson (d : HoverDiag) : Lean.Json :=
  Lean.Json.mkObj [
    ("severity", Lean.Json.str "error"),
    ("message", Lean.Json.str d.message),
    ("line", Lean.Json.num d.line),
    ("col", Lean.Json.num d.col),
    ("endLine", Lean.Json.num d.endLine),
    ("endCol", Lean.Json.num d.endCol)
  ]

/-- Successful lower+infer hover report. Bounds failures stay here as diagnostics
so symbols remain available (ascription/HM pretty) while LSP surfaces the error. -/
structure HoverReport where
  symbols : List RangedSymbol
  programTy : String
  diagnostics : List HoverDiag := []
  deriving Repr

/-- Ident-shaped binder name (surface value names; reject prose like `scrutinee`). -/
def isBinderIdentName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
      (c.isAlpha || c == '_') &&
        cs.all fun d => d.isAlphanum || d == '_' || d == '\''

/-- Extract binder name from structured Check prefixes only.
Do **not** split on arbitrary `" for "` (false positives: `scrutinee`, `synth`). -/
def binderNameFromBoundsMsg (msg : String) : Option String :=
  let tryPref (pref : String) : Option String :=
    if msg.startsWith pref then
      let rest := msg.drop pref.length
      let tok := (rest.splitOn " ").headD ""
      let name := (tok.splitOn "(").headD ""
      if isBinderIdentName name then some name else none
    else none
  match tryPref "bounds: error for " with
  | some n => some n
  | none =>
    match tryPref "bounds: ascription not met for " with
    | some n => some n
    | none => tryPref "bounds: scheme ascription for "

/-- Shallow: body is a top-level `match`, else full body hull (body-level diags). -/
def bodyDiagSpan (body : SpannedExpr) : Span :=
  match body with
  | .match_ s _ _ => s
  | _ => body.span

/-- Val binder def-site span by surface name. -/
def valBinderSpan (binders : List BinderSpan) (n : String) : Option Span :=
  (binders.find? fun b => b.kind == .val && b.name == n).map (·.span)

/-- Diagnostic extent for a top binding: prefer the **RHS** expression span
(`f e`, not `baaaad : … = f e`). Fall back to the binder name if RHS missing. -/
def bindingExtentSpan (binders : List BinderSpan) (p : Surface.Program)
    (sp : SpannedProgram) (n : String) : Option Span :=
  match (topRhsSpan p sp (.mk n)).map (·.span) with
  | some s => some s
  | none => valBinderSpan binders n

/-- First source occurrence of identifier `name` (1-based half-open token span). -/
def firstIdentSpan (src : String) (name : String) : Option Span :=
  match Surface.Lex.lex src with
  | .error _ => none
  | .ok toks =>
    Id.run do
      for t in toks do
        match t.token with
        | .ident raw _ =>
          if raw == name then return some (Span.ofTok t)
        | _ => pure ()
      return none

/-- Diagnostic covering a `Span` (or a single-column file-top fallback). -/
def diagAtSpan (msg : String) (s? : Option Span) : HoverDiag :=
  match s? with
  | some s =>
      { message := msg, line := s.startLine, col := s.startCol,
        endLine := s.endLine, endCol := s.endCol }
  | none => { message := msg, line := 1, col := 1, endLine := 1, endCol := 2 }

/-- Best-effort span for a bounds message: binding extent (name∪RHS), else body
hull / match, else file top.
Returns half-open `(startLine, startCol, endLine, endCol)`. -/
def spanForBoundsMsg (binders : List BinderSpan) (p : Surface.Program)
    (sp : SpannedProgram) (msg : String)
    (fallback : Option Span := none) : Nat × Nat × Nat × Nat :=
  match binderNameFromBoundsMsg msg with
  | some n =>
      match bindingExtentSpan binders p sp n with
      | some s => (s.startLine, s.startCol, s.endLine, s.endCol)
      | none =>
          match fallback with
          | some s => (s.startLine, s.startCol, s.endLine, s.endCol)
          | none => (1, 1, 1, 2)
  | none =>
      match fallback with
      | some s => (s.startLine, s.startCol, s.endLine, s.endCol)
      | none => (1, 1, 1, 2)

def boundsDiag (binders : List BinderSpan) (p : Surface.Program)
    (sp : SpannedProgram) (msg : String)
    (fallback : Option Span := none) : HoverDiag :=
  let (line, col, endLine, endCol) := spanForBoundsMsg binders p sp msg fallback
  { message := msg, line, col, endLine, endCol }

/-! ## Canonical BL presentation

The verified checker reports `BoundsTy` at Core paths.  This unverified layer
only joins those reports back to source IDs and chooses readable source names;
it never participates in acceptance. -/

namespace BLDisplay

open FHM.Bounds
open SurfaceBridge.Provenance

abbrev CountAliases := List (Nat × String)

structure Checked where
  body : BoundsTy
  reports : List FHM.Bounds.Found.NodeReport

def check (typed : TypedLowered) : Except String Checked := do
  let (result, reports) ← FHM.Bounds.RecursiveFound.synthNodes typed
  pure ⟨result.bounds, reports⟩

def countAliases (typed : TypedLowered) : CountAliases :=
  typed.lowering.counts.telescopes.flatMap fun telescope =>
    telescope.binders.map fun (name, id) => (id, prettyValName name)

def countName (aliases : CountAliases) (v : Var) : String :=
  match v.kind with
  | .inferable =>
      "?" ++ ((aliases.find? (fun p : Nat × String => p.1 == v.idx)).map (·.2)).getD s!"n{v.idx}"
  | .rigid => (aliases.find? (fun p => p.1 == v.idx)).map (·.2) |>.getD s!"n{v.idx}"

partial def count (aliases : CountAliases) : Count → String
  | .lit n => toString n
  | .inf => "∞"
  | .var v => countName aliases v
  | .add a b => s!"({count aliases a} + {count aliases b})"
  | .mul a b => s!"({count aliases a} * {count aliases b})"
  | .pred a => s!"(pred {count aliases a})"
  | .min a b => s!"(min {count aliases a} {count aliases b})"
  | .max a b => s!"(max {count aliases a} {count aliases b})"

def slot (aliases : CountAliases) : CountSlot → String
  | .hole => "_"
  | .solid c => count aliases c

mutual
partial def boundsAux (ctx : FHM.Unverified.HMDisplay.Context) (aliases : CountAliases)
    (prec : Nat) : BoundsTy → String
  | .prim p => prettyPrimTy p
  | .bvar i => ctx.boundNames[i]?.getD (prettyTyVarName i)
  | .fvar i => FHM.Unverified.HMDisplay.freeName ctx i
  | .arrow a b => prettyParenIf (prec ≥ 1)
      (boundsAux ctx aliases 1 a ++ " → " ++ boundsAux ctx aliases 0 b)
  | .list lo hi e => prettyParenIf (prec ≥ 2)
      ("BL " ++ count aliases lo ++ " " ++ count aliases hi ++ " " ++
        boundsAux ctx aliases 2 e)
  | .custom (.mk "Pair") [a, b] =>
      "(" ++ boundsAux ctx aliases 0 a ++ ", " ++ boundsAux ctx aliases 0 b ++ ")"
  | .custom (.mk name) args =>
      if args.isEmpty then name
      else prettyParenIf (prec ≥ 2)
        (name ++ " " ++ String.intercalate " " (boundsArgs ctx aliases args))

partial def boundsArgs (ctx : FHM.Unverified.HMDisplay.Context) (aliases : CountAliases) :
    List BoundsTy → List String
  | [] => []
  | a :: rest => boundsAux ctx aliases 2 a :: boundsArgs ctx aliases rest
end

mutual
partial def tyAux (ctx : FHM.Unverified.HMDisplay.Context) (aliases : CountAliases)
    (prec : Nat) : Ty → String
  | .prim p => prettyPrimTy p
  | .bvar i => ctx.boundNames[i]?.getD (prettyTyVarName i)
  | .fvar i => FHM.Unverified.HMDisplay.freeName ctx i
  | .arrow a b => prettyParenIf (prec ≥ 1)
      (tyAux ctx aliases 1 a ++ " → " ++ tyAux ctx aliases 0 b)
  | .bl lo hi e => prettyParenIf (prec ≥ 2)
      ("BL " ++ slot aliases lo ++ " " ++ slot aliases hi ++ " " ++ tyAux ctx aliases 2 e)
  | .customTy (.mk "Pair") [a, b] =>
      "(" ++ tyAux ctx aliases 0 a ++ ", " ++ tyAux ctx aliases 0 b ++ ")"
  | .customTy (.mk name) args =>
      if args.isEmpty then name
      else prettyParenIf (prec ≥ 2)
        (name ++ " " ++ String.intercalate " " (tyArgs ctx aliases args))

partial def tyArgs (ctx : FHM.Unverified.HMDisplay.Context) (aliases : CountAliases) :
    List Ty → List String
  | [] => []
  | a :: rest => tyAux ctx aliases 2 a :: tyArgs ctx aliases rest
end

def bounds (ctx : FHM.Unverified.HMDisplay.Context) (aliases : CountAliases)
    (β : BoundsTy) : String :=
  boundsAux { ctx with freeIds :=
    (ctx.freeIds ++ (FHM.Bounds.Synth.BoundsTy.toTy β).freeVars).eraseDups } aliases 0 β

/- Canonical Bounds checking may reindex its locally opened type variables.
Align them structurally with the HM type reported at the same Core node, whose
IDs are already related to source signature names by `HMDisplay.scopes`. -/
mutual
partial def alignTypeNames (ctx : FHM.Unverified.HMDisplay.Context) :
    Ty → BoundsTy → List (Nat × String)
  | .fvar hmId, .fvar boundsId => [(boundsId, FHM.Unverified.HMDisplay.freeName ctx hmId)]
  | .arrow ha hb, .arrow ba bb =>
      alignTypeNames ctx ha ba ++ alignTypeNames ctx hb bb
  | .bl _ _ he, .list _ _ be => alignTypeNames ctx he be
  | .customTy hn hargs, .custom bn bargs =>
      if hn == bn then alignTypeNameArgs ctx hargs bargs else []
  | _, _ => []

partial def alignTypeNameArgs (ctx : FHM.Unverified.HMDisplay.Context) :
    List Ty → List BoundsTy → List (Nat × String)
  | h :: hs, b :: bs => alignTypeNames ctx h b ++ alignTypeNameArgs ctx hs bs
  | _, _ => []
end

def boundsAtHM (ctx : FHM.Unverified.HMDisplay.Context) (aliases : CountAliases)
    (hm : Ty) (β : BoundsTy) : String :=
  bounds { ctx with aliases := (alignTypeNames ctx hm β ++ ctx.aliases).eraseDups }
    aliases β

mutual
partial def alignDeclaredNames (names : List String) : BoundsTy → Ty → List (Nat × String)
  | .fvar boundsId, .bvar binder =>
      (names[binder]?).toList.map fun name => (boundsId, name)
  | .arrow ba bb, .arrow ha hb =>
      alignDeclaredNames names ba ha ++ alignDeclaredNames names bb hb
  | .list _ _ be, .bl _ _ he => alignDeclaredNames names be he
  | .custom bn bargs, .customTy hn hargs =>
      if bn == hn then alignDeclaredNameArgs names bargs hargs else []
  | _, _ => []

partial def alignDeclaredNameArgs (names : List String) :
    List BoundsTy → List Ty → List (Nat × String)
  | b :: bs, h :: hs => alignDeclaredNames names b h ++ alignDeclaredNameArgs names bs hs
  | _, _ => []
end

def declaredTypeAliases (typed : TypedLowered)
    (locations : FHM.Unverified.HMArtifacts.Locations)
    (reports : List FHM.Bounds.Found.NodeReport) (path : CorePath) : List (Nat × String) :=
  locations.displays.flatMap fun display =>
    match FHM.Unverified.HMDisplay.rhsPath typed display.site,
        FHM.Unverified.HMArtifacts.declaredScheme typed display.site with
    | some root, some sig =>
        if root.isPrefixOf path then
          match reports.find? (fun report => report.node.path == root) with
          | some report =>
              match report.node.bounds with
              | some β => alignDeclaredNames display.names β sig.body
              | none => []
          | none => []
        else []
    | _, _ => []

def displayContext (typed : TypedLowered) (scopes : List FHM.Unverified.HMDisplay.Scope)
    (locations : FHM.Unverified.HMArtifacts.Locations)
    (reports : List FHM.Bounds.Found.NodeReport) (path : CorePath) (hm : Ty) :
    FHM.Unverified.HMDisplay.Context :=
  let ctx := FHM.Unverified.HMDisplay.context scopes path hm
  { ctx with aliases := (declaredTypeAliases typed locations reports path ++ ctx.aliases).eraseDups }

def scheme (ctx : FHM.Unverified.HMDisplay.Context) (aliases : CountAliases)
    (names : List String) (sig : PolyTy) : String :=
  let names := if names.length == sig.paramCount then names
    else (List.range sig.paramCount).map FHM.Unverified.HMDisplay.alphaName
  let body := tyAux { ctx with boundNames := names ++ ctx.boundNames } aliases 0 sig.body
  if names.isEmpty then body else "∀ " ++ String.intercalate " " names ++ ". " ++ body

def atPath? (reports : List FHM.Bounds.Found.NodeReport) (path : CorePath) :
    Option (Ty × BoundsTy) := do
  let report ← reports.find? fun report => report.node.path == path
  let β ← report.node.bounds
  pure (report.node.hm, β)

def source? (reports : List FHM.Bounds.Found.NodeReport) (id : SourceId) :
    Option (CorePath × Ty × BoundsTy) := do
  let report ← reports.find? fun report =>
    report.origin.source.id == id && match report.origin.kind with
      | .authored => true
      | .generated _ => false
  let β ← report.node.bounds
  pure (report.node.path, report.node.hm, β)

def sourceType (typed : TypedLowered) (scopes : List FHM.Unverified.HMDisplay.Scope)
    (locations : FHM.Unverified.HMArtifacts.Locations)
    (reports : List FHM.Bounds.Found.NodeReport) (id : SourceId) : Option String := do
  let (path, hm, β) ← source? reports id
  let ctx := displayContext typed scopes locations reports path hm
  pure (boundsAtHM ctx (countAliases typed) hm β)

def binderType (typed : TypedLowered) (scopes : List FHM.Unverified.HMDisplay.Scope)
    (locations : FHM.Unverified.HMArtifacts.Locations)
    (reports : List FHM.Bounds.Found.NodeReport) (site : SurfaceBinderSite) : Option String :=
  let aliases := countAliases typed
  let names := ((locations.displays.find? fun d => d.site == site).map (·.names)).getD []
  match FHM.Unverified.HMArtifacts.declaredScheme typed site with
  | some sig =>
      let path := (FHM.Unverified.HMDisplay.rhsPath typed site).getD []
      let outerScopes := scopes.filter fun s => s.path != path
      some (scheme (FHM.Unverified.HMDisplay.context outerScopes path sig.body) aliases names sig)
  | none => do
      let (_, target) ← typed.lowering.binderTargets.find? (fun p => p.1 == site)
      let sites ← match target with | .present sites => some sites | .absent _ => none
      let core ← sites.head?
      let path ← match core with
        | .letIn path => some (path ++ [.letRhs])
        | .letRec path member => some (path ++ [.letRecRhs member])
        | .lambda path => some path
        | _ => none
      let (hm, β) ← atPath? reports path
      let ctx := displayContext typed scopes locations reports path hm
      match core, hm, β with
      | .lambda _, .arrow hmDomain _, .arrow boundsDomain _ =>
          pure (boundsAtHM ctx aliases hmDomain boundsDomain)
      | _, _, _ => pure (boundsAtHM ctx aliases hm β)

end BLDisplay

/-- Infer Core spine + body type for a surface term under `ctors`, if possible.
The runnable term is the ERASED source (`eOut`/elaboration is gone). -/
def hmInfer (ctors : CtorEnv) (term : Surface.Expr) : Option (Expr × Ty) :=
  match lower ctors term with
  | none => none
  | some c =>
    match infer c.freshFloor ⟨[], ctors⟩ c with
    | some (_, _, τ) => some (c, τ)
    | none => none

/-- Does lower + InferW succeed on this surface term under `ctors`? -/
def hmSucceeds (ctors : CtorEnv) (term : Surface.Expr) : Bool :=
  (hmInfer ctors term).isSome

/-- Pretty surface name. -/
def prettySurfaceName : ValName → String
  | .mk s => s

/-- Clear a binding's HM ascription (keep params / RHS) for mismatch recovery. -/
def stripBindingAnn (b : Surface.Binding) : Surface.Binding :=
  { b with ann := none }

/-- Best-effort "expected vs got" when a binder with an ascription fails HM.
Strip that binder's ann, re-infer; if the RHS types, compare schemes. -/
def explainTypeMismatch (ctors : CtorEnv) (ke : KindEnv)
    (acc : List (List Surface.Binding)) (g : List Surface.Binding)
    (b : Surface.Binding) : String :=
  let nm := prettySurfaceName b.name
  match b.ann with
  | none => s!"typechecking failed in `{nm}`"
  | some σs =>
      let σs := (finalizeAnn b.tyParams b.params (some σs)).getD σs
      let wantStr :=
        match lowerPoly ke σs with
        | some σ => FHM.Unverified.HMDisplay.scheme {} (σs.foralls.map prettyValName) σ
        | none => Surface.PolyTy.pretty σs
      let g' := g.map fun b' =>
        if b'.name == b.name then stripBindingAnn b' else b'
      let probe := Surface.desugarGroups (acc ++ [g']) (.var b.name)
      match hmInfer ctors probe with
      | none =>
          s!"typechecking failed in `{nm}` (ascribed {wantStr}; RHS also fails without ascription)"
      | some (_, ty) =>
          let got := genScheme [] [] ty
          let gotStr := FHM.Unverified.HMDisplay.scheme {} [] got
          s!"type mismatch in `{nm}`: expected {wantStr}, got {gotStr}"

/-- Progressive HM location: first top-level group that fails when added, else body.
Each probe uses `desugarGroups acc (var firstName)` so prior bindings stay in scope.
On ascription failure, try to report expected vs inferred RHS type. -/
def locateTypecheckFail (ctors : CtorEnv) (ke : KindEnv) (p : Surface.Program)
    (binders : List BinderSpan) (sp : SpannedProgram) : HoverDiag :=
  let rec go (acc : List (List Surface.Binding))
      (rest : List (List Surface.Binding)) : HoverDiag :=
    match rest with
    | [] =>
        diagAtSpan "typechecking failed" (some (bodyDiagSpan sp.body))
    | g :: gs =>
        match g with
        | [] => go (acc ++ [g]) gs
        | b :: _ =>
            let acc' := acc ++ [g]
            let probe := Surface.desugarGroups acc' (.var b.name)
            if hmSucceeds ctors probe then
              go acc' gs
            else
              let nm := prettySurfaceName b.name
              let msg := explainTypeMismatch ctors ke acc g b
              match bindingExtentSpan binders p sp nm with
              | some s => diagAtSpan msg (some s)
              | none => diagAtSpan msg (some (bodyDiagSpan sp.body))
  go [] p.groups

/-- Lowering failure: prefer first free name’s use-site token; else body hull. -/
def locateLowerFail (src : String) (p : Surface.Program) (sp : SpannedProgram) :
    HoverDiag :=
  let free := freeNamesD [] p.term
  match free with
  | n :: _ =>
      let nm := prettySurfaceName n
      let msg := s!"unbound name `{nm}`"
      match firstIdentSpan src nm with
      | some s => diagAtSpan msg (some s)
      | none => diagAtSpan msg (some (bodyDiagSpan sp.body))
  | [] =>
      diagAtSpan
        "expression lowering failed (rejected sugar, bad annotation, or pattern λ)"
        (some (bodyDiagSpan sp.body))

/-- Declaration lower / elab failure: first data-decl span if any. -/
def locateDeclFail (sp : SpannedProgram) (msg : String) : HoverDiag :=
  match sp.declSpans with
  | s :: _ => diagAtSpan msg (some s)
  | [] => diagAtSpan msg none

/-- Full hover report for a parsed program + binder spans + spanned program.

Always erases surface `BL` → `List` before lower/infer (same as Live under `--bl`),
so BL buffers get symbols. Display types come from `assembleProgramReport`.

Bounds checks (`checkProgramAnns` + `checkProgramMatches`) mirror Live `--bl`.
On failure: keep symbols from the pre-check report (ascription/HM) and return a
diagnostic — do **not** silently swallow errors (diagnose reliability).

Lower / typecheck failures now return a diagnostic with a best-effort span
(unbound use site, progressive binder, or body) instead of collapsing to (1,1). -/
def collectHoverLegacyBL (src : String) (p : Surface.Program) (binders : List BinderSpan)
    (sp : SpannedProgram) : HoverReport :=
  -- Pre-erase program for the structural walk: `eraseProgram` clears `natBinders`
  -- but parse binder spans still emit `.count` entries.
  let pSurface := p
  let ep := FHM.Bounds.Erase.eraseProgram p
  let pErased := ep.toProgram
  let fail (d : HoverDiag) : HoverReport :=
    { symbols := [], programTy := "", diagnostics := [d] }
  match lowerDataDeclsIn preludeKindEnv pErased.decls with
  | none =>
      fail (locateDeclFail sp
        "declaration lowering failed (duplicate type/ctor, bad field, or unknown type)")
  | some userCore =>
    match elabDecls (preludeDecls ++ userCore) with
    | none =>
        fail (locateDeclFail sp "declaration elaboration failed (ill-formed data decls)")
    | some ctors =>
      let ke := DataDecls.kindEnv (preludeDecls ++ userCore)
      match lower ctors pErased.term with
      | none => fail (locateLowerFail src pErased sp)
      | some c =>
        match infer c.freshFloor ⟨[], ctors⟩ c with
        | none => fail (locateTypecheckFail ctors ke pErased binders sp)
        | some (_, _, τ) =>
          let bodyσ := genScheme [] [] τ
          let report0 :=
            assembleProgramReport pErased.groups (collectTopSchemes c) bodyσ ep
          let binderEnv := binderEnvFromGroups pErased.groups
          let boundsAnns := ProgramBoundsAnns.ofLower binderEnv ep
          -- Body-level match / ascription errors (no binder name): body/match hull.
          let bodyFallback : Option Span := some (bodyDiagSpan sp.body)
          let (report, diags) :=
            match FHM.Bounds.Check.checkProgramAnns c τ binderEnv boundsAnns with
            | .error msg =>
                (report0, [boundsDiag binders pSurface sp msg bodyFallback])
            | .ok (bctx, βBody) =>
                let report1 :=
                  report0.enrichFromSynth binderEnv (bctx.map BoundBinding.pretty)
                    (some (BoundsTy.pretty βBody))
                match FHM.Bounds.Check.checkProgramMatches ctors c τ binderEnv boundsAnns with
                | .error msg =>
                    (report1, [boundsDiag binders pSurface sp msg bodyFallback])
                | .ok () => (report1, [])
          let progScope := programWideScope binders sp
          let binderSyms :=
            buildHoverSymbols ctors ke pSurface sp binders report progScope
          let preludeSyms :=
            (preludeTypeCtorSymbols ctors progScope).filter fun s =>
              !(binderSyms.any fun b => b.name == s.name && b.kind == s.kind)
          let syms := binderSyms ++ collectLitOpSymbols src ctors ++ preludeSyms
          { symbols := syms, programTy := report.programPretty, diagnostics := diags }

/-- Editor inference from the shared provenance pipeline. In Bounds mode the
canonical recursive checker supplies every displayed `BoundsTy` and all Bounds
diagnostics; in HM mode annotations remain bounds-blind (Path R). Source-token
locations are unverified plumbing and never participate in acceptance. -/
def collectHoverMode (bounds : Bool) (src : String) (p : Surface.Program)
    (binders : List BinderSpan) (sp : SpannedProgram) : HoverReport :=
  let fail (d : HoverDiag) : HoverReport :=
    { symbols := [], programTy := "", diagnostics := [d] }
  match lowerDataDeclsIn preludeKindEnv p.decls with
  | none => fail (locateDeclFail sp "declaration lowering failed (duplicate type/ctor, bad field, or unknown type)")
  | some userCore =>
    match elabDecls (preludeDecls ++ userCore) with
    | none => fail (locateDeclFail sp "declaration elaboration failed (ill-formed data decls)")
    | some ctors =>
      let ke := DataDecls.kindEnv (preludeDecls ++ userCore)
      let scope := programWideScope binders sp
      match FHM.Unverified.HMArtifacts.programSpanned p sp scope with
      | none => fail (diagAtSpan "internal parser provenance shape mismatch" (some scope))
      | some tree =>
        match SurfaceBridge.Provenance.lowerWithProvenance ctors p.term tree with
        | none => fail (locateLowerFail src p sp)
        | some lowered =>
          match SurfaceBridge.Provenance.inferWithProvenance ctors lowered with
          | none => fail (locateTypecheckFail ctors ke p binders sp)
          | some typed =>
            if !lowered.provenanceTotal || !typed.sourceTypesTotal || !typed.patternBinderTypesTotal then
              fail (diagAtSpan "internal inferred provenance coverage failure" (some scope))
            else
              let identified := SurfaceBridge.Provenance.identify tree
              let collected := FHM.Unverified.HMArtifacts.collect binders p.term identified
              let wrapperIds := FHM.Unverified.HMArtifacts.programWrapperIds p.groups identified
              let authoredOccurrences := collected.occurrences.filter
                (fun occ => !(wrapperIds.contains occ.id))
              let locations := { collected with occurrences := authoredOccurrences }
              let displayScopes := FHM.Unverified.HMDisplay.scopes typed locations
              let blAttempt : Except String (Option BLDisplay.Checked) :=
                if bounds then (BLDisplay.check typed).map some else .ok none
              let blChecked? := match blAttempt with
                | .ok checked => checked
                | .error _ => none
              let blReports := (blChecked?.map (·.reports)).getD []
              let values := locations.binders.filterMap fun b =>
                let ty? := if bounds then
                  (BLDisplay.binderType typed displayScopes locations blReports b.site).orElse
                    (fun _ => FHM.Unverified.HMDisplay.binderType typed displayScopes locations b.site)
                  else FHM.Unverified.HMDisplay.binderType typed displayScopes locations b.site
                ty?.map fun ty =>
                  mkSym b.name b.kind.toString ty b.span b.scope
              let occurrences := locations.occurrences.filterMap fun occ => do
                let source ← lowered.sourceNodes.find? (fun n => n.id == occ.id)
                let ty ← (blChecked?.bind fun _ =>
                  BLDisplay.sourceType typed displayScopes locations blReports occ.id).orElse fun _ =>
                    FHM.Unverified.HMDisplay.sourceType typed displayScopes occ.id
                let name := if occ.kind == "lit" || occ.kind == "op" then
                  FHM.Unverified.HMArtifacts.spanText src source.span
                  else occ.name
                let kind := if occ.kind == "val" then
                  ((locations.binders.filter fun b => b.name == occ.name && b.scope.contains
                    source.span.startLine source.span.startCol).mergeSort
                    (fun a b => a.scope.area ≤ b.scope.area)).head? |>.map (·.kind.toString) |>.getD "val"
                  else occ.kind
                pure (mkSym name kind ty source.span source.span)
              -- Type declarations and scoped type/count variables are syntax
              -- facts, not inferred value facts. Never invent a missing type.
              let syntaxSyms := binders.filterMap fun b =>
                if locations.binders.any (fun s => s.span == b.span) then none
                else if b.kind == .type then
                  (p.decls.find? (fun d => prettyTyName d.name == b.name)).map fun d =>
                    mkSym b.name "type" (prettySurfaceDataDecl d) b.span scope
                else if b.kind == .ctor then
                  (LookupList.get? ctors (.mk b.name)).map fun c =>
                    let names := ((p.decls.find? fun d =>
                      d.ctors.any (fun (name, _) => prettyCtorName name == b.name)).map
                        (fun d => d.params.map prettyValName)).getD []
                    mkSym b.name "ctor" (FHM.Unverified.HMDisplay.scheme {} names c.toTy) b.span scope
                else if b.kind == .count then
                  some (mkSym b.name "count"
                    (if bounds then "count variable (Nat)"
                      else "count variable (unchecked in HM mode)")
                    b.span (b.scope?.getD b.span))
                else if b.kind == .param then
                  let decl := (p.decls.zip sp.declSpans).find? fun (_, s) =>
                    FHM.Unverified.HMArtifacts.inside b.span s
                  let label := match decl with
                    | some (d, _) => s!"type variable (of {prettyTyName d.name})"
                    | none => "type variable (scheme binder)"
                  let sc := match decl with
                    | some (_, s) => s
                    | none => b.scope?.getD scope
                  some (mkSym b.name "param" label b.span sc)
                else none
              let prelude := (preludeTypeCtorSymbols ctors scope).filter fun s =>
                !(syntaxSyms.any fun b => b.name == s.name && b.kind == s.kind)
              let sugarOps := (collectLitOpSymbols src ctors).filter fun s => s.name == "::"
              { symbols := prelude ++ syntaxSyms ++ values ++ sugarOps ++ occurrences
                programTy := match blChecked? with
                  | some checked => BLDisplay.bounds {} (BLDisplay.countAliases typed) checked.body
                  | none => FHM.Unverified.HMDisplay.scheme {} []
                      (genScheme [] [] typed.inference.ty.eraseBounds)
                diagnostics := match blAttempt with
                  | .error msg => [boundsDiag binders p sp msg (some (bodyDiagSpan sp.body))]
                  | .ok _ => [] }

/-- HM editor mode: Path R retains `BL` annotations but HM remains blind to
their count claims. This is also the compatibility default for `diagnose`. -/
def collectHover (src : String) (p : Surface.Program) (binders : List BinderSpan)
    (sp : SpannedProgram) : HoverReport :=
  collectHoverMode false src p binders sp

/-- Canonical Bounds editor mode. -/
def collectHoverBL (src : String) (p : Surface.Program) (binders : List BinderSpan)
    (sp : SpannedProgram) : HoverReport :=
  collectHoverMode true src p binders sp

/-- Parse-error diagnostic JSON object. -/
def parseDiagJson (e : ParseError) : Lean.Json :=
  Lean.Json.mkObj [
    ("severity", Lean.Json.str "error"),
    ("message", Lean.Json.str e.msg),
    ("line", Lean.Json.num e.line),
    ("col", Lean.Json.num e.col),
    ("endLine", Lean.Json.num e.endLine),
    ("endCol", Lean.Json.num e.endCol)
  ]

/-- Diagnose payload using a mode selected from the successfully parsed
program. Keeping selection here avoids reparsing in `diagnose --auto`. -/
def diagnosePayloadSelect (selectBounds : Surface.Program → Bool) (src : String) : Lean.Json :=
  match parseProgramWithSpans src with
  | .error e =>
    Lean.Json.mkObj [
      ("version", Lean.Json.num 3),
      ("diagnostics", Lean.Json.arr #[parseDiagJson e]),
      ("symbols", Lean.Json.arr #[])
    ]
  | .ok (p, binders, sp) =>
    let r := collectHoverMode (selectBounds p) src p binders sp
    Lean.Json.mkObj [
      ("version", Lean.Json.num 3),
      ("diagnostics", Lean.Json.arr (r.diagnostics.map HoverDiag.toJson).toArray),
      ("symbols", Lean.Json.arr (r.symbols.map RangedSymbol.toJson).toArray),
      ("programTy", Lean.Json.str r.programTy)
    ]

/-- Diagnose payload in an explicitly selected checker mode. -/
def diagnosePayloadMode (bounds : Bool) (src : String) : Lean.Json :=
  diagnosePayloadSelect (fun _ => bounds) src

/-- Select canonical Bounds checking exactly when the parsed program contains
a `BL` annotation. Intended for editors; batch clients should choose a mode. -/
def diagnosePayloadAuto (src : String) : Lean.Json :=
  diagnosePayloadSelect programContainsBl src

/-- Compatibility entry point: HM / Path-R diagnostics. -/
def diagnosePayload (src : String) : Lean.Json :=
  diagnosePayloadMode false src

def binderNames (bs : List BinderSpan) : List String :=
  bs.map (·.name)
