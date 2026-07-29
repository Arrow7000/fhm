import FHM.Surface.Parse
import FHM.Surface.Span
import FHM.Surface.Lex
import FHM.SurfaceBridge
import FHM.PipelineShared
import FHM.InferW
import FHM.Pretty
import FHM.Decls
import FHM.Bounds.Erase
import Lean.Data.Json

/-!
# Editor support helpers

Shared collection of hover symbols (bindings + type/ctor decls) for
`fhm diagnose`. Shared `collectTopSchemes` / `zipBindingTypes` via `PipelineShared`.

v3: structural walk emits complete `RangedSymbol`s (span + type + scope) at each
binder site — no parallel-stream zip. Top schemes are a name map from inference
(SCC order independent). Binder spans are consumed in parse/source order.
Resolves by def-span containment first, else name+innermost scope. Type/ctor
symbols use program-wide scope. Lit/op tokens from Core prim types.
-/

open Surface.Parse
open Surface.Span
open Surface.Lex (BinOpToken Punct Token)
open SurfaceBridge

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

/-- Emit head value-params with types from arrow domains (pad short peels). -/
def takeHeadValueParams (doms : List Ty) (scope : Span) (bs : List BinderSpan) :
    List BinderSpan × List RangedSymbol :=
  let rec go (ds : List Ty) (bs : List BinderSpan) (acc : List RangedSymbol) :
      List BinderSpan × List RangedSymbol :=
    match ds, bs with
    | [], _ => (bs, acc)
    | τ :: rest, _ =>
      match takeKind bs .param with
      | some (b, bs') =>
          go rest bs' (acc ++ [mkSym b.name "param" τ.pretty b.span scope])
      | none => (bs, acc)
  go doms bs []

/-- Head binders of one `Binding` (tyParams, value params, colon foralls) + val def.
    Returns remaining binders, symbols, and env extended with head value-params. -/
def hoverBindingHead (env : HoverEnv) (b : Surface.Binding) (σ? : Option PolyTy)
    (valScope : Span) (bs : List BinderSpan) :
    List BinderSpan × List RangedSymbol × HoverEnv :=
  match takeKind bs .val with
  | none => (bs, [], env)
  | some (vb, bs1) =>
      let valSym := mkSym vb.name "val" (optPolyStr σ?) vb.span valScope
      let nAnn := match b.ann with | some σ => σ.foralls.length | none => 0
      -- Nat sidecar binders come first in parse order (before colon foralls).
      let (bs1c, countSyms) := takeCountParams b.natBinders.length valScope bs1
      let (bs2, tySyms) :=
        takeTyVarParams b.tyParams.length valScope "type variable (scheme binder)" bs1c
      let doms :=
        match σ? with
        | some σ => peelArrowDoms b.params.length σ.body
        | none => []
      let doms' :=
        if doms.length < b.params.length then
          doms ++ List.replicate (b.params.length - doms.length) (.prim .unit)
        else
          doms.take b.params.length
      let (bs3, headSyms) := takeHeadValueParams doms' valScope bs2
      let (bs4, annSyms) :=
        takeTyVarParams nAnn valScope "type variable (scheme binder)" bs3
      -- Locals for RHS: head value-params (for scrut/pat hover inside the body).
      let headLocals : List (ValName × Ty) :=
        b.params.map (·.1) |>.zip doms'
      let env' := env.extendLocals headLocals
      let env'' :=
        match σ? with
        | some σ => env'.extendLets [(b.name, σ)]
        | none => env'
      (bs4, valSym :: countSyms ++ tySyms ++ headSyms ++ annSyms, env'')

/-- Structural walk: each binder site emits a full symbol. Consumes `bs` in parse order. -/
partial def hoverWalkExpr (ctors : CtorEnv) (ke : KindEnv) (env : HoverEnv)
    (expected : Option Ty) :
    Surface.Expr → SpannedExpr → List BinderSpan → List BinderSpan × List RangedSymbol
  | .lambda (.name n) _ body, .lambda _ bodyS, bs =>
      let τDom := match expected with | some (.arrow a _) => some a | _ => none
      let τCod := match expected with | some (.arrow _ b) => some b | _ => none
      match takeKind bs .param with
      | some (b, rest) =>
          let sym := mkSym b.name "param" (optTyStr τDom) b.span bodyS.span
          let env' :=
            match τDom with
            | some τ => env.extendLocal n τ
            | none => env
          let (rest', syms) := hoverWalkExpr ctors ke env' τCod body bodyS rest
          (rest', sym :: syms)
      | none => hoverWalkExpr ctors ke env none body bodyS bs
  | .lambda .wildcard _ body, .lambda _ bodyS, bs =>
      let τCod := match expected with | some (.arrow _ b) => some b | _ => none
      hoverWalkExpr ctors ke env τCod body bodyS bs
  | .lambda _ _ body, .lambda _ bodyS, bs =>
      hoverWalkExpr ctors ke env none body bodyS bs
  | .letIn name tyParams params ann rhs body, .letIn _ rhsS bodyS, bs =>
      -- Always synth this binding (ann / RHS). Do **not** look up `name` in
      -- `env.lets` — an outer same-named let would steal the scheme (shadowing).
      let σ? := surfaceLetScheme ctors ke env ann rhs
      let bind : Surface.Binding := { name, tyParams, params, ann, rhs }
      let (bs1, headSyms, envRhs) :=
        hoverBindingHead env bind σ? bodyS.span bs
      let rhsExp :=
        match σ? with
        | some σ => rhsExpectedAfterHead σ params.length
        | none => none
      let (bs2, rhsSyms) := hoverWalkExpr ctors ke envRhs rhsExp rhs rhsS bs1
      let envBody :=
        match σ? with
        | some σ => env.extendLets [(name, σ)]
        | none => env
      let (bs3, bodySyms) := hoverWalkExpr ctors ke envBody expected body bodyS bs2
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
              hoverBindingHead envBinds b σ? groupScope bsLeft
            let rhsExp :=
              match σ? with
              | some σ => rhsExpectedAfterHead σ b.params.length
              | none => none
            let (bs2, rhsSyms) :=
              hoverWalkExpr ctors ke envRhs rhsExp b.rhs sRhs bs1
            goBinds bs2 bs' rss' (acc ++ headSyms ++ rhsSyms)
        | _, _ => (bsLeft, acc)
      let (bs1, bindSyms) := goBinds bs binds rhss []
      let (bs2, bodySyms) := hoverWalkExpr ctors ke envBinds expected body bodyS bs1
      (bs2, bindSyms ++ bodySyms)
  | .app f x, .app _ fS xS, bs =>
      let (bs1, fSyms) := hoverWalkExpr ctors ke env none f fS bs
      let xExp :=
        match hoverExprTy ctors env f with
        | some (.arrow a _) => some a
        | _ => none
      let (bs2, xSyms) := hoverWalkExpr ctors ke env xExp x xS bs1
      (bs2, fSyms ++ xSyms)
  | .pair a b, .pair _ aS bS, bs =>
      let (bs1, aSyms) := hoverWalkExpr ctors ke env none a aS bs
      let (bs2, bSyms) := hoverWalkExpr ctors ke env none b bS bs1
      (bs2, aSyms ++ bSyms)
  | .cons h t, .cons _ hS tS, bs =>
      let (bs1, hSyms) := hoverWalkExpr ctors ke env none h hS bs
      let (bs2, tSyms) := hoverWalkExpr ctors ke env none t tS bs1
      (bs2, hSyms ++ tSyms)
  | .list items, .list _ itemSs, bs =>
      let rec go (bs : List BinderSpan) (es : List Surface.Expr)
          (ss : List SpannedExpr) (acc : List RangedSymbol) :
          List BinderSpan × List RangedSymbol :=
        match es, ss with
        | e :: es', s :: ss' =>
            let (bs', syms) := hoverWalkExpr ctors ke env none e s bs
            go bs' es' ss' (acc ++ syms)
        | _, _ => (bs, acc)
      go bs items itemSs []
  | .match_ scrut arms, .match_ _ scrutS armSs, bs =>
      let (bs1, scrutSyms) := hoverWalkExpr ctors ke env none scrut scrutS bs
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
              hoverWalkExpr ctors ke envArm none body bodyS bs2
            goArms bs3 as' ss' (acc ++ patSyms ++ bodySyms)
        | _, _ => (bs, acc)
      let (bs2, armSyms) := goArms bs1 arms armSs []
      (bs2, scrutSyms ++ armSyms)
  | .ife c t f, .ife _ cS tS fS, bs =>
      let (bs1, cSyms) := hoverWalkExpr ctors ke env none c cS bs
      let (bs2, tSyms) := hoverWalkExpr ctors ke env none t tS bs1
      let (bs3, fSyms) := hoverWalkExpr ctors ke env none f fS bs2
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
    (topSchemes : List (ValName × PolyTy)) (programScope : Span) :
    List RangedSymbol :=
  let flatBinds := p.groups.flatMap id
  let topScopes := collectTopValScopes p sp
  let env0 : HoverEnv := { lets := topSchemes, locals := [] }
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
          hoverWalkExpr ctors ke env0 none p.body sp.body bs
        (bs', acc ++ bodySyms)
    | nm :: nms =>
        let n : ValName := .mk nm
        match lookupBinding flatBinds n with
        | none => goTops nms bs acc
        | some b =>
            let σ? := lookupScheme topSchemes n
            let valScope := (lookupSpan topScopes n).getD programScope
            let sRhs := (topRhsSpan p sp n).getD (.leaf Span.empty)
            let (bsH, headSyms, envRhs) :=
              hoverBindingHead env0 b σ? valScope bs
            let rhsExp :=
              match σ? with
              | some σ => rhsExpectedAfterHead σ b.params.length
              | none => none
            let (bsR, rhsSyms) :=
              hoverWalkExpr ctors ke envRhs rhsExp b.rhs sRhs bsH
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

/-- Full hover report for a parsed program + binder spans + spanned program.

Always erases surface `BL` → `List` before lower/infer (same as Live under `--bl`),
so BL buffers get symbols. Types still pretty as `List …` until bounds report. -/
def collectHover (src : String) (p : Surface.Program) (binders : List BinderSpan)
    (sp : SpannedProgram) : Option (List RangedSymbol × String) := do
  let p := (FHM.Bounds.Erase.eraseProgram p).toProgram
  let userCore ← lowerDataDeclsIn preludeKindEnv p.decls
  let ctors ← elabDecls (preludeDecls ++ userCore)
  let ke := DataDecls.kindEnv (preludeDecls ++ userCore)
  let c ← lower ctors p.term
  let (_, _, eOut, τ) ← infer c.freshFloor ⟨[], ctors⟩ c
  let topSchemes := zipBindingTypes p.groups (collectTopSchemes eOut)
  let progScope := programWideScope binders sp
  let binderSyms := buildHoverSymbols ctors ke p sp binders topSchemes progScope
  let preludeSyms :=
    (preludeTypeCtorSymbols ctors progScope).filter fun s =>
      !(binderSyms.any fun b => b.name == s.name && b.kind == s.kind)
  let syms := binderSyms ++ collectLitOpSymbols src ctors ++ preludeSyms
  pure (syms, (genScheme [] [] τ).pretty)

/-- Parse-error diagnostic JSON object. -/
def parseDiagJson (e : ParseError) : Lean.Json :=
  Lean.Json.mkObj [
    ("severity", Lean.Json.str "error"),
    ("message", Lean.Json.str e.msg),
    ("line", Lean.Json.num e.line),
    ("col", Lean.Json.num e.col)
  ]

/-- Diagnose payload: versioned object with diagnostics, symbols, optional programTy. -/
def diagnosePayload (src : String) : Lean.Json :=
  match parseProgramWithSpans src with
  | .error e =>
    Lean.Json.mkObj [
      ("version", Lean.Json.num 3),
      ("diagnostics", Lean.Json.arr #[parseDiagJson e]),
      ("symbols", Lean.Json.arr #[])
    ]
  | .ok (p, binders, sp) =>
    match collectHover src p binders sp with
    | none =>
      Lean.Json.mkObj [
        ("version", Lean.Json.num 3),
        ("diagnostics", Lean.Json.arr #[Lean.Json.mkObj [
          ("severity", Lean.Json.str "error"),
          ("message", Lean.Json.str "lowering or typechecking failed"),
          ("line", Lean.Json.num 1),
          ("col", Lean.Json.num 1)
        ]]),
        ("symbols", Lean.Json.arr #[])
      ]
    | some (syms, programTy) =>
      Lean.Json.mkObj [
        ("version", Lean.Json.num 3),
        ("diagnostics", Lean.Json.arr #[]),
        ("symbols", Lean.Json.arr (syms.map RangedSymbol.toJson).toArray),
        ("programTy", Lean.Json.str programTy)
      ]

def binderNames (bs : List BinderSpan) : List String :=
  bs.map (·.name)
