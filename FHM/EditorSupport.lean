import FHM.Surface.Parse
import FHM.Surface.Span
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty
import FHM.Decls
import Lean.Data.Json

/-!
# Editor support helpers

Shared collection of hover symbols (bindings + type/ctor decls) for
`fhm_diagnose`. Duplicates the small `collectTopSchemes` / `zipBindingTypes`
helpers from `Live` rather than importing the live exe module.

v2: binder spans from the parse sidecar joined with inferred types; hover
resolves by **span containment** (smallest span wins).
-/

open Surface.Parse
open Surface.Span
open SurfaceBridge

/-- Collect schemes from the outer `letIn (some σ)` spine produced by
    `letRecElab` (stops at the first non-annotated-let). -/
partial def collectTopSchemes : Expr → List PolyTy
  | .letIn (some σ) _ body => σ :: collectTopSchemes body
  | _ => []

/-- Drop `n` outer annotated `letIn`s (inverse of taking the first `n` from
    `collectTopSchemes`). -/
def dropAnnotatedLets : Nat → Expr → Expr
  | 0, e => e
  | n + 1, .letIn (some _) _ body => dropAnnotatedLets n body
  | _, e => e

/-- `letRecElab` wraps group members outermost-last, so each group's chunk of
    schemes from `collectTopSchemes` is reversed relative to binding order.
    Undo that per SCC group and zip with surface names. -/
def zipBindingTypes (groups : List (List Surface.Binding)) (schemes : List PolyTy) :
    List (ValName × PolyTy) :=
  let rec go (gs : List (List Surface.Binding)) (ss : List PolyTy)
      (acc : List (ValName × PolyTy)) : List (ValName × PolyTy) :=
    match gs with
    | [] => acc
    | g :: gs' =>
      let n := g.length
      let chunk := (ss.take n).reverse
      let pairs := g.map (·.name) |>.zip chunk
      go gs' (ss.drop n) (acc ++ pairs)
  go groups schemes []

/-- Zip a surface list spine against Core `Cons`/`Nil` after infer. -/
partial def zipExprListBindingTypes (zip : Surface.Expr → Expr → List (ValName × PolyTy)) :
    List Surface.Expr → Expr → List (ValName × PolyTy)
  | [], _ => []
  | x :: xs, .app (.app (.ctor ⟨"Cons"⟩) eh) et =>
      zip x eh ++ zipExprListBindingTypes zip xs et
  | _, _ => []

/-- Zip a surface expression against its Core elaboration-after-infer, collecting
    nested `let` / `let rec` binding schemes. Stops at `match_` / `ife` so we do
    not walk into compiler-generated match lets. For `letRecIn`, only the body is
    walked further (RHS Core shape is `letRecElab` wrappers, not the surface RHS). -/
partial def zipExprBindingTypes : Surface.Expr → Expr → List (ValName × PolyTy)
  | .letIn name _ sRhs sBody, .letIn (some σ) eRhs eBody =>
      (name, σ) :: zipExprBindingTypes sRhs eRhs ++ zipExprBindingTypes sBody eBody
  | .letRecIn binds sBody, e =>
      let n := binds.length
      let schemes := (collectTopSchemes e).take n
      let chunk := schemes.reverse
      let pairs := binds.map (·.1) |>.zip chunk
      let eBody := dropAnnotatedLets n e
      pairs ++ zipExprBindingTypes sBody eBody
  | .lambda _ _ sBody, .lambda _ eBody =>
      zipExprBindingTypes sBody eBody
  | .app sf sx, .app ef ex =>
      zipExprBindingTypes sf ef ++ zipExprBindingTypes sx ex
  | .pair sa sb, .app (.app (.ctor ⟨"Pair"⟩) ea) eb =>
      zipExprBindingTypes sa ea ++ zipExprBindingTypes sb eb
  | .cons sh st, .app (.app (.ctor ⟨"Cons"⟩) eh) et =>
      zipExprBindingTypes sh eh ++ zipExprBindingTypes st et
  | .list items, e =>
      zipExprListBindingTypes zipExprBindingTypes items e
  | .match_ _ _, _ => []
  | .ife _ _ _, _ => []
  | _, _ => []

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

/-- Best-effort surface type for app spines (var + arrow peel). -/
partial def hoverExprTy (env : HoverEnv) : Surface.Expr → Option Ty
  | .var n => env.lookupTy n
  | .app f _ =>
      match hoverExprTy env f with
      | some (.arrow _ b) => some b
      | _ => none
  | _ => none

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

/-- Peel λ domains from an expected type on surface expressions alone.
    Used for top-level / letRec RHSs where Core pairing is not 1:1.
    On `.app f x`, if `f` has an arrow type in `env`, recurse into `x` with the domain. -/
partial def zipExprParamTypesSurface (ctors : CtorEnv) (env : HoverEnv)
    (expected : Option Ty) : Surface.Expr → List (ValName × Ty)
  | .lambda (.name n) _ sBody =>
      match expected with
      | some (.arrow a b) =>
          (n, a) ::
            zipExprParamTypesSurface ctors (env.extendLocal n a) (some b) sBody
      | _ => zipExprParamTypesSurface ctors env none sBody
  | .lambda .wildcard _ sBody =>
      match expected with
      | some (.arrow _ b) => zipExprParamTypesSurface ctors env (some b) sBody
      | _ => zipExprParamTypesSurface ctors env none sBody
  | .lambda _ _ sBody => zipExprParamTypesSurface ctors env none sBody
  | .letIn name _ sRhs sBody =>
      -- Nested surface annotations are Surface.Ty; schemes come from `env.lets`
      -- (top / nested vals preloaded) or from the caller's `expected` on tops.
      let rhsExpected :=
        match env.lets.find? (fun p => p.1 == name) with
        | some ⟨_, σ⟩ => some σ.body
        | none => none
      zipExprParamTypesSurface ctors env rhsExpected sRhs ++
        zipExprParamTypesSurface ctors env expected sBody
  | .letRecIn binds sBody =>
      binds.flatMap (fun t =>
        let exp :=
          match env.lets.find? (fun p => p.1 == t.1) with
          | some ⟨_, σ⟩ => some σ.body
          | none => none
        zipExprParamTypesSurface ctors env exp t.2.2) ++
        zipExprParamTypesSurface ctors env expected sBody
  | .app f x =>
      match hoverExprTy env f with
      | some (.arrow a _) =>
          zipExprParamTypesSurface ctors env none f ++
            zipExprParamTypesSurface ctors env (some a) x
      | _ =>
          zipExprParamTypesSurface ctors env none f ++
            zipExprParamTypesSurface ctors env none x
  | .pair a b =>
      zipExprParamTypesSurface ctors env none a ++
        zipExprParamTypesSurface ctors env none b
  | .cons h t =>
      zipExprParamTypesSurface ctors env none h ++
        zipExprParamTypesSurface ctors env none t
  | .list items => items.flatMap (zipExprParamTypesSurface ctors env none)
  | .match_ s arms =>
      let τScrut :=
        match s with
        | .var n => env.lookupTy n
        | _ => none
      zipExprParamTypesSurface ctors env none s ++
        arms.flatMap fun ⟨pat, e⟩ =>
          let envArm :=
            match τScrut with
            | some τ => env.extendLocals (patLocalPairs ctors pat τ)
            | none => env
          zipExprParamTypesSurface ctors envArm none e
  | .ife c t f =>
      zipExprParamTypesSurface ctors env none c ++
        zipExprParamTypesSurface ctors env none t ++
        zipExprParamTypesSurface ctors env none f
  | _ => []

/-- Collect pattern-bind types in parse / `patVars` order.
    Always one `Option Ty` per binder so `joinRangedSymbols` stays aligned with
    `.pat` spans. v1: only **var** scrutinees yield types (`env.lookupTy`). -/
partial def collectPatTypes (ctors : CtorEnv) (env : HoverEnv)
    (expected : Option Ty) : Surface.Expr → List (Option Ty)
  | .lambda (.name n) _ sBody =>
      match expected with
      | some (.arrow a b) =>
          collectPatTypes ctors (env.extendLocal n a) (some b) sBody
      | _ => collectPatTypes ctors env none sBody
  | .lambda .wildcard _ sBody =>
      match expected with
      | some (.arrow _ b) => collectPatTypes ctors env (some b) sBody
      | _ => collectPatTypes ctors env none sBody
  | .lambda _ _ sBody => collectPatTypes ctors env none sBody
  | .letIn name _ sRhs sBody =>
      let rhsExpected :=
        match env.lets.find? (fun p => p.1 == name) with
        | some ⟨_, σ⟩ => some σ.body
        | none => none
      collectPatTypes ctors env rhsExpected sRhs ++
        collectPatTypes ctors env expected sBody
  | .letRecIn binds sBody =>
      binds.flatMap (fun t =>
        let exp :=
          match env.lets.find? (fun p => p.1 == t.1) with
          | some ⟨_, σ⟩ => some σ.body
          | none => none
        collectPatTypes ctors env exp t.2.2) ++
        collectPatTypes ctors env expected sBody
  | .app f x =>
      match hoverExprTy env f with
      | some (.arrow a _) =>
          collectPatTypes ctors env none f ++
            collectPatTypes ctors env (some a) x
      | _ =>
          collectPatTypes ctors env none f ++
            collectPatTypes ctors env none x
  | .pair a b =>
      collectPatTypes ctors env none a ++ collectPatTypes ctors env none b
  | .cons h t =>
      collectPatTypes ctors env none h ++ collectPatTypes ctors env none t
  | .list items => items.flatMap (collectPatTypes ctors env none)
  | .match_ s arms =>
      let τScrut :=
        match s with
        | .var n => env.lookupTy n
        | _ => none
      collectPatTypes ctors env none s ++
        arms.flatMap fun ⟨pat, body⟩ =>
          let slots := patSlots ctors pat τScrut
          let envArm :=
            match τScrut with
            | some τ => env.extendLocals (patLocalPairs ctors pat τ)
            | none => env
          slots ++ collectPatTypes ctors envArm none body
  | .ife c t f =>
      collectPatTypes ctors env none c ++
        collectPatTypes ctors env none t ++
        collectPatTypes ctors env none f
  | _ => []

/-- Top-level bindings elaborate through `letRecElab` as
    `letIn σ (letRec anns [rhs] (var i)) body`. Peel that wrapper so nested
    surface lets can zip against the real Core RHS. -/
partial def peelLetRecWrapper : Expr → Expr
  | e@(.letRec _ binds (.var i _)) =>
      match binds[i]? with
      | some e' => peelLetRecWrapper e'
      | none => e
  | e => e

/-- Walk Core `letIn` spine in lockstep with flat top bindings, collecting nested
    vals inside each RHS (e.g. `let y = let x = True in x`). -/
partial def zipTopRhsBindingTypes :
    List Surface.Binding → Expr → List (ValName × PolyTy)
  | [], _ => []
  | b :: bs, .letIn (some _) eRhs eBody =>
      zipExprBindingTypes b.rhs (peelLetRecWrapper eRhs) ++
        zipTopRhsBindingTypes bs eBody
  | b :: bs, .letIn none eRhs eBody =>
      zipExprBindingTypes b.rhs (peelLetRecWrapper eRhs) ++
        zipTopRhsBindingTypes bs eBody
  | _ :: _, _ => []

/-- Collect val binding types (top-level groups + nested lets in RHSs + body). -/
def collectValTypes (p : Surface.Program) (eOut : Expr) : List (ValName × PolyTy) :=
  let flat := p.groups.flatMap id
  let topCount := flat.length
  let topBinds := zipBindingTypes p.groups (collectTopSchemes eOut)
  let nestedRhs := zipTopRhsBindingTypes flat eOut
  let bodyCore := dropAnnotatedLets topCount eOut
  let nestedBody := zipExprBindingTypes p.body bodyCore
  topBinds ++ nestedRhs ++ nestedBody

/-- Collect λ param types in `simpleBinder` emit order (type-decl params are
    consumed earlier in `joinRangedSymbols`). -/
def collectParamTypes (ctors : CtorEnv) (p : Surface.Program) (eOut : Expr) :
    List (ValName × Ty) :=
  let topPairs := zipBindingTypes p.groups (collectTopSchemes eOut)
  -- All vals (tops + nested) so nested `let` RHS peels can look up schemes;
  -- mutual-rec tops are all present for `.app` domain peel in bodies.
  let env0 : HoverEnv := { lets := collectValTypes p eOut, locals := [] }
  let flatBinds := p.groups.flatMap id
  let fromTops :=
    flatBinds.zip topPairs |>.flatMap fun (b, ⟨_, σ⟩) =>
      zipExprParamTypesSurface ctors env0 (some σ.body) b.rhs
  let fromBody := zipExprParamTypesSurface ctors env0 none p.body
  fromTops ++ fromBody

/-- Collect pat types for all match binders in program walk order. -/
def collectPatTypesProg (ctors : CtorEnv) (p : Surface.Program) (eOut : Expr) :
    List (Option Ty) :=
  let topPairs := zipBindingTypes p.groups (collectTopSchemes eOut)
  let env0 : HoverEnv := { lets := collectValTypes p eOut, locals := [] }
  let flatBinds := p.groups.flatMap id
  let fromTops :=
    flatBinds.zip topPairs |>.flatMap fun (b, ⟨_, σ⟩) =>
      collectPatTypes ctors env0 (some σ.body) b.rhs
  let fromBody := collectPatTypes ctors env0 none p.body
  fromTops ++ fromBody

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

/-- Spanned hover symbol (v2). -/
structure RangedSymbol where
  name : String
  kind : String
  type_ : String
  span : Span
  deriving Repr, BEq

def RangedSymbol.toJson (s : RangedSymbol) : Lean.Json :=
  Lean.Json.mkObj [
    ("name", Lean.Json.str s.name),
    ("kind", Lean.Json.str s.kind),
    ("type", Lean.Json.str s.type_),
    ("startLine", Lean.Json.num s.span.startLine),
    ("startCol", Lean.Json.num s.span.startCol),
    ("endLine", Lean.Json.num s.span.endLine),
    ("endCol", Lean.Json.num s.span.endCol)
  ]

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

/-- Take the first binder of `kind`, preserving relative order of the rest. -/
def takeFirstKind (bs : List BinderSpan) (k : BinderKind) :
    Option (BinderSpan × List BinderSpan) :=
  let rec go (pref : List BinderSpan) : List BinderSpan → Option (BinderSpan × List BinderSpan)
    | [] => none
    | b :: rest =>
      if b.kind == k then some (b, pref ++ rest)
      else go (pref ++ [b]) rest
  go [] bs

/-- Join parse binder spans with inferred types.
    Decl type/ctor/params consumed first; then vals; then λ params; then pat
    slots (`Option Ty` — `none` → empty pretty). Leftovers get empty types. -/
def joinRangedSymbols (binders : List BinderSpan) (p : Surface.Program)
    (valTys : List (ValName × PolyTy)) (paramTys : List (ValName × Ty))
    (patTys : List (Option Ty)) (ctors : CtorEnv) : List RangedSymbol :=
  Id.run do
    let mut bs := binders
    let mut out : List RangedSymbol := []
    for d in p.decls do
      let typeStr := prettySurfaceDataDecl d
      match takeFirstKind bs .type with
      | some (b, rest) =>
        bs := rest
        out := out ++ [{ name := b.name, kind := "type", type_ := typeStr, span := b.span }]
      | none => pure ()
      for _ in d.params do
        match takeFirstKind bs .param with
        | some (b, rest) =>
          bs := rest
          out := out ++ [{ name := b.name, kind := "param", type_ := "", span := b.span }]
        | none => pure ()
      for ⟨cname, _⟩ in d.ctors do
        let ctorTy :=
          match LookupList.get? ctors cname with
          | some ctor => ctor.toTy.pretty
          | none => prettyCtorName cname
        match takeFirstKind bs .ctor with
        | some (b, rest) =>
          bs := rest
          out := out ++ [{ name := b.name, kind := "ctor", type_ := ctorTy, span := b.span }]
        | none => pure ()
    for ⟨_, σ⟩ in valTys do
      match takeFirstKind bs .val with
      | some (b, rest) =>
        bs := rest
        out := out ++ [{
          name := b.name, kind := "val", type_ := σ.pretty, span := b.span
        }]
      | none => pure ()
    for ⟨_, τ⟩ in paramTys do
      match takeFirstKind bs .param with
      | some (b, rest) =>
        bs := rest
        out := out ++ [{
          name := b.name, kind := "param", type_ := τ.pretty, span := b.span
        }]
      | none => pure ()
    for ot in patTys do
      match takeFirstKind bs .pat with
      | some (b, rest) =>
        bs := rest
        let typeStr :=
          match ot with
          | some τ => τ.pretty
          | none => ""
        out := out ++ [{
          name := b.name, kind := "pat", type_ := typeStr, span := b.span
        }]
      | none => pure ()
    for b in bs do
      out := out ++ [{
        name := b.name, kind := b.kind.toString, type_ := "", span := b.span
      }]
    return out

/-- Full hover report for a parsed program + binder spans. -/
def collectHover (p : Surface.Program) (binders : List BinderSpan) :
    Option (List RangedSymbol × String) := do
  let userCore ← lowerDataDeclsIn preludeKindEnv p.decls
  let ctors ← elabDecls (preludeDecls ++ userCore)
  let c ← lower ctors p.term
  let (_, _, eOut, τ) ← infer c.freshFloor ⟨[], ctors⟩ c
  let vals := collectValTypes p eOut
  let params := collectParamTypes ctors p eOut
  let pats := collectPatTypesProg ctors p eOut
  let syms := joinRangedSymbols binders p vals params pats ctors
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
  match parseProgramWithBinders src with
  | .error e =>
    Lean.Json.mkObj [
      ("version", Lean.Json.num 2),
      ("diagnostics", Lean.Json.arr #[parseDiagJson e]),
      ("symbols", Lean.Json.arr #[])
    ]
  | .ok (p, binders) =>
    match collectHover p binders with
    | none =>
      Lean.Json.mkObj [
        ("version", Lean.Json.num 2),
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
        ("version", Lean.Json.num 2),
        ("diagnostics", Lean.Json.arr #[]),
        ("symbols", Lean.Json.arr (syms.map RangedSymbol.toJson).toArray),
        ("programTy", Lean.Json.str programTy)
      ]

def binderNames (bs : List BinderSpan) : List String :=
  bs.map (·.name)
