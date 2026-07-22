import FHM.Surface.Parse
import FHM.Surface.Span
import FHM.Surface.Lex
import FHM.SurfaceBridge
import FHM.PipelineShared
import FHM.InferW
import FHM.Pretty
import FHM.Decls
import Lean.Data.Json

/-!
# Editor support helpers

Shared collection of hover symbols (bindings + type/ctor decls) for
`fhm diagnose`. Shared `collectTopSchemes` / `zipBindingTypes` via `PipelineShared`.

v3: binder spans + lexical `scope` spans for use-site hover; resolves by
def-span containment first, else name+innermost scope. Type/ctor symbols use
program-wide scope (global names). Lit/op tokens get spanned symbols from Core
`PrimLitExpr.ty` / `PrimBinOp.ty` / `Ctor.toTy`.
-/

open Surface.Parse
open Surface.Span
open Surface.Lex (BinOpToken Punct Token)
open SurfaceBridge

/-- Drop `n` outer annotated `letIn`s (inverse of taking the first `n` from
    `collectTopSchemes`). -/
def dropAnnotatedLets : Nat → Expr → Expr
  | 0, e => e
  | n + 1, .letIn (some _) _ body => dropAnnotatedLets n body
  | _, e => e

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
  | .letIn name _ _ sRhs sBody, .letIn (some σ) eRhs eBody =>
      (name, σ) :: zipExprBindingTypes sRhs eRhs ++ zipExprBindingTypes sBody eBody
  | .letRecIn binds sBody, e =>
      let n := binds.length
      let schemes := (collectTopSchemes e).take n
      let chunk := schemes.reverse
      let pairs := binds.map (·.name) |>.zip chunk
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
  | .letIn name _ _ sRhs sBody =>
      -- Nested surface annotations are Surface.Ty; schemes come from `env.lets`
      -- (top / nested vals preloaded) or from the caller's `expected` on tops.
      let rhsExpected :=
        match env.lets.find? (fun p => p.1 == name) with
        | some ⟨_, σ⟩ => some σ.body
        | none => none
      zipExprParamTypesSurface ctors env rhsExpected sRhs ++
        zipExprParamTypesSurface ctors env expected sBody
  | .letRecIn binds sBody =>
      binds.flatMap (fun b =>
        let exp :=
          match env.lets.find? (fun p => p.1 == b.name) with
          | some ⟨_, σ⟩ => some σ.body
          | none => none
        zipExprParamTypesSurface ctors env exp b.rhs) ++
        zipExprParamTypesSurface ctors env expected sBody
  | .app f x =>
      match hoverExprTy ctors env f with
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
      let τScrut := hoverExprTy ctors env s
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
    `.pat` spans. Scrutinee type via `hoverExprTy` (best effort). -/
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
  | .letIn name _ _ sRhs sBody =>
      let rhsExpected :=
        match env.lets.find? (fun p => p.1 == name) with
        | some ⟨_, σ⟩ => some σ.body
        | none => none
      collectPatTypes ctors env rhsExpected sRhs ++
        collectPatTypes ctors env expected sBody
  | .letRecIn binds sBody =>
      binds.flatMap (fun b =>
        let exp :=
          match env.lets.find? (fun p => p.1 == b.name) with
          | some ⟨_, σ⟩ => some σ.body
          | none => none
        collectPatTypes ctors env exp b.rhs) ++
        collectPatTypes ctors env expected sBody
  | .app f x =>
      match hoverExprTy ctors env f with
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
      let τScrut := hoverExprTy ctors env s
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

/-- Scheme for a surface let: lowered annotation, else synth RHS, else `none`. -/
def surfaceLetScheme (ctors : CtorEnv) (ke : KindEnv) (env : HoverEnv)
    (ann : Option Surface.PolyTy) (rhs : Surface.Expr) : Option PolyTy :=
  match ann with
  | some σs => lowerPoly ke σs
  | none => (hoverExprTy ctors env rhs).map PolyTy.mkTrivial

/-- All `let`/`let rec` vals inside an expression (surface walk; for match/if arms). -/
partial def collectAllSurfaceValTypes (ctors : CtorEnv) (ke : KindEnv) (env : HoverEnv) :
    Surface.Expr → List (ValName × Option PolyTy)
  | .letIn name _ _ ann rhs body =>
      let σ? := surfaceLetScheme ctors ke env ann rhs
      let envRhs := env
      let envBody :=
        match σ? with
        | some σ => env.extendLets [(name, σ)]
        | none => env
      (name, σ?) ::
        collectAllSurfaceValTypes ctors ke envRhs rhs ++
        collectAllSurfaceValTypes ctors ke envBody body
  | .letRecIn binds body =>
      let pairs : List (ValName × Option PolyTy) :=
        binds.map fun b => (b.name, surfaceLetScheme ctors ke env b.ann b.rhs)
      let envBinds :=
        env.extendLets (pairs.filterMap fun ⟨n, σ?⟩ => σ?.map fun σ => (n, σ))
      pairs ++
        binds.flatMap (fun b => collectAllSurfaceValTypes ctors ke envBinds b.rhs) ++
        collectAllSurfaceValTypes ctors ke envBinds body
  | .lambda (.name _) _ body =>
      collectAllSurfaceValTypes ctors ke env body
  | .lambda _ _ body => collectAllSurfaceValTypes ctors ke env body
  | .app f x =>
      collectAllSurfaceValTypes ctors ke env f ++
        collectAllSurfaceValTypes ctors ke env x
  | .pair a b =>
      collectAllSurfaceValTypes ctors ke env a ++
        collectAllSurfaceValTypes ctors ke env b
  | .cons h t =>
      collectAllSurfaceValTypes ctors ke env h ++
        collectAllSurfaceValTypes ctors ke env t
  | .list items => items.flatMap (collectAllSurfaceValTypes ctors ke env)
  | .match_ s arms =>
      let τScrut := hoverExprTy ctors env s
      collectAllSurfaceValTypes ctors ke env s ++
        arms.flatMap fun ⟨pat, body⟩ =>
          let envArm :=
            match τScrut with
            | some τ => env.extendLocals (patLocalPairs ctors pat τ)
            | none => env
          collectAllSurfaceValTypes ctors ke envArm body
  | .ife c t f =>
      collectAllSurfaceValTypes ctors ke env c ++
        collectAllSurfaceValTypes ctors ke env t ++
        collectAllSurfaceValTypes ctors ke env f
  | _ => []

/-- Zip surface against Core for nested lets; at `match_`/`ife`, surface-walk arms
    (Core is PatComp-shaped and must not be zipped). -/
partial def zipExprBindingTypesOpt (ctors : CtorEnv) (ke : KindEnv) (env : HoverEnv) :
    Surface.Expr → Expr → List (ValName × Option PolyTy)
  | .letIn name _ _ sRhs sBody, .letIn (some σ) eRhs eBody =>
      let env' := env.extendLets [(name, σ)]
      (name, some σ) ::
        zipExprBindingTypesOpt ctors ke env sRhs eRhs ++
        zipExprBindingTypesOpt ctors ke env' sBody eBody
  | .letIn name _ _ ann sRhs sBody, .letIn none eRhs eBody =>
      let σ? := surfaceLetScheme ctors ke env ann sRhs
      let env' :=
        match σ? with
        | some σ => env.extendLets [(name, σ)]
        | none => env
      (name, σ?) ::
        zipExprBindingTypesOpt ctors ke env sRhs eRhs ++
        zipExprBindingTypesOpt ctors ke env' sBody eBody
  | .letRecIn binds sBody, e =>
      let n := binds.length
      let schemes := (collectTopSchemes e).take n
      let chunk := schemes.reverse
      let pairs := binds.map (·.name) |>.zip chunk
      let eBody := dropAnnotatedLets n e
      let env' := env.extendLets pairs
      pairs.map (fun ⟨n, σ⟩ => (n, some σ)) ++
        zipExprBindingTypesOpt ctors ke env' sBody eBody
  | .lambda _ _ sBody, .lambda _ eBody =>
      zipExprBindingTypesOpt ctors ke env sBody eBody
  | .app sf sx, .app ef ex =>
      zipExprBindingTypesOpt ctors ke env sf ef ++
        zipExprBindingTypesOpt ctors ke env sx ex
  | .pair sa sb, .app (.app (.ctor ⟨"Pair"⟩) ea) eb =>
      zipExprBindingTypesOpt ctors ke env sa ea ++
        zipExprBindingTypesOpt ctors ke env sb eb
  | .cons sh st, .app (.app (.ctor ⟨"Cons"⟩) eh) et =>
      zipExprBindingTypesOpt ctors ke env sh eh ++
        zipExprBindingTypesOpt ctors ke env st et
  | .list items, _ =>
      items.flatMap (collectAllSurfaceValTypes ctors ke env)
  | .match_ s arms, _ =>
      let τScrut := hoverExprTy ctors env s
      -- scrut may contain lets (rare); surface-walk it
      collectAllSurfaceValTypes ctors ke env s ++
        arms.flatMap fun ⟨pat, body⟩ =>
          let envArm :=
            match τScrut with
            | some τ => env.extendLocals (patLocalPairs ctors pat τ)
            | none => env
          collectAllSurfaceValTypes ctors ke envArm body
  | .ife c t f, _ =>
      collectAllSurfaceValTypes ctors ke env c ++
        collectAllSurfaceValTypes ctors ke env t ++
        collectAllSurfaceValTypes ctors ke env f
  | _, _ => []

/-- Walk Core `letIn` spine in lockstep with flat top bindings, collecting nested
    vals inside each RHS (e.g. `let y = let x = True in x`). -/
partial def zipTopRhsBindingTypesOpt (ctors : CtorEnv) (ke : KindEnv) (env : HoverEnv) :
    List Surface.Binding → Expr → List (ValName × Option PolyTy)
  | [], _ => []
  | b :: bs, .letIn (some σ) eRhs eBody =>
      let env' := env.extendLets [(b.name, σ)]
      zipExprBindingTypesOpt ctors ke env b.rhs (peelLetRecWrapper eRhs) ++
        zipTopRhsBindingTypesOpt ctors ke env' bs eBody
  | b :: bs, .letIn none eRhs eBody =>
      zipExprBindingTypesOpt ctors ke env b.rhs (peelLetRecWrapper eRhs) ++
        zipTopRhsBindingTypesOpt ctors ke env bs eBody
  | _ :: _, _ => []

/-- Collect val binding types (top-level groups + nested lets, incl. match/if arms). -/
def collectValTypesOpt (ctors : CtorEnv) (ke : KindEnv) (p : Surface.Program) (eOut : Expr) :
    List (ValName × Option PolyTy) :=
  let flat := p.groups.flatMap id
  let topCount := flat.length
  let topBinds := (zipBindingTypes p.groups (collectTopSchemes eOut)).map
    fun ⟨n, σ⟩ => (n, some σ)
  let env0 : HoverEnv := {
    lets := topBinds.filterMap fun ⟨n, σ?⟩ => σ?.map fun σ => (n, σ)
    locals := []
  }
  let nestedRhs := zipTopRhsBindingTypesOpt ctors ke env0 flat eOut
  let bodyCore := dropAnnotatedLets topCount eOut
  let nestedBody := zipExprBindingTypesOpt ctors ke env0 p.body bodyCore
  topBinds ++ nestedRhs ++ nestedBody

/-- Concrete schemes from `collectValTypesOpt` (drops failed synth). -/
def collectValTypes (ctors : CtorEnv) (ke : KindEnv) (p : Surface.Program) (eOut : Expr) :
    List (ValName × PolyTy) :=
  (collectValTypesOpt ctors ke p eOut).filterMap fun ⟨n, σ?⟩ =>
    σ?.map fun σ => (n, σ)

/-- Collect λ param types in `simpleBinder` emit order (type-decl params are
    consumed earlier in `joinRangedSymbols`). -/
def collectParamTypes (ctors : CtorEnv) (ke : KindEnv) (p : Surface.Program) (eOut : Expr) :
    List (ValName × Ty) :=
  let topPairs := zipBindingTypes p.groups (collectTopSchemes eOut)
  -- All vals (tops + nested) so nested `let` RHS peels can look up schemes;
  -- mutual-rec tops are all present for `.app` domain peel in bodies.
  let env0 : HoverEnv := { lets := collectValTypes ctors ke p eOut, locals := [] }
  let flatBinds := p.groups.flatMap id
  let fromTops :=
    flatBinds.zip topPairs |>.flatMap fun (b, ⟨_, σ⟩) =>
      zipExprParamTypesSurface ctors env0 (some σ.body) b.rhs
  let fromBody := zipExprParamTypesSurface ctors env0 none p.body
  fromTops ++ fromBody

/-- Collect pat types for all match binders in program walk order. -/
def collectPatTypesProg (ctors : CtorEnv) (ke : KindEnv) (p : Surface.Program) (eOut : Expr) :
    List (Option Ty) :=
  let topPairs := zipBindingTypes p.groups (collectTopSchemes eOut)
  let env0 : HoverEnv := { lets := collectValTypes ctors ke p eOut, locals := [] }
  let flatBinds := p.groups.flatMap id
  let fromTops :=
    flatBinds.zip topPairs |>.flatMap fun (b, ⟨_, σ⟩) =>
      collectPatTypes ctors env0 (some σ.body) b.rhs
  let fromBody := collectPatTypes ctors env0 none p.body
  fromTops ++ fromBody

/-- Nested val scopes (lockstep with `SpannedExpr`). -/
partial def collectExprValScopes : Surface.Expr → SpannedExpr → List (ValName × Span)
  | .letIn name _ _ sRhs sBody, .letIn _ sRhsS sBodyS =>
      (name, sBodyS.span) ::
        collectExprValScopes sRhs sRhsS ++ collectExprValScopes sBody sBodyS
  | .letRecIn binds sBody, .letRecIn _ rhss sBodyS =>
      let groupScope :=
        match Span.hull (rhss.map SpannedExpr.span ++ [sBodyS.span]) with
        | some s => s
        | none => sBodyS.span
      binds.map (fun b => (b.name, groupScope)) ++
        (binds.map (·.rhs)).zip rhss |>.flatMap (fun (e, s) => collectExprValScopes e s) ++
        collectExprValScopes sBody sBodyS
  | .lambda _ _ sBody, .lambda _ sBodyS => collectExprValScopes sBody sBodyS
  | .app sf sx, .app _ sfS sxS =>
      collectExprValScopes sf sfS ++ collectExprValScopes sx sxS
  | .pair a b, .pair _ aS bS =>
      collectExprValScopes a aS ++ collectExprValScopes b bS
  | .cons h t, .cons _ hS tS =>
      collectExprValScopes h hS ++ collectExprValScopes t tS
  | .list items, .list _ itemSs =>
      items.zip itemSs |>.flatMap (fun (e, s) => collectExprValScopes e s)
  | .match_ s arms, .match_ _ sS armSs =>
      collectExprValScopes s sS ++
        (arms.zip armSs |>.flatMap fun (⟨_, body⟩, bodyS) =>
          collectExprValScopes body bodyS)
  | .ife c t f, .ife _ cS tS fS =>
      collectExprValScopes c cS ++ collectExprValScopes t tS ++ collectExprValScopes f fS
  | _, _ => []

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

/-- All val scopes in program order (tops + nested in RHSs/body, incl. match/if). -/
def collectValScopes (p : Surface.Program) (sp : SpannedProgram) : List (ValName × Span) :=
  let tops := collectTopValScopes p sp
  let nestedRhs :=
    (p.groups.flatMap id).zip (sp.groups.flatMap id) |>.flatMap fun (b, s) =>
      collectExprValScopes b.rhs s
  let nestedBody := collectExprValScopes p.body sp.body
  tops ++ nestedRhs ++ nestedBody

/-- λ param scopes (body of that λ). -/
partial def collectExprParamScopes : Surface.Expr → SpannedExpr → List (ValName × Span)
  | .lambda (.name n) _ sBody, .lambda _ sBodyS =>
      (n, sBodyS.span) :: collectExprParamScopes sBody sBodyS
  | .lambda _ _ sBody, .lambda _ sBodyS =>
      collectExprParamScopes sBody sBodyS
  | .letIn _ _ _ sRhs sBody, .letIn _ sRhsS sBodyS =>
      collectExprParamScopes sRhs sRhsS ++ collectExprParamScopes sBody sBodyS
  | .letRecIn binds sBody, .letRecIn _ rhss sBodyS =>
      (binds.map (·.rhs)).zip rhss |>.flatMap (fun (e, s) => collectExprParamScopes e s) ++
        collectExprParamScopes sBody sBodyS
  | .app sf sx, .app _ sfS sxS =>
      collectExprParamScopes sf sfS ++ collectExprParamScopes sx sxS
  | .pair a b, .pair _ aS bS =>
      collectExprParamScopes a aS ++ collectExprParamScopes b bS
  | .cons h t, .cons _ hS tS =>
      collectExprParamScopes h hS ++ collectExprParamScopes t tS
  | .list items, .list _ itemSs =>
      items.zip itemSs |>.flatMap (fun (e, s) => collectExprParamScopes e s)
  | .match_ s arms, .match_ _ sS armSs =>
      collectExprParamScopes s sS ++
        (arms.zip armSs |>.flatMap fun (⟨_, body⟩, bodyS) =>
          collectExprParamScopes body bodyS)
  | .ife c t f, .ife _ cS tS fS =>
      collectExprParamScopes c cS ++ collectExprParamScopes t tS ++
        collectExprParamScopes f fS
  | _, _ => []

def collectParamScopes (p : Surface.Program) (sp : SpannedProgram) : List (ValName × Span) :=
  let fromTops :=
    (p.groups.flatMap id).zip (sp.groups.flatMap id) |>.flatMap fun (b, s) =>
      collectExprParamScopes b.rhs s
  fromTops ++ collectExprParamScopes p.body sp.body

/-- Pattern-binder scopes (arm body); one span per `patVars` binder. -/
partial def collectExprPatScopes : Surface.Expr → SpannedExpr → List Span
  | .lambda _ _ sBody, .lambda _ sBodyS => collectExprPatScopes sBody sBodyS
  | .letIn _ _ _ sRhs sBody, .letIn _ sRhsS sBodyS =>
      collectExprPatScopes sRhs sRhsS ++ collectExprPatScopes sBody sBodyS
  | .letRecIn binds sBody, .letRecIn _ rhss sBodyS =>
      (binds.map (·.rhs)).zip rhss |>.flatMap (fun (e, s) => collectExprPatScopes e s) ++
        collectExprPatScopes sBody sBodyS
  | .app sf sx, .app _ sfS sxS =>
      collectExprPatScopes sf sfS ++ collectExprPatScopes sx sxS
  | .pair a b, .pair _ aS bS =>
      collectExprPatScopes a aS ++ collectExprPatScopes b bS
  | .cons h t, .cons _ hS tS =>
      collectExprPatScopes h hS ++ collectExprPatScopes t tS
  | .list items, .list _ itemSs =>
      items.zip itemSs |>.flatMap (fun (e, s) => collectExprPatScopes e s)
  | .match_ s arms, .match_ _ sS armSs =>
      collectExprPatScopes s sS ++
        (arms.zip armSs |>.flatMap fun (⟨pat, body⟩, bodyS) =>
          let ns := patVars pat
          ns.map (fun _ => bodyS.span) ++ collectExprPatScopes body bodyS)
  | .ife c t f, .ife _ cS tS fS =>
      collectExprPatScopes c cS ++ collectExprPatScopes t tS ++ collectExprPatScopes f fS
  | _, _ => []

def collectPatScopes (p : Surface.Program) (sp : SpannedProgram) : List Span :=
  let fromTops :=
    (p.groups.flatMap id).zip (sp.groups.flatMap id) |>.flatMap fun (b, s) =>
      collectExprPatScopes b.rhs s
  fromTops ++ collectExprPatScopes p.body sp.body

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

/-- Take the first binder of `kind`, preserving relative order of the rest. -/
def takeFirstKind (bs : List BinderSpan) (k : BinderKind) :
    Option (BinderSpan × List BinderSpan) :=
  let rec go (pref : List BinderSpan) : List BinderSpan → Option (BinderSpan × List BinderSpan)
    | [] => none
    | b :: rest =>
      if b.kind == k then some (b, pref ++ rest)
      else go (pref ++ [b]) rest
  go [] bs

/-- Flush leading λ params (`scope? = none`) and pattern binders from the front
    of the binder queue. Must run before each subsequent top-level `val`, otherwise
    searching for the next val reshuffles RHS binders ahead of the next binding’s
    scheme params and desyncs types. -/
def flushRhsBinders
    (bs : List BinderSpan) (out : List RangedSymbol)
    (paramTys : List (ValName × Ty)) (paramScopes : List Span) (pi : Nat)
    (patTys : List (Option Ty)) (patScopes : List Span) (pai : Nat) :
    List BinderSpan × List RangedSymbol × Nat × Nat :=
  match bs with
  | b2 :: rest2 =>
    if b2.kind == .param && b2.scope?.isNone then
      let sc := paramScopes[pi]?.getD b2.span
      let τStr :=
        match paramTys[pi]? with
        | some ⟨_, τ⟩ => τ.pretty
        | none => ""
      flushRhsBinders rest2 (out ++ [{
        name := b2.name, kind := "param", type_ := τStr,
        span := b2.span, scope := sc
      }]) paramTys paramScopes (pi + 1) patTys patScopes pai
    else if b2.kind == .pat then
      let sc := patScopes[pai]?.getD b2.span
      let τStr :=
        match patTys[pai]? with
        | some (some τ) => τ.pretty
        | _ => ""
      flushRhsBinders rest2 (out ++ [{
        name := b2.name, kind := "pat", type_ := τStr,
        span := b2.span, scope := sc
      }]) paramTys paramScopes pi patTys patScopes (pai + 1)
    else
      (bs, out, pi, pai)
  | [] => (bs, out, pi, pai)

/-- Peel scheme-ann `{a}` params (`scope? = some`) immediately after a val. -/
def peelSchemeBinders (bs : List BinderSpan) (out : List RangedSymbol) :
    List BinderSpan × List RangedSymbol :=
  match bs with
  | b2 :: rest2 =>
    if b2.kind == .param && b2.scope?.isSome then
      peelSchemeBinders rest2 (out ++ [{
        name := b2.name, kind := "param",
        type_ := "type variable (scheme binder)",
        span := b2.span, scope := b2.scope?.getD b2.span
      }])
    else
      (bs, out)
  | [] => (bs, out)

/-- Join parse binder spans with inferred types and scopes.
    Decl type/ctor: `scope := programScope` (global use-site). Type-decl params
    get a tyvar label and `scope :=` that data decl’s hull (`declScopes`).
    Scheme-ann `{a b}` params (parse sets `scope?`) are peeled after each val.
    λ params / pats for each RHS are flushed before the next val (parse order). -/
def joinRangedSymbols (binders : List BinderSpan) (p : Surface.Program)
    (valTys : List (ValName × Option PolyTy)) (valScopes : List Span)
    (paramTys : List (ValName × Ty)) (paramScopes : List Span)
    (patTys : List (Option Ty)) (patScopes : List Span)
    (ctors : CtorEnv) (programScope : Span) (declScopes : List Span) :
    List RangedSymbol :=
  Id.run do
    let mut bs := binders
    let mut out : List RangedSymbol := []
    let mut vi : Nat := 0
    let mut pi : Nat := 0
    let mut pai : Nat := 0
    let mut di : Nat := 0
    for d in p.decls do
      let typeStr := prettySurfaceDataDecl d
      let typeName := prettyTyName d.name
      let declScope := declScopes[di]?.getD programScope
      di := di + 1
      match takeFirstKind bs .type with
      | some (b, rest) =>
        bs := rest
        out := out ++ [{
          name := b.name, kind := "type", type_ := typeStr,
          span := b.span, scope := programScope
        }]
      | none => pure ()
      for _ in d.params do
        match takeFirstKind bs .param with
        | some (b, rest) =>
          bs := rest
          out := out ++ [{
            name := b.name, kind := "param",
            type_ := s!"type variable (of {typeName})",
            span := b.span, scope := declScope
          }]
        | none => pure ()
      for ⟨cname, _⟩ in d.ctors do
        let ctorTy :=
          match LookupList.get? ctors cname with
          | some ctor => ctor.toTy.pretty
          | none => prettyCtorName cname
        match takeFirstKind bs .ctor with
        | some (b, rest) =>
          bs := rest
          out := out ++ [{
            name := b.name, kind := "ctor", type_ := ctorTy,
            span := b.span, scope := programScope
          }]
        | none => pure ()
    for ⟨_, σ?⟩ in valTys do
      let (bs1, out1, pi1, pai1) :=
        flushRhsBinders bs out paramTys paramScopes pi patTys patScopes pai
      bs := bs1; out := out1; pi := pi1; pai := pai1
      match bs with
      | b :: rest =>
        if b.kind == .val then
          bs := rest
          let sc := valScopes[vi]?.getD b.span
          vi := vi + 1
          let typeStr :=
            match σ? with
            | some σ => σ.pretty
            | none => ""
          out := out ++ [{
            name := b.name, kind := "val", type_ := typeStr,
            span := b.span, scope := sc
          }]
          let (bs2, out2) := peelSchemeBinders bs out
          bs := bs2; out := out2
        else
          pure ()
      | [] => pure ()
    let (bs3, out3, _, _) :=
      flushRhsBinders bs out paramTys paramScopes pi patTys patScopes pai
    bs := bs3; out := out3
    for b in bs do
      let sc := b.scope?.getD b.span
      let typeStr :=
        if b.kind == .param && b.scope?.isSome then "type variable (scheme binder)"
        else ""
      out := out ++ [{
        name := b.name, kind := b.kind.toString, type_ := typeStr,
        span := b.span, scope := sc
      }]
    return out

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

/-- Full hover report for a parsed program + binder spans + spanned program. -/
def collectHover (src : String) (p : Surface.Program) (binders : List BinderSpan)
    (sp : SpannedProgram) : Option (List RangedSymbol × String) := do
  let userCore ← lowerDataDeclsIn preludeKindEnv p.decls
  let ctors ← elabDecls (preludeDecls ++ userCore)
  let ke := DataDecls.kindEnv (preludeDecls ++ userCore)
  let c ← lower ctors p.term
  let (_, _, eOut, τ) ← infer c.freshFloor ⟨[], ctors⟩ c
  let valTys := collectValTypesOpt ctors ke p eOut
  let params := collectParamTypes ctors ke p eOut
  let pats := collectPatTypesProg ctors ke p eOut
  let valScopes := collectValScopes p sp |>.map (·.2)
  let paramScopes := collectParamScopes p sp |>.map (·.2)
  let patScopes := collectPatScopes p sp
  let progScope := programWideScope binders sp
  let binderSyms :=
    joinRangedSymbols binders p valTys valScopes params paramScopes pats patScopes
      ctors progScope sp.declSpans
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
