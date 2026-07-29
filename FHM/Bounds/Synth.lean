import FHM.Bounds.Typing
import FHM.Pretty

/-!
# Executable HasBounds synthesizer (slice 4)

Origin-based Core → `BoundsTy` walk mirroring declarative `HasBounds`.
Does **not** invent list intervals from bare `List` (D22). Nil’s `[0,0]` is an
origin. Unascribed List λ-params fail (D24 deferred).
-/

namespace FHM.Bounds.Synth

open FHM.Bounds

instance : Inhabited BoundsTy := ⟨.prim .unit⟩
instance : Inhabited Ty := ⟨.prim .unit⟩
instance : Inhabited (Ty × BoundsTy) := ⟨(.prim .unit, .prim .unit)⟩

/-- Forget intervals — recover an HM spine from `BoundsTy` (for app domain types). -/
def BoundsTy.toTy : BoundsTy → Ty
  | .prim p => .prim p
  | .arrow a b => .arrow (BoundsTy.toTy a) (BoundsTy.toTy b)
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .list _ _ e => listTy (BoundsTy.toTy e)
  | .custom n as => .customTy n (as.map BoundsTy.toTy)

/-- Structural Agrees template for non-origin positions (Nil elem, non-List λ
params, prim ops). List intervals here are still scaffold — only used when an
origin does not supply them (e.g. Nil’s element type). -/
def elemBounds : Ty → BoundsTy := defaultBounds

/-- Executable `Sub Δ β β'`. List proper-subtype uses `checkValid` (Z3). -/
partial def checkSub (Δ : List Constraint) : BoundsTy → BoundsTy → Bool
  | .prim p, .prim q => p == q
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .arrow a b, .arrow a' b' =>
      checkSub Δ a' a && checkSub Δ b b'
  | .list lo hi e, .list lo' hi' e' =>
      if lo == lo' && hi == hi' then
        checkSub Δ e e'
      else if !lo'.isDemandOK || !hi'.isDemandOK then
        false
      else
        checkValid (Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩) == .valid
          && checkSub Δ e e'
  | .custom n as, .custom m bs =>
      n == m && as.length == bs.length &&
        (as.zip bs).all fun ⟨a, b⟩ => checkSub Δ a b
  | _, _ => false

/-- Solid ascription only (holes fail until Live runs `ElabAnn`). -/
def checkMeetsAscription (Δ : List Constraint) (β : BoundsTy) (ann : BoundsAnnTy) : Bool :=
  match BoundsAnnTy.toBoundsTy? ann with
  | none => false
  | some β' => checkSub Δ β β'

private partial def tyEq : Ty → Ty → Bool
  | .prim p, .prim q => p == q
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .arrow a b, .arrow a' b' => tyEq a a' && tyEq b b'
  | .customTy n as, .customTy m bs =>
      n == m && as.length == bs.length &&
        (as.zip bs).all fun ⟨a, b⟩ => tyEq a b
  | _, _ => false

private partial def prettyβ : BoundsTy → String
  | .prim p =>
      match p with
      | .unit => "Unit" | .int => "Int" | .nat => "Nat" | .char => "Char"
  | .arrow a b => s!"{prettyβ a} → {prettyβ b}"
  | .bvar i => s!"β{i}"
  | .fvar i => s!"?β{i}"
  | .list lo hi e =>
      let p : Count → String
        | .lit n => toString n
        | .inf => "∞"
        | c => reprStr c
      s!"BL {p lo} {p hi} {prettyβ e}"
  | .custom n as =>
      let nm := match n with | .mk s => s
      if as.isEmpty then nm
      else nm ++ " " ++ String.intercalate " " (as.map prettyβ)

mutual

/-- List match: Nil+Cons join, or single-branch under oracle emptiness. -/
partial def synthMatch (Δ : List Constraint) (bctx : BoundEnv)
    (_α : Ty) (lo hi : Count) (βe : BoundsTy) :
    List (MatchPattern × Expr) → Except String (Ty × BoundsTy)
  | [(.named n 0, eNil), (.named c 2, eCons)] => do
      unless n == nilCtorName && c == consCtorName do
        throw "bounds: expected Nil/Cons match arms"
      let Δnil := Δ ++ nilRefine lo hi
      let (τ, βnil) ← inferBounds Δnil bctx eNil
      let Δcons := Δ ++ consRefine hi
      let βcons ← checkBounds Δcons (consBoundEnv bctx lo hi βe) eCons τ
      match joinBoundsTy βnil βcons with
      | some β => pure (τ, β)
      | none => throw "bounds: match branches have incompatible bounds"
  | [(.named n 0, eNil)] => do
      unless n == nilCtorName do throw "bounds: expected Nil-only arm"
      unless checkValid (mustBeEmpty Δ hi) == .valid do
        throw "bounds: Nil-only match but upper bound not proved empty"
      inferBounds (Δ ++ nilRefine lo hi) bctx eNil
  | [(.named c 2, eCons)] => do
      unless c == consCtorName do throw "bounds: expected Cons-only arm"
      unless checkValid (mustBeNonempty Δ lo) == .valid do
        throw "bounds: Cons-only match but lower bound not proved nonempty"
      inferBounds (Δ ++ consRefine hi) (consBoundEnv bctx lo hi βe) eCons
  | _ =>
      throw "bounds: unsupported match shape (want Nil+Cons or single arm)"

/-- Infer mode: synthesize both HM spine and bounds. -/
partial def inferBounds (Δ : List Constraint) (bctx : BoundEnv) :
    Expr → Except String (Ty × BoundsTy)
  | .primLit p =>
      pure (PrimLitExpr.ty p, boundInfoOfPrimLit p)
  | .var i _tyArgs =>
      match bctx[i]? with
      | none => .error s!"bounds: unbound var {i}"
      | some β => pure (BoundsTy.toTy β, β)
  | .ctor name =>
      if name == nilCtorName then
        .error "bounds: Nil needs an expected List type"
      else
        .error s!"bounds: cannot infer bounds for ctor {repr name}"
  | .primBinOp op =>
      .error s!"bounds: primBinOp {repr op} needs expected type"
  | .app f arg => do
      let (τf, βf) ← inferBounds Δ bctx f
      match τf, βf with
      | .arrow τa τr, .arrow βa βr => do
          let βa' ← checkBounds Δ bctx arg τa
          unless checkSub Δ βa' βa do
            throw "bounds: argument does not meet function domain"
          pure (τr, βr)
      | _, _ =>
          throw "bounds: applying a non-function"
  | .lambda paramAnn body => do
      let τp ← match paramAnn with
        | some t => pure t
        | none => throw "bounds: lambda param needs a type ascription for synth"
      if (isListTy τp).isSome then
        throw "bounds: unascribed List λ-param (annotate with BL, or wait for D24)"
      let βp := elemBounds τp
      let (τb, βb) ← inferBounds Δ (βp :: bctx) body
      pure (.arrow τp τb, .arrow βp βb)
  | .letIn ann? rhs body => do
      let β1 ← match ann? with
        | some σ => checkBounds Δ bctx rhs σ.body
        | none => Prod.snd <$> inferBounds Δ bctx rhs
      inferBounds Δ (β1 :: bctx) body
  | .letRec anns bindings body => do
      if anns.length != bindings.length then
        throw "bounds: letRec anns/bindings length mismatch"
      -- Core scheme is HM (List after erase). BL lives in ofLower anns — do not
      -- demand BL on σ here. Synth RHS at σ.body (Nil/Cons origins for List).
      let βs ← anns.zip bindings |>.mapM fun ⟨ann?, rhs⟩ => do
        match ann? with
        | some σ => checkBounds Δ bctx rhs σ.body
        | none => Prod.snd <$> inferBounds Δ bctx rhs
      -- Approximate mutual: synth each under outer bctx only (fine for non-recursive
      -- list literals). Recursive List members need binder anns via checkLetSpine.
      let bctx' := βs ++ bctx
      inferBounds Δ bctx' body
  | .match_ scrut brs => do
      let (τs, βs) ← inferBounds Δ bctx scrut
      match isListTy τs, βs with
      | some α, .list lo hi βe =>
          synthMatch Δ bctx α lo hi βe brs
      | _, _ =>
          throw "bounds: match on non-List (HM exh covers these; BoundCovers later)"

/-- Check mode: given expected `τ`, synthesize `β`. -/
partial def checkBounds (Δ : List Constraint) (bctx : BoundEnv)
    (e : Expr) (τ : Ty) : Except String BoundsTy := do
  match e with
  | .primLit p => do
      unless tyEq (PrimLitExpr.ty p) τ do
        throw "bounds: prim lit type mismatch"
      pure (boundInfoOfPrimLit p)
  | .var i _tyArgs => do
      match bctx[i]? with
      | none => throw s!"bounds: unbound var {i}"
      | some β =>
          let _ := τ
          pure β
  | .ctor name => do
      if name == nilCtorName then
        match isListTy τ with
        | some α => pure (.list (.lit 0) (.lit 0) (elemBounds α))
        | none => throw "bounds: Nil at non-List type"
      else if name == consCtorName then
        throw "bounds: bare Cons ctor (expected saturated Cons apps)"
      else
        if (isListTy τ).isSome then
          throw "bounds: non-Nil ctor at List type"
        pure (elemBounds τ)
  | .primBinOp _op =>
      pure (elemBounds τ)
  | .app f arg => do
      match f, isListTy τ with
      | .app (.ctor c) h, some α =>
          if c == consCtorName then do
            let βh ← checkBounds Δ bctx h α
            let βt ← checkBounds Δ bctx arg (listTy α)
            match βt with
            | .list lo hi βe => do
                unless checkSub Δ βh βe do
                  throw "bounds: Cons head does not meet element bounds"
                pure (.list (.add lo (.lit 1)) (.add hi (.lit 1)) βe)
            | _ => throw "bounds: Cons tail is not a list bounds"
          else do
            checkAppGeneral Δ bctx f arg τ
      | _, _ =>
          checkAppGeneral Δ bctx f arg τ
  | .lambda _paramAnn body => do
      match τ with
      | .arrow τp τb => do
          if (isListTy τp).isSome then
            throw "bounds: unascribed List λ-param (annotate with BL, or wait for D24)"
          let βp := elemBounds τp
          let βb ← checkBounds Δ (βp :: bctx) body τb
          pure (.arrow βp βb)
      | _ => throw "bounds: lambda at non-arrow type"
  | .letIn ann? rhs body => do
      let β1 ← match ann? with
        | some σ => checkBounds Δ bctx rhs σ.body
        | none => Prod.snd <$> inferBounds Δ bctx rhs
      checkBounds Δ (β1 :: bctx) body τ
  | .letRec anns bindings body => do
      if anns.length != bindings.length then
        throw "bounds: letRec anns/bindings length mismatch"
      let βs ← anns.zip bindings |>.mapM fun ⟨ann?, rhs⟩ => do
        match ann? with
        | some σ => checkBounds Δ bctx rhs σ.body
        | none => Prod.snd <$> inferBounds Δ bctx rhs
      let bctx' := βs ++ bctx
      checkBounds Δ bctx' body τ
  | .match_ scrut brs => do
      let (τs, βs) ← inferBounds Δ bctx scrut
      match isListTy τs, βs with
      | some α, .list lo hi βe => do
          let (_τ, β) ← synthMatch Δ bctx α lo hi βe brs
          let _ := τ
          pure β
      | _, _ =>
          throw "bounds: match on non-List"

partial def checkAppGeneral (Δ : List Constraint) (bctx : BoundEnv)
    (f arg : Expr) (τ : Ty) : Except String BoundsTy := do
  let (τf, βf) ← inferBounds Δ bctx f
  match τf, βf with
  | .arrow τa τr, .arrow βa βr => do
      unless tyEq τr τ do
        throw "bounds: app result type mismatch"
      let βa' ← checkBounds Δ bctx arg τa
      unless checkSub Δ βa' βa do
        throw "bounds: argument does not meet function domain"
      pure βr
  | _, _ => throw "bounds: applying a non-function"

end

/-- Top-level entry: synth `β` for `e` at HM type `τ`. -/
def synthBounds (Δ : List Constraint) (bctx : BoundEnv) (e : Expr) (τ : Ty) :
    Except String BoundsTy :=
  checkBounds Δ bctx e τ

/-- Check against demanded β (executable `CheckBounds.ofSub`).

For λ with demanded `.arrow βp βb`, push `βp` from ascription (no List invention). -/
partial def checkAgainst (Δ : List Constraint) (bctx : BoundEnv)
    (e : Expr) (τ : Ty) (β : BoundsTy) : Except String Unit := do
  match e, τ, β with
  | .lambda _ body, .arrow _τp τb, .arrow βp βb =>
      checkAgainst Δ (βp :: bctx) body τb βb
  | .letIn ann? rhs body, τ', β' => do
      let β1 ← match ann? with
        | some σ => checkBounds Δ bctx rhs σ.body
        | none => Prod.snd <$> inferBounds Δ bctx rhs
      checkAgainst Δ (β1 :: bctx) body τ' β'
  | _, _, _ => do
      let β' ← checkBounds Δ bctx e τ
      unless checkSub Δ β' β do
        throw s!"bounds: synthesized {prettyβ β'} does not meet demand {prettyβ β}"

end FHM.Bounds.Synth
