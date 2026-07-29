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

/-- Forget intervals — recover an HM spine from `BoundsTy` (for app domain types). -/
def BoundsTy.toTy : BoundsTy → Ty
  | .prim p => .prim p
  | .arrow a b => .arrow (BoundsTy.toTy a) (BoundsTy.toTy b)
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .list _ _ e => listTy (BoundsTy.toTy e)
  | .custom n as => .customTy n (as.map BoundsTy.toTy)

mutual
/-- Executable `Sub Δ β β'`. List proper-subtype uses `checkValid` (Z3). -/
def checkSub (Δ : List Constraint) (a b : BoundsTy) : Bool :=
  match a, b with
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
      n == m && as.length == bs.length && checkSubAll Δ as bs
  | _, _ => false
termination_by sizeOf a + sizeOf b

def checkSubAll (Δ : List Constraint) (as bs : List BoundsTy) : Bool :=
  match as, bs with
  | [], [] => true
  | a :: as, b :: bs => checkSub Δ a b && checkSubAll Δ as bs
  | _, _ => false
termination_by sizeOf as + sizeOf bs
decreasing_by
  all_goals (simp_wf; try omega)
end

/-- Solid ascription only (no hole fill). Prefer `checkMeetsAscriptionPinned` under `--bl`. -/
def checkMeetsAscription (Δ : List Constraint) (β : BoundsTy) (ann : BoundsAnnTy) : Bool :=
  match BoundsAnnTy.toBoundsTy? ann with
  | none => false
  | some β' => checkSub Δ β β'

mutual
def tyEq (a b : Ty) : Bool :=
  match a, b with
  | .prim p, .prim q => p == q
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .arrow a b, .arrow a' b' => tyEq a a' && tyEq b b'
  | .customTy n as, .customTy m bs =>
      n == m && as.length == bs.length && tyEqAll as bs
  | _, _ => false
termination_by sizeOf a + sizeOf b

def tyEqAll (as bs : List Ty) : Bool :=
  match as, bs with
  | [], [] => true
  | a :: as, b :: bs => tyEq a b && tyEqAll as bs
  | _, _ => false
termination_by sizeOf as + sizeOf bs
decreasing_by
  all_goals (simp_wf; try omega)
end

private def prettyβ : BoundsTy → String
  | .prim p =>
      match p with
      | .unit => "Unit" | .int => "Int" | .nat => "Nat" | .char => "Char"
  | .arrow a b =>
      let sa := prettyβ a
      let sb := prettyβ b
      s!"{sa} → {sb}"
  | .bvar i => s!"β{i}"
  | .fvar i => s!"?β{i}"
  | .list lo hi e =>
      let se := prettyβ e
      s!"BL {Count.pretty lo} {Count.pretty hi} {se}"
  | .custom n as =>
      let nm := match n with | .mk s => s
      if as.isEmpty then nm
      else nm ++ " " ++ String.intercalate " " (as.map prettyβ)

/-- Pin ascription count hole to the synth Count; keep solid ascription counts. -/
def pinCount : AnnoCount → Count → Count
  | .hole, c => c
  | .solid c, _ => c

mutual
/-- Fill `_` holes in `ann` from matching slots of origin-synth `β` (pin-to-synth).

Spine of `ann` must match `β`. Solid counts are kept from the ascription; holes
copy the corresponding `Count` from `β`. Then caller checks `Sub β (pin …)`. -/
def pinHoles (ann : BoundsAnnTy) (β : BoundsTy) : Except String BoundsTy :=
  match ann, β with
  | .prim p, .prim q =>
      if p == q then pure (.prim p)
      else throw "bounds: pinHoles prim mismatch"
  | .bvar i, .bvar j =>
      if i == j then pure (.bvar i)
      else throw "bounds: pinHoles bvar mismatch"
  | .fvar i, .fvar j =>
      if i == j then pure (.fvar i)
      else throw "bounds: pinHoles fvar mismatch"
  | .arrow d c, .arrow βd βc => do
      let d' ← pinHoles d βd
      let c' ← pinHoles c βc
      pure (.arrow d' c')
  | .list lo hi e, .list loβ hiβ eβ => do
      let e' ← pinHoles e eβ
      pure (.list (pinCount lo loβ) (pinCount hi hiβ) e')
  | .custom n as, .custom m bs => do
      if n != m then throw "bounds: pinHoles custom name mismatch"
      if as.length != bs.length then throw "bounds: pinHoles custom arity mismatch"
      let args ← pinHolesAll as bs
      pure (.custom n args)
  | _, _ => throw "bounds: pinHoles shape mismatch"
termination_by sizeOf ann

def pinHolesAll (as : List BoundsAnnTy) (bs : List BoundsTy) : Except String (List BoundsTy) :=
  match as, bs with
  | [], [] => pure []
  | a :: as, b :: bs => do
      let a' ← pinHoles a b
      let rest ← pinHolesAll as bs
      pure (a' :: rest)
  | _, _ => throw "bounds: pinHoles custom args length mismatch"
termination_by sizeOf as
decreasing_by
  all_goals (simp_wf; try omega)
end

/-- Synth `β` meets ascription `ann` after pin-to-synth hole fill. -/
def checkMeetsAscriptionPinned (Δ : List Constraint) (β : BoundsTy) (ann : BoundsAnnTy) :
    Except String Unit := do
  let βann ← pinHoles ann β
  unless checkSub Δ β βann do
    throw s!"bounds: synthesized {prettyβ β} ≰ pinned ascription {prettyβ βann}"

private theorem size_lt_sizeBranches_one {p : MatchPattern} {e : Expr} :
    e.size < Expr.sizeBranches [(p, e)] := by
  simp [Expr.sizeBranches]

private theorem size_lt_sizeBranches_two {p1 p2 : MatchPattern} {e1 e2 : Expr} :
    e1.size < Expr.sizeBranches [(p1, e1), (p2, e2)] := by
  simp [Expr.sizeBranches]
  have := Expr.size_pos e2
  omega

private theorem size_lt_sizeBranches_two_snd {p1 p2 : MatchPattern} {e1 e2 : Expr} :
    e2.size < Expr.sizeBranches [(p1, e1), (p2, e2)] := by
  simp [Expr.sizeBranches]
  have := Expr.size_pos e1
  omega

private theorem expr_size_lt_double_app_ctor {c : CtorName} {h arg : Expr} :
    h.size < (((Expr.ctor c).app h).app arg).size := by
  simp [Expr.size]
  have := Expr.size_pos arg
  omega

private theorem add_sizes_lt_app {f arg : Expr} :
    f.size + arg.size < (f.app arg).size := by
  simp [Expr.size]

private theorem size_lt_app_fn {f arg : Expr} : f.size < (f.app arg).size := by
  simp [Expr.size]
  have := Expr.size_pos arg
  omega

private theorem size_lt_app_arg {f arg : Expr} : arg.size < (f.app arg).size := by
  simp [Expr.size]

private theorem body_size_lt_letRec {anns : List (Option PolyTy)} {bindings : List Expr}
    {body : Expr} :
    body.size < (Expr.letRec anns bindings body).size := by
  simp [Expr.size]

private theorem sizeRecGroup_lt_letRec {anns : List (Option PolyTy)} {bindings : List Expr}
    {body : Expr} :
    Expr.sizeRecGroup bindings < (Expr.letRec anns bindings body).size := by
  simp [Expr.size]
  have := Expr.size_pos body
  omega

mutual

/-- Synth letRec binders under outer `bctx` (list-structural on `bindings`). -/
def inferLetRecGroup (Δ : List Constraint) (bctx : BoundEnv)
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    Except String (List BoundsTy) :=
  match anns, bindings with
  | [], [] => pure []
  | ann? :: anns', rhs :: bindings' => do
      let β ← match ann? with
        | some σ => checkBounds Δ bctx rhs σ.body
        | none => Prod.snd <$> inferBounds Δ bctx rhs
      let βs ← inferLetRecGroup Δ bctx anns' bindings'
      pure (β :: βs)
  | _, _ => throw "bounds: letRec anns/bindings length mismatch"
termination_by Expr.sizeRecGroup bindings
decreasing_by all_goals (simp_wf; simp [Expr.sizeRecGroup, Expr.size]; try omega)

/-- List match: Nil+Cons join, or single-branch under oracle emptiness. -/
def synthMatch (Δ : List Constraint) (bctx : BoundEnv)
    (_α : Ty) (lo hi : Count) (βe : BoundsTy)
    (brs : List (MatchPattern × Expr)) : Except String (Ty × BoundsTy) :=
  match brs with
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
termination_by Expr.sizeBranches brs
decreasing_by all_goals (first | exact size_lt_sizeBranches_two | exact size_lt_sizeBranches_two_snd | exact size_lt_sizeBranches_one | (try simp only [Expr.size, Expr.sizeBranches]; omega))

/-- Check mode for generic `f arg` (infer fn spine, check arg). -/
def checkBoundsApp (Δ : List Constraint) (bctx : BoundEnv) (f arg : Expr) (τ : Ty) :
    Except String BoundsTy := do
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
termination_by f.size + arg.size
decreasing_by all_goals (simp_wf; have := Expr.size_pos arg; have := Expr.size_pos f; omega)

/-- Infer mode: synthesize both HM spine and bounds. -/
def inferBounds (Δ : List Constraint) (bctx : BoundEnv) (e : Expr) :
    Except String (Ty × BoundsTy) :=
  match e with
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
      let βp := agreesTemplate τp
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
      let βs ← inferLetRecGroup Δ bctx anns bindings
      inferBounds Δ (βs ++ bctx) body
  | .match_ scrut brs => do
      let (τs, βs) ← inferBounds Δ bctx scrut
      match isListTy τs, βs with
      | some α, .list lo hi βe =>
          synthMatch Δ bctx α lo hi βe brs
      | _, _ =>
          throw "bounds: match on non-List (HM exh covers these; BoundCovers later)"
termination_by e.size
decreasing_by all_goals (
  simp_wf
  first
  | exact size_lt_app_fn
  | exact size_lt_app_arg
  | exact body_size_lt_letRec
  | exact sizeRecGroup_lt_letRec
  | (simp only [Expr.size, Expr.sizeBranches, Expr.sizeRecGroup]; omega))

/-- Check mode: given expected `τ`, synthesize `β`. -/
def checkBounds (Δ : List Constraint) (bctx : BoundEnv)
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
        | some α => pure (.list (.lit 0) (.lit 0) (agreesTemplate α))
        | none => throw "bounds: Nil at non-List type"
      else if name == consCtorName then
        throw "bounds: bare Cons ctor (expected saturated Cons apps)"
      else
        if (isListTy τ).isSome then
          throw "bounds: non-Nil ctor at List type"
        pure (agreesTemplate τ)
  | .primBinOp _op =>
      pure (agreesTemplate τ)
  | .app (.app (.ctor c) h) arg =>
      match isListTy τ with
      | some α =>
          if c == consCtorName then do
            let βh ← checkBounds Δ bctx h α
            let βt ← checkBounds Δ bctx arg (listTy α)
            match βt with
            | .list lo hi βe => do
                unless checkSub Δ βh βe do
                  throw "bounds: Cons head does not meet element bounds"
                pure (.list (.add lo (.lit 1)) (.add hi (.lit 1)) βe)
            | _ => throw "bounds: Cons tail is not a list bounds"
          else
            checkBoundsApp Δ bctx (.app (.ctor c) h) arg τ
      | none =>
          checkBoundsApp Δ bctx (.app (.ctor c) h) arg τ
  | .app f arg =>
      checkBoundsApp Δ bctx f arg τ
  | .lambda _paramAnn body => do
      match τ with
      | .arrow τp τb => do
          if (isListTy τp).isSome then
            throw "bounds: unascribed List λ-param (annotate with BL, or wait for D24)"
          let βp := agreesTemplate τp
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
      let βs ← inferLetRecGroup Δ bctx anns bindings
      checkBounds Δ (βs ++ bctx) body τ
  | .match_ scrut brs => do
      let (τs, βs) ← inferBounds Δ bctx scrut
      match isListTy τs, βs with
      | some α, .list lo hi βe => do
          let (_τ, β) ← synthMatch Δ bctx α lo hi βe brs
          let _ := τ
          pure β
      | _, _ =>
          throw "bounds: match on non-List"
termination_by e.size
decreasing_by all_goals (
  simp_wf
  first
  | exact size_lt_app_fn
  | exact size_lt_app_arg
  | exact expr_size_lt_double_app_ctor
  | exact add_sizes_lt_app
  | exact body_size_lt_letRec
  | exact sizeRecGroup_lt_letRec
  | (simp only [Expr.size, Expr.sizeBranches, Expr.sizeRecGroup]; omega))

end

/-- Top-level entry: synth `β` for `e` at HM type `τ`. -/
def synthBounds (Δ : List Constraint) (bctx : BoundEnv) (e : Expr) (τ : Ty) :
    Except String BoundsTy :=
  checkBounds Δ bctx e τ

/-- Check against demanded β (executable `CheckBounds.ofSub`).

For λ with demanded `.arrow βp βb`, push `βp` from ascription (no List invention). -/
def checkAgainst (Δ : List Constraint) (bctx : BoundEnv)
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
termination_by e.size
decreasing_by all_goals (try simp only [Expr.size]; omega)

end FHM.Bounds.Synth
