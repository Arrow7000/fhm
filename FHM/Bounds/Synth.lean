import FHM.Bounds.Typing
import FHM.Pretty

/-!
# Executable HasBounds synthesizer (slices 4–7)

Origin-based Core → `BoundsTy` walk mirroring declarative `HasBounds`.
Does **not** invent list intervals from bare `List` (D22). Nil’s `[0,0]` is an
origin. Unascribed List λ-params get fresh `?lo`/`?hi` (D24). Schemes
instantiate at var use via `BoundBinding.scheme`.
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

/-- Rank-1 app meet: when `checkSub` ∀ fails, still accept concrete intervals into
fresh inferable demands (`BL ?i ?j` / `BL ?n ?n`), and prims into HM type stubs. -/
def checkSubInst (Δ : List Constraint) (got want : BoundsTy) : Bool :=
  if checkSub Δ got want then true
  else
    match got, want with
    | .prim _, .fvar _ => true
    | .prim _, .bvar _ => true
    | .list glo ghi ge, .list wlo whi we =>
        checkSubInst Δ ge we &&
          match wlo, whi with
          | .var ⟨.inferable, i⟩, .var ⟨.inferable, j⟩ =>
              if i == j then glo == ghi else true
          | _, _ => false
    | .arrow da ca, .arrow db cb =>
        checkSubInst Δ db da && checkSubInst Δ ca cb
    | _, _ => false
termination_by sizeOf got + sizeOf want

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

/-- Look up env slot; schemes instantiate at fresh inferables from `Φ`,
then fill HM type stubs from Core `tyArgs`. -/
def lookupBound (bctx : BoundEnv) (Φ : Nat) (i : Nat) (tyArgs : List Ty) :
    Except String (Nat × BoundsTy) :=
  match bctx[i]? with
  | none => throw s!"bounds: unbound var {i}"
  | some (.mono β) =>
      -- Mono: only fill leftover erase fvar stubs; keep real bvars.
      pure (Φ, β.instTyArgs [])
  | some (.scheme s) =>
      let (Φ', β) := s.openFresh Φ
      pure (Φ', β.instTyArgs tyArgs)

/-- D24: List param gets fresh `?lo`/`?hi`; non-List uses `agreesTemplate`. -/
def freshParamBounds (Φ : Nat) (τp : Ty) : Nat × BoundsTy :=
  match isListTy τp with
  | some α =>
      (Φ + 2,
        .list (.var ⟨.inferable, Φ⟩) (.var ⟨.inferable, Φ + 1⟩) (agreesTemplate α))
  | none => (Φ, agreesTemplate τp)

mutual

/-- Synth letRec binders under outer `bctx` (list-structural on `bindings`). -/
def inferLetRecGroup (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    Except String (Nat × List BoundsTy) :=
  match anns, bindings with
  | [], [] => pure (Φ, [])
  | ann? :: anns', rhs :: bindings' => do
      let (Φ1, β) ← match ann? with
        | some σ => checkBoundsΦ Δ bctx Φ rhs σ.body
        | none => do
            let (Φ', _, β) ← inferBoundsΦ Δ bctx Φ rhs
            pure (Φ', β)
      let (Φ2, βs) ← inferLetRecGroup Δ bctx Φ1 anns' bindings'
      pure (Φ2, β :: βs)
  | _, _ => throw "bounds: letRec anns/bindings length mismatch"
termination_by Expr.sizeRecGroup bindings
decreasing_by all_goals (simp_wf; simp [Expr.sizeRecGroup, Expr.size]; try omega)

/-- List match: Nil+Cons join (either arm order), or single-branch under oracle. -/
def synthMatch (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (_α : Ty) (lo hi : Count) (βe : BoundsTy)
    (brs : List (MatchPattern × Expr)) : Except String (Nat × Ty × BoundsTy) :=
  match brs with
  | [(.named n 0, eNil), (.named c 2, eCons)] => do
      unless n == nilCtorName && c == consCtorName do
        throw "bounds: expected Nil/Cons match arms"
      let Δnil := Δ ++ nilRefine lo hi
      let (Φ1, τ, βnil) ← inferBoundsΦ Δnil bctx Φ eNil
      let Δcons := Δ ++ consRefine hi
      let (Φ2, βcons) ← checkBoundsΦ Δcons (consBoundEnv bctx lo hi βe) Φ1 eCons τ
      match joinBoundsTy βnil βcons with
      | some β => pure (Φ2, τ, β)
      | none => throw "bounds: match branches have incompatible bounds"
  | [(.named c 2, eCons), (.named n 0, eNil)] => do
      unless n == nilCtorName && c == consCtorName do
        throw "bounds: expected Nil/Cons match arms"
      let Δnil := Δ ++ nilRefine lo hi
      let (Φ1, τ, βnil) ← inferBoundsΦ Δnil bctx Φ eNil
      let Δcons := Δ ++ consRefine hi
      let (Φ2, βcons) ← checkBoundsΦ Δcons (consBoundEnv bctx lo hi βe) Φ1 eCons τ
      match joinBoundsTy βnil βcons with
      | some β => pure (Φ2, τ, β)
      | none => throw "bounds: match branches have incompatible bounds"
  | [(.named n 0, eNil)] => do
      unless n == nilCtorName do throw "bounds: expected Nil-only arm"
      unless checkValid (mustBeEmpty Δ hi) == .valid do
        throw "bounds: Nil-only match but upper bound not proved empty"
      inferBoundsΦ (Δ ++ nilRefine lo hi) bctx Φ eNil
  | [(.named c 2, eCons)] => do
      unless c == consCtorName do throw "bounds: expected Cons-only arm"
      unless checkValid (mustBeNonempty Δ lo) == .valid do
        throw "bounds: Cons-only match but lower bound not proved nonempty"
      inferBoundsΦ (Δ ++ consRefine hi) (consBoundEnv bctx lo hi βe) Φ eCons
  | _ =>
      throw "bounds: unsupported match shape (want Nil+Cons or single arm)"
termination_by Expr.sizeBranches brs
decreasing_by all_goals (first | exact size_lt_sizeBranches_two | exact size_lt_sizeBranches_two_snd | exact size_lt_sizeBranches_one | (try simp only [Expr.size, Expr.sizeBranches]; omega))

/-- Check mode for generic `f arg` (infer fn spine, check arg). -/
def checkBoundsApp (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (f arg : Expr) (τ : Ty) : Except String (Nat × BoundsTy) := do
  let (Φ1, τf, βf) ← inferBoundsΦ Δ bctx Φ f
  match τf, βf with
  | .arrow τa τr, .arrow βa βr => do
      -- HM types already checked by Infer; bounds spine may use bvar/fvar stubs.
      let (Φ2, βa') ← checkBoundsΦ Δ bctx Φ1 arg τa
      unless checkSubInst Δ βa' βa do
        throw "bounds: argument does not meet function domain"
      pure (Φ2, βr)
  | _, _ => throw "bounds: applying a non-function"
termination_by f.size + arg.size
decreasing_by all_goals (simp_wf; have := Expr.size_pos arg; have := Expr.size_pos f; omega)

/-- Infer mode: synthesize both HM spine and bounds; thread freshness `Φ`. -/
def inferBoundsΦ (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat) (e : Expr) :
    Except String (Nat × Ty × BoundsTy) :=
  match e with
  | .primLit p =>
      pure (Φ, PrimLitExpr.ty p, boundInfoOfPrimLit p)
  | .var i tyArgs => do
      let (Φ', β) ← lookupBound bctx Φ i tyArgs
      pure (Φ', BoundsTy.toTy β, β)
  | .ctor name =>
      if name == nilCtorName then
        .error "bounds: Nil needs an expected List type"
      else
        .error s!"bounds: cannot infer bounds for ctor {repr name}"
  | .primBinOp op =>
      .error s!"bounds: primBinOp {repr op} needs expected type"
  | .app f arg => do
      let (Φ1, τf, βf) ← inferBoundsΦ Δ bctx Φ f
      match τf, βf with
      | .arrow τa τr, .arrow βa βr => do
          let (Φ2, βa') ← checkBoundsΦ Δ bctx Φ1 arg τa
          unless checkSubInst Δ βa' βa do
            throw "bounds: argument does not meet function domain"
          pure (Φ2, τr, βr)
      | _, _ =>
          throw "bounds: applying a non-function"
  | .lambda paramAnn body => do
      let τp ← match paramAnn with
        | some t => pure t
        | none => throw "bounds: lambda param needs a type ascription for synth"
      let (Φ1, βp) := freshParamBounds Φ τp
      let (Φ2, τb, βb) ← inferBoundsΦ Δ (BoundEnv.extend bctx βp) Φ1 body
      pure (Φ2, .arrow τp τb, .arrow βp βb)
  | .letIn ann? rhs body => do
      let (Φ1, β1) ← match ann? with
        | some σ => checkBoundsΦ Δ bctx Φ rhs σ.body
        | none => do
            let (Φ', _, β) ← inferBoundsΦ Δ bctx Φ rhs
            pure (Φ', β)
      inferBoundsΦ Δ (BoundEnv.extend bctx β1) Φ1 body
  | .letRec anns bindings body => do
      if anns.length != bindings.length then
        throw "bounds: letRec anns/bindings length mismatch"
      let (Φ1, βs) ← inferLetRecGroup Δ bctx Φ anns bindings
      inferBoundsΦ Δ (BoundEnv.extendMany bctx βs) Φ1 body
  | .match_ scrut brs => do
      let (Φ1, τs, βs) ← inferBoundsΦ Δ bctx Φ scrut
      match isListTy τs, βs with
      | some α, .list lo hi βe =>
          synthMatch Δ bctx Φ1 α lo hi βe brs
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

/-- Check mode: given expected `τ`, synthesize `β`; thread freshness `Φ`. -/
def checkBoundsΦ (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (e : Expr) (τ : Ty) : Except String (Nat × BoundsTy) := do
  match e with
  | .primLit p => do
      -- HM type already checked by Infer; bounds are prim-shaped.
      let _ := τ
      pure (Φ, boundInfoOfPrimLit p)
  | .var i tyArgs => do
      let (Φ', β) ← lookupBound bctx Φ i tyArgs
      let _ := τ
      pure (Φ', β)
  | .ctor name => do
      if name == nilCtorName then
        match isListTy τ with
        | some α => pure (Φ, .list (.lit 0) (.lit 0) (agreesTemplate α))
        | none => throw "bounds: Nil at non-List type"
      else if name == consCtorName then
        throw "bounds: bare Cons ctor (expected saturated Cons apps)"
      else
        if (isListTy τ).isSome then
          throw "bounds: non-Nil ctor at List type"
        pure (Φ, agreesTemplate τ)
  | .primBinOp _op =>
      pure (Φ, agreesTemplate τ)
  | .app (.app (.ctor c) h) arg =>
      match isListTy τ with
      | some α =>
          if c == consCtorName then do
            let (Φ1, βh) ← checkBoundsΦ Δ bctx Φ h α
            let (Φ2, βt) ← checkBoundsΦ Δ bctx Φ1 arg (listTy α)
            match βt with
            | .list lo hi βe => do
                unless checkSubInst Δ βh βe do
                  throw "bounds: Cons head does not meet element bounds"
                pure (Φ2, .list (.add lo (.lit 1)) (.add hi (.lit 1)) βe)
            | _ => throw "bounds: Cons tail is not a list bounds"
          else
            checkBoundsApp Δ bctx Φ (.app (.ctor c) h) arg τ
      | none =>
          checkBoundsApp Δ bctx Φ (.app (.ctor c) h) arg τ
  | .app f arg =>
      checkBoundsApp Δ bctx Φ f arg τ
  | .lambda _paramAnn body => do
      match τ with
      | .arrow τp τb => do
          let (Φ1, βp) := freshParamBounds Φ τp
          let (Φ2, βb) ← checkBoundsΦ Δ (BoundEnv.extend bctx βp) Φ1 body τb
          pure (Φ2, .arrow βp βb)
      | _ => throw "bounds: lambda at non-arrow type"
  | .letIn ann? rhs body => do
      let (Φ1, β1) ← match ann? with
        | some σ => checkBoundsΦ Δ bctx Φ rhs σ.body
        | none => do
            let (Φ', _, β) ← inferBoundsΦ Δ bctx Φ rhs
            pure (Φ', β)
      checkBoundsΦ Δ (BoundEnv.extend bctx β1) Φ1 body τ
  | .letRec anns bindings body => do
      if anns.length != bindings.length then
        throw "bounds: letRec anns/bindings length mismatch"
      let (Φ1, βs) ← inferLetRecGroup Δ bctx Φ anns bindings
      checkBoundsΦ Δ (BoundEnv.extendMany bctx βs) Φ1 body τ
  | .match_ scrut brs => do
      let (Φ1, τs, βs) ← inferBoundsΦ Δ bctx Φ scrut
      match isListTy τs, βs with
      | some α, .list lo hi βe => do
          let (Φ2, _τ, β) ← synthMatch Δ bctx Φ1 α lo hi βe brs
          let _ := τ
          pure (Φ2, β)
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

/-- Infer without exposing freshness (starts at `Φ = 0`). -/
def inferBounds (Δ : List Constraint) (bctx : BoundEnv) (e : Expr) :
    Except String (Ty × BoundsTy) := do
  let (_, τ, β) ← inferBoundsΦ Δ bctx 0 e
  pure (τ, β)

/-- Check without exposing freshness (starts at `Φ = 0`). -/
def checkBounds (Δ : List Constraint) (bctx : BoundEnv)
    (e : Expr) (τ : Ty) : Except String BoundsTy := do
  Prod.snd <$> checkBoundsΦ Δ bctx 0 e τ

/-- Top-level entry: synth `β` for `e` at HM type `τ`. -/
def synthBounds (Δ : List Constraint) (bctx : BoundEnv) (e : Expr) (τ : Ty) :
    Except String BoundsTy :=
  checkBounds Δ bctx e τ

/-- Check against demanded β (executable `CheckBounds.ofSub`).

For λ with demanded `.arrow βp βb`, push `βp` from ascription (no List invention).
Peels Infer’s singleton `letRec` wrapper (`let f = (let rec f = λ… in f)`). -/
def checkAgainstΦ (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (e : Expr) (τ : Ty) (β : BoundsTy) : Except String Nat := do
  match e, τ, β with
  | .lambda _ body, .arrow _τp τb, .arrow βp βb =>
      checkAgainstΦ Δ (BoundEnv.extend bctx βp) Φ body τb βb
  | .letIn ann? rhs body, τ', β' => do
      let (Φ1, β1) ← match ann? with
        | some σ => checkBoundsΦ Δ bctx Φ rhs σ.body
        | none => do
            let (Φ', _, β) ← inferBoundsΦ Δ bctx Φ rhs
            pure (Φ', β)
      checkAgainstΦ Δ (BoundEnv.extend bctx β1) Φ1 body τ' β'
  | .letRec _anns bindings body, τ', β' => do
      match bindings with
      | [rhs] => do
          let Φ1 ← checkAgainstΦ Δ (BoundEnv.extend bctx β') Φ rhs τ' β'
          checkAgainstΦ Δ (BoundEnv.extend bctx β') Φ1 body τ' β'
      | _ => do
          let (Φ1, β₀) ← checkBoundsΦ Δ bctx Φ e τ'
          unless checkSub Δ β₀ β' do
            throw s!"bounds: synthesized {prettyβ β₀} does not meet demand {prettyβ β'}"
          pure Φ1
  | _, _, _ => do
      let (Φ1, β') ← checkBoundsΦ Δ bctx Φ e τ
      unless checkSubInst Δ β' β do
        throw s!"bounds: synthesized {prettyβ β'} does not meet demand {prettyβ β}"
      pure Φ1
termination_by e.size
decreasing_by all_goals (try simp only [Expr.size, Expr.sizeRecGroup]; omega)

def checkAgainst (Δ : List Constraint) (bctx : BoundEnv)
    (e : Expr) (τ : Ty) (β : BoundsTy) : Except String Unit := do
  let _ ← checkAgainstΦ Δ bctx 0 e τ β
  pure ()
