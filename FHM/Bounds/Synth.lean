import FHM.Bounds.Typing
import FHM.Bounds.Escape
import FHM.Pretty

/-!
# Executable HasBounds synthesizer (slices 4–7 + J1 + R3 residual)

Origin-based Core → `BoundsTy` walk mirroring declarative `HasBounds`.
Does **not** invent list intervals from bare `List` (D22). Nil’s `[0,0]` is an
origin. Unascribed List λ-params get fresh `?lo`/`?hi` (D24). Schemes
instantiate at var use via `BoundBinding.scheme`.

**Match results:** List scrutinees use `synthMatch` (path refine + join). Non-List
multi-arm (`if`/Bool/…) uses `synthJoinArms` / `synthJoinArmsAt` — synth/check
each arm, `joinBoundsTy` (min lo / max hi). Coverage stays HM / `coreCtorCoverage`.

**R3 residual:** app meets may accumulate Exists Sub goals (`meetForApp`) into a
`ResM` state; Check pack feeds them to `packAtEscape` for uniqueOnly.
-/

namespace FHM.Bounds.Synth

open FHM.Bounds

/-- Residual accumulator for app-meet Exists goals (R3). -/
abbrev ResM := StateT (List Constraint) (Except String)

def emitResidual (cs : List Constraint) : ResM Unit :=
  if cs.isEmpty then pure () else modify (fun r => r ++ cs)

def runRes (x : ResM α) : Except String (α × List Constraint) :=
  StateT.run x []

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
fresh inferable demands (`BL ?i ?j` / `BL ?n ?n`), and prims / HM type stubs
(`fvar`/`bvar`) that Infer already unified. -/
def checkSubInst (Δ : List Constraint) (got want : BoundsTy) : Bool :=
  if checkSub Δ got want then true
  else
    match got, want with
    | .prim _, .fvar _ => true
    | .prim _, .bvar _ => true
    | .fvar _, .fvar _ => true
    | .fvar _, .bvar _ => true
    | .fvar _, .prim _ => true
    | .bvar _, .fvar _ => true
    | .bvar _, .prim _ => true
    | .list glo ghi ge, .list wlo whi we =>
        checkSubInst Δ ge we &&
          match wlo, whi with
          | .var ⟨.inferable, i⟩, .var ⟨.inferable, j⟩ =>
              if i == j then glo == ghi else true
          | _, _ =>
              -- Rigid/ground demand: Z3 interval Sub (e.g. `0+1` ≤ `1`).
              wlo.isDemandOK && whi.isDemandOK &&
                checkValid (Interval.subGoals Δ ⟨glo, ghi⟩ ⟨wlo, whi⟩) == .valid
    | .arrow da ca, .arrow db cb =>
        checkSubInst Δ db da && checkSubInst Δ ca cb
    | .custom n as, .custom m bs =>
        n == m && checkSubInstAll Δ as bs
    | _, _ => false
termination_by sizeOf got + sizeOf want

def checkSubInstAll (Δ : List Constraint) (as bs : List BoundsTy) : Bool :=
  match as, bs with
  | [], [] => true
  | a :: as, b :: bs => checkSubInst Δ a b && checkSubInstAll Δ as bs
  | _, _ => false
termination_by sizeOf as + sizeOf bs
decreasing_by all_goals (simp_wf; try omega)

def checkSubAll (Δ : List Constraint) (as bs : List BoundsTy) : Bool :=
  match as, bs with
  | [], [] => true
  | a :: as, b :: bs => checkSub Δ a b && checkSubAll Δ as bs
  | _, _ => false
termination_by sizeOf as + sizeOf bs
decreasing_by
  all_goals (simp_wf; try omega)
end

/-- Invert a DemandOK demand count against a ground synth count (T5).

Examples: `?i` ← `3`; `?i+1` ← `3` pins `?i ↦ 2`; `2*?i` ← `10` pins `?i ↦ 5`.
Used so `head`/`tail` domains `BL (n+1) m` pin from concrete args. -/
def tryExactCountPin (got want : Count) : Option (List (Nat × Count)) :=
  match want, got with
  | .var ⟨.inferable, i⟩, c =>
      some [(i, c)]
  | .add (.var ⟨.inferable, i⟩) (.lit k), .lit n =>
      if n ≥ k then some [(i, .lit (n - k))] else none
  | .add (.lit k) (.var ⟨.inferable, i⟩), .lit n =>
      if n ≥ k then some [(i, .lit (n - k))] else none
  | .mul (.var ⟨.inferable, i⟩) (.lit k), .lit n =>
      if k ≠ 0 && n % k == 0 then some [(i, .lit (n / k))] else none
  | .mul (.lit k) (.var ⟨.inferable, i⟩), .lit n =>
      if k ≠ 0 && n % k == 0 then some [(i, .lit (n / k))] else none
  | .add (.mul (.var ⟨.inferable, i⟩) (.lit k)) (.lit e), .lit n =>
      if k ≠ 0 && n ≥ e && (n - e) % k == 0 then
        some [(i, .lit ((n - e) / k))]
      else none
  | .add (.mul (.lit k) (.var ⟨.inferable, i⟩)) (.lit e), .lit n =>
      if k ≠ 0 && n ≥ e && (n - e) % k == 0 then
        some [(i, .lit ((n - e) / k))]
      else none
  | w, g =>
      if w == g then some [] else none

/-- Merge pin lists; conflicting pins for the same index ⇒ none. -/
def mergePins (a b : List (Nat × Count)) : Option (List (Nat × Count)) :=
  b.foldl (fun acc? ⟨i, c⟩ =>
    match acc? with
    | none => none
    | some acc =>
        match acc.find? fun ⟨j, _⟩ => j = i with
        | some ⟨_, c'⟩ => if c == c' then some acc else none
        | none => some (acc ++ [(i, c)])) (some a)

/-- Pins from a successful meet: bare fresh intervals, **or** exact inversion of
DemandOK compound endpoints (T5: `BL (n+1) m` ← `BL 3 3` pins `n↦2, m↦3`). -/
def collectInstPins (got want : BoundsTy) : List (Nat × Count) :=
  match got, want with
  | .list glo ghi ge, .list wlo whi we =>
      let head : List (Nat × Count) :=
        match wlo, whi with
        | .var ⟨.inferable, i⟩, .var ⟨.inferable, j⟩ =>
            if i = j then
              if glo == ghi then [(i, glo)] else []
            else
              [(i, glo), (j, ghi)]
        | _, _ =>
            -- T5 exact endpoint inversion (both ends must pin).
            match tryExactCountPin glo wlo, tryExactCountPin ghi whi with
            | some pl, some ph =>
                match mergePins pl ph with
                | some ps => ps
                | none => []
            | _, _ => []
      head ++ collectInstPins ge we
  | .arrow da ca, .arrow db cb =>
      collectInstPins db da ++ collectInstPins ca cb
  | _, _ => []
termination_by sizeOf got + sizeOf want

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

/-- App domain meet: pin exact/compound demands, else Exists residual (R3 mid-case).

* Prefer `collectInstPins` (bare + T5 exact inversion); accept if Sub holds after pin.
* Else `checkSub` / `checkSubInst` with those pins.
* Else `subConstraints?` + `solve` sat → residual (no pin) for escape uniqueOnly.
* Unsat / shape fail → error.
-/
def meetForApp (Δ : List Constraint) (got want : BoundsTy) :
    Except String (List (Nat × Count) × List Constraint) := do
  let pins := collectInstPins got want
  let want' := want.substInferables pins
  if !pins.isEmpty && checkSubInst Δ got want' then
    pure (pins, [])
  else if checkSub Δ got want then
    pure (pins, [])
  else if checkSubInst Δ got want then
    pure (pins, [])
  else
    match BoundsTy.subConstraints? want got with
    | none =>
        throw s!"bounds: argument {prettyβ got} does not meet function domain {prettyβ want}"
    | some cs =>
        if cs.isEmpty then
          throw s!"bounds: argument {prettyβ got} does not meet function domain {prettyβ want}"
        else
          let vs := constraintsInferVars cs
          let ψ := mkEscapeProblem Δ vs cs
          match solve ψ with
          | .witness _ => pure ([], cs)
          | .unsat | .unknown =>
              throw s!"bounds: argument {prettyβ got} does not meet function domain {prettyβ want}"

/-- ResM wrapper: emit residual, return pins. -/
def meetForAppM (Δ : List Constraint) (got want : BoundsTy) :
    ResM (List (Nat × Count)) := do
  match meetForApp Δ got want with
  | .error e => throw e
  | .ok (pins, res) => do
      emitResidual res
      pure pins

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

private theorem size_lt_sizeBranches_cons_head {p : MatchPattern} {e : Expr}
    {rest : List (MatchPattern × Expr)} :
    e.size < Expr.sizeBranches ((p, e) :: rest) := by
  simp only [Expr.sizeBranches]; omega

private theorem size_lt_sizeBranches_cons_tail {p : MatchPattern} {e : Expr}
    {rest : List (MatchPattern × Expr)} :
    Expr.sizeBranches rest < Expr.sizeBranches ((p, e) :: rest) := by
  simp only [Expr.sizeBranches]; omega

private theorem expr_size_lt_double_app_ctor {c : CtorName} {h arg : Expr} :
    h.size < (((Expr.ctor c).app h).app arg).size := by
  simp [Expr.size]
  have := Expr.size_pos arg
  omega

private theorem expr_size_lt_double_app_ctor_arg {c : CtorName} {h arg : Expr} :
    arg.size < (((Expr.ctor c).app h).app arg).size := by
  simp [Expr.size, Expr.size_pos]

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

private theorem size_lt_match_branch_two_fst {scrut : Expr} {p1 p2 : MatchPattern}
    {e1 e2 : Expr} :
    e1.size < (Expr.match_ scrut [(p1, e1), (p2, e2)]).size := by
  simp [Expr.size, Expr.sizeBranches]
  have := Expr.size_pos scrut
  have := Expr.size_pos e2
  omega

private theorem size_lt_match_branch_two_snd {scrut : Expr} {p1 p2 : MatchPattern}
    {e1 e2 : Expr} :
    e2.size < (Expr.match_ scrut [(p1, e1), (p2, e2)]).size := by
  simp [Expr.size, Expr.sizeBranches]
  have := Expr.size_pos scrut
  have := Expr.size_pos e1
  omega

private theorem size_lt_match_branch_one {scrut : Expr} {p : MatchPattern} {e : Expr} :
    e.size < (Expr.match_ scrut [(p, e)]).size := by
  simp [Expr.size, Expr.sizeBranches]
  have := Expr.size_pos scrut
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

/-- Provisional env slot for a letRec member (de Bruijn index = position in group).

Infer’s `letRec` / `letRecElab` puts the group at indices `0 … k-1` while checking
each RHS; outer binders start at `k`. Without these slots, lookups are off-by-one
(map reads filter’s scheme, etc.). Use the ascribed HM type’s template; the
real `β` is synthesized by `inferLetRecGroupCore`. -/
private def letRecProvisional (ann? : Option PolyTy) : BoundBinding :=
  match ann? with
  | some σ => .mono (agreesTemplate σ.body)
  | none => .mono (.fvar 0)

mutual

/-- Synth letRec binders under `bctxRec` (list-structural on `bindings`).

`bctxRec` must already include provisional slots for every group member; see
`inferLetRecGroup`. -/
def inferLetRecGroupCore (Δ : List Constraint) (bctxRec : BoundEnv) (Φ : Nat)
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    ResM (Nat × List BoundsTy) :=
  match anns, bindings with
  | [], [] => pure (Φ, [])
  | ann? :: anns', rhs :: bindings' => do
      let (Φ1, β) ← match ann? with
        | some σ => checkBoundsΦ Δ bctxRec Φ rhs σ.body
        | none => do
            let (Φ', _, β) ← inferBoundsΦ Δ bctxRec Φ rhs
            pure (Φ', β)
      let (Φ2, βs) ← inferLetRecGroupCore Δ bctxRec Φ1 anns' bindings'
      pure (Φ2, β :: βs)
  | _, _ => throw "bounds: letRec anns/bindings length mismatch"
termination_by Expr.sizeRecGroup bindings
decreasing_by all_goals (simp_wf; simp [Expr.sizeRecGroup, Expr.size]; try omega)

/-- List match: Nil+Cons join (either arm order), or single-branch under oracle. -/
def synthMatch (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (_α : Ty) (lo hi : Count) (βe : BoundsTy)
    (brs : List (MatchPattern × Expr)) : ResM (Nat × Ty × BoundsTy) :=
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

/-- Non-List match arm env: no path-Δ refine (that is List/BoundCovers only).
Nullary / wildcard leave `bctx` alone. `named _ n` pushes `n` stub slots so
de Bruijn field binders resolve; field βs are not origin-precise (HM typed). -/
def nonListArmEnv (bctx : BoundEnv) : MatchPattern → BoundEnv
  | .wildcard => bctx
  | .named _ n => BoundEnv.extendMany bctx (List.replicate n (.fvar 0))

/-- Non-List multi-arm: synth each arm body, join βs (`joinBoundsTy` / min-lo max-hi).
Coverage is HM exhaustiveness (and `checkProgramMatches` ctor coverage) — not BoundCovers.

First arm is inferred (anchors result τ); remaining arms are checked at that τ
then joined — same discipline as List `synthMatch` Nil+Cons. -/
def synthJoinArms (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (brs : List (MatchPattern × Expr)) : ResM (Nat × Ty × BoundsTy) :=
  match brs with
  | [] => throw "bounds: empty match"
  | [(pat, e)] =>
      inferBoundsΦ Δ (nonListArmEnv bctx pat) Φ e
  | (pat, e) :: rest => do
      let (Φ1, τ, β1) ← inferBoundsΦ Δ (nonListArmEnv bctx pat) Φ e
      let (Φ2, βrest) ← synthJoinArmsAt Δ bctx Φ1 τ rest
      match joinBoundsTy β1 βrest with
      | some β => pure (Φ2, τ, β)
      | none => throw "bounds: match branches have incompatible bounds"
termination_by Expr.sizeBranches brs
decreasing_by all_goals (first
  | exact size_lt_sizeBranches_cons_head
  | exact size_lt_sizeBranches_one
  | (try simp only [Expr.sizeBranches]; omega))

/-- Check remaining non-List arms at fixed `τ`, joining their βs. -/
def synthJoinArmsAt (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat) (τ : Ty)
    (brs : List (MatchPattern × Expr)) : ResM (Nat × BoundsTy) :=
  match brs with
  | [] => throw "bounds: empty match arms"
  | [(pat, e)] => do
      let (Φ1, β) ← checkBoundsΦ Δ (nonListArmEnv bctx pat) Φ e τ
      pure (Φ1, β)
  | (pat, e) :: rest => do
      let (Φ1, β1) ← checkBoundsΦ Δ (nonListArmEnv bctx pat) Φ e τ
      let (Φ2, βrest) ← synthJoinArmsAt Δ bctx Φ1 τ rest
      match joinBoundsTy β1 βrest with
      | some β => pure (Φ2, β)
      | none => throw "bounds: match branches have incompatible bounds"
termination_by Expr.sizeBranches brs
decreasing_by all_goals (first
  | exact size_lt_sizeBranches_cons_head
  | exact size_lt_sizeBranches_cons_tail
  | exact size_lt_sizeBranches_one
  | (try simp only [Expr.sizeBranches]; omega))

/-- Check mode for generic `f arg` (infer fn spine, check arg). R3 residual via meetForAppM. -/
def checkBoundsApp (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (f arg : Expr) (τ : Ty) : ResM (Nat × BoundsTy) := do
  let (Φ1, τf, βf) ← inferBoundsΦ Δ bctx Φ f
  match τf, βf with
  | .arrow τa τr, .arrow βa βr => do
      -- HM types already checked by Infer; bounds spine may use bvar/fvar stubs.
      let (Φ2, βa') ← checkBoundsΦ Δ bctx Φ1 arg τa
      let pins ← meetForAppM Δ βa' βa
      pure (Φ2, βr.substInferables pins)
  | _, _ => throw "bounds: applying a non-function"
termination_by f.size + arg.size
decreasing_by all_goals (simp_wf; have := Expr.size_pos arg; have := Expr.size_pos f; omega)

/-- Infer mode: synthesize both HM spine and bounds; thread freshness `Φ`. -/
def inferBoundsΦ (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat) (e : Expr) :
    ResM (Nat × Ty × BoundsTy) :=
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
      -- Origin: primops have fixed prim/Bool spines (no List invention).
      let β : BoundsTy :=
        match op with
        | .intAdd | .intSub =>
            .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))
        | .intLt =>
            .arrow (.prim .int) (.arrow (.prim .int) (.custom boolTyName []))
        | .charLt =>
            .arrow (.prim .char) (.arrow (.prim .char) (.custom boolTyName []))
      pure (Φ, BoundsTy.toTy β, β)
  | .app (.app (.ctor c) x) y =>
      if c == pairCtorName then do
        let (Φ1, τx, βx) ← inferBoundsΦ Δ bctx Φ x
        let (Φ2, τy, βy) ← inferBoundsΦ Δ bctx Φ1 y
        pure (Φ2, .customTy pairTyName [τx, τy], .custom pairTyName [βx, βy])
      else do
        let (Φ1, τf, βf) ← inferBoundsΦ Δ bctx Φ (.app (.ctor c) x)
        match τf, βf with
        | .arrow τa τr, .arrow βa βr => do
            let (Φ2, βa') ← checkBoundsΦ Δ bctx Φ1 y τa
            let pins ← meetForAppM Δ βa' βa
            pure (Φ2, τr, βr.substInferables pins)
        | _, _ =>
            throw "bounds: applying a non-function"
  | .app f arg => do
      let (Φ1, τf, βf) ← inferBoundsΦ Δ bctx Φ f
      match τf, βf with
      | .arrow τa τr, .arrow βa βr => do
          let (Φ2, βa') ← checkBoundsΦ Δ bctx Φ1 arg τa
          let pins ← meetForAppM Δ βa' βa
          pure (Φ2, τr, βr.substInferables pins)
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
      let (Φ1, βs) ← inferLetRecGroupCore Δ (anns.map letRecProvisional ++ bctx) Φ anns bindings
      inferBoundsΦ Δ (BoundEnv.extendMany bctx βs) Φ1 body
  | .match_ scrut brs => do
      let (Φ1, τs, βs) ← inferBoundsΦ Δ bctx Φ scrut
      match isListTy τs, βs with
      | some α, .list lo hi βe =>
          synthMatch Δ bctx Φ1 α lo hi βe brs
      | _, _ =>
          -- Non-List: no path refine; join arm results (Bool `if`, Maybe, …).
          synthJoinArms Δ bctx Φ1 brs
termination_by e.size
decreasing_by all_goals (
  simp_wf
  first
  | exact size_lt_app_fn
  | exact size_lt_app_arg
  | exact expr_size_lt_double_app_ctor
  | exact expr_size_lt_double_app_ctor_arg
  | exact body_size_lt_letRec
  | exact sizeRecGroup_lt_letRec
  | (simp only [Expr.size, Expr.sizeBranches, Expr.sizeRecGroup]; omega))

/-- Check mode: given expected `τ`, synthesize `β`; thread freshness `Φ`. -/
def checkBoundsΦ (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (e : Expr) (τ : Ty) : ResM (Nat × BoundsTy) := do
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
          match τ with
          | .customTy n [τa, τb] =>
              if n == pairTyName && c == pairCtorName then do
                let (Φ1, βa) ← checkBoundsΦ Δ bctx Φ h τa
                let (Φ2, βb) ← checkBoundsΦ Δ bctx Φ1 arg τb
                pure (Φ2, .custom pairTyName [βa, βb])
              else
                checkBoundsApp Δ bctx Φ (.app (.ctor c) h) arg τ
          | _ =>
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
      let (Φ1, βs) ← inferLetRecGroupCore Δ (anns.map letRecProvisional ++ bctx) Φ anns bindings
      checkBoundsΦ Δ (BoundEnv.extendMany bctx βs) Φ1 body τ
  | .match_ scrut brs => do
      let (Φ1, τs, βs) ← inferBoundsΦ Δ bctx Φ scrut
      match isListTy τs, βs with
      | some α, .list lo hi βe => do
          let (Φ2, _τ, β) ← synthMatch Δ bctx Φ1 α lo hi βe brs
          let _ := τ
          pure (Φ2, β)
      | _, _ => do
          -- Expected `τ` from check mode: check every arm at `τ`, join βs.
          -- (Infer-first fails on list literals — Nil/Cons need a List demand.)
          let (Φ2, β) ← synthJoinArmsAt Δ bctx Φ1 τ brs
          pure (Φ2, β)
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

/-- Synth letRec binders: check every RHS under provisional group slots plus outer
`bctx`, then return real `β`s for `extendMany` on the body. -/
def inferLetRecGroup (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (anns : List (Option PolyTy)) (bindings : List Expr) :
    Except String (Nat × List BoundsTy) :=
  match runRes (inferLetRecGroupCore Δ (anns.map letRecProvisional ++ bctx) Φ anns bindings) with
  | .error e => .error e
  | .ok (x, _) => .ok x

/-- Infer with residual (R3). -/
def inferBoundsWithRes (Δ : List Constraint) (bctx : BoundEnv) (e : Expr) :
    Except String (Ty × BoundsTy × List Constraint) := do
  let ((_, τ, β), res) ← runRes (inferBoundsΦ Δ bctx 0 e)
  pure (τ, β, res)

/-- Infer without exposing freshness (starts at `Φ = 0`). -/
def inferBounds (Δ : List Constraint) (bctx : BoundEnv) (e : Expr) :
    Except String (Ty × BoundsTy) := do
  let (τ, β, _) ← inferBoundsWithRes Δ bctx e
  pure (τ, β)

/-- Check with residual Exists goals from app meets (R3 pack path). -/
def checkBoundsWithRes (Δ : List Constraint) (bctx : BoundEnv)
    (e : Expr) (τ : Ty) : Except String (BoundsTy × List Constraint) := do
  let ((_, β), res) ← runRes (checkBoundsΦ Δ bctx 0 e τ)
  pure (β, res)

/-- Check without exposing freshness (starts at `Φ = 0`). -/
def checkBounds (Δ : List Constraint) (bctx : BoundEnv)
    (e : Expr) (τ : Ty) : Except String BoundsTy := do
  Prod.fst <$> checkBoundsWithRes Δ bctx e τ

/-- Top-level entry: synth `β` for `e` at HM type `τ`. -/
def synthBounds (Δ : List Constraint) (bctx : BoundEnv) (e : Expr) (τ : Ty) :
    Except String BoundsTy :=
  checkBounds Δ bctx e τ

/-- Check against demanded β (executable `CheckBounds.ofSub`).

For λ with demanded `.arrow βp βb`, push `βp` from ascription (no List invention).
Peels Infer’s singleton `letRec` wrapper. Residual from nested apps is accumulated
in `ResM` (usually discarded by `checkAgainst`). -/
def checkAgainstΦ (Δ : List Constraint) (bctx : BoundEnv) (Φ : Nat)
    (e : Expr) (τ : Ty) (β : BoundsTy) : ResM Nat := do
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
  | .match_ scrut brs, τ', β' => do
      let (Φ1, _τs, βs) ← inferBoundsΦ Δ bctx Φ scrut
      match βs, brs with
      | .list lo hi βe, [(.named n 0, eNil), (.named c 2, eCons)] => do
          unless n == nilCtorName && c == consCtorName do
            throw "bounds: expected Nil/Cons match arms"
          let Φ2 ← checkAgainstΦ (Δ ++ nilRefine lo hi) bctx Φ1 eNil τ' β'
          checkAgainstΦ (Δ ++ consRefine hi) (consBoundEnv bctx lo hi βe) Φ2 eCons τ' β'
      | .list lo hi βe, [(.named c 2, eCons), (.named n 0, eNil)] => do
          unless n == nilCtorName && c == consCtorName do
            throw "bounds: expected Nil/Cons match arms"
          let Φ2 ← checkAgainstΦ (Δ ++ nilRefine lo hi) bctx Φ1 eNil τ' β'
          checkAgainstΦ (Δ ++ consRefine hi) (consBoundEnv bctx lo hi βe) Φ2 eCons τ' β'
      | .list lo hi _βe, [(.named n 0, eNil)] => do
          unless n == nilCtorName do throw "bounds: expected Nil-only arm"
          unless checkValid (mustBeEmpty Δ hi) == .valid do
            throw "bounds: Nil-only match but upper bound not proved empty"
          checkAgainstΦ (Δ ++ nilRefine lo hi) bctx Φ1 eNil τ' β'
      | .list lo hi βe, [(.named c 2, eCons)] => do
          unless c == consCtorName do throw "bounds: expected Cons-only arm"
          unless checkValid (mustBeNonempty Δ lo) == .valid do
            throw "bounds: Cons-only match but lower bound not proved nonempty"
          checkAgainstΦ (Δ ++ consRefine hi) (consBoundEnv bctx lo hi βe) Φ1 eCons τ' β'
      | _, [(.named _ 0, e1), (.named _ 0, e2)] => do
          -- Bool `if` (and other nullary 2-ctor matches): same demand both arms.
          let Φ2 ← checkAgainstΦ Δ bctx Φ1 e1 τ' β'
          checkAgainstΦ Δ bctx Φ2 e2 τ' β'
      | _, _ => do
          let (Φ2, β₀) ← checkBoundsΦ Δ bctx Φ1 (.match_ scrut brs) τ'
          unless checkSubInst Δ β₀ β' do
            throw s!"bounds: synthesized {prettyβ β₀} does not meet demand {prettyβ β'}"
          pure Φ2
  | _, _, _ => do
      let (Φ1, β') ← checkBoundsΦ Δ bctx Φ e τ
      -- Prefer residual meet at final Sub (same as app); pin when possible.
      let _pins ← meetForAppM Δ β' β
      pure Φ1
termination_by e.size
decreasing_by all_goals (first
  | exact size_lt_match_branch_two_fst
  | exact size_lt_match_branch_two_snd
  | exact size_lt_match_branch_one
  | (try simp only [Expr.size, Expr.sizeRecGroup]; omega))

def checkAgainst (Δ : List Constraint) (bctx : BoundEnv)
    (e : Expr) (τ : Ty) (β : BoundsTy) : Except String Unit := do
  let _ ← runRes (checkAgainstΦ Δ bctx 0 e τ β)
  pure ()
