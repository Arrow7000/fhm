import FHM.Bounds.Synth
import FHM.Pretty

/-!
# Computational bounds checks for Live (slices 4–6)

Walk Infer’s Core `eOut` with origin `synthBounds`, then
`checkMeetsAscriptionPinned` against erase/`ofLower` anns (pin `_` to synth).

Under `--bl`, `checkProgramMatches` replaces surface `checkExhaustive`: List
scrutinees use `checkBoundCovers`; other types use `coreCtorCoverage`.
-/

namespace FHM.Bounds.Check

open FHM.Bounds
open FHM.Bounds.Synth

/-- Re-export for callers that imported Check for Sub / Meets. -/
abbrev checkSub := Synth.checkSub
abbrev checkMeetsAscription := Synth.checkMeetsAscription
abbrev checkMeetsAscriptionPinned := Synth.checkMeetsAscriptionPinned
abbrev pinHoles := Synth.pinHoles

/-- Infer wraps recursive binders as `let rec f = rhs in f`. Expose `rhs` so a
scheme ascription can sit in `bctx` for honest self-application (openFresh+pin). -/
def unwrapLetRecId : Expr → Expr
  | .letRec _ [rhs] (.var _ _) => rhs
  | e => e

/-- Look up a binder’s HM monotype body by name. -/
def tyOfBinder (binds : List (ValName × PolyTy)) (n : ValName) : Option Ty :=
  (binds.find? fun ⟨n', _⟩ => n' = n).map fun ⟨_, σ⟩ => σ.body

/-- Walk the outer `letIn` / `letRec` spine from Infer, checking each binder’s
erase ascription, then the body.

`binderEnv` / `anns.binderAnns` are 0 = innermost; the spine is outermost-first,
so the k-th outer binder group occupies the next high indices.

**Solid mono ascriptions** (`toBoundsTy?`): `checkAgainst` the RHS at the
ascribed `β`, then push that **ascription** `β` into `bctx` (§2.3).

**Scheme ascriptions** (`{n : Nat,…}`): open body at fresh `?`s, `checkAgainst`,
push packed `BoundBinding.scheme` (inst at later var uses).

**Holes (R1):** origin-synth, pin-meet (`Sub β₁ (pinHoles ann β₁)`), then push the
**pinned template** into `bctx` — same interface story as solid ascriptions, not
the tight origin-synth β. Bare / no ann: synth packs free inferables (D24). -/
def checkLetSpine
    (binderEnv : List ValName)
    (anns : ProgramBoundsAnns)
    (Δ : List Constraint)
    (bctx : BoundEnv)
    (outerIdx : Nat)
    (e : Expr)
    (τBody : Ty) : Except String (BoundEnv × BoundsTy) := do
  let meetMono (i : Nat) (β1 : BoundsTy) (ann : BoundsAnnTy) : Except String Unit := do
    match checkMeetsAscriptionPinned Δ β1 ann with
    | .ok () => pure ()
    | .error msg =>
        let n := binderEnv[i]?.getD ⟨"?"⟩
        throw s!"bounds: ascription not met for {prettyValName n} ({msg})"
  -- RHS of surface binder `i` at HM `τ` → env binding to push.
  let checkBinderRhs (i : Nat) (rhs : Expr) (τ : Ty) : Except String BoundBinding := do
    let rhs' := unwrapLetRecId rhs
    -- Infer's `letRecElab` singleton wrapper shifts free vars up by one; scheme
    -- checking prepends `scheme s` to compensate — mirror that for mono/inferred.
    let bctx' := match rhs with
      | .letRec _ [_] (.var _ _) => BoundEnv.extend bctx (agreesTemplate τ)
      | _ => bctx
    match anns.binderAnns[i]? with
    | some (some (.scheme sAnn)) =>
        match BoundsSchemeAnn.toBScheme? sAnn with
        | none =>
            let n := binderEnv[i]?.getD ⟨"?"⟩
            throw s!"bounds: scheme ascription for {prettyValName n} not solid/WF"
        | some s => do
            -- Rigid scheme body + scheme self in env (not mono openFresh).
            match checkAgainst Δ (.scheme s :: bctx) rhs' τ s.body with
            | .ok () => pure (.scheme s)
            | .error msg =>
                let n := binderEnv[i]?.getD ⟨"?"⟩
                throw s!"bounds: ascription not met for {prettyValName n} ({msg})"
    | some (some (.mono ann)) =>
        match BoundsAnnTy.toBoundsTy? ann with
        | some βWant => do
            match checkAgainst Δ bctx' rhs' τ βWant with
            | .ok () => pure (.mono βWant)
            | .error msg =>
                let n := binderEnv[i]?.getD ⟨"?"⟩
                throw s!"bounds: ascription not met for {prettyValName n} ({msg})"
        | none => do
            -- R1: pin holes from synth, meet, push **pinned** interface (not β1).
            let β1 ← checkBounds Δ bctx' rhs' τ
            meetMono i β1 ann
            let βPinned ← pinHoles ann β1
            pure (.mono βPinned)
    | _ => do
        let β1 ← checkBounds Δ bctx' rhs' τ
        pure (BoundsTy.packScheme? β1)
  match e with
  | .letIn (some σ) rhs body => do
      let nBind := binderEnv.length
      if outerIdx ≥ nBind then
        let β1 ← checkBounds Δ bctx rhs σ.body
        checkLetSpine binderEnv anns Δ (BoundEnv.extend bctx β1) outerIdx body τBody
      else
        let i := nBind - 1 - outerIdx
        let bb ← checkBinderRhs i rhs σ.body
        checkLetSpine binderEnv anns Δ (bb :: bctx) (outerIdx + 1) body τBody
  | .letIn none rhs body => do
      let β1 ← Prod.snd <$> inferBounds Δ bctx rhs
      checkLetSpine binderEnv anns Δ (BoundEnv.extend bctx β1) outerIdx body τBody
  | .letRec recAnns bindings body => do
      let k := bindings.length
      unless recAnns.length == k do
        throw "bounds: letRec anns/bindings length mismatch"
      let nBind := binderEnv.length
      if outerIdx + k > nBind then
        throw "bounds: letRec group longer than remaining binderEnv"
      let start := nBind - outerIdx - k
      let bbs ← (List.range k).zip (recAnns.zip bindings) |>.mapM fun ⟨j, (ann?, rhs)⟩ => do
        let τj ← match ann? with
          | some σ => pure σ.body
          | none => throw "bounds: letRec member needs scheme ascription from Infer"
        checkBinderRhs (start + j) rhs τj
      checkLetSpine binderEnv anns Δ (bbs ++ bctx) (outerIdx + k) body τBody
  | _ => do
      let β ← checkBounds Δ bctx e τBody
      match anns.bodyAnn with
      | none => pure (bctx, β)
      | some ann => do
          match checkMeetsAscriptionPinned Δ β ann with
          | .ok () => pure (bctx, β)
          | .error msg =>
              throw s!"bounds: body ascription not met ({msg})"
termination_by e.size
decreasing_by all_goals (try simp only [Expr.size, Expr.sizeRecGroup]; omega)

/-- Origin-synth Core `e` at HM `τ`, checking erase/`ofLower` ascriptions.

Holes in anns are pinned to synth Counts, then `Sub`. Under `--bl` only.
Returns binder `BoundEnv` (0 = innermost ‖ `binderEnv`) and body `β`. -/
def checkProgramAnns
    (e : Expr)
    (τ : Ty)
    (binderEnv : List ValName)
    (anns : ProgramBoundsAnns) : Except String (BoundEnv × BoundsTy) :=
  checkLetSpine binderEnv anns [] [] 0 e τ

/-! ## Slice 6 — BoundCovers / ctor coverage on Core matches -/

/-- Executable List match coverage under scrutinee bounds `β`. -/
def checkBoundCovers (Δ : List Constraint) (β : BoundsTy)
    (brs : List (MatchPattern × Expr)) : Bool :=
  match β with
  | .list lo hi _ =>
      hasWildcardBranchB brs ||
        (hasNilBranchB brs && hasConsBranchB brs) ||
        (hasNilBranchB brs && checkValid (mustBeEmpty Δ hi) == .valid) ||
        (hasConsBranchB brs && checkValid (mustBeNonempty Δ lo) == .valid)
  | _ => false

private def instFieldTys (ctors : CtorEnv) (c : CtorName) (tyArgs : List Ty) : List Ty :=
  ((LookupList.get? ctors c).map (fun ctor => ctor.contents.map (Ty.openWith tyArgs))).getD []

private theorem size_lt_sizeBranches_one {p : MatchPattern} {e : Expr} :
    e.size < Expr.sizeBranches [(p, e)] := by
  simp [Expr.sizeBranches]

private theorem size_lt_sizeBranches_tail {p : MatchPattern} {e : Expr} {rest : List (MatchPattern × Expr)} :
    Expr.sizeBranches rest < Expr.sizeBranches ((p, e) :: rest) := by
  simp [Expr.sizeBranches, Expr.size_pos]

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

/-- Singleton Infer wrapper: RHS size is strictly below the `letRec`. -/
private theorem size_lt_letRec_singleton_binding {anns : List (Option PolyTy)}
    {rhs body : Expr} :
    rhs.size < (Expr.letRec anns [rhs] body).size := by
  simp [Expr.size, Expr.sizeRecGroup]
  have := Expr.size_pos body
  omega

private theorem sizeBranches_lt_match {scrut : Expr} {brs : List (MatchPattern × Expr)} :
    Expr.sizeBranches brs < (Expr.match_ scrut brs).size := by
  simp [Expr.size, Expr.size_pos]

/-- Non-List flat ctor coverage: every env ctor of `τ`'s ADT appears in `brs`. -/
def coreCtorCoverage (ctors : CtorEnv) (τ : Ty) (brs : List (MatchPattern × Expr)) : Bool :=
  if hasWildcardBranchB brs then true
  else if (isListTy τ).isSome then false
  else match τ with
  | .customTy T _ =>
      ctors.all fun ⟨cName, ctor⟩ =>
        if ctor.tyName != T then true
        else brs.any fun
          | (.named c n, _) => c == cName && n == ctor.contents.length
          | (.wildcard, _) => false
  | _ => false

private def branchBctx (ctors : CtorEnv) (τs : Ty) (βs : BoundsTy) (bctx : BoundEnv)
    (lo hi : Count) (βe : BoundsTy) (pat : MatchPattern) : BoundEnv :=
  match βs with
  | .list _ _ _ =>
      match pat with
      | .named c 2 => if c == consCtorName then consBoundEnv bctx lo hi βe else bctx
      | _ => bctx
  | _ =>
      match pat with
      | .wildcard => bctx
      | .named c n =>
          match τs with
          | .customTy _ tyArgs =>
              let fieldTys := (instFieldTys ctors c tyArgs).take n
              BoundEnv.extendMany bctx (fieldTys.map agreesTemplate).reverse
          | _ => bctx

mutual
/-- Recurse into match branch bodies (mutual with `checkProgramMatchesGo`). -/
def checkProgramMatchesBranches (ctors : CtorEnv) (Δ : List Constraint) (bctx : BoundEnv)
    (τs : Ty) (βs : BoundsTy) (lo hi : Count) (βe : BoundsTy)
    (demand : Option BoundsTy)
    (brs : List (MatchPattern × Expr)) : Except String Unit :=
  match brs with
  | [] => pure ()
  | (pat, body) :: rest => do
      let bctx' := branchBctx ctors τs βs bctx lo hi βe pat
      checkProgramMatchesGo ctors Δ bctx' demand body
      checkProgramMatchesBranches ctors Δ bctx τs βs lo hi βe demand rest
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (first | exact size_lt_sizeBranches_one | exact size_lt_sizeBranches_tail | (simp only [Expr.sizeBranches]; omega))

/-- Walk a Core subterm for nested matches under `bctx` and optional β-demand.

Demand peels through λ the same way as `checkAgainst`. Unascribed List λs get
fresh `?lo`/`?hi` (D24) so BoundCovers can see parametric intervals. -/
def checkProgramMatchesGo (ctors : CtorEnv) (Δ : List Constraint) (bctx : BoundEnv)
    (demand : Option BoundsTy) (e : Expr) : Except String Unit :=
  match e with
  | .primLit _ | .primBinOp _ | .var _ _ | .ctor _ => pure ()
  | .lambda ann body =>
      match demand with
      | some (.arrow βp βb) =>
          checkProgramMatchesGo ctors Δ (BoundEnv.extend bctx βp) (some βb) body
      | _ =>
          match ann with
          | some τp =>
              let (_, βp) := freshParamBounds 0 τp
              checkProgramMatchesGo ctors Δ (BoundEnv.extend bctx βp) none body
          | none =>
              -- Infer often emits unannotated `λ` (e.g. `λy. let z : Bool = y in …`).
              -- Still push a stub so de Bruijn indices in the body line up.
              checkProgramMatchesGo ctors Δ (BoundEnv.extend bctx (.fvar 0)) none body
  | .app f arg => do
      checkProgramMatchesGo ctors Δ bctx none f
      checkProgramMatchesGo ctors Δ bctx none arg
  | .letIn ann? rhs body => do
      -- Env slot for the binder: List keeps origin-synth β (BoundCovers); non-List
      -- uses the HM ascription template so ADT matches (Bool `if`) see a real
      -- `customTy` scrutinee even when the RHS var was a λ-stub (unascribed λ).
      let β1 ← match ann? with
        | some σ =>
            if (isListTy σ.body).isSome then
              checkBounds Δ bctx rhs σ.body
            else
              pure (agreesTemplate σ.body)
        | none => Prod.snd <$> inferBounds Δ bctx rhs
      checkProgramMatchesGo ctors Δ bctx none rhs
      checkProgramMatchesGo ctors Δ (BoundEnv.extend bctx β1) demand body
  | .letRec anns bindings body => do
      if anns.length != bindings.length then
        throw "bounds: letRec anns/bindings length mismatch"
      match demand, bindings with
      | some β', [rhs] => do
          checkProgramMatchesGo ctors Δ (BoundEnv.extend bctx β') (some β') rhs
          checkProgramMatchesGo ctors Δ (BoundEnv.extend bctx β') demand body
      | _, _ => do
          let (_, βs) ← inferLetRecGroup Δ bctx 0 anns bindings
          checkProgramMatchesGo ctors Δ (BoundEnv.extendMany bctx βs) demand body
  | .match_ scrut brs => do
      checkProgramMatchesGo ctors Δ bctx none scrut
      let (τs, βs) ← inferBounds Δ bctx scrut
      match βs with
      | .list lo hi βe =>
          unless checkBoundCovers Δ βs brs do
            throw "bounds: list match does not cover scrutinee bounds"
          checkProgramMatchesBranches ctors Δ bctx τs βs lo hi βe demand brs
      | _ =>
          unless coreCtorCoverage ctors τs brs do
            throw "bounds: match not exhaustive for scrutinee type"
          checkProgramMatchesBranches ctors Δ bctx τs βs (.lit 0) (.lit 0) βs demand brs
  termination_by e.size
  decreasing_by all_goals (
    first
    | exact sizeBranches_lt_match
    | exact size_lt_app_fn
    | exact size_lt_app_arg
    | exact size_lt_letRec_singleton_binding
    | exact body_size_lt_letRec
    | exact sizeRecGroup_lt_letRec
    | (simp only [Expr.size, Expr.sizeRecGroup]; omega))

end

def checkProgramMatchesSpine
    (ctors : CtorEnv)
    (binderEnv : List ValName)
    (anns : ProgramBoundsAnns)
    (Δ : List Constraint)
    (bctx : BoundEnv)
    (outerIdx : Nat)
    (e : Expr) : Except String Unit := do
  match e with
  | .letIn (some σ) rhs body => do
      let nBind := binderEnv.length
      if outerIdx ≥ nBind then
        let β1 ← checkBounds Δ bctx rhs σ.body
        checkProgramMatchesGo ctors Δ bctx none rhs
        checkProgramMatchesSpine ctors binderEnv anns Δ (BoundEnv.extend bctx β1) outerIdx body
      else
        let i := nBind - 1 - outerIdx
        let (bb, dem) :=
          match anns.binderAnns[i]? with
          | some (some (.scheme sAnn)) =>
              match BoundsSchemeAnn.toBScheme? sAnn with
              | some s =>
                  (BoundBinding.scheme s, some s.body)
              | none => (BoundBinding.mono (agreesTemplate σ.body), none)
          | some (some (.mono ann)) =>
              match BoundsAnnTy.toBoundsTy? ann with
              | some βWant => (BoundBinding.mono βWant, some βWant)
              | none => (BoundBinding.mono (agreesTemplate σ.body), none)
          | _ => (BoundBinding.mono (agreesTemplate σ.body), none)
        let rhs' := unwrapLetRecId rhs
        checkProgramMatchesGo ctors Δ (bb :: bctx) dem rhs'
        checkProgramMatchesSpine ctors binderEnv anns Δ (bb :: bctx) (outerIdx + 1) body
  | .letIn none rhs body => do
      let β1 ← Prod.snd <$> inferBounds Δ bctx rhs
      checkProgramMatchesGo ctors Δ bctx none rhs
      checkProgramMatchesSpine ctors binderEnv anns Δ (BoundEnv.extend bctx β1) outerIdx body
  | .letRec recAnns bindings body => do
      let k := bindings.length
      unless recAnns.length == k do
        throw "bounds: letRec anns/bindings length mismatch"
      let nBind := binderEnv.length
      if outerIdx + k > nBind then
        throw "bounds: letRec group longer than remaining binderEnv"
      let start := nBind - outerIdx - k
      let bbs ← (List.range k).zip (recAnns.zip bindings) |>.mapM fun ⟨j, (ann?, rhs)⟩ => do
        let τj ← match ann? with
          | some σ => pure σ.body
          | none => throw "bounds: letRec member needs scheme ascription from Infer"
        let i := start + j
        let (bb, dem) :=
          match anns.binderAnns[i]? with
          | some (some (.scheme sAnn)) =>
              match BoundsSchemeAnn.toBScheme? sAnn with
              | some s =>
                  (BoundBinding.scheme s, some s.body)
              | none => (BoundBinding.mono (agreesTemplate τj), none)
          | some (some (.mono ann)) =>
              match BoundsAnnTy.toBoundsTy? ann with
              | some βWant => (BoundBinding.mono βWant, some βWant)
              | none => (BoundBinding.mono (agreesTemplate τj), none)
          | _ => (BoundBinding.mono (agreesTemplate τj), none)
        checkProgramMatchesGo ctors Δ (bb :: bctx) dem (unwrapLetRecId rhs)
        pure bb
      checkProgramMatchesSpine ctors binderEnv anns Δ (bbs ++ bctx) (outerIdx + k) body
  | _ =>
      let demand :=
        match anns.bodyAnn with
        | some ann => BoundsAnnTy.toBoundsTy? ann
        | none => none
      checkProgramMatchesGo ctors Δ bctx demand e
termination_by e.size
decreasing_by all_goals (try simp only [Expr.size, Expr.sizeRecGroup]; omega)

/-- Top-level Core match coverage walk for Live `--bl`. -/
def checkProgramMatches
    (ctors : CtorEnv) (e : Expr) (_τ : Ty)
    (binderEnv : List ValName) (anns : ProgramBoundsAnns) : Except String Unit := do
  checkProgramMatchesSpine ctors binderEnv anns [] [] 0 e
  pure ()

/-! ## Guards (Core Nil/Cons origin synth + pin-to-synth holes) -/

private def nilE : Expr := .ctor nilCtorName
private def unitE : Expr := .primLit .unit
private def consE (h t : Expr) : Expr :=
  .app (.app (.ctor consCtorName) h) t
private def tyInt : Ty := .prim .int
private def tyListInt : Ty := listTy tyInt

private def twoInts : Expr :=
  consE (.primLit (.int 1)) (consE (.primLit (.int 2)) nilE)

#guard match synthBounds [] [] nilE tyListInt with
  | .ok (.list (.lit 0) (.lit 0) _) => true | _ => false

#guard match synthBounds [] [] (consE (.primLit (.int 1)) nilE) tyListInt with
  | .ok (.list (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1)) _) => true
  | _ => false

#guard match synthBounds [] [] twoInts tyListInt with
  | .ok (.list (.add (.add (.lit 0) (.lit 1)) (.lit 1))
               (.add (.add (.lit 0) (.lit 1)) (.lit 1)) _) => true
  | _ => false

-- `[1,2]` meets `BL 2 2 Int` via Z3 Sub on add-normal form.
#guard match synthBounds [] [] twoInts tyListInt with
  | .ok β =>
      checkMeetsAscription [] β
        (.list (.solid (.lit 2)) (.solid (.lit 2)) (.prim .int))
  | _ => false

-- `[1,2]` does not meet `BL 0 0 Int`.
#guard match synthBounds [] [] twoInts tyListInt with
  | .ok β =>
      !(checkMeetsAscription [] β
          (.list (.solid (.lit 0)) (.solid (.lit 0)) (.prim .int)))
  | _ => false

-- `[]` meets `BL 0 5 Int`.
#guard match synthBounds [] [] nilE tyListInt with
  | .ok β =>
      checkMeetsAscription [] β
        (.list (.solid (.lit 0)) (.solid (.lit 5)) (.prim .int))
  | _ => false

-- Slice 5: pin `_` to synth, then Sub.
#guard match synthBounds [] [] twoInts tyListInt with
  | .ok β =>
      (checkMeetsAscriptionPinned [] β
        (.list .hole (.solid (.lit 5)) (.prim .int))).isOk
  | _ => false

#guard match synthBounds [] [] twoInts tyListInt with
  | .ok β =>
      (checkMeetsAscriptionPinned [] β
        (.list (.solid (.lit 0)) .hole (.prim .int))).isOk
  | _ => false

#guard match synthBounds [] [] twoInts tyListInt with
  | .ok β =>
      (checkMeetsAscriptionPinned [] β
        (.list .hole .hole (.prim .int))).isOk
  | _ => false

-- Hole cannot rescue solid conflict: pin `_` in `BL _ 0` still fails Sub.
#guard match synthBounds [] [] twoInts tyListInt with
  | .ok β =>
      !(checkMeetsAscriptionPinned [] β
          (.list .hole (.solid (.lit 0)) (.prim .int))).isOk
  | _ => false

/-! ## BoundCovers guards (slice 6) -/

private def brNilOnly (e : Expr) : List (MatchPattern × Expr) :=
  [(.named nilCtorName 0, e)]

private def brConsOnly (e : Expr) : List (MatchPattern × Expr) :=
  [(.named consCtorName 2, e)]

private def brNilCons (eNil eCons : Expr) : List (MatchPattern × Expr) :=
  [(.named nilCtorName 0, eNil), (.named consCtorName 2, eCons)]

private def brWild (e : Expr) : List (MatchPattern × Expr) :=
  [(.wildcard, e)]

private def βListAny : BoundsTy := .list (.lit 0) (.lit 5) (.prim .int)

#guard checkBoundCovers [] βListAny (brNilCons unitE unitE)

#guard checkBoundCovers [] βListAny (brWild unitE)

#guard checkBoundCovers [] (.list (.lit 0) (.lit 0) (.prim .int)) (brNilOnly unitE)

#guard checkBoundCovers [] (.list (.lit 1) (.lit 1) (.prim .int)) (brConsOnly unitE)

#guard !(checkBoundCovers [] βListAny (brNilOnly unitE))

end FHM.Bounds.Check
