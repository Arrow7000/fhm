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

private def BoundsTy.pretty : BoundsTy → String
  | .prim p =>
      match p with
      | .unit => "Unit" | .int => "Int" | .nat => "Nat" | .char => "Char"
  | .arrow a b => s!"{BoundsTy.pretty a} → {BoundsTy.pretty b}"
  | .bvar i => s!"β{i}"
  | .fvar i => s!"?β{i}"
  | .list lo hi e =>
      let rec p : Count → String
        | .lit n => toString n
        | .inf => "∞"
        | .add a b => s!"({p a} + {p b})"
        | .mul a b => s!"({p a} * {p b})"
        | .pred a => s!"(pred {p a})"
        | .min a b => s!"(min {p a} {p b})"
        | .max a b => s!"(max {p a} {p b})"
        | .var v => reprStr v
      s!"BL {p lo} {p hi} {BoundsTy.pretty e}"
  | .custom n as =>
      let nm := match n with | .mk s => s
      if as.isEmpty then nm
      else nm ++ " " ++ String.intercalate " " (as.map BoundsTy.pretty)

/-- Look up a binder’s HM monotype body by name. -/
def tyOfBinder (binds : List (ValName × PolyTy)) (n : ValName) : Option Ty :=
  (binds.find? fun ⟨n', _⟩ => n' = n).map fun ⟨_, σ⟩ => σ.body

/-- Walk the outer `letIn` / `letRec` spine from Infer, checking each binder’s
erase ascription against origin-synth of its RHS, then the body.

`binderEnv` / `anns.binderAnns` are 0 = innermost; the spine is outermost-first,
so the k-th outer binder group occupies the next high indices. -/
def checkLetSpine
    (binderEnv : List ValName)
    (anns : ProgramBoundsAnns)
    (Δ : List Constraint)
    (bctx : BoundEnv)
    (outerIdx : Nat)
    (e : Expr)
    (τBody : Ty) : Except String BoundsTy := do
  let meetBinder (i : Nat) (β1 : BoundsTy) : Except String Unit := do
    match anns.binderAnns[i]? with
    | some (some ann) => do
        match checkMeetsAscriptionPinned Δ β1 ann with
        | .ok () => pure ()
        | .error msg =>
            let n := binderEnv[i]?.getD ⟨"?"⟩
            throw s!"bounds: ascription not met for {prettyValName n} ({msg})"
    | _ => pure ()
  match e with
  | .letIn (some σ) rhs body => do
      let nBind := binderEnv.length
      let β1 ← checkBounds Δ bctx rhs σ.body
      if outerIdx ≥ nBind then
        -- Infer-inserted let (not a surface group binder); extend bctx only.
        checkLetSpine binderEnv anns Δ (β1 :: bctx) outerIdx body τBody
      else
        let i := nBind - 1 - outerIdx
        meetBinder i β1
        checkLetSpine binderEnv anns Δ (β1 :: bctx) (outerIdx + 1) body τBody
  | .letIn none rhs body => do
      let β1 ← Prod.snd <$> inferBounds Δ bctx rhs
      checkLetSpine binderEnv anns Δ (β1 :: bctx) outerIdx body τBody
  | .letRec recAnns bindings body => do
      let k := bindings.length
      unless recAnns.length == k do
        throw "bounds: letRec anns/bindings length mismatch"
      let nBind := binderEnv.length
      if outerIdx + k > nBind then
        throw "bounds: letRec group longer than remaining binderEnv"
      let start := nBind - outerIdx - k
      -- Non-recursive synth under current bctx (list literals / non-mutual).
      let βs ← recAnns.zip bindings |>.mapM fun ⟨ann?, rhs⟩ => do
        let τj ← match ann? with
          | some σ => pure σ.body
          | none => throw "bounds: letRec member needs scheme ascription from Infer"
        checkBounds Δ bctx rhs τj
      for pair in (List.range k).zip βs do
        meetBinder (start + pair.1) pair.2
      checkLetSpine binderEnv anns Δ (βs ++ bctx) (outerIdx + k) body τBody
  | _ => do
      let β ← checkBounds Δ bctx e τBody
      match anns.bodyAnn with
      | none => pure β
      | some ann => do
          match checkMeetsAscriptionPinned Δ β ann with
          | .ok () => pure β
          | .error msg =>
              throw s!"bounds: body ascription not met ({msg})"
termination_by e.size
decreasing_by all_goals (try simp only [Expr.size, Expr.sizeRecGroup]; omega)

/-- Origin-synth Core `e` at HM `τ`, checking erase/`ofLower` ascriptions.

Holes in anns are pinned to synth Counts, then `Sub`. Under `--bl` only. -/
def checkProgramAnns
    (e : Expr)
    (τ : Ty)
    (binderEnv : List ValName)
    (anns : ProgramBoundsAnns) : Except String Unit := do
  let _ ← checkLetSpine binderEnv anns [] [] 0 e τ
  pure ()

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
              (fieldTys.map agreesTemplate).reverse ++ bctx
          | _ => bctx

mutual
/-- Recurse into match branch bodies (mutual with `checkProgramMatchesGo`). -/
def checkProgramMatchesBranches (ctors : CtorEnv) (Δ : List Constraint) (bctx : BoundEnv)
    (τs : Ty) (βs : BoundsTy) (lo hi : Count) (βe : BoundsTy)
    (brs : List (MatchPattern × Expr)) : Except String Unit :=
  match brs with
  | [] => pure ()
  | (pat, body) :: rest => do
      let bctx' := branchBctx ctors τs βs bctx lo hi βe pat
      checkProgramMatchesGo ctors Δ bctx' body
      checkProgramMatchesBranches ctors Δ bctx τs βs lo hi βe rest
termination_by Expr.sizeBranches brs
decreasing_by
  all_goals (first | exact size_lt_sizeBranches_one | exact size_lt_sizeBranches_tail | (simp only [Expr.sizeBranches]; omega))

/-- Walk Core for nested matches; check coverage at each `match_`. -/
def checkProgramMatchesGo (ctors : CtorEnv) (Δ : List Constraint) (bctx : BoundEnv)
    (e : Expr) : Except String Unit :=
  match e with
  | .primLit _ | .primBinOp _ | .var _ _ | .ctor _ => pure ()
  | .lambda ann body =>
      match ann with
      | some τp => checkProgramMatchesGo ctors Δ (agreesTemplate τp :: bctx) body
      | none => checkProgramMatchesGo ctors Δ bctx body
  | .app f arg => do
      checkProgramMatchesGo ctors Δ bctx f
      checkProgramMatchesGo ctors Δ bctx arg
  | .letIn ann? rhs body => do
      let β1 ← match ann? with
        | some σ => checkBounds Δ bctx rhs σ.body
        | none => Prod.snd <$> inferBounds Δ bctx rhs
      checkProgramMatchesGo ctors Δ (β1 :: bctx) body
  | .letRec anns bindings body => do
      if anns.length != bindings.length then
        throw "bounds: letRec anns/bindings length mismatch"
      let βs ← inferLetRecGroup Δ bctx anns bindings
      checkProgramMatchesGo ctors Δ (βs ++ bctx) body
  | .match_ scrut brs => do
      let (τs, βs) ← inferBounds Δ bctx scrut
      -- @TODO(bounds-path-Δ): Δ stays `[]` at Live v1; nested “tail empty ⇒ inner
      -- Nil-only” needs `nilRefine`/`consRefine` stacked along match paths later.
      match βs with
      | .list lo hi βe =>
          unless checkBoundCovers Δ βs brs do
            throw "bounds: list match does not cover scrutinee bounds"
          checkProgramMatchesBranches ctors Δ bctx τs βs lo hi βe brs
      | _ =>
          unless coreCtorCoverage ctors τs brs do
            throw "bounds: match not exhaustive for scrutinee type"
          checkProgramMatchesBranches ctors Δ bctx τs βs (.lit 0) (.lit 0) βs brs
  termination_by e.size
  decreasing_by all_goals (
    first
    | exact sizeBranches_lt_match
    | exact size_lt_app_fn
    | exact size_lt_app_arg
    | exact body_size_lt_letRec
    | exact sizeRecGroup_lt_letRec
    | (simp only [Expr.size]; omega))

end

/-- Top-level Core match coverage walk for Live `--bl`. -/
def checkProgramMatches (ctors : CtorEnv) (e : Expr) (_τ : Ty) : Except String Unit := do
  checkProgramMatchesGo ctors [] [] e
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
