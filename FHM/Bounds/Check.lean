import FHM.Bounds.Synth
import FHM.Pretty

/-!
# Computational bounds checks for Live (slice 4)

Walk Infer’s Core `eOut` with origin `synthBounds`, then
`checkMeetsAscriptionPinned` against erase/`ofLower` anns (pin `_` to synth).
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
      if outerIdx ≥ nBind then
        throw "bounds: let spine longer than binderEnv"
      let i := nBind - 1 - outerIdx
      let β1 ← checkBounds Δ bctx rhs σ.body
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

/-! ## Guards (Core Nil/Cons origin synth + pin-to-synth holes) -/

private def nilE : Expr := .ctor nilCtorName
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

end FHM.Bounds.Check
