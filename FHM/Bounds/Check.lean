import FHM.Bounds.Typing
import FHM.Pretty

/-!
# Computational bounds checks for Live (P4c-hasbounds)

Executable mirrors of `Sub` / `MeetsAscription` using `checkValid` (Z3).
Synthesized β is **`defaultBounds τ`** until a HasBounds synthesizer exists —
enough to reject impossible solid ascriptions and to exercise the oracle path.
-/

namespace FHM.Bounds.Check

open FHM.Bounds

private partial def BoundsTy.pretty : BoundsTy → String
  | .prim p =>
      match p with
      | .unit => "Unit" | .int => "Int" | .nat => "Nat" | .char => "Char"
  | .arrow a b => s!"{BoundsTy.pretty a} → {BoundsTy.pretty b}"
  | .bvar i => s!"β{i}"
  | .fvar i => s!"?β{i}"
  | .list lo hi e =>
      let p : Count → String
        | .lit n => toString n
        | .inf => "∞"
        | c => reprStr c
      s!"BL {p lo} {p hi} {BoundsTy.pretty e}"
  | .custom n as =>
      let nm := match n with | .mk s => s
      if as.isEmpty then nm
      else nm ++ " " ++ String.intercalate " " (as.map BoundsTy.pretty)

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

/-- Look up a binder’s HM monotype body by name. -/
def tyOfBinder (binds : List (ValName × PolyTy)) (n : ValName) : Option Ty :=
  (binds.find? fun ⟨n', _⟩ => n' = n).map fun ⟨_, σ⟩ => σ.body

/-- Check erase/`ofLower` ascriptions against `defaultBounds` of HM types.

Fails on holes or when `defaultBounds τ ≰ ann`. Under `--bl` only. -/
def checkProgramAnns
    (binds : List (ValName × PolyTy))
    (binderEnv : List ValName)
    (anns : ProgramBoundsAnns)
    (programTy : PolyTy) : Except String Unit := do
  for pair in binderEnv.zip anns.binderAnns do
    let n := pair.1
    let a? := pair.2
    match a? with
    | none => pure ()
    | some ann =>
        match BoundsAnnTy.toBoundsTy? ann with
        | none =>
            throw s!"bounds: ascription on {prettyValName n} has holes (elab not in Live yet)"
        | some _ =>
            match tyOfBinder binds n with
            | none =>
                throw s!"bounds: no HM type for binder {prettyValName n}"
            | some τ =>
                let β := defaultBounds τ
                unless checkMeetsAscription [] β ann do
                  throw s!"bounds: ascription not met for {prettyValName n} \
(synth {BoundsTy.pretty β} ≰ {ann.pretty})"
  match anns.bodyAnn with
  | none => pure ()
  | some ann =>
      match BoundsAnnTy.toBoundsTy? ann with
      | none =>
          throw "bounds: body ascription has holes (elab not in Live yet)"
      | some _ =>
          let β := defaultBounds programTy.body
          unless checkMeetsAscription [] β ann do
            throw s!"bounds: body ascription not met (synth {BoundsTy.pretty β} ≰ {ann.pretty})"
  pure ()

end FHM.Bounds.Check
