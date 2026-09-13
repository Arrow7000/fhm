import FHM.Bounds.ScopedScheme

/-! # Certified decoding of scoped, carried annotations

Read bounds demands from Core annotations, checking every solid count against
an explicit lexical scope. The resulting demand has exactly the annotation's
HM-erased skeleton. Bare List means the top interval, not an exact origin.

Decoding does not check an expression against the demand. A declared contract
still requires an RHS derivation before its use is justified; the initial
`Typed.walk` deliberately remains unchanged until that integration exists.
-/

namespace FHM.Bounds.ScopedAnnotation

open Scope ScopedScheme

structure Decoded (ids : List Nat) (τ : Ty) where
  bounds : BoundsTy
  inScope : BoundsScoped ids bounds
  shape : Synth.BoundsTy.toTy bounds = τ.eraseBounds

structure DecodedList (ids : List Nat) (as : List Ty) where
  bounds : List BoundsTy
  inScope : BoundsListScoped ids bounds
  shape : bounds.map Synth.BoundsTy.toTy = TyList.eraseBounds as

mutual
def decode (ids : List Nat) (τ : Ty) : Except String (Decoded ids τ) := do
  match τ with
  | .prim p => pure ⟨.prim p, trivial, by simp only [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩
  | .fvar i => pure ⟨.fvar i, trivial, by simp only [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩
  | .bvar i => pure ⟨.bvar i, trivial, by simp only [Synth.BoundsTy.toTy, Ty.eraseBounds]⟩
  | .arrow a b =>
      let da ← decode ids a
      let db ← decode ids b
      pure ⟨.arrow da.bounds db.bounds, ⟨da.inScope, db.inScope⟩, by
        simp only [Synth.BoundsTy.toTy, Ty.eraseBounds, da.shape, db.shape]⟩
  | .bl (.solid lo) (.solid hi) a =>
      if hlo : countScopedBool ids lo = true then
        if hhi : countScopedBool ids hi = true then
          let da ← decode ids a
          pure ⟨.list lo hi da.bounds,
            ⟨countScopedBool_sound hlo, countScopedBool_sound hhi, da.inScope⟩, by
              simp only [Synth.BoundsTy.toTy, Ty.eraseBounds, listTy, bareListTy,
                FHM.Bounds.listTyName, _root_.listTyName, da.shape]⟩
        else throw "bounds: annotation upper count is outside lexical scope"
      else throw "bounds: annotation lower count is outside lexical scope"
  | .bl _ _ _ => throw "bounds: count holes need a separate inference/escape contract"
  | .customTy name args =>
      if hn : name = listTyName then
        match args with
        | [a] =>
            let da ← decode ids a
            pure ⟨.list (.lit 0) .inf da.bounds, ⟨trivial, trivial, da.inScope⟩, by
              simp only [Synth.BoundsTy.toTy, Ty.eraseBounds, TyList.eraseBounds,
                listTy, da.shape, hn]⟩
        | _ => throw "bounds: malformed List annotation arity"
      else
        let ds ← decodeList ids args
        pure ⟨.custom name ds.bounds, ds.inScope, by
          simp only [Synth.BoundsTy.toTy, Ty.eraseBounds, ds.shape]⟩
termination_by sizeOf τ

def decodeList (ids : List Nat) (as : List Ty) : Except String (DecodedList ids as) := do
  match as with
  | [] => pure ⟨[], trivial, by simp only [List.map_nil, TyList.eraseBounds]⟩
  | a :: as =>
      let da ← decode ids a
      let ds ← decodeList ids as
      pure ⟨da.bounds :: ds.bounds, ⟨da.inScope, ds.inScope⟩, by
        simp only [List.map_cons, TyList.eraseBounds, da.shape, ds.shape]⟩
termination_by sizeOf as
end

structure Contract (quantified captures : List Nat) (premises : List Constraint)
    (τ : Ty) where
  annotation : Decoded (quantified ++ captures) τ
  wf : Scheme.WF ⟨quantified, captures, premises, annotation.bounds⟩

def Contract.scheme {quantified captures premises τ}
    (c : Contract quantified captures premises τ) : Scheme :=
  ⟨quantified, captures, premises, c.annotation.bounds⟩

theorem Contract.shape {quantified captures premises τ}
    (c : Contract quantified captures premises τ) :
    Synth.BoundsTy.toTy c.scheme.body = τ.eraseBounds := c.annotation.shape

/-- The counts in the annotation must come from its own telescope or explicit
    captures. An invalid interface fails even when the body uses no counts. -/
def contract (quantified captures : List Nat) (premises : List Constraint) (τ : Ty) :
    Except String (Contract quantified captures premises τ) := do
  let ann ← decode (quantified ++ captures) τ
  let s : Scheme := ⟨quantified, captures, premises, ann.bounds⟩
  if hw : s.wfBool = true then
    pure ⟨ann, Scheme.wfBool_sound hw⟩
  else throw "bounds: declared count contract has an invalid interface or premises"

#print axioms decode
#print axioms contract
#print axioms Contract.shape

end FHM.Bounds.ScopedAnnotation
