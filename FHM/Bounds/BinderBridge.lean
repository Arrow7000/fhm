import FHM.Bounds.TypeSubstitution
import FHM.InferW

/-! # Checked bridges from inferred binder schemes

Structural matching proposes slot arguments, but acceptance carries exact
relational HM instantiation evidence. Bounds abstraction closes only a checked,
injective list of free HM identities and preserves all count payloads.

These certificates do not prove artifact coherence or universal RHS typing.
In particular, syntactic abstraction alone is not permission to generalize.
The initial abstraction API rejects enclosing bound-type-variable scopes.
-/

namespace FHM.Bounds.BinderBridge

mutual
def equalTy (a b : Ty) : Option (PLift (a = b)) :=
  match a, b with
  | .prim p, .prim q => if h : p = q then some ⟨by subst q; rfl⟩ else none
  | .fvar i, .fvar j => if h : i = j then some ⟨by subst j; rfl⟩ else none
  | .bvar i, .bvar j => if h : i = j then some ⟨by subst j; rfl⟩ else none
  | .arrow a b, .arrow c d => do
      let ha ← equalTy a c
      let hb ← equalTy b d
      pure ⟨by rw [ha.down, hb.down]⟩
  | .customTy n as, .customTy m bs =>
      if hn : n = m then do
        let hs ← equalTys as bs
        pure ⟨by rw [hn, hs.down]⟩
      else none
  | _, _ => none
termination_by sizeOf a + sizeOf b

def equalTys (as bs : List Ty) : Option (PLift (as = bs)) :=
  match as, bs with
  | [], [] => some ⟨rfl⟩
  | a :: as, b :: bs => do
      let hh ← equalTy a b
      let ht ← equalTys as bs
      pure ⟨by rw [hh.down, ht.down]⟩
  | _, _ => none
termination_by sizeOf as + sizeOf bs
end

mutual
/-- Proposals are untrusted until the complete opening is checked below. -/
private def collect (pattern target : Ty) : Option (List (Nat × Ty)) :=
  match pattern, target with
  | .bvar i, t => some [(i, t)]
  | .prim p, .prim q => if p = q then some [] else none
  | .fvar i, .fvar j => if i = j then some [] else none
  | .arrow a b, .arrow c d => do
      pure ((← collect a c) ++ (← collect b d))
  | .customTy n as, .customTy m bs => if n = m then collectList as bs else none
  | _, _ => none
termination_by sizeOf pattern + sizeOf target

private def collectList (as bs : List Ty) : Option (List (Nat × Ty)) :=
  match as, bs with
  | [], [] => some []
  | a :: as, b :: bs => do
      pure ((← collect a b) ++ (← collectList as bs))
  | _, _ => none
termination_by sizeOf as + sizeOf bs
end

structure Instance (σ : PolyTy) (found : Ty) where
  args : List Ty
  arity : args.length = σ.paramCount
  wf : σ.eraseBounds.WF
  witness : σ.eraseBounds.InstantiatesTo args found.eraseBounds

/-- An unused slot receives an explicit Unit witness. Repeated slots must agree
    in the final opening; out-of-range slots never reach a default lookup. -/
def instantiate (σ : PolyTy) (found : Ty) : Except String (Instance σ found) := do
  let body := σ.body.eraseBounds
  if hw : body.bvarsBelow σ.paramCount = true then
    let uses ← match collect body found.eraseBounds with
      | none => throw "bounds: found type is not an instance of inferred binder scheme"
      | some uses => pure uses
    let args := (List.range σ.paramCount).map fun i =>
      ((uses.find? (fun row => row.1 == i)).map Prod.snd).getD (.prim .unit)
    let opened := Ty.openWith args body
    let he ← match equalTy opened found.eraseBounds with
      | none => throw "bounds: inconsistent repeated HM slot or captured type"
      | some he => pure he
    have wf : σ.eraseBounds.WF := (Ty.bvarsBelow_iff body).mp hw
    have arity : args.length = σ.paramCount := by simp [args]
    have hi := InstantiatesBy.openWith wf (Nat.le_of_eq arity.symm)
    pure ⟨args, arity, wf, by
      change InstantiatesBy args body found.eraseBounds
      rw [← he.down]
      exact hi⟩
  else throw "bounds: inferred binder scheme has an out-of-scope HM slot"

mutual
def close (ids : List Nat) : BoundsTy → BoundsTy
  | .prim p => .prim p
  | .bvar i => .bvar i
  | .fvar i => match ids.idxOf? i with
      | none => .fvar i
      | some slot => .bvar slot
  | .arrow a b => .arrow (close ids a) (close ids b)
  | .list lo hi elem => .list lo hi (close ids elem)
  | .custom n as => .custom n (closeList ids as)

def closeList (ids : List Nat) : List BoundsTy → List BoundsTy
  | [] => []
  | a :: as => close ids a :: closeList ids as
end

mutual
theorem close_shape (ids : List Nat) (β : BoundsTy) :
    Synth.BoundsTy.toTy (close ids β) = (Synth.BoundsTy.toTy β).closeOver ids := by
  cases β with
  | prim | bvar => simp only [close, Synth.BoundsTy.toTy, Ty.closeOver]
  | fvar i =>
      simp only [close, Synth.BoundsTy.toTy, Ty.closeOver]
      cases ids.idxOf? i <;> simp only [Synth.BoundsTy.toTy]
  | arrow a b => simp only [close, Synth.BoundsTy.toTy, Ty.closeOver, close_shape ids a, close_shape ids b]
  | list lo hi elem =>
      simp only [close, Synth.BoundsTy.toTy, listTy, Ty.closeOver, TyList.closeOver, close_shape ids elem]
  | custom n as => simp only [close, Synth.BoundsTy.toTy, Ty.closeOver, closeList_shape ids as]
termination_by sizeOf β

private theorem closeList_shape (ids : List Nat) (as : List BoundsTy) :
    (closeList ids as).map Synth.BoundsTy.toTy = TyList.closeOver ids (as.map Synth.BoundsTy.toTy) := by
  cases as with
  | nil => simp only [closeList, List.map_nil, TyList.closeOver]
  | cons a as => simp only [closeList, List.map_cons, TyList.closeOver, close_shape ids a, closeList_shape ids as]
termination_by sizeOf as
end

mutual
theorem close_inScope {scope β} (ids : List Nat) (h : ScopedScheme.BoundsScoped scope β) :
    ScopedScheme.BoundsScoped scope (close ids β) := by
  cases β with
  | prim | bvar => trivial
  | fvar i =>
      simp only [close]
      cases ids.idxOf? i <;> trivial
  | arrow a b => exact ⟨close_inScope ids h.1, close_inScope ids h.2⟩
  | list lo hi elem => exact ⟨h.1, h.2.1, close_inScope ids h.2.2⟩
  | custom n as => exact closeList_inScope ids h
termination_by sizeOf β

private theorem closeList_inScope {scope as} (ids : List Nat) (h : ScopedScheme.BoundsListScoped scope as) :
    ScopedScheme.BoundsListScoped scope (closeList ids as) := by
  cases as with
  | nil => trivial
  | cons a as => exact ⟨close_inScope ids h.1, closeList_inScope ids h.2⟩
termination_by sizeOf as
end

private def fvarId : Ty → Option Nat
  | .fvar i => some i
  | _ => none

structure Abstraction (σ : PolyTy) (actual : BoundsTy) (captures : List Ty) where
  ids : List Nat
  arity : ids.length = σ.paramCount
  distinct : ids.Nodup
  fresh : ∀ i ∈ ids, ∀ t ∈ captures, i ∉ t.freeVars
  originalLC : (Synth.BoundsTy.toTy actual).IsLC
  hmOpening : Instance σ (Synth.BoundsTy.toTy actual)
  shape : Synth.BoundsTy.toTy (close ids actual) = σ.body.eraseBounds

/-- Recover generalized identities only from a certified opening at free HM
    variables. A type-constrained slot, duplicate identity, escaped capture or
    enclosing bound-variable scope is not silently interpreted as abstraction. -/
def abstract (σ : PolyTy) (actual : BoundsTy) (captures : List Ty) :
    Except String (Abstraction σ actual captures) := do
  let mono := Synth.BoundsTy.toTy actual
  if hlc : mono.bvarsBelow 0 = true then
    let opening ← instantiate σ mono
    let ids ← match opening.args.mapM fvarId with
      | none => throw "bounds: inferred binder slot is not a generalized free identity"
      | some ids => pure ids
    if ha : ids.length = σ.paramCount then
      if hd : ids.Nodup then
        if hf : ids.all (fun i => captures.all (fun t => !t.freeVars.contains i)) = true then
          let he ← match equalTy (Synth.BoundsTy.toTy (close ids actual)) σ.body.eraseBounds with
            | none => throw "bounds: abstraction does not match inferred binder scheme"
            | some he => pure he
          pure ⟨ids, ha, hd, by
            intro i hi t ht
            have h := List.all_eq_true.mp (List.all_eq_true.mp hf i hi) t ht
            simpa [List.contains_iff_mem] using h,
            (Ty.bvarsBelow_iff mono).mp hlc, opening, he.down⟩
        else throw "bounds: generalized HM identity escapes into captured type interface"
      else throw "bounds: different inferred slots alias one free HM identity"
    else throw "bounds: recovered binder abstraction has wrong arity"
  else throw "bounds: abstraction under enclosing HM bound slots is not supported yet"

/-- Combine a certified abstraction with an independently checked use. Caller
    bounds arguments must correspond to the actual HM instantiation witness. -/
theorem use_shape {σ actual captures found} (binding : Abstraction σ actual captures)
    (use : Instance σ found) (rows : CountSubstitution.Bindings) (args : Nat → BoundsTy)
    (ha : ∀ i t, use.args[i]? = some t → Synth.BoundsTy.toTy (args i) = t) :
    Synth.BoundsTy.toTy (TypeSubstitution.combined rows args (close binding.ids actual)) =
      found.eraseBounds :=
  TypeSubstitution.found_shape rows args binding.shape use.witness ha

def candidates (schemes : BinderSchemeMap) (site : CoreBinderSite) : List PolyTy :=
  (schemes.filter (fun row => row.1 == site)).map Prod.snd

structure AtSite (schemes : BinderSchemeMap) (site : CoreBinderSite)
    (actual : BoundsTy) (captures : List Ty) where
  scheme : PolyTy
  selected : candidates schemes site = [scheme]
  abstraction : Abstraction scheme actual captures

/-- Require exactly one inferred fact for this Core occurrence, not one source
    name or the first matching row. Compiler clones have different Core sites. -/
def atSite (schemes : BinderSchemeMap) (site : CoreBinderSite)
    (actual : BoundsTy) (captures : List Ty) :
    Except String (AtSite schemes site actual captures) := do
  match h : candidates schemes site with
  | [] => throw "bounds: missing inferred binder scheme at Core site"
  | [σ] =>
      let a ← abstract σ actual captures
      pure ⟨σ, h, a⟩
  | _ => throw "bounds: duplicate inferred binder schemes at Core site"

#print axioms instantiate
#print axioms abstract
#print axioms close_shape
#print axioms use_shape
#print axioms atSite

end FHM.Bounds.BinderBridge
