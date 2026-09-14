import FHM.Bounds.ScopedWalk

/-! # Construct a count-contract certificate from a checked typed RHS

Exact Core sites select count telescopes and unannotated machine HM facts.
Unannotated RHSs generalize through checked, fresh machine identities; annotated
HM declarations remain monomorphic in this slice. A recursive
member's RHS may be inspected, but this is NOT acceptance of its recursive
group: no recursive assumptions or group contract rule are supplied here.
Checks consume found children and original annotations before using the proved
erasure bridge. Full artifact coherence and product wiring remain separate.
-/

namespace FHM.Bounds.ScopedDeclaration

open CountSubstitution

structure RHS where
  annotation : Option PolyTy
  expr : Expr
  path : CorePath

def locate (output : Expr) (site : CoreBinderSite) : Except String RHS := do
  match site with
  | .letIn path =>
      match output.atCorePath path with
      | some (.found _ (.letIn ann rhs _)) => pure ⟨ann, rhs, path ++ [.letRhs]⟩
      | _ => throw "bounds: requested site is not a typed let declaration"
  | .letRec path member =>
      match output.atCorePath path with
      | some (.found _ (.letRec anns rhss _)) =>
          unless anns.length = rhss.length do throw "bounds: recursive annotation/RHS arity mismatch"
          match anns[member]?, rhss[member]? with
          | some ann, some rhs => pure ⟨ann, rhs, path ++ [.letRecRhs member]⟩
          | _, _ => throw "bounds: requested recursive member is outside group"
      | _ => throw "bounds: requested site is not a typed recursive declaration"
  | _ => throw "bounds: requested site is not a let declaration"

def telescope (metadata : Scope.Metadata) (site : CoreBinderSite) : Except String (List Nat) :=
  match metadata.telescopes.filter (fun t => t.site == site) with
  | [] => .ok []
  | [t] => .ok (t.binders.map Prod.snd)
  | _ => .error "bounds: duplicate count telescope at Core site"

structure Checked (env : List BoundsTy) (captures : List Nat) (premises : List Constraint) where
  site : CoreBinderSite
  rhs : RHS
  quantified : List Nat
  typed : ScopedWalk.Result (quantified ++ captures) [] (quantified ++ captures) premises env rhs.expr
  certificate : CountContract.Certified (env.map SchemeTyping.Binding.mono) rhs.expr.stripFound.erase

private def abstraction (schemes : BinderSchemeMap) (site : CoreBinderSite)
    (ann : Option PolyTy) (hm : Ty) (β : BoundsTy) (captures : List Ty) :
    Except String (Σ σ, BinderBridge.Abstraction σ β captures) := do
  match ann with
  | none =>
      let fact ← BinderBridge.atSite schemes site β captures
      pure ⟨fact.scheme, fact.abstraction⟩
  | some _ =>
      let σ : PolyTy := ⟨0, hm⟩
      let a ← BinderBridge.abstract σ β captures
      pure ⟨σ, a⟩

/-- Construct a certificate only after checking the actual typed RHS and its
    declared obligation. This is not an entry point for accepting whole groups. -/
def checkRHS (output : Expr) (schemes : BinderSchemeMap) (metadata : Scope.Metadata)
    (site : CoreBinderSite) (captures : List Nat := []) (env : List BoundsTy := [])
    (premises : List Constraint := []) : Except String (Checked env captures premises) := do
  unless metadata.problems.isEmpty do throw "bounds: unresolved or duplicate count binder scope"
  let rhs ← locate output site
  let quantified ← telescope metadata site
  let ids := quantified ++ captures
  let actual ← ScopedWalk.walk ids [] ids premises env rhs.path rhs.expr schemes
  match rhs.annotation with
  | none => pure ()
  | some σ =>
      unless σ.paramCount = 0 do throw "bounds: polymorphic HM annotation unsupported in scoped certificate slice"
      match BinderBridge.equalTy actual.hm σ.body.eraseBounds with
      | none => throw "bounds: annotated RHS HM specialization unsupported in scoped certificate slice"
      | some _ => pure ()
      let _ ← InterpretedAnnotation.check ids [] ids premises σ.body actual.bounds
      pure ()
  let ⟨_, a⟩ ← abstraction schemes site rhs.annotation actual.hm actual.bounds
    (env.map Synth.BoundsTy.toTy ++ rhs.expr.stripFound.tyFreeVars.map Ty.fvar)
  let hm := SchemeTyping.fromBinder a
  let countScheme : ScopedScheme.Scheme := ⟨quantified, captures, premises, hm.body⟩
  if hw : countScheme.wfBool = true then
    if hc : env.all (ScopedScheme.boundsScopedBool captures) = true then
      let cert : CountContract.Certified (env.map SchemeTyping.Binding.mono)
          rhs.expr.stripFound.erase :=
        { hm, counts := countScheme, body := rfl
          wf := ScopedScheme.Scheme.wfBool_sound hw
          captureScope := by
            intro b hb
            obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hb
            exact ScopedScheme.boundsScopedBool_sound (List.all_eq_true.mp hc β hβ)
          typing := ScopedTyping.binder_instances a actual.derivation }
      pure ⟨site, rhs, quantified, actual, cert⟩
    else throw "bounds: declaration environment contains counts outside explicit captures"
  else throw "bounds: checked RHS escapes declared count interface or has invalid premises"

#print axioms checkRHS

end FHM.Bounds.ScopedDeclaration
