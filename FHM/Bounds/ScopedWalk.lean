import FHM.Bounds.ScopedTyping

/-! Opt-in found-driven monomorphic RHS traversal. Symbolic carried annotations
are interpreted separately from the source; annotations remain obligations at
every nesting depth. Generalized HM let uses and nested count telescopes require
later introduction rules and are explicitly rejected here. -/

namespace FHM.Bounds.ScopedWalk

open CountSubstitution ScopedTyping

structure Result (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BoundsTy) (e : Expr) where
  hm : Ty
  bounds : BoundsTy
  root : Typed.rootHM? e = some hm
  shape : Synth.BoundsTy.toTy bounds = hm
  derivation : Derives ids rows Δ env e.stripFound bounds
  finite : Finite rows
  countScope : ScopedScheme.BoundsScoped caller bounds
  nodes : List Typed.NodeResult

private def equal (a b : Ty) (message : String) : Except String (PLift (a = b)) :=
  match BinderBridge.equalTy a b with | some h => .ok h | none => .error message

private def finish (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BoundsTy) (e : Expr) (path : CorePath)
    (hm : Ty) (β : BoundsTy) (h : Derives ids rows Δ env e.stripFound β)
    (children : List Typed.NodeResult) : Except String (Result ids rows caller Δ env e) := do
  match hr : Typed.rootHM? e with
  | none => throw "bounds: missing root found payload"
  | some actual =>
      let he ← equal actual hm "bounds: inconsistent root found payload"
      let hs ← equal (Synth.BoundsTy.toTy β) hm "bounds: synthesized shape disagrees with found payload"
      if hf : rows.all (fun row => row.2.noInf) = true then
        if hc : ScopedScheme.boundsScopedBool caller β = true then
          pure ⟨hm, β, by rw [hr, he.down], hs.down, h,
            fun row hr => Count.noInf_of_isNoInf (List.all_eq_true.mp hf row hr),
            ScopedScheme.boundsScopedBool_sound hc, ⟨path, hm, some β⟩ :: children⟩
        else throw "bounds: scoped RHS counts are outside caller scope"
      else throw "bounds: annotation interpretation contains an infinite Nat replacement"

private def chooseParam (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (ann : Option Ty) (hm : Ty) : Except String
      (Σ param, PLift (InterpretedAnnotation.ParamOK ids rows Δ ann param)) := do
  match ann with
  | none =>
      let ⟨param, _⟩ ← Typed.chooseParam Δ none hm
      pure ⟨param, ⟨True.intro⟩⟩
  | some τ =>
      let d ← InterpretedAnnotation.decode ids rows caller τ
      let _ ← equal (Synth.BoundsTy.toTy d.bounds) hm "bounds: parameter annotation disagrees with found type"
      pure ⟨d.bounds, ⟨d.source, d.decoded, SemanticSub.refl Δ _⟩⟩

private def checkBinding (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (ann : Option PolyTy) (actual : BoundsTy) :
    Except String (PLift (InterpretedAnnotation.BindingOK ids rows Δ ann actual)) := do
  match ann with
  | none => pure ⟨True.intro⟩
  | some σ =>
      if hσ : σ.paramCount = 0 then
        let obligation ← InterpretedAnnotation.check ids rows caller Δ σ.body actual
        pure ⟨hσ, obligation.down⟩
      else throw "bounds: polymorphic HM annotation unsupported in scoped RHS slice"

def walk (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (env : List BoundsTy) (path : CorePath) (e : Expr) (schemes : BinderSchemeMap) :
    Except String (Result ids rows caller Δ env e) := do
  match e with
  | .found hm (.primLit p) =>
      finish ids rows caller Δ env (.found hm (.primLit p)) path hm.eraseBounds (boundInfoOfPrimLit p)
        (by simp only [Expr.stripFound]; exact .literal) []
  | .found hm (.primBinOp op) =>
      finish ids rows caller Δ env (.found hm (.primBinOp op)) path hm.eraseBounds (Typed.primOpBounds op)
        (by simp only [Expr.stripFound]; exact .primBinOp) []
  | .found hm (.ctor name) =>
      if hn : name = nilCtorName then
        match hm.eraseBounds with
        | .customTy n [a] =>
            if n = listTyName then do
              let elem ← Typed.shapeTop a
              finish ids rows caller Δ env (.found hm (.ctor name)) path hm.eraseBounds (.list (.lit 0) (.lit 0) elem)
                (by subst name; simp only [Expr.stripFound]; exact .nil) []
            else throw "bounds: Nil has non-List found type"
        | _ => throw "bounds: Nil has non-List found type"
      else throw "bounds: standalone constructor unsupported in scoped RHS slice"
  | .found hm (.var i) =>
      match hv : env[i]? with
      | none => throw "bounds: variable outside scoped RHS environment"
      | some β =>
          finish ids rows caller Δ env (.found hm (.var i)) path hm.eraseBounds β
            (by simp only [Expr.stripFound]; exact .var hv) []
  | .found hm (.lambda ann body) =>
      match hm.eraseBounds with
      | .arrow paramTy _ =>
          let ⟨param, hp⟩ ← chooseParam ids rows caller Δ ann paramTy
          let _ ← equal (Synth.BoundsTy.toTy param) paramTy "bounds: parameter shape disagrees with found type"
          let result ← walk ids rows caller Δ (param :: env) (path ++ [.lambdaBody]) body schemes
          finish ids rows caller Δ env (.found hm (.lambda ann body)) path hm.eraseBounds (.arrow param result.bounds)
            (by simpa only [Expr.stripFound] using Derives.lambda hp.down result.derivation) result.nodes
      | _ => throw "bounds: lambda has non-arrow found type"
  | .found hm (.letIn ann rhs body) =>
      let actual ← walk ids rows caller Δ env (path ++ [.letRhs]) rhs schemes
      if ann.isNone then
        let fact ← BinderBridge.atSite schemes (.letIn path) actual.bounds
          (env.map Synth.BoundsTy.toTy ++ rhs.stripFound.tyFreeVars.map Ty.fvar)
        unless fact.scheme.paramCount = 0 do
          throw "bounds: generalized HM let unsupported in scoped RHS slice"
      let hp ← checkBinding ids rows caller Δ ann actual.bounds
      let result ← walk ids rows caller Δ (actual.bounds :: env) (path ++ [.letBody]) body schemes
      finish ids rows caller Δ env (.found hm (.letIn ann rhs body)) path hm.eraseBounds result.bounds
        (by simpa only [Expr.stripFound] using Derives.letMono hp.down actual.derivation result.derivation)
        (actual.nodes ++ result.nodes)
  | .found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail) =>
      if hn : name = consCtorName then
        let h ← walk ids rows caller Δ env (path ++ [.appFun, .appArg]) head schemes
        let t ← walk ids rows caller Δ env (path ++ [.appArg]) tail schemes
        match ht : t.bounds with
        | .list lo hi elem =>
            let _ ← equal ctorTy.eraseBounds (.arrow h.hm (.arrow t.hm t.hm)) "bounds: inconsistent Cons found type"
            let _ ← equal partialTy.eraseBounds (.arrow t.hm t.hm) "bounds: inconsistent partial Cons found type"
            let hs ← Typed.subtype Δ h.bounds elem
            finish ids rows caller Δ env
              (.found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail)) path hm.eraseBounds
              (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
              (by subst name; simpa only [Expr.stripFound] using
                Derives.cons h.derivation (by simpa only [ht] using t.derivation) hs.down)
              (⟨path ++ [.appFun], partialTy.eraseBounds, none⟩ ::
                ⟨path ++ [.appFun, .appFun], ctorTy.eraseBounds, none⟩ :: h.nodes ++ t.nodes)
        | _ => throw "bounds: Cons tail has non-List bounds"
      else throw "bounds: unsupported constructor application in scoped RHS slice"
  | .found hm (.app fn arg) =>
      let f ← walk ids rows caller Δ env (path ++ [.appFun]) fn schemes
      let actual ← walk ids rows caller Δ env (path ++ [.appArg]) arg schemes
      match hf : f.bounds with
      | .arrow domain result =>
          let hs ← Typed.subtype Δ actual.bounds domain
          finish ids rows caller Δ env (.found hm (.app fn arg)) path hm.eraseBounds result
            (by simpa only [Expr.stripFound] using
              Derives.app (by simpa only [hf] using f.derivation) actual.derivation hs.down)
            (f.nodes ++ actual.nodes)
      | _ => throw "bounds: application has non-function bounds"
  | .found _ _ => throw "bounds: expression form unsupported in scoped RHS slice"
  | _ => throw "bounds: every logical node must have one found wrapper"
termination_by sizeOf e

#print axioms walk

end FHM.Bounds.ScopedWalk
