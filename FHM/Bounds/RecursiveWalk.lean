import FHM.Bounds.RecursiveVariable
import FHM.Bounds.RecursiveCountTransport

/-! # Found-driven symbolic RHS checking under recursive assumptions

Consumes the existing HM artifact; never reruns inference or invents recursive
HM slots. Every supported annotation remains an interpreted obligation. Results
carry conditional derivations and the explicit fragment proof for universal RHS
transport. This checks RHSs, not groups, and does not export an assumed contract.
-/

namespace FHM.Bounds.RecursiveWalk

open RecursiveTyping CountSubstitution RecursiveCountTransport

structure Result (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) (e : Expr) where
  hm : Ty
  bounds : BoundsTy
  root : Typed.rootHM? e = some hm
  shape : Synth.BoundsTy.toTy bounds = hm
  derivation : Derives ids rows Δ env e.stripFound bounds
  noGroups : NoGroups e.stripFound
  finite : Finite rows
  countScope : ScopedScheme.BoundsScoped caller bounds
  nodes : List Typed.NodeResult

private def equal (a b : Ty) (message : String) : Except String (PLift (a = b)) :=
  match BinderBridge.equalTy a b with | some h => .ok h | none => .error message

private def bindingHM : Binding → Ty
  | .mono β => Synth.BoundsTy.toTy β
  | .recursive c => c.hm

private def finish (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) (e : Expr) (path : CorePath)
    (hm : Ty) (β : BoundsTy) (h : Derives ids rows Δ env e.stripFound β)
    (hn : NoGroups e.stripFound) (children : List Typed.NodeResult) :
    Except String (Result ids rows caller Δ env e) := do
  match hr : Typed.rootHM? e with
  | none => throw "bounds: missing recursive RHS root found payload"
  | some actual =>
      let he ← equal actual hm "bounds: inconsistent recursive RHS root found payload"
      let hs ← equal (Synth.BoundsTy.toTy β) hm "bounds: recursive RHS shape disagrees with found payload"
      if hf : rows.all (fun row => row.2.noInf) = true then
        if hc : ScopedScheme.boundsScopedBool caller β = true then
          pure ⟨hm, β, by rw [hr, he.down], hs.down, h, hn,
            fun row hr => Count.noInf_of_isNoInf (List.all_eq_true.mp hf row hr),
            ScopedScheme.boundsScopedBool_sound hc, ⟨path, hm, some β⟩ :: children⟩
        else throw "bounds: recursive RHS counts are outside caller scope"
      else throw "bounds: recursive RHS interpretation contains an infinite Nat replacement"

private def chooseParam (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (ann : Option Ty) (hm : Ty) : Except String
      (Σ param, PLift (InterpretedAnnotation.ParamOK ids rows Δ ann param)) := do
  match ann with
  | none =>
      let ⟨param, _⟩ ← Typed.chooseParam Δ none hm
      pure ⟨param, ⟨True.intro⟩⟩
  | some τ =>
      let d ← InterpretedAnnotation.decode ids rows caller τ
      let _ ← equal (Synth.BoundsTy.toTy d.bounds) hm "bounds: recursive parameter annotation disagrees with found type"
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
      else throw "bounds: polymorphic HM internal binding unsupported in recursive RHS slice"

def walk (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (env : List Binding) (path : CorePath) (e : Expr) (schemes : BinderSchemeMap) :
    Except String (Result ids rows caller Δ env e) := do
  match e with
  | .found hm (.primLit p) =>
      finish ids rows caller Δ env (.found hm (.primLit p)) path hm.eraseBounds (boundInfoOfPrimLit p)
        (by simp only [Expr.stripFound]; exact .literal) (by simp [Expr.stripFound, NoGroups]) []
  | .found hm (.primBinOp op) =>
      finish ids rows caller Δ env (.found hm (.primBinOp op)) path hm.eraseBounds (Typed.primOpBounds op)
        (by simp only [Expr.stripFound]; exact .primBinOp) (by simp [Expr.stripFound, NoGroups]) []
  | .found hm (.ctor name) =>
      if hn : name = nilCtorName then
        match hm.eraseBounds with
        | .customTy n [a] =>
            if n = listTyName then do
              let elem ← Typed.shapeTop a
              finish ids rows caller Δ env (.found hm (.ctor name)) path hm.eraseBounds (.list (.lit 0) (.lit 0) elem)
                (by subst name; simp only [Expr.stripFound]; exact .nil) (by simp [Expr.stripFound, NoGroups]) []
            else throw "bounds: recursive RHS Nil has non-List found type"
        | _ => throw "bounds: recursive RHS Nil has non-List found type"
      else throw "bounds: standalone constructor unsupported in recursive RHS slice"
  | .found hm (.var i) =>
      match env[i]? with
      | some (.recursive c) =>
          unless c.counts.quantified.isEmpty do
            throw "bounds: standalone count-polymorphic recursive variable needs an argument origin"
      | _ => pure ()
      let used ← RecursiveVariable.check ids rows Δ env i hm [] caller
      finish ids rows caller Δ env (.found hm (.var i)) path hm.eraseBounds used.bounds
        (by simpa only [Expr.stripFound] using used.derivation) (by simp [Expr.stripFound, NoGroups]) []
  | .found hm (.lambda ann body) =>
      match hm.eraseBounds with
      | .arrow paramTy _ =>
          let ⟨param, hp⟩ ← chooseParam ids rows caller Δ ann paramTy
          let result ← walk ids rows caller Δ (.mono param :: env) (path ++ [.lambdaBody]) body schemes
          finish ids rows caller Δ env (.found hm (.lambda ann body)) path hm.eraseBounds (.arrow param result.bounds)
            (by simpa only [Expr.stripFound] using Derives.lambda hp.down result.derivation)
            (by simpa only [Expr.stripFound, NoGroups] using result.noGroups) result.nodes
      | _ => throw "bounds: recursive RHS lambda has non-arrow found type"
  | .found hm (.letIn ann rhs body) =>
      let actual ← walk ids rows caller Δ env (path ++ [.letRhs]) rhs schemes
      if ann.isNone then
        let fact ← BinderBridge.atSite schemes (.letIn path) actual.bounds
          (env.map bindingHM ++ rhs.stripFound.tyFreeVars.map Ty.fvar)
        unless fact.scheme.paramCount = 0 do
          throw "bounds: generalized HM internal let unsupported in recursive RHS slice"
      let hp ← checkBinding ids rows caller Δ ann actual.bounds
      let result ← walk ids rows caller Δ (.mono actual.bounds :: env) (path ++ [.letBody]) body schemes
      finish ids rows caller Δ env (.found hm (.letIn ann rhs body)) path hm.eraseBounds result.bounds
        (by simpa only [Expr.stripFound] using Derives.letMono hp.down actual.derivation result.derivation)
        (by simpa only [Expr.stripFound, NoGroups] using And.intro actual.noGroups result.noGroups)
        (actual.nodes ++ result.nodes)
  | .found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail) =>
      if hn : name = consCtorName then
        let h ← walk ids rows caller Δ env (path ++ [.appFun, .appArg]) head schemes
        let t ← walk ids rows caller Δ env (path ++ [.appArg]) tail schemes
        match ht : t.bounds with
        | .list lo hi elem =>
            let _ ← equal ctorTy.eraseBounds (.arrow h.hm (.arrow t.hm t.hm)) "bounds: inconsistent recursive RHS Cons found type"
            let _ ← equal partialTy.eraseBounds (.arrow t.hm t.hm) "bounds: inconsistent recursive RHS partial Cons found type"
            let hs ← Typed.subtype Δ h.bounds elem
            finish ids rows caller Δ env
              (.found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail)) path hm.eraseBounds
              (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
              (by subst name; simpa only [Expr.stripFound] using
                Derives.cons h.derivation (by simpa only [ht] using t.derivation) hs.down)
              (by simpa only [Expr.stripFound, NoGroups] using And.intro (And.intro True.intro h.noGroups) t.noGroups)
              (⟨path ++ [.appFun], partialTy.eraseBounds, none⟩ ::
                ⟨path ++ [.appFun, .appFun], ctorTy.eraseBounds, none⟩ :: h.nodes ++ t.nodes)
        | _ => throw "bounds: recursive RHS Cons tail has non-List bounds"
      else throw "bounds: unsupported constructor application in recursive RHS slice"
  | .found hm (.app (.found functionHM (.var i)) arg) =>
      let actual ← walk ids rows caller Δ env (path ++ [.appArg]) arg schemes
      let used ← match env[i]? with
        | some (.recursive _) =>
            RecursiveVariable.inferApplication ids rows Δ env i arg.stripFound actual.bounds
              actual.derivation functionHM hm caller
        | _ =>
            RecursiveVariable.application ids rows Δ env i arg.stripFound actual.bounds
              actual.derivation functionHM hm [] caller
      finish ids rows caller Δ env (.found hm (.app (.found functionHM (.var i)) arg)) path hm.eraseBounds used.bounds
        (by simpa only [Expr.stripFound] using used.derivation)
        (by simpa only [Expr.stripFound, NoGroups] using And.intro True.intro actual.noGroups)
        (⟨path ++ [.appFun], functionHM.eraseBounds, some (.arrow used.domain used.bounds)⟩ :: actual.nodes)
  | .found hm (.app fn arg) =>
      let f ← walk ids rows caller Δ env (path ++ [.appFun]) fn schemes
      let actual ← walk ids rows caller Δ env (path ++ [.appArg]) arg schemes
      match hf : f.bounds with
      | .arrow domain result =>
          let hs ← Typed.subtype Δ actual.bounds domain
          finish ids rows caller Δ env (.found hm (.app fn arg)) path hm.eraseBounds result
            (by simpa only [Expr.stripFound] using
              Derives.app (by simpa only [hf] using f.derivation) actual.derivation hs.down)
            (by simpa only [Expr.stripFound, NoGroups] using And.intro f.noGroups actual.noGroups)
            (f.nodes ++ actual.nodes)
      | _ => throw "bounds: recursive RHS application has non-function bounds"
  | .found _ (.letRec _ _ _) => throw "bounds: nested recursive group needs captured-template transport"
  | .found _ _ => throw "bounds: expression form unsupported in recursive RHS slice"
  | _ => throw "bounds: every recursive RHS logical node must have one found wrapper"
termination_by sizeOf e

#print axioms walk

end FHM.Bounds.RecursiveWalk
