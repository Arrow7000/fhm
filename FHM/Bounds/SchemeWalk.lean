import FHM.Bounds.StructuralApplication
import FHM.Bounds.SchemeTransport

/-! # Proof-carrying traversal with inferred HM schemes

All logical child types come from `.found`. Generalized lets consume the unique
machine binder fact at their exact Core site and a universal mixed-environment
RHS typing proof. Polymorphic application proposals use structural argument
bounds, validated by exact HM specialization and semantic domain inclusion.
Unsupported forms never fall back to the legacy checker. This is not yet the
CLI/LSP launch route, a runtime interpretation or full artifact-coherence proof.
-/

namespace FHM.Bounds.SchemeWalk

open SchemeTyping

structure Result (Δ : List Constraint) (env : List Binding) (e : Expr) (scope : List Nat) where
  hm : Ty
  bounds : BoundsTy
  root : Typed.rootHM? e = some hm
  shape : Synth.BoundsTy.toTy bounds = hm
  derivation : Derives Δ env e.stripFound bounds
  countScope : ScopedScheme.BoundsScoped scope bounds
  nodes : List Typed.NodeResult

private def equal (a b : Ty) (message : String) : Except String (PLift (a = b)) :=
  match BinderBridge.equalTy a b with
  | none => .error message
  | some evidence => .ok evidence

private def finish (Δ : List Constraint) (env : List Binding) (e : Expr) (scope : List Nat)
    (path : CorePath) (hm : Ty) (β : BoundsTy) (h : Derives Δ env e.stripFound β)
    (children : List Typed.NodeResult) : Except String (Result Δ env e scope) := do
  match hr : Typed.rootHM? e with
  | none => throw "bounds: missing root found payload"
  | some actual =>
      let he ← equal actual hm "bounds: inconsistent root found payload"
      let hs ← equal (Synth.BoundsTy.toTy β) hm "bounds: synthesized shape disagrees with found payload"
      if hc : ScopedScheme.boundsScopedBool scope β = true then
        pure ⟨hm, β, by rw [hr, he.down], hs.down, h,
          ScopedScheme.boundsScopedBool_sound hc, ⟨path, hm, some β⟩ :: children⟩
      else throw "bounds: synthesized counts are outside caller scope"

/-- The unique exact-site binder scheme is mandatory, even for a monomorphic
    inferred let. Freshness includes captured schemes and source annotations. -/
def walk (Δ : List Constraint) (env : List Binding) (path : CorePath) (e : Expr)
    (schemes : BinderSchemeMap) (scope : List Nat := []) :
    Except String (Result Δ env e scope) := do
  match e with
  | .found hm (.primLit p) =>
      finish Δ env (.found hm (.primLit p)) scope path hm.eraseBounds (boundInfoOfPrimLit p)
        (by simpa only [Expr.stripFound] using (Derives.literal (Δ := Δ) (env := env) (p := p))) []
  | .found hm (.primBinOp op) =>
      finish Δ env (.found hm (.primBinOp op)) scope path hm.eraseBounds (Typed.primOpBounds op)
        (by simpa only [Expr.stripFound] using (Derives.primBinOp (Δ := Δ) (env := env) (op := op))) []
  | .found hm (.ctor name) =>
      if hn : name = nilCtorName then
        match hm.eraseBounds with
        | .customTy n [a] =>
            if n = listTyName then do
              let elem ← Typed.shapeTop a
              finish Δ env (.found hm (.ctor name)) scope path hm.eraseBounds (.list (.lit 0) (.lit 0) elem)
                (by subst name; simpa only [Expr.stripFound] using (Derives.nil (Δ := Δ) (env := env) (elem := elem))) []
            else throw "bounds: Nil has non-List found type"
        | _ => throw "bounds: Nil has non-List found type"
      else throw "bounds: standalone constructor unsupported in scheme-aware slice"
  | .found hm (.var i) =>
      match env[i]? with
      | some (.poly _) => throw "bounds: standalone polymorphic use needs justified bounds arguments"
      | _ =>
          let result ← SchemeVariable.check Δ env i hm [] scope
          finish Δ env (.found hm (.var i)) scope path hm.eraseBounds result.bounds
            (by simpa only [Expr.stripFound] using result.derivation) []
  | .found hm (.lambda ann body) =>
      match hm.eraseBounds with
      | .arrow paramTy _ =>
          let ⟨param, hp⟩ ← Typed.chooseParam Δ ann paramTy
          let _ ← equal (Synth.BoundsTy.toTy param) paramTy "bounds: parameter annotation disagrees with found type"
          let result ← walk Δ (.mono param :: env) (path ++ [.lambdaBody]) body schemes scope
          finish Δ env (.found hm (.lambda ann body)) scope path hm.eraseBounds (.arrow param result.bounds)
            (by simpa only [Expr.stripFound] using (Derives.lambda hp.down result.derivation)) result.nodes
      | _ => throw "bounds: lambda has non-arrow found type"
  | .found hm (.letIn ann rhs body) =>
      let actual ← walk Δ env (path ++ [.letRhs]) rhs schemes scope
      match ann with
      | none =>
          let checked ← BinderBridge.atSite schemes (.letIn path) actual.bounds
            (env.map SchemeTransport.interface ++ rhs.stripFound.tyFreeVars.map Ty.fvar)
          if checked.scheme.paramCount = 0 then
            let result ← walk Δ (.mono actual.bounds :: env) (path ++ [.letBody]) body schemes scope
            finish Δ env (.found hm (.letIn none rhs body)) scope path hm.eraseBounds result.bounds
              (by simpa only [Expr.stripFound] using (Derives.letMono (ann := none) True.intro actual.derivation result.derivation))
              (actual.nodes ++ result.nodes)
          else
            let result ← walk Δ (.poly (SchemeTyping.fromBinder checked.abstraction) :: env)
              (path ++ [.letBody]) body schemes scope
            finish Δ env (.found hm (.letIn none rhs body)) scope path hm.eraseBounds result.bounds
              (by simpa only [Expr.stripFound] using
                (SchemeTransport.let_fromBinder checked.abstraction actual.derivation result.derivation))
              (actual.nodes ++ result.nodes)
      | some σ =>
          let hp ← Typed.checkBinding Δ (some σ) actual.bounds
          let result ← walk Δ (.mono actual.bounds :: env) (path ++ [.letBody]) body schemes scope
          finish Δ env (.found hm (.letIn (some σ) rhs body)) scope path hm.eraseBounds result.bounds
            (by simpa only [Expr.stripFound] using (Derives.letMono hp.down actual.derivation result.derivation))
            (actual.nodes ++ result.nodes)
  | .found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail) =>
      if hn : name = consCtorName then
        let h ← walk Δ env (path ++ [.appFun, .appArg]) head schemes scope
        let t ← walk Δ env (path ++ [.appArg]) tail schemes scope
        match ht : t.bounds with
        | .list lo hi elem =>
            let _ ← equal ctorTy.eraseBounds (.arrow h.hm (.arrow t.hm t.hm))
              "bounds: inconsistent Cons constructor found type"
            let _ ← equal partialTy.eraseBounds (.arrow t.hm t.hm)
              "bounds: inconsistent Cons partial application found type"
            let he ← Typed.subtype Δ h.bounds elem
            finish Δ env (.found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail)) scope path hm.eraseBounds
              (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
              (by subst name; simpa only [Expr.stripFound] using
                (Derives.cons h.derivation (by simpa only [ht] using t.derivation) he.down))
              (⟨path ++ [.appFun], partialTy.eraseBounds, none⟩ ::
                ⟨path ++ [.appFun, .appFun], ctorTy.eraseBounds, none⟩ :: h.nodes ++ t.nodes)
        | _ => throw "bounds: Cons tail has non-List bounds"
      else throw "bounds: unsupported constructor application in scheme-aware slice"
  | .found hm (.app (.found functionHM (.var i)) arg) =>
      match env[i]? with
      | some (.poly _) =>
          let actual ← walk Δ env (path ++ [.appArg]) arg schemes scope
          let result ← StructuralApplication.check Δ env i arg.stripFound actual.bounds actual.derivation
            functionHM hm scope
          finish Δ env (.found hm (.app (.found functionHM (.var i)) arg)) scope path hm.eraseBounds result.bounds
            (by simpa only [Expr.stripFound] using result.derivation)
            (⟨path ++ [.appFun], functionHM.eraseBounds, some (.arrow result.domain result.bounds)⟩ :: actual.nodes)
      | _ =>
          let fn ← walk Δ env (path ++ [.appFun]) (.found functionHM (.var i)) schemes scope
          let actual ← walk Δ env (path ++ [.appArg]) arg schemes scope
          match hf : fn.bounds with
          | .arrow domain result =>
              let hs ← Typed.subtype Δ actual.bounds domain
              finish Δ env (.found hm (.app (.found functionHM (.var i)) arg)) scope path hm.eraseBounds result
                (by simpa only [Expr.stripFound] using
                  (Derives.app (by simpa only [hf, Expr.stripFound] using fn.derivation) actual.derivation hs.down))
                (fn.nodes ++ actual.nodes)
          | _ => throw "bounds: application has non-function bounds"
  | .found hm (.app fn arg) =>
      let f ← walk Δ env (path ++ [.appFun]) fn schemes scope
      let actual ← walk Δ env (path ++ [.appArg]) arg schemes scope
      match hf : f.bounds with
      | .arrow domain result =>
          let hs ← Typed.subtype Δ actual.bounds domain
          finish Δ env (.found hm (.app fn arg)) scope path hm.eraseBounds result
            (by simpa only [Expr.stripFound] using
              (Derives.app (by simpa only [hf] using f.derivation) actual.derivation hs.down))
            (f.nodes ++ actual.nodes)
      | _ => throw "bounds: application has non-function bounds"
  | .found _ _ => throw "bounds: expression form unsupported in scheme-aware slice"
  | _ => throw "bounds: every logical node must have one found wrapper"
termination_by sizeOf e

theorem Result.sound {Δ env e scope} (r : Result Δ env e scope) :
    Derives Δ env e.stripFound r.bounds := r.derivation

#print axioms walk
#print axioms Result.sound

end FHM.Bounds.SchemeWalk
