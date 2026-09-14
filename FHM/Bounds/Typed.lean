import FHM.Bounds.Semantic
import FHM.Bounds.Synth
import FHM.CorePath
import FHM.Bounds.BinderBridge

/-! # Proof-carrying typed bounds slice

Consumes child `.found` payloads, not reconstructed HM types. This deliberately
small fragment excludes polymorphic binding uses, recursion and
matches. Constructor scaffolding is reported explicitly without pretending a
saturated-Cons rule synthesizes bounds for the partial constructor functions.
The derivations below establish static synthesis/annotation soundness for this
fragment; they are not yet a runtime interpretation or artifact-coherence proof.
-/

namespace FHM.Bounds.Typed

open FHM.Bounds.Synth

private def spine := FHM.Bounds.Synth.BoundsTy.toTy

private def require (x : Option α) (msg : String) : Except String α :=
  match x with
  | some value => .ok value
  | none => .error msg

/-- Decidable evidence for the slice's type shapes; no global equality instance
    or comparison of proof-carrying inference outputs is introduced. -/
private def equalTy := BinderBridge.equalTy

/-- Positive arithmetic verdicts produce semantic evidence. There are no HM
    stub shortcuts, demand-fragment restrictions or fallback to legacy checks. -/
def subtype (Δ : List Constraint) (a b : BoundsTy) :
    Except String (PLift (SemanticSub Δ a b)) := do
  match a, b with
  | .prim p, .prim q =>
      if h : p = q then pure ⟨by subst q; exact .prim⟩ else throw "bounds: primitive mismatch"
  | .fvar i, .fvar j =>
      if h : i = j then pure ⟨by subst j; exact .fvar⟩ else throw "bounds: type-variable mismatch"
  | .bvar i, .bvar j =>
      if h : i = j then pure ⟨by subst j; exact .bvar⟩ else throw "bounds: type-variable mismatch"
  | .arrow a b, .arrow a' b' =>
      return ⟨.arrow (← subtype Δ a' a).down (← subtype Δ b b').down⟩
  | .list lo hi e, .list lo' hi' e' =>
      let he ← subtype Δ e e'
      let query := Interval.subGoals Δ ⟨lo, hi⟩ ⟨lo', hi'⟩
      if h : checkValid query = .valid then
        pure ⟨.list (checkValid_sound query h) he.down⟩
      else throw "bounds: interval inclusion not established (invalid or unknown)"
  | .custom n [], .custom m [] =>
      if h : n = m then pure ⟨by subst m; exact .custom .nil⟩
      else throw "bounds: data type mismatch"
  | _, _ => throw "bounds: unsupported subtype shape in typed slice"
termination_by sizeOf a + sizeOf b

/-- Shape-only top information, used for Nil element shapes and bare List
    demands, never as evidence of an exact origin or a fresh parameter bound. -/
def shapeTop (τ : Ty) : Except String BoundsTy := do
  match τ with
  | .prim p => pure (.prim p)
  | .fvar i => pure (.fvar i)
  | .bvar i => pure (.bvar i)
  | .arrow a b => return .arrow (← shapeTop a) (← shapeTop b)
  | .customTy n [a] =>
      if n = listTyName then return .list (.lit 0) .inf (← shapeTop a)
      else throw "bounds: unsupported data type in typed slice"
  | _ => throw "bounds: unsupported type shape in typed slice"
termination_by sizeOf τ

/-- Decode annotations directly from their carried Core slots. Until count
    telescopes survive lowering, symbolic counts are explicitly rejected: an
    unresolved surface name must not be accepted as lowering's rigid-0 stub. -/
def annotation (τ : Ty) : Except String BoundsTy := do
  match τ with
  | .bl (.solid lo) (.solid hi) a =>
      unless lo.isGround && hi.isGround do
        throw "bounds: symbolic annotation needs preserved count scope"
      return .list lo hi (← annotation a)
  | .bl _ _ _ => throw "bounds: count holes unsupported in typed slice"
  | .arrow a b => return .arrow (← annotation a) (← annotation b)
  | .customTy n [a] =>
      if n = listTyName then return .list (.lit 0) .inf (← annotation a)
      else throw "bounds: unsupported annotation data type"
  | .prim p => pure (.prim p)
  | .fvar i => pure (.fvar i)
  | .bvar i => pure (.bvar i)
  | _ => throw "bounds: unsupported annotation shape"
termination_by sizeOf τ

def AnnotationOK (Δ : List Constraint) (τ : Ty) (β : BoundsTy) : Prop :=
  ∃ demand, annotation τ = .ok demand ∧ SemanticSub Δ β demand

def ParamOK (Δ : List Constraint) (ann : Option Ty) (β : BoundsTy) : Prop :=
  match ann with
  | none => True
  | some τ => AnnotationOK Δ τ β

def BindingOK (Δ : List Constraint) (ann : Option PolyTy) (β : BoundsTy) : Prop :=
  match ann with
  | none => True
  | some σ => σ.paramCount = 0 ∧ AnnotationOK Δ σ.body β

def primOpBounds : PrimBinOp → BoundsTy
  | .intAdd | .intSub => .arrow (.prim .int) (.arrow (.prim .int) (.prim .int))
  | .intLt => .arrow (.prim .int) (.arrow (.prim .int) (.custom boolTyName []))
  | .charLt => .arrow (.prim .char) (.arrow (.prim .char) (.custom boolTyName []))

/-- Declarative static bounds derivations for precisely the initial fragment.
    Unlike legacy `HasBounds`, annotation obligations are explicit. -/
inductive Derives (Δ : List Constraint) : List BoundsTy → Expr → BoundsTy → Prop where
  | literal {env p} : Derives Δ env (.primLit p) (boundInfoOfPrimLit p)
  | primBinOp {env op} : Derives Δ env (.primBinOp op) (primOpBounds op)
  | nil {env elem} : Derives Δ env (.ctor nilCtorName) (.list (.lit 0) (.lit 0) elem)
  | cons {env h t head elem lo hi} :
      Derives Δ env h head → Derives Δ env t (.list lo hi elem) →
      SemanticSub Δ head elem →
      Derives Δ env (.app (.app (.ctor consCtorName) h) t)
        (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
  | var {env i β} : env[i]? = some β → Derives Δ env (.var i) β
  | app {env f arg domain actual result} :
      Derives Δ env f (.arrow domain result) → Derives Δ env arg actual →
      SemanticSub Δ actual domain → Derives Δ env (.app f arg) result
  | lambda {env ann body param result} :
      ParamOK Δ ann param → Derives Δ (param :: env) body result →
      Derives Δ env (.lambda ann body) (.arrow param result)
  | letIn {env ann rhs body actual result} :
      BindingOK Δ ann actual → Derives Δ env rhs actual →
      Derives Δ (actual :: env) body result →
      Derives Δ env (.letIn ann rhs body) result

structure NodeResult where
  path : CorePath
  hm : Ty
  /-- `none` only for the explicitly checked saturated-Cons scaffold. -/
  bounds : Option BoundsTy

def rootHM? : Expr → Option Ty
  | .found hm _ => some hm.eraseBounds
  | _ => none

structure Result (Δ : List Constraint) (env : List BoundsTy) (e : Expr) where
  hm : Ty
  bounds : BoundsTy
  root : rootHM? e = some hm
  shape : spine bounds = hm
  derivation : Derives Δ env e.stripFound bounds
  nodes : List NodeResult

private def finish (Δ : List Constraint) (env : List BoundsTy) (e : Expr)
    (path : CorePath) (hm : Ty) (β : BoundsTy)
    (proof : Derives Δ env e.stripFound β) (children : List NodeResult) :
    Except String (Result Δ env e) := do
  match hr : rootHM? e with
  | none => throw "bounds: missing root found payload"
  | some actual =>
      let he ← require (equalTy actual hm) "bounds: inconsistent root found payload"
      let hs ← require (equalTy (spine β) hm)
        "bounds: synthesized shape disagrees with found payload"
      pure ⟨hm, β, by rw [hr, he.down], hs.down, proof, ⟨path, hm, some β⟩ :: children⟩

private def checkAnnotation (Δ : List Constraint) (τ : Ty) (β : BoundsTy) :
    Except String (PLift (AnnotationOK Δ τ β)) := do
  match h : annotation τ with
  | .error msg => throw msg
  | .ok demand => return ⟨⟨demand, h, (← subtype Δ β demand).down⟩⟩

/-- Initial open parameters support scalar/type-variable shapes only. Fresh
    List origins and their scope/escape contract are a subsequent checkpoint. -/
private def scalarParam (τ : Ty) : Except String BoundsTy :=
  match τ with
  | .prim p => .ok (.prim p)
  | .fvar i => .ok (.fvar i)
  | .bvar i => .ok (.bvar i)
  | _ => .error "bounds: unannotated non-scalar parameter unsupported in typed slice"

def chooseParam (Δ : List Constraint) (ann : Option Ty) (hm : Ty) :
    Except String (Σ β, PLift (ParamOK Δ ann β)) :=
  match ann with
  | none => do
      let β ← scalarParam hm
      pure ⟨β, ⟨True.intro⟩⟩
  | some τ => do
      let β ← annotation τ
      let hp ← checkAnnotation Δ τ β
      pure ⟨β, hp⟩

def checkBinding (Δ : List Constraint) (ann : Option PolyTy) (β : BoundsTy) :
    Except String (PLift (BindingOK Δ ann β)) :=
  match ann with
  | none => .ok ⟨True.intro⟩
  | some σ => do
      if hq : σ.paramCount = 0 then
        let hp ← checkAnnotation Δ σ.body β
        pure ⟨⟨hq, hp.down⟩⟩
      else throw "bounds: polymorphic annotation unsupported in typed slice"

/-- Artifact-backed lets validate the inferred generalization interface before
    checking their body. Standalone hand-built slice tests can omit the map.
    This check does not provide universal bounds typing for polymorphic uses. -/
private def checkInferredBinding (schemes : Option BinderSchemeMap) (path : CorePath)
    (ann : Option PolyTy) (actual : BoundsTy) (env : List BoundsTy)
    (sourceFvars : List Nat) : Except String Bool := do
  match ann, schemes with
  | none, some facts =>
      let checked ← BinderBridge.atSite facts (.letIn path) actual
        (env.map spine ++ sourceFvars.map Ty.fvar)
      pure (checked.scheme.paramCount != 0)
  | _, _ => pure false

/-- Artifact-backed mode checks inferred let schemes. `deferredSchemes` tracks
    their unsupported polymorphic uses at the same de Bruijn depth as `env`;
    lambda parameters and newly shadowing monomorphic lets push `false`. -/
def walk (Δ : List Constraint) (env : List BoundsTy) (path : CorePath) (e : Expr)
    (schemes : Option BinderSchemeMap := none) (deferredSchemes : List Bool := []) :
    Except String (Result Δ env e) := do
  match e with
  | .found hm (.primLit p) =>
      finish Δ env (.found hm (.primLit p)) path hm.eraseBounds (boundInfoOfPrimLit p)
        (by simpa only [Expr.stripFound] using (Derives.literal (Δ := Δ) (env := env) (p := p))) []
  | .found hm (.primBinOp op) =>
      finish Δ env (.found hm (.primBinOp op)) path hm.eraseBounds (primOpBounds op)
        (by simpa only [Expr.stripFound] using (Derives.primBinOp (Δ := Δ) (env := env) (op := op))) []
  | .found hm (.ctor name) =>
      if hn : name = nilCtorName then
        match hm.eraseBounds with
        | .customTy n [a] =>
            if n = listTyName then do
              let elem ← shapeTop a
              finish Δ env (.found hm (.ctor name)) path hm.eraseBounds (.list (.lit 0) (.lit 0) elem)
                (by subst name; simpa only [Expr.stripFound] using (Derives.nil (Δ := Δ) (env := env) (elem := elem))) []
            else throw "bounds: Nil has non-List found type"
        | _ => throw "bounds: Nil has non-List found type"
      else throw "bounds: standalone constructor unsupported in typed slice"
  | .found hm (.var i) =>
      if deferredSchemes[i]?.getD false then
        throw "bounds: polymorphic binding use needs a generalized RHS bounds derivation"
      match h : env[i]? with
      | none => throw "bounds: variable outside typed bounds environment"
      | some β =>
          finish Δ env (.found hm (.var i)) path hm.eraseBounds β
            (by simpa only [Expr.stripFound] using (Derives.var (Δ := Δ) h)) []
  | .found hm (.lambda ann body) =>
      match hm.eraseBounds with
      | .arrow paramTy _ =>
          let ⟨param, hp⟩ ← chooseParam Δ ann paramTy
          let _ ← require (equalTy (spine param) paramTy)
            "bounds: parameter annotation disagrees with found type"
          let result ← walk Δ (param :: env) (path ++ [.lambdaBody]) body schemes (false :: deferredSchemes)
          finish Δ env (.found hm (.lambda ann body)) path hm.eraseBounds (.arrow param result.bounds)
            (by simpa only [Expr.stripFound] using (Derives.lambda hp.down result.derivation)) result.nodes
      | _ => throw "bounds: lambda has non-arrow found type"
  | .found hm (.letIn ann rhs body) =>
      let actual ← walk Δ env (path ++ [.letRhs]) rhs schemes deferredSchemes
      let deferred ← checkInferredBinding schemes path ann actual.bounds env rhs.stripFound.tyFreeVars
      let hp ← checkBinding Δ ann actual.bounds
      let result ← walk Δ (actual.bounds :: env) (path ++ [.letBody]) body schemes (deferred :: deferredSchemes)
      finish Δ env (.found hm (.letIn ann rhs body)) path hm.eraseBounds result.bounds
        (by simpa only [Expr.stripFound] using (Derives.letIn hp.down actual.derivation result.derivation))
        (actual.nodes ++ result.nodes)
  | .found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail) =>
      if hn : name = consCtorName then
        let h ← walk Δ env (path ++ [.appFun, .appArg]) head schemes deferredSchemes
        let t ← walk Δ env (path ++ [.appArg]) tail schemes deferredSchemes
        match ht : t.bounds with
        | .list lo hi elem =>
            let _ ← require (equalTy ctorTy.eraseBounds (.arrow h.hm (.arrow t.hm t.hm)))
              "bounds: inconsistent Cons constructor found type"
            let _ ← require (equalTy partialTy.eraseBounds (.arrow t.hm t.hm))
              "bounds: inconsistent Cons partial application found type"
            let he ← subtype Δ h.bounds elem
            finish Δ env (.found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail))
              path hm.eraseBounds
              (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
              (by
                subst name
                simpa only [Expr.stripFound] using
                  (Derives.cons h.derivation (by simpa only [ht] using t.derivation) he.down))
              (⟨path ++ [.appFun], partialTy.eraseBounds, none⟩ ::
               ⟨path ++ [.appFun, .appFun], ctorTy.eraseBounds, none⟩ :: h.nodes ++ t.nodes)
        | _ => throw "bounds: Cons tail has non-List bounds"
      else throw "bounds: unsupported constructor application in typed slice"
  | .found hm (.app f arg) =>
      let fn ← walk Δ env (path ++ [.appFun]) f schemes deferredSchemes
      let actual ← walk Δ env (path ++ [.appArg]) arg schemes deferredSchemes
      match hf : fn.bounds with
      | .arrow domain result =>
          let hsub ← subtype Δ actual.bounds domain
          finish Δ env (.found hm (.app f arg)) path hm.eraseBounds result
            (by
              simpa only [Expr.stripFound] using
                (Derives.app (by simpa only [hf] using fn.derivation) actual.derivation hsub.down))
            (fn.nodes ++ actual.nodes)
      | _ => throw "bounds: application has non-function bounds"
  | .found _ _ => throw "bounds: expression form unsupported in typed slice"
  | _ => throw "bounds: every logical node must have one found wrapper"
termination_by sizeOf e

/-- Successful results carry the fragment's declarative derivation. -/
theorem Result.sound {Δ env e} (r : Result Δ env e) :
    Derives Δ env e.stripFound r.bounds := r.derivation

#print axioms walk
#print axioms Result.sound

end FHM.Bounds.Typed
