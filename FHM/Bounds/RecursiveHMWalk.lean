import FHM.Bounds.RecursiveHMAnnotation
import FHM.Bounds.CountProposal

/-! Initial executable interpreted RHS traversal. Reads original found payloads
and carried annotations, builds real recursive HM derivations, and records
interpreted per-node bounds without rewriting the expression. Generalized local
lets, match merging, deferred callback spines and nested groups remain explicit
unsupported cases until their existing checker mechanisms are migrated. -/

namespace FHM.Bounds.RecursiveHMWalk

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme

structure Result (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (e : Expr) where
  originalHM : Ty
  root : Typed.rootHM? e = some originalHM
  bounds : BoundsTy
  shape : Synth.BoundsTy.toTy bounds = HMFoundView.ty types originalHM
  derivation : Derives types ids rows Δ env e.stripFound bounds
  countScope : BoundsScoped caller bounds
  finite : Finite rows
  nodes : List Typed.NodeResult

private def finish (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (e : Expr)
    (path : CorePath) (β : BoundsTy) (h : Derives types ids rows Δ env e.stripFound β)
    (children : List Typed.NodeResult) : Except String (Result types ids rows caller Δ env e) := do
  match hr : Typed.rootHM? e with
  | none => throw "bounds: interpreted RHS is missing its original found payload"
  | some original =>
      let viewed := HMFoundView.ty types original
      let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy β) viewed with
        | some h => pure h
        | none => throw "bounds: actual RHS disagrees with HM-interpreted found payload"
      if hs : boundsScopedBool caller β = true then
        if hf : rows.all (fun row => row.2.noInf) = true then
          pure ⟨original, hr, β, shape.down, h, boundsScopedBool_sound hs,
            fun row hm => Count.noInf_of_isNoInf (List.all_eq_true.mp hf row hm),
            ⟨path, viewed, some β⟩ :: children⟩
        else throw "bounds: interpreted RHS contains an infinite Nat replacement"
      else throw "bounds: actual interpreted RHS counts are outside caller scope"

def walk (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (path : CorePath)
    (e : Expr) (schemes : BinderSchemeMap) (expected : Option BoundsTy := none) :
    Except String (Result types ids rows caller Δ env e) := do
  match e with
  | .found hm (.primLit p) =>
      finish types ids rows caller Δ env (.found hm (.primLit p)) path (boundInfoOfPrimLit p)
        (by simpa only [Expr.stripFound] using (Derives.literal (types := types) (env := env) (p := p))) []
  | .found hm (.primBinOp op) =>
      finish types ids rows caller Δ env (.found hm (.primBinOp op)) path (Typed.primOpBounds op)
        (by simpa only [Expr.stripFound] using (Derives.primBinOp (types := types) (env := env) (op := op))) []
  | .found hm (.ctor name) =>
      if hn : name = nilCtorName then
        match HMFoundView.ty types hm with
        | .customTy listName [a] =>
            unless listName = listTyName do throw "bounds: interpreted Nil has a non-List HM type"
            let elem ← match expected with
              | some (.list _ _ elem) => pure elem
              | _ => Typed.shapeTop a
            finish types ids rows caller Δ env (.found hm (.ctor name)) path (.list (.lit 0) (.lit 0) elem)
              (by subst name; simpa only [Expr.stripFound] using (Derives.nil (types := types) (env := env) (elem := elem))) []
        | _ => throw "bounds: interpreted Nil has a non-List HM type"
      else if hb : BoolBranches.IsCtor name then
        finish types ids rows caller Δ env (.found hm (.ctor name)) path (.custom boolTyName [])
          (by simpa only [Expr.stripFound] using (Derives.boolCtor (types := types) (env := env) hb)) []
      else throw "bounds: standalone constructor unsupported in interpreted RHS traversal"
  | .found hm (.var i) =>
      match hv : env[i]? with
      | none => throw "bounds: interpreted variable outside assumption environment"
      | some (.mono β) =>
          finish types ids rows caller Δ env (.found hm (.var i)) path β
            (by simpa only [Expr.stripFound] using (Derives.varMono (types := types) (ids := ids) (rows := rows) (Δ := Δ) hv)) []
      | some (.recursive c) =>
          let used ← RecursiveHMContract.check c.fixed Δ c.hm [] caller
          finish types ids rows caller Δ env (.found hm (.var i)) path used.bounds
            (by simpa only [Expr.stripFound] using (Derives.varRecursive (types := types) (ids := ids) (rows := rows) hv used)) []
  | .found hm (.lambda ann body) =>
      match hm.eraseBounds with
      | .arrow paramHM _ =>
          let paramHint := match expected with | some (.arrow a _) => some a | _ => none
          let bodyHint := match expected with | some (.arrow _ b) => some b | _ => none
          let param ← RecursiveHMAnnotation.chooseParam types ids rows caller Δ ann paramHM paramHint
          let result ← walk types ids rows caller Δ (.mono param.bounds :: env)
            (path ++ [.lambdaBody]) body schemes bodyHint
          finish types ids rows caller Δ env (.found hm (.lambda ann body)) path (.arrow param.bounds result.bounds)
            (by simpa only [Expr.stripFound] using (Derives.lambda param.obligation result.derivation)) result.nodes
      | _ => throw "bounds: interpreted lambda has a non-arrow original found type"
  | .found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail) =>
      if hn : name = consCtorName then
        let headHint := match expected with | some (.list _ _ elem) => some elem | _ => none
        let h ← walk types ids rows caller Δ env (path ++ [.appFun, .appArg]) head schemes headHint
        let t ← walk types ids rows caller Δ env (path ++ [.appArg]) tail schemes
          (some (.list (.lit 0) .inf h.bounds))
        match ht : t.bounds with
        | .list lo hi elem =>
            let _ ← match BinderBridge.equalTy (HMFoundView.ty types ctorTy)
                (.arrow (HMFoundView.ty types h.originalHM)
                  (.arrow (HMFoundView.ty types t.originalHM) (HMFoundView.ty types t.originalHM))) with
              | some h => pure h | none => throw "bounds: inconsistent interpreted Cons found type"
            let _ ← match BinderBridge.equalTy (HMFoundView.ty types partialTy)
                (.arrow (HMFoundView.ty types t.originalHM) (HMFoundView.ty types t.originalHM)) with
              | some h => pure h | none => throw "bounds: inconsistent interpreted partial Cons found type"
            let sub ← Typed.subtype Δ h.bounds elem
            finish types ids rows caller Δ env
              (.found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail))
              path (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
              (by subst name; simpa only [Expr.stripFound] using
                (Derives.cons h.derivation (by simpa only [ht] using t.derivation) sub.down))
              (⟨path ++ [.appFun], HMFoundView.ty types partialTy, none⟩ ::
                ⟨path ++ [.appFun, .appFun], HMFoundView.ty types ctorTy, none⟩ :: h.nodes ++ t.nodes)
        | _ => throw "bounds: interpreted Cons tail is not a List"
      else throw "bounds: constructor application unsupported in interpreted RHS traversal"
  | .found hm (.app (.found functionHM (.var i)) arg) =>
      -- Only count arguments are proposed: HM arguments belong to the fixed
      -- common group vector. Proposals inspect the CLOSED template so counts
      -- in inserted HM arguments cannot be mistaken for callee coordinates.
      match hv : env[i]? with
      | some (.recursive c) =>
          match c.template.counts.body with
          | .arrow _ _ =>
              let actual ← walk types ids rows caller Δ env (path ++ [.appArg]) arg schemes
              let counts ← CountProposal.proposeArguments c.template.counts.quantified
                c.template.counts.body [actual.bounds]
              let used ← RecursiveHMContract.check c.fixed Δ c.hm counts caller
              let fn ← finish types ids rows caller Δ env (.found functionHM (.var i))
                (path ++ [.appFun]) used.bounds
                (by simpa only [Expr.stripFound] using (Derives.varRecursive hv used)) []
              match hf : fn.bounds with
              | .arrow domain result =>
                  let sub ← Typed.subtype Δ actual.bounds domain
                  finish types ids rows caller Δ env (.found hm (.app (.found functionHM (.var i)) arg)) path result
                    (by simpa only [Expr.stripFound] using
                      (Derives.app (by simpa only [hf, Expr.stripFound] using fn.derivation) actual.derivation sub.down))
                    (fn.nodes ++ actual.nodes)
              | _ => throw "bounds: interpreted recursive assumption is not an arrow"
          | _ => throw "bounds: interpreted recursive contract is not an arrow"
      | _ =>
          let fn ← walk types ids rows caller Δ env (path ++ [.appFun]) (.found functionHM (.var i)) schemes
          match hf : fn.bounds with
          | .arrow domain result =>
              let actual ← walk types ids rows caller Δ env (path ++ [.appArg]) arg schemes (some domain)
              let sub ← Typed.subtype Δ actual.bounds domain
              finish types ids rows caller Δ env (.found hm (.app (.found functionHM (.var i)) arg)) path result
                (by simpa only [Expr.stripFound] using
                  (Derives.app (by simpa only [hf, Expr.stripFound] using fn.derivation) actual.derivation sub.down))
                (fn.nodes ++ actual.nodes)
          | _ => throw "bounds: interpreted application callee is not an arrow"
  | .found hm (.app function arg) =>
      let fn ← walk types ids rows caller Δ env (path ++ [.appFun]) function schemes
      match hf : fn.bounds with
      | .arrow domain result =>
          let actual ← walk types ids rows caller Δ env (path ++ [.appArg]) arg schemes (some domain)
          let sub ← Typed.subtype Δ actual.bounds domain
          finish types ids rows caller Δ env (.found hm (.app function arg)) path result
            (by simpa only [Expr.stripFound] using
              (Derives.app (by simpa only [hf] using fn.derivation) actual.derivation sub.down))
            (fn.nodes ++ actual.nodes)
      | _ => throw "bounds: interpreted application callee is not an arrow"
  | .found _ (.letRec _ _ _) => throw "bounds: nested groups unsupported in interpreted universal RHS traversal"
  | .found hm (.letIn ann rhs body) =>
      let hint ← RecursiveHMAnnotation.bindingHint types ids rows caller ann
      let actual ← walk types ids rows caller Δ env (path ++ [.letRhs]) rhs schemes hint
      -- A mono proof cannot silently stand in for an inferred generalized let.
      -- Keep the original machine HM interface, not the interpreted payload.
      let _ ← match BinderBridge.candidates schemes (.letIn path) with
        | [σ] => do
            unless σ.paramCount = 0 do
              throw "bounds: generalized local HM let unsupported in interpreted recursive RHS slice"
            let _ ← BinderBridge.instantiate σ actual.originalHM
            pure ()
        | [] => throw "bounds: missing inferred local binder scheme in interpreted RHS"
        | _ => throw "bounds: duplicate inferred local binder scheme in interpreted RHS"
      let obligation ← RecursiveHMAnnotation.checkBinding types ids rows caller Δ ann actual.bounds
      let result ← walk types ids rows caller Δ (.mono actual.bounds :: env)
        (path ++ [.letBody]) body schemes expected
      finish types ids rows caller Δ env (.found hm (.letIn ann rhs body)) path result.bounds
        (by simpa only [Expr.stripFound] using
          (Derives.letMono obligation.down actual.derivation result.derivation)) (actual.nodes ++ result.nodes)
  | .found _ (.match_ _ _) => throw "bounds: matches not yet migrated to interpreted RHS traversal"
  | _ => throw "bounds: unsupported or missing found node in interpreted RHS traversal"
termination_by sizeOf e

#print axioms walk

end FHM.Bounds.RecursiveHMWalk
