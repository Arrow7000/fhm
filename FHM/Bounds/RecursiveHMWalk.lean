import FHM.Bounds.RecursiveHMAnnotation
import FHM.Bounds.CountProposal
import FHM.Bounds.BranchMerge

/-! Initial executable interpreted RHS traversal. Reads original found payloads
and carried annotations, builds real recursive HM derivations, and records
interpreted per-node bounds without rewriting the expression. List/Bool matches
retain constructor coverage and variance-correct joins. Generalized local
lets, deferred callback spines and nested groups remain explicit
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

private inductive BranchContext where
  | list (lo hi : Count) (elem : BoundsTy)
  | bool

private def BranchContext.refine : BranchContext → MatchPattern → List Constraint
  | .list lo hi _, p => RecursiveTyping.branchRefine p lo hi
  | .bool, _ => []

private def BranchContext.extend : BranchContext → MatchPattern → List Binding → List Binding
  | .list lo hi elem, p, env => branchEnv p lo hi elem env
  | .bool, _, env => env

private def BranchContext.Pattern : BranchContext → MatchPattern → Prop
  | .list _ _ _, p => RecursiveTyping.ListPattern p
  | .bool, p => BoolBranches.Pattern p

private instance (ctx : BranchContext) (p : MatchPattern) : Decidable (ctx.Pattern p) := by
  cases ctx <;> unfold BranchContext.Pattern <;> infer_instance

private structure BranchResults (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (ctx : BranchContext)
    (branches : List (MatchPattern × Expr)) where
  actuals : Nat → BoundsTy
  typing : ∀ i br, branches[i]? = some br →
    Derives types ids rows (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2.stripFound (actuals i)
  patterns : ∀ br ∈ branches, ctx.Pattern br.1
  bounds : Option BoundsTy
  inclusions : ∀ i br, branches[i]? = some br →
    match bounds with
    | none => False
    | some β => SemanticSub (Δ ++ ctx.refine br.1) (actuals i) β
  nodes : List Typed.NodeResult

private def prependBranches {types ids rows caller Δ env br branches} {ctx : BranchContext}
    (head : Result types ids rows caller (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2)
    (hp : ctx.Pattern br.1) (tail : BranchResults types ids rows caller Δ env ctx branches)
    (β : BoundsTy) (hh : SemanticSub (Δ ++ ctx.refine br.1) head.bounds β)
    (ht : ∀ i arm, branches[i]? = some arm → SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) β) :
    BranchResults types ids rows caller Δ env ctx (br :: branches) where
  actuals := fun i => match i with | 0 => head.bounds | i + 1 => tail.actuals i
  typing := by
    intro i arm h
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst arm; exact head.derivation
    | succ i => exact tail.typing i arm (by simpa only [List.getElem?_cons_succ] using h)
  patterns := by
    intro arm h
    rcases List.mem_cons.mp h with rfl | h
    · exact hp
    · exact tail.patterns arm h
  bounds := some β
  inclusions := by
    intro i arm h
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst arm; exact hh
    | succ i => exact ht i arm (by simpa only [List.getElem?_cons_succ] using h)
  nodes := head.nodes ++ tail.nodes

private theorem stripBranches (branches : List (MatchPattern × Expr)) :
    Expr.stripFoundBranches branches = branches.map (fun br => (br.1, br.2.stripFound)) := by
  induction branches with
  | nil => simp [Expr.stripFoundBranches]
  | cons br rest ih => cases br; simp only [Expr.stripFoundBranches, List.map_cons, ih]

private theorem path_assuming (Δ Γ : List Constraint) :
    (⟨Δ ++ Γ, Δ⟩ : ForallProblem).Valid := fun _ h c hc => h c (List.mem_append_left Γ hc)

private theorem strip_index {branches : List (MatchPattern × Expr)} {i : Nat}
    {arm : MatchPattern × Expr} (h : (Expr.stripFoundBranches branches)[i]? = some arm) :
    ∃ br, branches[i]? = some br ∧ arm = (br.1, br.2.stripFound) := by
  rw [stripBranches, List.getElem?_map] at h
  cases hg : branches[i]? with
  | none => simp [hg] at h
  | some br => exact ⟨br, rfl, by simpa [hg] using h.symm⟩

private theorem list_match_typing {types ids rows caller Δ env branches lo hi elem β} {scrut : Expr}
    (hs : Derives types ids rows Δ env scrut.stripFound (.list lo hi elem))
    (arms : BranchResults types ids rows caller Δ env (.list lo hi elem) branches)
    (hb : arms.bounds = some β)
    (hc : ListBranches.Covers Δ ⟨lo, hi⟩ (Expr.stripFoundBranches branches)) :
    Derives types ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
  simp only [Expr.stripFound]
  apply Derives.matchList (actuals := arms.actuals) hs hc
  · intro arm ha
    rw [stripBranches] at ha
    rcases List.mem_map.mp ha with ⟨br, hm, rfl⟩
    exact arms.patterns br hm
  · intro i arm ha
    rcases strip_index ha with ⟨br, hm, rfl⟩
    exact arms.typing i br hm
  · intro i arm ha
    rcases strip_index ha with ⟨br, hm, rfl⟩
    simpa only [hb] using arms.inclusions i br hm

private theorem bool_match_typing {types ids rows caller Δ env branches β} {scrut : Expr}
    (hs : Derives types ids rows Δ env scrut.stripFound (.custom boolTyName []))
    (arms : BranchResults types ids rows caller Δ env .bool branches) (hb : arms.bounds = some β)
    (hc : BoolBranches.Covers (Expr.stripFoundBranches branches)) :
    Derives types ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
  simp only [Expr.stripFound]
  apply Derives.matchBool (actuals := arms.actuals) hs hc
  · intro arm ha
    rw [stripBranches] at ha
    rcases List.mem_map.mp ha with ⟨br, hm, rfl⟩
    exact arms.patterns br hm
  · intro i arm ha
    rcases strip_index ha with ⟨br, hm, rfl⟩
    simpa only [BranchContext.refine, BranchContext.extend, List.append_nil] using arms.typing i br hm
  · intro i arm ha
    rcases strip_index ha with ⟨br, hm, rfl⟩
    simpa only [hb, BranchContext.refine, List.append_nil] using arms.inclusions i br hm

mutual
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
  | .found hm (.match_ scrut branches) =>
      let input ← walk types ids rows caller Δ env (path ++ [.matchScrut]) scrut schemes
      match hin : input.bounds with
      | .list lo hi elem =>
          let coverage ← ListBranches.check Δ ⟨lo, hi⟩ (Expr.stripFoundBranches branches)
          let arms ← walkBranches types ids rows caller Δ env (.list lo hi elem) path branches 0 schemes expected
          match hb : arms.bounds with
          | none => throw "bounds: interpreted List match has no result-producing branch"
          | some β =>
            finish types ids rows caller Δ env (.found hm (.match_ scrut branches)) path β
              (by simpa only [Expr.stripFound] using
                list_match_typing (by simpa only [hin] using input.derivation) arms hb coverage.down)
              (input.nodes ++ arms.nodes)
      | .custom name [] =>
          if hn : name = boolTyName then
            let coverage ← BoolBranches.check (Expr.stripFoundBranches branches)
            let arms ← walkBranches types ids rows caller Δ env .bool path branches 0 schemes expected
            match hb : arms.bounds with
            | none => throw "bounds: interpreted Bool match has no result-producing branch"
            | some β =>
              finish types ids rows caller Δ env (.found hm (.match_ scrut branches)) path β
                (by simpa only [Expr.stripFound] using
                  bool_match_typing (by simpa only [hin, hn] using input.derivation) arms hb coverage.down)
                (input.nodes ++ arms.nodes)
          else throw "bounds: interpreted match scrutinee is neither List nor Bool"
      | _ => throw "bounds: interpreted match scrutinee is neither List nor Bool"
  | _ => throw "bounds: unsupported or missing found node in interpreted RHS traversal"
termination_by (sizeOf e, 1)

private def walkBranches (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (ctx : BranchContext)
    (path : CorePath) (branches : List (MatchPattern × Expr)) (index : Nat)
    (schemes : BinderSchemeMap) (expected : Option BoundsTy) :
    Except String (BranchResults types ids rows caller Δ env ctx branches) := do
  match branches with
  | [] => pure ⟨(fun _ => .prim .int), (by intros; contradiction), (by intros; contradiction),
      none, (by intros; contradiction), []⟩
  | br :: rest =>
      if hp : ctx.Pattern br.1 then
        let head ← walk types ids rows caller (Δ ++ ctx.refine br.1) (ctx.extend br.1 env)
          (path ++ [.matchBranch index]) br.2 schemes expected
        let tail ← walkBranches types ids rows caller Δ env ctx path rest (index + 1) schemes expected
        match expected with
        | some β =>
            let hs ← Typed.subtype (Δ ++ ctx.refine br.1) head.bounds β
            match ht : tail.bounds with
            | none => pure (prependBranches head hp tail β hs.down (by
                intro i arm ha
                have impossible := tail.inclusions i arm ha
                simp only [ht] at impossible))
            | some τ =>
                let ts ← Typed.subtype Δ τ β
                pure (prependBranches head hp tail β hs.down (by
                  intro i arm ha
                  have sub : SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) τ :=
                    by simpa only [ht] using tail.inclusions i arm ha
                  exact sub.trans (ts.down.assuming (path_assuming _ _))))
        | none =>
            match ht : tail.bounds with
            | none => pure (prependBranches head hp tail head.bounds (SemanticSub.refl _ _) (by
                intro i arm ha
                have impossible := tail.inclusions i arm ha
                simp only [ht] at impossible))
            | some τ =>
                let ⟨β, merged⟩ ← BranchMerge.combine .upper head.bounds τ
                let subs := merged.down.sound Δ
                pure (prependBranches head hp tail β (subs.1.assuming (path_assuming _ _)) (by
                  intro i arm ha
                  have sub : SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) τ :=
                    by simpa only [ht] using tail.inclusions i arm ha
                  exact sub.trans (subs.2.assuming (path_assuming _ _))))
      else throw "bounds: unsupported interpreted match pattern or constructor arity"
termination_by (sizeOf branches, 0)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (cases br; simp_all; omega)
end

#print axioms walk

end FHM.Bounds.RecursiveHMWalk
