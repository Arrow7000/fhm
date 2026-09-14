import FHM.Bounds.RecursiveVariable
import FHM.Bounds.RecursiveCountTransport
import FHM.Bounds.BranchMerge
import FHM.Bounds.RecursiveSpine

/-! # Found-driven symbolic RHS checking under recursive assumptions

Consumes the existing HM artifact; never reruns inference or invents recursive
HM slots. Every supported annotation remains an interpreted obligation. Results
carry conditional derivations and the explicit fragment proof for universal RHS
transport. List matches add constructor path premises; Bool matches have finite
constructor coverage without new length assumptions. Both use a proved semantic
merge or a common checked result demand. This checks RHSs, not groups, and does
not export an assumed contract.
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

/-- Checking an unannotated lambda at an explicit domain introduces that
    domain as an assumption. It does not infer a fresh count or specialize HM.
    Carried annotations remain authoritative and outer inclusion is separate. -/
private def chooseParam (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (ann : Option Ty) (hm : Ty) (expected : Option BoundsTy) : Except String
      (Σ param, PLift (InterpretedAnnotation.ParamOK ids rows Δ ann param)) := do
  match ann with
  | none =>
      match expected with
      | some param =>
          let _ ← equal (Synth.BoundsTy.toTy param) hm
            "bounds: declared parameter needs specialization to found HM type"
          pure ⟨param, ⟨True.intro⟩⟩
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

private def bindingHint (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (ann : Option PolyTy) : Except String (Option BoundsTy) := do
  match ann with
  | some σ =>
      if σ.paramCount = 0 then do
        let d ← InterpretedAnnotation.decode ids rows caller σ.body
        pure (some d.bounds)
      else pure none
  | none => pure none

private inductive BranchContext where
  | list (lo hi : Count) (elem : BoundsTy)
  | bool

private def BranchContext.refine : BranchContext → MatchPattern → List Constraint
  | .list lo hi _, p => branchRefine p lo hi
  | .bool, _ => []

private def BranchContext.extend : BranchContext → MatchPattern → List Binding → List Binding
  | .list lo hi elem, p, env => branchEnv p lo hi elem env
  | .bool, _, env => env

private def BranchContext.Pattern : BranchContext → MatchPattern → Prop
  | .list _ _ _, p => ListPattern p
  | .bool, p => BoolBranches.Pattern p

private instance (ctx : BranchContext) (p : MatchPattern) : Decidable (ctx.Pattern p) := by
  cases ctx <;> unfold BranchContext.Pattern <;> infer_instance

/-- Branch evidence is indexed by the original ordered input, not by a report
    reconstructed from found types. Empty arms have no synthesized result. -/
private structure BranchResults (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) (ctx : BranchContext)
    (branches : List (MatchPattern × Expr)) where
  actuals : Nat → BoundsTy
  typing : ∀ i br, branches[i]? = some br →
    Derives ids rows (Δ ++ ctx.refine br.1)
      (ctx.extend br.1 env) br.2.stripFound (actuals i)
  patterns : ∀ br ∈ branches, ctx.Pattern br.1
  noGroups : ∀ br ∈ branches, NoGroups br.2.stripFound
  bounds : Option BoundsTy
  inclusions : ∀ i br, branches[i]? = some br →
    match bounds with
    | none => False
    | some β => SemanticSub (Δ ++ ctx.refine br.1) (actuals i) β
  nodes : List Typed.NodeResult

private def prependBranches {ids rows caller Δ env br branches} {ctx : BranchContext}
    (head : Result ids rows caller (Δ ++ ctx.refine br.1)
      (ctx.extend br.1 env) br.2)
    (hp : ctx.Pattern br.1) (tail : BranchResults ids rows caller Δ env ctx branches)
    (β : BoundsTy)
    (hh : SemanticSub (Δ ++ ctx.refine br.1) head.bounds β)
    (ht : ∀ i arm, branches[i]? = some arm →
      SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) β) :
    BranchResults ids rows caller Δ env ctx (br :: branches) where
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
  noGroups := by
    intro arm h
    rcases List.mem_cons.mp h with rfl | h
    · exact head.noGroups
    · exact tail.noGroups arm h
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
    (⟨Δ ++ Γ, Δ⟩ : ForallProblem).Valid :=
  fun _ h c hc => h c (List.mem_append_left Γ hc)

private theorem strip_index {branches : List (MatchPattern × Expr)} {i : Nat}
    {arm : MatchPattern × Expr}
    (h : (Expr.stripFoundBranches branches)[i]? = some arm) :
    ∃ br, branches[i]? = some br ∧ arm = (br.1, br.2.stripFound) := by
  rw [stripBranches, List.getElem?_map] at h
  cases hg : branches[i]? with
  | none => simp [hg] at h
  | some br => exact ⟨br, rfl, by simpa [hg] using h.symm⟩

private theorem match_typing {ids rows caller Δ env branches lo hi elem β} {scrut : Expr}
    (hs : Derives ids rows Δ env scrut.stripFound (.list lo hi elem))
    (arms : BranchResults ids rows caller Δ env (.list lo hi elem) branches)
    (hb : arms.bounds = some β)
    (hc : ListBranches.Covers Δ ⟨lo, hi⟩ (Expr.stripFoundBranches branches)) :
    Derives ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
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

private theorem bool_match_typing {ids rows caller Δ env branches β} {scrut : Expr}
    (hs : Derives ids rows Δ env scrut.stripFound (.custom boolTyName []))
    (arms : BranchResults ids rows caller Δ env .bool branches)
    (hb : arms.bounds = some β)
    (hc : BoolBranches.Covers (Expr.stripFoundBranches branches)) :
    Derives ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
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

private theorem match_noGroups {ids rows caller Δ env ctx branches} {scrut : Expr}
    (hs : NoGroups scrut.stripFound) (arms : BranchResults ids rows caller Δ env ctx branches) :
    NoGroups (Expr.match_ scrut branches).stripFound := by
  simp only [Expr.stripFound, NoGroups]
  refine ⟨hs, ?_⟩
  rw [stripBranches]
  intro arm ha
  rcases List.mem_map.mp ha with ⟨br, hm, rfl⟩
  exact arms.noGroups br hm

mutual
/-- The optional demand guides match checking and unannotated lambda domains,
    not an unchecked coercion of arbitrary node results. RHS certificates still
    check the outer inclusion; applications still check argument inclusion. -/
def walk (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (env : List Binding) (path : CorePath) (e : Expr) (schemes : BinderSchemeMap)
    (expected : Option BoundsTy := none) :
    Except String (Result ids rows caller Δ env e) := do
  match RecursiveSpine.parseApplication path e with
  | some spine =>
      match env[spine.index]? with
      | some (.recursive _) =>
          let checked ← checkSpineArguments ids rows caller Δ env spine schemes
          let used ← RecursiveSpine.infer checked
          return ← finish ids rows caller Δ env e path spine.hm.eraseBounds used.bounds
            used.typing checked.noGroups used.nodes.tail
      | _ => pure ()
  | none => pure ()
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
      else if hb : BoolBranches.IsCtor name then
        finish ids rows caller Δ env (.found hm (.ctor name)) path hm.eraseBounds (.custom boolTyName [])
          (by simp only [Expr.stripFound]; exact .boolCtor hb) (by simp [Expr.stripFound, NoGroups]) []
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
          let paramHint := match expected with | some (.arrow β _) => some β | _ => none
          let ⟨param, hp⟩ ← chooseParam ids rows caller Δ ann paramTy paramHint
          let bodyHint := match expected with | some (.arrow _ β) => some β | _ => none
          let result ← walk ids rows caller Δ (.mono param :: env) (path ++ [.lambdaBody]) body schemes bodyHint
          finish ids rows caller Δ env (.found hm (.lambda ann body)) path hm.eraseBounds (.arrow param result.bounds)
            (by simpa only [Expr.stripFound] using Derives.lambda hp.down result.derivation)
            (by simpa only [Expr.stripFound, NoGroups] using result.noGroups) result.nodes
      | _ => throw "bounds: recursive RHS lambda has non-arrow found type"
  | .found hm (.letIn ann rhs body) =>
      let rhsHint ← bindingHint ids rows caller ann
      let actual ← walk ids rows caller Δ env (path ++ [.letRhs]) rhs schemes rhsHint
      if ann.isNone then
        let fact ← BinderBridge.atSite schemes (.letIn path) actual.bounds
          (env.map bindingHM ++ rhs.stripFound.tyFreeVars.map Ty.fvar)
        unless fact.scheme.paramCount = 0 do
          throw "bounds: generalized HM internal let unsupported in recursive RHS slice"
      let hp ← checkBinding ids rows caller Δ ann actual.bounds
      let result ← walk ids rows caller Δ (.mono actual.bounds :: env) (path ++ [.letBody]) body schemes expected
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
      let argHint := match env[i]? with
        | some (.mono (.arrow domain _)) => some domain
        | _ => none
      let actual ← walk ids rows caller Δ env (path ++ [.appArg]) arg schemes argHint
      -- Recursive heads use the full-spine route above; this introduces no
      -- second count-proposal authority for an ordinary variable application.
      let used ← RecursiveVariable.application ids rows Δ env i arg.stripFound actual.bounds
        actual.derivation functionHM hm [] caller
      finish ids rows caller Δ env (.found hm (.app (.found functionHM (.var i)) arg)) path hm.eraseBounds used.bounds
        (by simpa only [Expr.stripFound] using used.derivation)
        (by simpa only [Expr.stripFound, NoGroups] using And.intro True.intro actual.noGroups)
        (⟨path ++ [.appFun], functionHM.eraseBounds, some (.arrow used.domain used.bounds)⟩ :: actual.nodes)
  | .found hm (.app fn arg) =>
      let f ← walk ids rows caller Δ env (path ++ [.appFun]) fn schemes
      match hf : f.bounds with
      | .arrow domain result =>
          let actual ← walk ids rows caller Δ env (path ++ [.appArg]) arg schemes (some domain)
          let hs ← Typed.subtype Δ actual.bounds domain
          finish ids rows caller Δ env (.found hm (.app fn arg)) path hm.eraseBounds result
            (by simpa only [Expr.stripFound] using
              Derives.app (by simpa only [hf] using f.derivation) actual.derivation hs.down)
            (by simpa only [Expr.stripFound, NoGroups] using And.intro f.noGroups actual.noGroups)
            (f.nodes ++ actual.nodes)
      | _ => throw "bounds: recursive RHS application has non-function bounds"
  | .found hm (.match_ scrut branches) =>
      let input ← walk ids rows caller Δ env (path ++ [.matchScrut]) scrut schemes
      match hin : input.bounds with
      | .list lo hi elem =>
          let coverage ← ListBranches.check Δ ⟨lo, hi⟩ (Expr.stripFoundBranches branches)
          let arms ← walkBranches ids rows caller Δ env (.list lo hi elem) path branches 0 schemes expected
          match hb : arms.bounds with
          | none => throw "bounds: List match has no result-producing branch"
          | some β =>
              finish ids rows caller Δ env (.found hm (.match_ scrut branches)) path hm.eraseBounds β
                (by simpa only [Expr.stripFound] using
                  match_typing (by simpa only [hin] using input.derivation) arms hb coverage.down)
                (by simpa only [Expr.stripFound] using match_noGroups input.noGroups arms)
                (input.nodes ++ arms.nodes)
      | .custom name [] =>
          if hn : name = boolTyName then
            let coverage ← BoolBranches.check (Expr.stripFoundBranches branches)
            let arms ← walkBranches ids rows caller Δ env .bool path branches 0 schemes expected
            match hb : arms.bounds with
            | none => throw "bounds: Bool match has no result-producing branch"
            | some β =>
                finish ids rows caller Δ env (.found hm (.match_ scrut branches)) path hm.eraseBounds β
                  (by simpa only [Expr.stripFound] using
                    bool_match_typing (by simpa only [hin, hn] using input.derivation) arms hb coverage.down)
                  (by simpa only [Expr.stripFound] using match_noGroups input.noGroups arms)
                  (input.nodes ++ arms.nodes)
          else throw "bounds: recursive RHS match scrutinee has non-List/non-Bool bounds"
      | _ => throw "bounds: recursive RHS match scrutinee has non-List bounds"
  | .found _ (.letRec _ _ _) => throw "bounds: nested recursive group needs captured-template transport"
  | .found _ _ => throw "bounds: expression form unsupported in recursive RHS slice"
  | _ => throw "bounds: every recursive RHS logical node must have one found wrapper"
termination_by (sizeOf e, 1)

private def walkBranches (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) (ctx : BranchContext)
    (path : CorePath) (branches : List (MatchPattern × Expr)) (index : Nat)
    (schemes : BinderSchemeMap) (expected : Option BoundsTy) :
    Except String (BranchResults ids rows caller Δ env ctx branches) := do
  match branches with
  | [] => pure ⟨(fun _ => .prim .int),
      (by intros; contradiction), (by intros; contradiction),
      (by intros; contradiction), none, (by intros; contradiction), []⟩
  | br :: rest =>
      if hp : ctx.Pattern br.1 then
        let head ← walk ids rows caller (Δ ++ ctx.refine br.1)
          (ctx.extend br.1 env) (path ++ [.matchBranch index]) br.2 schemes expected
        let tail ← walkBranches ids rows caller Δ env ctx path rest (index + 1) schemes expected
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
      else match ctx with
        | .list _ _ _ => throw "bounds: unsupported List pattern or constructor arity"
        | .bool => throw "bounds: unsupported Bool pattern or constructor arity"
termination_by (sizeOf branches, 0)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (cases br; simp_all; omega)

private def checkSpineArguments (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) {e : Expr} (spine : RecursiveSpine.Syntax e)
    (schemes : BinderSchemeMap) : Except String (RecursiveSpine.Checked ids rows caller Δ env spine) := do
  match spine with
  | .head path i hm => pure (.head path i hm)
  | .app path hm previous arg =>
      let prior ← checkSpineArguments ids rows caller Δ env previous schemes
      let actual ← walk ids rows caller Δ env (path ++ [.appArg]) arg schemes
      pure (.app path hm prior ⟨actual.bounds, actual.derivation, actual.countScope,
        actual.noGroups, actual.nodes⟩)
termination_by (sizeOf e, 0)
end

#print axioms walk

end FHM.Bounds.RecursiveWalk
