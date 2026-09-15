import FHM.Bounds.RecursiveHMAnnotation
import FHM.Bounds.CountProposal
import FHM.Bounds.BranchMerge
import FHM.Bounds.ScopedHMFoundView
import FHM.Bounds.RecursiveSpine
import FHM.Bounds.StructuralApplication

/-! Initial executable interpreted RHS traversal. Reads original found payloads
and carried annotations, builds real recursive HM derivations, and records
interpreted per-node bounds without rewriting the expression. List/Bool/Pair matches
retain constructor coverage and variance-correct joins. Full recursive spines
collect independent count origins before checking guided pending arguments.
Generalized local lets and nested groups remain explicit
unsupported cases until their existing checker mechanisms are migrated. -/

namespace FHM.Bounds.RecursiveHMWalk

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme

/- Refine every occurrence of an instantiated constructor argument shape in
   its result with the bounds obtained from the actual argument.  The found HM
   payload still checks the resulting shape in `finish`; this function only
   transports quantitative information through nominal result structure. -/
mutual
def transferCtorOrigin (origin : Ty) (actual : BoundsTy) (target : Ty) :
    Except String BoundsTy := do
  match BinderBridge.equalTy target origin with
  | some _ => pure actual
  | none =>
    match target with
    | .prim p => pure (.prim p)
    | .fvar i => pure (.fvar i)
    | .bvar i => pure (.bvar i)
    | .arrow a b =>
        let domain ← transferCtorOrigin origin actual a
        let result ← transferCtorOrigin origin actual b
        pure (.arrow domain result)
    | .customTy n args =>
        if n = listTyName then
          match args with
          | [a] =>
              let elem ← transferCtorOrigin origin actual a
              pure (.list (.lit 0) .inf elem)
          | _ => throw "bounds: malformed List type in constructor result"
        else
          let refined ← transferCtorOrigins origin actual args
          pure (.custom n refined)
    | .bl _ _ _ => throw "bounds: unerased BL node in constructor HM payload"
termination_by sizeOf target

def transferCtorOrigins (origin : Ty) (actual : BoundsTy) (targets : List Ty) :
    Except String (List BoundsTy) := do
  match targets with
  | [] => pure []
  | target :: rest =>
      let head ← transferCtorOrigin origin actual target
      let tail ← transferCtorOrigins origin actual rest
      pure (head :: tail)
termination_by sizeOf targets
end

structure ScopedResult (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (e : Expr) where
  originalHM : Ty
  root : Typed.rootHM? e = some originalHM
  bounds : BoundsTy
  shape : Synth.BoundsTy.toTy bounds = ScopedHMInterpretation.ty types slots originalHM
  derivation : ScopedDerives types slots ids rows Δ env e.stripFound bounds
  countScope : BoundsScoped caller bounds
  finite : Finite rows
  nodes : List Typed.NodeResult
  runtimeReady : Option (PLift (ScopedDerives.RuntimeReady derivation))

private def finish (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (e : Expr)
    (path : CorePath) (β : BoundsTy) (h : ScopedDerives types slots ids rows Δ env e.stripFound β)
    (children : List Typed.NodeResult)
    (ready : Option (PLift (ScopedDerives.RuntimeReady h))) :
    Except String (ScopedResult types slots ids rows caller Δ env e) := do
  match hr : Typed.rootHM? e with
  | none => throw "bounds: interpreted RHS is missing its original found payload"
  | some original =>
      let viewed := ScopedHMInterpretation.ty types slots original
      let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy β) viewed with
        | some h => pure h
        | none => throw s!"bounds: actual RHS disagrees with HM-interpreted found payload at {repr path}: {β.pretty} versus {repr viewed}"
      if hs : boundsScopedBool caller β = true then
        if hf : rows.all (fun row => row.2.noInf) = true then
          pure ⟨original, hr, β, shape.down, h, boundsScopedBool_sound hs,
            fun row hm => Count.noInf_of_isNoInf (List.all_eq_true.mp hf row hm),
            ⟨path, viewed, some β⟩ :: children, ready⟩
        else throw "bounds: interpreted RHS contains an infinite Nat replacement"
      else throw "bounds: actual interpreted RHS counts are outside caller scope"

private inductive BranchContext where
  | list (lo hi : Count) (elem : BoundsTy)
  | bool
  | pair (left right : BoundsTy)
  | opaque (scrutinee : BoundsTy)

private def BranchContext.refine : BranchContext → MatchPattern → List Constraint
  | .list lo hi _, p => RecursiveTyping.branchRefine p lo hi
  | .bool, _ => []
  | .pair _ _, _ => []
  | .opaque _, _ => []

private def BranchContext.extend : BranchContext → MatchPattern → List Binding → List Binding
  | .list lo hi elem, p, env => branchEnv p lo hi elem env
  | .bool, _, env => env
  | .pair left right, p, env => pairBranchEnv p left right env
  | .opaque _, _, env => env

private def BranchContext.Pattern : BranchContext → MatchPattern → Prop
  | .list _ _ _, p => RecursiveTyping.ListPattern p
  | .bool, p => BoolBranches.Pattern p
  | .pair _ _, p => PairBranches.Pattern p
  | .opaque _, p => p = .wildcard

private instance (ctx : BranchContext) (p : MatchPattern) : Decidable (ctx.Pattern p) := by
  cases ctx <;> unfold BranchContext.Pattern <;> infer_instance

private structure BranchResults (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (ctx : BranchContext)
    (branches : List (MatchPattern × Expr)) where
  actuals : Nat → BoundsTy
  typing : ∀ i br, branches[i]? = some br →
    ScopedDerives types slots ids rows (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2.stripFound (actuals i)
  patterns : ∀ br ∈ branches, ctx.Pattern br.1
  bounds : Option BoundsTy
  inclusions : ∀ i br, branches[i]? = some br →
    match bounds with
    | none => False
    | some β => SemanticSub (Δ ++ ctx.refine br.1) (actuals i) β
  nodes : List Typed.NodeResult
  runtimeReady : Option (PLift (∀ i br atIndex, ScopedDerives.RuntimeReady (typing i br atIndex)))

private def prependBranches {types slots ids rows caller Δ env br branches} {ctx : BranchContext}
    (head : ScopedResult types slots ids rows caller (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2)
    (hp : ctx.Pattern br.1) (tail : BranchResults types slots ids rows caller Δ env ctx branches)
    (β : BoundsTy) (hh : SemanticSub (Δ ++ ctx.refine br.1) head.bounds β)
    (ht : ∀ i arm, branches[i]? = some arm → SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) β) :
    BranchResults types slots ids rows caller Δ env ctx (br :: branches) where
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
  runtimeReady := do
    let hh ← head.runtimeReady
    let ht ← tail.runtimeReady
    pure ⟨by
      intro i arm atIndex
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
          subst arm
          exact hh.down
      | succ i => exact ht.down i arm (by simpa only [List.getElem?_cons_succ] using atIndex)⟩

/-- Structural branch erasure shared by original-node RHS and body checking. -/
theorem stripBranches (branches : List (MatchPattern × Expr)) :
    Expr.stripFoundBranches branches = branches.map (fun br => (br.1, br.2.stripFound)) := by
  induction branches with
  | nil => simp [Expr.stripFoundBranches]
  | cons br rest ih => cases br; simp only [Expr.stripFoundBranches, List.map_cons, ih]

private theorem path_assuming (Δ Γ : List Constraint) :
    (⟨Δ ++ Γ, Δ⟩ : ForallProblem).Valid := fun _ h c hc => h c (List.mem_append_left Γ hc)

/-- A zero-forall machine fact can refer to enclosing lexical slots. These are
    captures, not fresh local HM parameters; closed-scheme WF/instantiation is
    therefore the wrong check. Compare the exact ORIGINAL mono payload instead. -/
private def checkMonoFact (σ : PolyTy) (original : Ty) : Except String Unit := do
  unless σ.paramCount = 0 do
    throw "bounds: generalized local HM let unsupported in interpreted recursive RHS slice"
  match BinderBridge.equalTy σ.body.eraseBounds original.eraseBounds with
  | some _ => pure ()
  | none => throw "bounds: monomorphic local binder fact disagrees with original found payload"

/-- Shared exact-source mono-local interface check for RHS and program bodies.
    This validates metadata only; actual typing/inclusion remain separate. -/
def checkLocalInterface (ann : Option PolyTy) (schemes : BinderSchemeMap)
    (site : CoreBinderSite) (original : Ty) : Except String Unit := do
  match ann with
  | some σ => unless σ.paramCount = 0 do
      throw "bounds: polymorphic HM internal binding unsupported in interpreted recursive RHS slice"
  | none => pure ()
  match BinderBridge.candidates schemes site with
  | [σ] => checkMonoFact σ original
  | [] => match ann with
      | some _ => pure ()
      | none => throw "bounds: missing inferred local binder scheme in interpreted RHS"
  | _ => throw "bounds: duplicate inferred local binder scheme in interpreted RHS"

/-- Erasure preserves each branch's index and pattern. -/
theorem strip_index {branches : List (MatchPattern × Expr)} {i : Nat}
    {arm : MatchPattern × Expr} (h : (Expr.stripFoundBranches branches)[i]? = some arm) :
    ∃ br, branches[i]? = some br ∧ arm = (br.1, br.2.stripFound) := by
  rw [stripBranches, List.getElem?_map] at h
  cases hg : branches[i]? with
  | none => simp [hg] at h
  | some br => exact ⟨br, rfl, by simpa [hg] using h.symm⟩

private theorem list_match_typing {types slots ids rows caller Δ env branches lo hi elem β} {scrut : Expr}
    (hs : ScopedDerives types slots ids rows Δ env scrut.stripFound (.list lo hi elem))
    (arms : BranchResults types slots ids rows caller Δ env (.list lo hi elem) branches)
    (hb : arms.bounds = some β)
    (hc : ListBranches.Covers Δ ⟨lo, hi⟩ (Expr.stripFoundBranches branches)) :
    ScopedDerives types slots ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
  simp only [Expr.stripFound]
  apply ScopedDerives.matchList (actuals := arms.actuals) hs hc
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

private theorem bool_match_typing {types slots ids rows caller Δ env branches β} {scrut : Expr}
    (hs : ScopedDerives types slots ids rows Δ env scrut.stripFound (.custom boolTyName []))
    (arms : BranchResults types slots ids rows caller Δ env .bool branches) (hb : arms.bounds = some β)
    (hc : BoolBranches.Covers (Expr.stripFoundBranches branches)) :
    ScopedDerives types slots ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
  simp only [Expr.stripFound]
  apply ScopedDerives.matchBool (actuals := arms.actuals) hs hc
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

private def list_match_ready {types slots ids rows caller Δ env branches lo hi elem β} {scrut : Expr}
    (hs : ScopedDerives types slots ids rows Δ env scrut.stripFound (.list lo hi elem))
    (arms : BranchResults types slots ids rows caller Δ env (.list lo hi elem) branches)
    (hb : arms.bounds = some β)
    (hc : ListBranches.Covers Δ ⟨lo, hi⟩ (Expr.stripFoundBranches branches))
    (ready : Option (PLift (ScopedDerives.RuntimeReady hs))) :
    Option (PLift (ScopedDerives.RuntimeReady (list_match_typing hs arms hb hc))) := do
  let input ← ready
  let bodies ← arms.runtimeReady
  let result ← Runtime.supported? β
  pure ⟨by
    simp only [Expr.stripFound]
    refine ScopedDerives.RuntimeReady.matchList (actuals := arms.actuals) hc ?_ ?_ ?_ input.down ?_ result.down
    · intro arm member
      rw [stripBranches] at member
      obtain ⟨br, atSource, rfl⟩ := List.mem_map.mp member
      exact arms.patterns br atSource
    · intro i arm atIndex
      rcases strip_index atIndex with ⟨br, atSource, rfl⟩
      exact arms.typing i br atSource
    · intro i arm atIndex
      rcases strip_index atIndex with ⟨br, atSource, rfl⟩
      simpa only [hb] using arms.inclusions i br atSource
    · intro i arm atIndex
      rcases strip_index atIndex with ⟨br, atSource, rfl⟩
      exact bodies.down i br atSource⟩

private def bool_match_ready {types slots ids rows caller Δ env branches β} {scrut : Expr}
    (hs : ScopedDerives types slots ids rows Δ env scrut.stripFound (.custom boolTyName []))
    (arms : BranchResults types slots ids rows caller Δ env .bool branches) (hb : arms.bounds = some β)
    (hc : BoolBranches.Covers (Expr.stripFoundBranches branches))
    (ready : Option (PLift (ScopedDerives.RuntimeReady hs))) :
    Option (PLift (ScopedDerives.RuntimeReady (bool_match_typing hs arms hb hc))) := do
  let input ← ready
  let bodies ← arms.runtimeReady
  let result ← Runtime.supported? β
  pure ⟨by
    simp only [Expr.stripFound]
    refine ScopedDerives.RuntimeReady.matchBool (actuals := arms.actuals) hc ?_ ?_ ?_ input.down ?_ result.down
    · intro arm member
      rw [stripBranches] at member
      obtain ⟨br, atSource, rfl⟩ := List.mem_map.mp member
      exact arms.patterns br atSource
    · intro i arm atIndex
      rcases strip_index atIndex with ⟨br, atSource, rfl⟩
      simpa only [BranchContext.refine, BranchContext.extend, List.append_nil] using arms.typing i br atSource
    · intro i arm atIndex
      rcases strip_index atIndex with ⟨br, atSource, rfl⟩
      simpa only [hb, BranchContext.refine, List.append_nil] using arms.inclusions i br atSource
    · intro i arm atIndex
      rcases strip_index atIndex with ⟨br, atSource, rfl⟩
      simpa only [BranchContext.refine, BranchContext.extend, List.append_nil] using bodies.down i br atSource⟩

private theorem pair_match_typing {types slots ids rows caller Δ env branches left right β}
    {scrut : Expr}
    (hs : ScopedDerives types slots ids rows Δ env scrut.stripFound
      (.custom pairTyName [left, right]))
    (arms : BranchResults types slots ids rows caller Δ env (.pair left right) branches)
    (hb : arms.bounds = some β)
    (hc : PairBranches.Covers (Expr.stripFoundBranches branches)) :
    ScopedDerives types slots ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
  simp only [Expr.stripFound]
  apply ScopedDerives.matchPair (actuals := arms.actuals) hs hc
  · intro arm ha
    rw [stripBranches] at ha
    rcases List.mem_map.mp ha with ⟨br, hm, rfl⟩
    exact arms.patterns br hm
  · intro i arm ha
    rcases strip_index ha with ⟨br, hm, rfl⟩
    simpa only [BranchContext.refine, BranchContext.extend, List.append_nil] using
      arms.typing i br hm
  · intro i arm ha
    rcases strip_index ha with ⟨br, hm, rfl⟩
    simpa only [hb, BranchContext.refine, List.append_nil] using arms.inclusions i br hm

private def pair_match_ready {types slots ids rows caller Δ env branches left right β}
    {scrut : Expr}
    (hs : ScopedDerives types slots ids rows Δ env scrut.stripFound
      (.custom pairTyName [left, right]))
    (arms : BranchResults types slots ids rows caller Δ env (.pair left right) branches)
    (hb : arms.bounds = some β)
    (hc : PairBranches.Covers (Expr.stripFoundBranches branches))
    (ready : Option (PLift (ScopedDerives.RuntimeReady hs))) :
    Option (PLift (ScopedDerives.RuntimeReady (pair_match_typing hs arms hb hc))) := do
  let input ← ready
  let bodies ← arms.runtimeReady
  let result ← Runtime.supported? β
  pure ⟨by
    simp only [Expr.stripFound]
    refine ScopedDerives.RuntimeReady.matchPair (actuals := arms.actuals) hc ?_ ?_ ?_
      input.down ?_ result.down
    · intro arm member
      rw [stripBranches] at member
      obtain ⟨br, atSource, rfl⟩ := List.mem_map.mp member
      exact arms.patterns br atSource
    · intro i arm atIndex
      rcases strip_index atIndex with ⟨br, atSource, rfl⟩
      simpa only [BranchContext.refine, BranchContext.extend, List.append_nil] using
        arms.typing i br atSource
    · intro i arm atIndex
      rcases strip_index atIndex with ⟨br, atSource, rfl⟩
      simpa only [hb, BranchContext.refine, List.append_nil] using arms.inclusions i br atSource
    · intro i arm atIndex
      rcases strip_index atIndex with ⟨br, atSource, rfl⟩
      simpa only [BranchContext.refine, BranchContext.extend, List.append_nil] using
        bodies.down i br atSource⟩

private theorem opaque_match_typing {types slots ids rows caller Δ env branches scrutinee β}
    {scrut : Expr}
    (hs : ScopedDerives types slots ids rows Δ env scrut.stripFound scrutinee)
    (arms : BranchResults types slots ids rows caller Δ env (.opaque scrutinee) branches)
    (hb : arms.bounds = some β) :
    ScopedDerives types slots ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
  simp only [Expr.stripFound]
  apply ScopedDerives.matchOpaque (actuals := arms.actuals) hs
  · intro arm member
    rw [stripBranches] at member
    obtain ⟨br, atSource, rfl⟩ := List.mem_map.mp member
    exact arms.patterns br atSource
  · intro i arm atIndex
    rcases strip_index atIndex with ⟨br, atSource, rfl⟩
    simpa only [BranchContext.refine, BranchContext.extend, List.append_nil] using
      arms.typing i br atSource
  · intro i arm atIndex
    rcases strip_index atIndex with ⟨br, atSource, rfl⟩
    simpa only [hb, BranchContext.refine, List.append_nil] using
      arms.inclusions i br atSource

private def appendScoped {types slots ids rows caller Δ env fn arg} (path : CorePath) (hm : Ty)
    (prior : ScopedResult types slots ids rows caller Δ env fn)
    (actual : ScopedResult types slots ids rows caller Δ env arg) :
    Except String (ScopedResult types slots ids rows caller Δ env (.found hm (.app fn arg))) := do
  match hf : prior.bounds with
  | .arrow domain result =>
      let sub ← Typed.subtype Δ actual.bounds domain
      finish types slots ids rows caller Δ env (.found hm (.app fn arg)) path result
        (by simpa only [Expr.stripFound] using
          (ScopedDerives.app (by simpa only [hf] using prior.derivation) actual.derivation sub.down))
        (prior.nodes ++ actual.nodes)
        (do
          let fn ← prior.runtimeReady
          let arg ← actual.runtimeReady
          pure ⟨by
            simp only [Expr.stripFound]
            apply ScopedDerives.RuntimeReady.app sub.down
            · simpa only [hf] using fn.down
            · exact arg.down⟩)
  | _ => throw "bounds: interpreted application callee is not an arrow"

/-- Preparation only: absent arguments have neither bounds nor typing evidence.
    They may be accepted only by the source-indexed completion below. -/
private inductive ScopedSpine (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) :
    {e : Expr} → RecursiveSpine.Syntax e → Type where
  | head (path : CorePath) (i : Nat) (hm : Ty) : ScopedSpine types slots ids rows caller Δ env (.head path i hm)
  | app {fn : Expr} {prior : RecursiveSpine.Syntax fn} {arg : Expr} (path : CorePath) (hm : Ty)
      (previous : ScopedSpine types slots ids rows caller Δ env prior)
      (actual : Option (ScopedResult types slots ids rows caller Δ env arg)) :
      ScopedSpine types slots ids rows caller Δ env (.app path hm prior arg)

private def ScopedSpine.actualsRev {types slots ids rows caller Δ env e} {spine : RecursiveSpine.Syntax e} :
    ScopedSpine types slots ids rows caller Δ env spine → List (Option BoundsTy)
  | .head _ _ _ => []
  | .app _ _ previous actual => actual.map (·.bounds) :: previous.actualsRev

mutual
def walkScoped (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (path : CorePath)
    (e : Expr) (schemes : BinderSchemeMap) (expected : Option BoundsTy := none) :
    Except String (ScopedResult types slots ids rows caller Δ env e) := do
  match e with
  | .found hm (.primLit p) =>
      finish types slots ids rows caller Δ env (.found hm (.primLit p)) path (boundInfoOfPrimLit p)
        (by simpa only [Expr.stripFound] using (ScopedDerives.literal (types := types) (slots := slots) (env := env) (p := p))) []
        (some ⟨by simpa only [Expr.stripFound] using
          (@ScopedDerives.RuntimeReady.literal types slots ids rows Δ env p)⟩)
  | .found hm (.primBinOp op) =>
      finish types slots ids rows caller Δ env (.found hm (.primBinOp op)) path (Typed.primOpBounds op)
        (by simpa only [Expr.stripFound] using (ScopedDerives.primBinOp (types := types) (slots := slots) (env := env) (op := op))) []
        (some ⟨by simpa only [Expr.stripFound] using
          (@ScopedDerives.RuntimeReady.primBinOp types slots ids rows Δ env op)⟩)
  | .found hm (.ctor name) =>
      if hn : name = nilCtorName then
        match ScopedHMInterpretation.ty types slots hm with
        | .customTy listName [a] =>
            unless listName = listTyName do throw "bounds: interpreted Nil has a non-List HM type"
            let elem ← match expected with
              | some (.list _ _ elem) => pure elem
              | _ => Typed.shapeTop a
            finish types slots ids rows caller Δ env (.found hm (.ctor name)) path (.list (.lit 0) (.lit 0) elem)
              (by subst name; simpa only [Expr.stripFound] using (ScopedDerives.nil (types := types) (slots := slots) (env := env) (elem := elem))) []
              (do
                let supported ← Runtime.supported? elem
                pure ⟨by
                  subst name
                  simpa only [Expr.stripFound] using
                    (@ScopedDerives.RuntimeReady.nil types slots ids rows Δ env elem supported.down)⟩)
        | _ => throw "bounds: interpreted Nil has a non-List HM type"
      else if hb : BoolBranches.IsCtor name then
        finish types slots ids rows caller Δ env (.found hm (.ctor name)) path (.custom boolTyName [])
          (by simpa only [Expr.stripFound] using (ScopedDerives.boolCtor (types := types) (slots := slots) (env := env) hb)) []
          (some ⟨by simpa only [Expr.stripFound] using
            (ScopedDerives.RuntimeReady.boolCtor (types := types) (slots := slots)
              (ids := ids) (rows := rows) (name := name) hb)⟩)
      else
        let β ← match expected with
          | some β => pure β
          | none => Typed.shapeTop (ScopedHMInterpretation.ty types slots hm)
        finish types slots ids rows caller Δ env (.found hm (.ctor name)) path β
          (by simpa only [Expr.stripFound] using
            (ScopedDerives.ctor (types := types) (slots := slots) (env := env) hn)) [] none
  | .found hm (.var i) =>
      match hv : env[i]? with
      | none => throw "bounds: interpreted variable outside assumption environment"
      | some (.mono β) =>
          finish types slots ids rows caller Δ env (.found hm (.var i)) path β
            (by simpa only [Expr.stripFound] using (ScopedDerives.varMono (types := types) (slots := slots) (ids := ids) (rows := rows) (Δ := Δ) hv)) []
            (do
              let supported ← Runtime.supported? β
              pure ⟨by simpa only [Expr.stripFound] using
                (ScopedDerives.RuntimeReady.varMono (types := types) (slots := slots)
                  (ids := ids) (rows := rows) (i := i) hv supported.down)⟩)
      | some (.recursive c) =>
          let used ← RecursiveHMContract.check c.fixed Δ c.hm [] caller
          finish types slots ids rows caller Δ env (.found hm (.var i)) path used.bounds
            (by simpa only [Expr.stripFound] using (ScopedDerives.varRecursive (types := types) (slots := slots) (ids := ids) (rows := rows) hv used)) []
            (do
              let supported ← Runtime.supported? used.bounds
              pure ⟨by simpa only [Expr.stripFound] using
                (ScopedDerives.RuntimeReady.varRecursive (types := types) (slots := slots)
                  (ids := ids) (rows := rows) (env := env) (i := i) (c := c) hv used supported.down)⟩)
      | some (.exported s) =>
          if s.hm.paramCount == 0 && s.counts.quantified.isEmpty then
            let used ← HMCountScheme.check s Δ (ScopedHMInterpretation.ty types slots hm) [] [] caller
            finish types slots ids rows caller Δ env (.found hm (.var i)) path used.bounds
              (by simpa only [Expr.stripFound] using
                (ScopedDerives.varExported (types := types) (slots := slots)
                  (ids := ids) (rows := rows) hv used)) []
              (do
                let supported ← Runtime.supported? used.bounds
                let arguments ← Runtime.supportedArguments? used.types
                pure ⟨by simpa only [Expr.stripFound] using
                  (ScopedDerives.RuntimeReady.varExported (types := types) (slots := slots)
                    (ids := ids) (rows := rows) (i := i) hv used supported.down arguments.down)⟩)
          else throw "bounds: exported polymorphic RHS use needs origin-backed arguments"
  | .found hm (.lambda ann body) =>
      match hm.eraseBounds with
      | .arrow paramHM _ =>
          let paramHint := match expected with | some (.arrow a _) => some a | _ => none
          let bodyHint := match expected with | some (.arrow _ b) => some b | _ => none
          let param ← RecursiveHMAnnotation.chooseScopedParam types slots ids rows caller Δ ann paramHM paramHint
          let result ← walkScoped types slots ids rows caller Δ (.mono param.bounds :: env)
            (path ++ [.lambdaBody]) body schemes bodyHint
          finish types slots ids rows caller Δ env (.found hm (.lambda ann body)) path (.arrow param.bounds result.bounds)
            (by simpa only [Expr.stripFound] using (ScopedDerives.lambda param.obligation result.derivation)) result.nodes
            (do
              let supported ← Runtime.supported? param.bounds
              let body ← result.runtimeReady
              pure ⟨by
                simpa only [Expr.stripFound] using
                  (ScopedDerives.RuntimeReady.lambda (ann := ann) param.obligation supported.down body.down)⟩)
      | _ => throw "bounds: interpreted lambda has a non-arrow original found type"
  | .found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail) =>
      if hn : name = consCtorName then
        let headHint := match expected with | some (.list _ _ elem) => some elem | _ => none
        let h ← walkScoped types slots ids rows caller Δ env (path ++ [.appFun, .appArg]) head schemes headHint
        let t ← walkScoped types slots ids rows caller Δ env (path ++ [.appArg]) tail schemes
          (some (.list (.lit 0) .inf h.bounds))
        match ht : t.bounds with
        | .list lo hi elem =>
            let _ ← match BinderBridge.equalTy (ScopedHMInterpretation.ty types slots ctorTy)
                (.arrow (ScopedHMInterpretation.ty types slots h.originalHM)
                  (.arrow (ScopedHMInterpretation.ty types slots t.originalHM) (ScopedHMInterpretation.ty types slots t.originalHM))) with
              | some h => pure h | none => throw "bounds: inconsistent interpreted Cons found type"
            let _ ← match BinderBridge.equalTy (ScopedHMInterpretation.ty types slots partialTy)
                (.arrow (ScopedHMInterpretation.ty types slots t.originalHM) (ScopedHMInterpretation.ty types slots t.originalHM)) with
              | some h => pure h | none => throw "bounds: inconsistent interpreted partial Cons found type"
            let sub ← Typed.subtype Δ h.bounds elem
            finish types slots ids rows caller Δ env
              (.found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail))
              path (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
              (by subst name; simpa only [Expr.stripFound] using
                (ScopedDerives.cons h.derivation (by simpa only [ht] using t.derivation) sub.down))
              (⟨path ++ [.appFun], ScopedHMInterpretation.ty types slots partialTy, none⟩ ::
                ⟨path ++ [.appFun, .appFun], ScopedHMInterpretation.ty types slots ctorTy, none⟩ :: h.nodes ++ t.nodes)
              (do
                let head ← h.runtimeReady
                let tail ← t.runtimeReady
                pure ⟨by
                  subst name
                  simp only [Expr.stripFound]
                  apply ScopedDerives.RuntimeReady.cons sub.down head.down
                  simpa only [ht] using tail.down⟩)
        | _ => throw "bounds: interpreted Cons tail is not a List"
      else if hp : name = pairCtorName then
        let leftHint := match expected with
          | some (.custom pairName [left, _]) => if pairName = pairTyName then some left else none
          | _ => none
        let rightHint := match expected with
          | some (.custom pairName [_, right]) => if pairName = pairTyName then some right else none
          | _ => none
        let left ← walkScoped types slots ids rows caller Δ env
          (path ++ [.appFun, .appArg]) head schemes leftHint
        let right ← walkScoped types slots ids rows caller Δ env
          (path ++ [.appArg]) tail schemes rightHint
        let interpretedResult := ScopedHMInterpretation.ty types slots hm
        let _ ← match BinderBridge.equalTy (ScopedHMInterpretation.ty types slots ctorTy)
            (.arrow (ScopedHMInterpretation.ty types slots left.originalHM)
              (.arrow (ScopedHMInterpretation.ty types slots right.originalHM) interpretedResult)) with
          | some h => pure h
          | none => throw "bounds: inconsistent interpreted Pair found type"
        let _ ← match BinderBridge.equalTy (ScopedHMInterpretation.ty types slots partialTy)
            (.arrow (ScopedHMInterpretation.ty types slots right.originalHM) interpretedResult) with
          | some h => pure h
          | none => throw "bounds: inconsistent interpreted partial Pair found type"
        finish types slots ids rows caller Δ env
          (.found hm (.app (.found partialTy (.app (.found ctorTy (.ctor name)) head)) tail))
          path (.custom pairTyName [left.bounds, right.bounds])
          (by subst name; simpa only [Expr.stripFound] using
            (ScopedDerives.pair left.derivation right.derivation))
          (⟨path ++ [.appFun], ScopedHMInterpretation.ty types slots partialTy, none⟩ ::
            ⟨path ++ [.appFun, .appFun], ScopedHMInterpretation.ty types slots ctorTy, none⟩ ::
            left.nodes ++ right.nodes)
          (do
            let leftReady ← left.runtimeReady
            let rightReady ← right.runtimeReady
            pure ⟨by
              subst name
              simpa only [Expr.stripFound] using
                ScopedDerives.RuntimeReady.pair leftReady.down rightReady.down⟩)
      else
        let fn ← walkScoped types slots ids rows caller Δ env (path ++ [.appFun])
          (.found partialTy (.app (.found ctorTy (.ctor name)) head)) schemes
        let arg ← walkScoped types slots ids rows caller Δ env (path ++ [.appArg]) tail schemes
        appendScoped path hm fn arg
  | .found hm (.app (.found ctorHM (.ctor name)) arg) =>
      if hn : name = nilCtorName then
        throw "bounds: Nil cannot be applied"
      else if hc : name = consCtorName then
        throw "bounds: partial Cons application unsupported in interpreted RHS traversal"
      else if hp : name = pairCtorName then
        throw "bounds: partial Pair application unsupported in interpreted RHS traversal"
      else if hb : BoolBranches.IsCtor name then
        throw "bounds: Bool constructor cannot be applied"
      else
        match ScopedHMInterpretation.ty types slots ctorHM with
        | .arrow domainHM resultHM =>
            let actual ← walkScoped types slots ids rows caller Δ env
              (path ++ [.appArg]) arg schemes
            let result ← transferCtorOrigin domainHM actual.bounds resultHM
            let function ← finish types slots ids rows caller Δ env
              (.found ctorHM (.ctor name)) (path ++ [.appFun])
              (.arrow actual.bounds result)
              (by simpa only [Expr.stripFound] using
                (ScopedDerives.ctor (types := types) (slots := slots) (env := env) hn)) [] none
            appendScoped path hm function actual
        | _ => throw "bounds: applied constructor has a non-arrow interpreted HM type"
  | .found hm (.app function arg) =>
      match RecursiveSpine.Syntax.parse path (.found hm (.app function arg)) with
      | some spine =>
          match hv : env[spine.index]? with
          | some (.recursive c) =>
              let checked ← walkScopedSpine types slots ids rows caller Δ env spine schemes
              let counts ← CountProposal.proposeOrigins c.template.counts.quantified
                c.template.counts.body checked.actualsRev.reverse
              let used ← RecursiveHMContract.check c.fixed Δ c.hm counts caller
              return ← completeScopedSpine types slots ids rows caller Δ env checked hv used schemes
          | some (.exported s) =>
              let checked ← walkScopedSpine types slots ids rows caller Δ env spine schemes
              let origins := checked.actualsRev.reverse
              let typeArgs ← StructuralApplication.proposeOrigins
                s.counts.body origins s.hm.paramCount
              let counts ← CountProposal.proposeOrigins s.counts.quantified s.counts.body origins
              let used ← HMCountScheme.check s Δ
                (ScopedHMInterpretation.ty types slots spine.headHM) counts typeArgs caller
              return ← completeExportedScopedSpine types slots ids rows caller Δ env checked hv used schemes
          | _ => pure ()
      | none => pure ()
      let fn ← walkScoped types slots ids rows caller Δ env (path ++ [.appFun]) function schemes
      match hf : fn.bounds with
      | .arrow domain result =>
          let actual ← walkScoped types slots ids rows caller Δ env (path ++ [.appArg]) arg schemes (some domain)
          appendScoped path hm fn actual
      | _ => throw "bounds: interpreted application callee is not an arrow"
  | .found _ (.letRec _ _ _) => throw "bounds: nested groups unsupported in interpreted universal RHS traversal"
  | .found hm (.letIn ann rhs body) =>
      let hint ← RecursiveHMAnnotation.scopedBindingHint types slots ids rows caller ann
      let actual ← walkScoped types slots ids rows caller Δ env (path ++ [.letRhs]) rhs schemes hint
      -- Unannotated locals require a unique original machine fact. Annotated
      -- mono declarations do not have one; their source obligation is checked
      -- below. If a compatibility artifact includes a fact, cross-check it.
      let _ ← checkLocalInterface ann schemes (.letIn path) actual.originalHM
      let obligation ← RecursiveHMAnnotation.checkScopedBinding types slots ids rows caller Δ ann actual.bounds
      let result ← walkScoped types slots ids rows caller Δ (.mono actual.bounds :: env)
        (path ++ [.letBody]) body schemes expected
      finish types slots ids rows caller Δ env (.found hm (.letIn ann rhs body)) path result.bounds
        (by simpa only [Expr.stripFound] using
          (ScopedDerives.letMono obligation.down actual.derivation result.derivation)) (actual.nodes ++ result.nodes)
        (do
          let rhs ← actual.runtimeReady
          let body ← result.runtimeReady
          pure ⟨by
            simpa only [Expr.stripFound] using
              (ScopedDerives.RuntimeReady.letMono (ann := ann) obligation.down rhs.down body.down)⟩)
  | .found hm (.match_ scrut branches) =>
      let input ← walkScoped types slots ids rows caller Δ env (path ++ [.matchScrut]) scrut schemes
      match hin : input.bounds with
      | .list lo hi elem =>
          let coverage ← ListBranches.check Δ ⟨lo, hi⟩ (Expr.stripFoundBranches branches)
          let arms ← walkScopedBranches types slots ids rows caller Δ env (.list lo hi elem) path branches 0 schemes expected
          match hb : arms.bounds with
          | none => throw "bounds: interpreted List match has no result-producing branch"
          | some β =>
            finish types slots ids rows caller Δ env (.found hm (.match_ scrut branches)) path β
              (by simpa only [Expr.stripFound] using
                list_match_typing (by simpa only [hin] using input.derivation) arms hb coverage.down)
              (input.nodes ++ arms.nodes)
              (by simpa only [Expr.stripFound] using
                (list_match_ready (by simpa only [hin] using input.derivation) arms hb coverage.down
                  (by simpa only [hin] using input.runtimeReady)))
      | .custom name [] =>
          if hn : name = boolTyName then
            let coverage ← BoolBranches.check (Expr.stripFoundBranches branches)
            let arms ← walkScopedBranches types slots ids rows caller Δ env .bool path branches 0 schemes expected
            match hb : arms.bounds with
            | none => throw "bounds: interpreted Bool match has no result-producing branch"
            | some β =>
              finish types slots ids rows caller Δ env (.found hm (.match_ scrut branches)) path β
                (by simpa only [Expr.stripFound] using
                  bool_match_typing (by simpa only [hin, hn] using input.derivation) arms hb coverage.down)
                (input.nodes ++ arms.nodes)
                (by simpa only [Expr.stripFound] using
                  (bool_match_ready (by simpa only [hin, hn] using input.derivation) arms hb coverage.down
                    (by simpa only [hin, hn] using input.runtimeReady)))
          else throw "bounds: interpreted match scrutinee is not List, Bool, or Pair"
      | .custom name [left, right] =>
          if hn : name = pairTyName then
            let coverage ← PairBranches.check (Expr.stripFoundBranches branches)
            let arms ← walkScopedBranches types slots ids rows caller Δ env (.pair left right)
              path branches 0 schemes expected
            match hb : arms.bounds with
            | none => throw "bounds: interpreted Pair match has no result-producing branch"
            | some β =>
              let pairTyping := pair_match_typing
                (by simpa only [hin, hn] using input.derivation) arms hb coverage.down
              let pairReady := pair_match_ready
                (by simpa only [hin, hn] using input.derivation) arms hb coverage.down
                  (by simpa only [hin, hn] using input.runtimeReady)
              finish types slots ids rows caller Δ env (.found hm (.match_ scrut branches)) path β
                (by simpa only [Expr.stripFound] using pairTyping)
                (input.nodes ++ arms.nodes)
                (by simpa only [Expr.stripFound] using pairReady)
          else throw "bounds: interpreted match scrutinee is not List, Bool, or Pair"
      | _ =>
          let arms ← walkScopedBranches types slots ids rows caller Δ env
            (.opaque input.bounds) path branches 0 schemes expected
          match hb : arms.bounds with
          | none => throw "bounds: interpreted wildcard match has no result-producing branch"
          | some β =>
              finish types slots ids rows caller Δ env (.found hm (.match_ scrut branches)) path β
                (by simpa only [Expr.stripFound] using
                  opaque_match_typing input.derivation arms hb)
                (input.nodes ++ arms.nodes) none
  | _ => throw "bounds: unsupported or missing found node in interpreted RHS traversal"
termination_by (sizeOf e, 1)

private def walkScopedSpine (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) {e : Expr}
    (spine : RecursiveSpine.Syntax e) (schemes : BinderSchemeMap) :
    Except String (ScopedSpine types slots ids rows caller Δ env spine) := do
  match spine with
  | .head path i hm => pure (.head path i hm)
  | .app path hm prior arg =>
      let previous ← walkScopedSpine types slots ids rows caller Δ env prior schemes
      let actual := match walkScoped types slots ids rows caller Δ env (path ++ [.appArg]) arg schemes with
        | .ok result => some result
        | .error _ => none
      pure (.app path hm previous actual)
termination_by (sizeOf e, 0)

/-- Fixed HM vector and ONE count vector. Missing independent arguments are
    checked only against domains obtained from the real instantiated callee;
    they never become count origins. Every source frame still needs a proof. -/
private def completeScopedSpine (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) {e : Expr}
    {spine : RecursiveSpine.Syntax e} (prepared : ScopedSpine types slots ids rows caller Δ env spine)
    {c : Contract} (lookup : env[spine.index]? = some (.recursive c))
    (used : RecursiveHMContract.Use c.fixed Δ c.hm caller) (schemes : BinderSchemeMap) :
    Except String (ScopedResult types slots ids rows caller Δ env e) := do
  match prepared with
  | .head path i hm =>
      finish types slots ids rows caller Δ env (.found hm (.var i)) path used.bounds
        (by simpa only [Expr.stripFound] using ScopedDerives.varRecursive lookup used) []
        (do
          let supported ← Runtime.supported? used.bounds
          pure ⟨by simpa only [Expr.stripFound] using
            (ScopedDerives.RuntimeReady.varRecursive (types := types) (slots := slots)
              (ids := ids) (rows := rows) (i := i) lookup used supported.down)⟩)
  | .app (arg := arg) path hm previous actual =>
      let prior ← completeScopedSpine types slots ids rows caller Δ env previous lookup used schemes
      match prior.bounds with
      | .arrow domain _ =>
          let checked ← match actual with
            | some checked => pure checked
            | none => walkScoped types slots ids rows caller Δ env (path ++ [.appArg]) arg schemes (some domain)
          appendScoped path hm prior checked
      | _ => throw "bounds: deferred recursive spine applies a non-arrow contract result"
termination_by (sizeOf e, 0)

private def completeExportedScopedSpine (types slots : Nat → BoundsTy) (ids : List Nat)
    (rows : Bindings) (caller : List Nat) (Δ : List Constraint) (env : List Binding) {e : Expr}
    {spine : RecursiveSpine.Syntax e}
    (prepared : ScopedSpine types slots ids rows caller Δ env spine)
    {s : HMCountScheme.Scheme} (lookup : env[spine.index]? = some (.exported s))
    (used : HMCountScheme.Use s Δ (ScopedHMInterpretation.ty types slots spine.headHM) caller)
    (schemes : BinderSchemeMap) :
    Except String (ScopedResult types slots ids rows caller Δ env e) := do
  match prepared with
  | .head path i hm =>
      finish types slots ids rows caller Δ env (.found hm (.var i)) path used.bounds
        (by simpa only [Expr.stripFound] using ScopedDerives.varExported lookup used) []
        (do
          let supported ← Runtime.supported? used.bounds
          let arguments ← Runtime.supportedArguments? used.types
          pure ⟨by simpa only [Expr.stripFound] using
            (ScopedDerives.RuntimeReady.varExported (types := types) (slots := slots)
              (ids := ids) (rows := rows) (i := i) lookup used supported.down arguments.down)⟩)
  | .app (arg := arg) path hm previous actual =>
      let prior ← completeExportedScopedSpine types slots ids rows caller Δ env
        previous lookup used schemes
      match prior.bounds with
      | .arrow domain _ =>
          let checked ← match actual with
            | some checked => pure checked
            | none => walkScoped types slots ids rows caller Δ env (path ++ [.appArg]) arg schemes (some domain)
          appendScoped path hm prior checked
      | _ => throw "bounds: deferred exported spine applies a non-arrow scheme result"
termination_by (sizeOf e, 0)

private def walkScopedBranches (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (ctx : BranchContext)
    (path : CorePath) (branches : List (MatchPattern × Expr)) (index : Nat)
    (schemes : BinderSchemeMap) (expected : Option BoundsTy) :
    Except String (BranchResults types slots ids rows caller Δ env ctx branches) := do
  match branches with
  | [] => pure ⟨(fun _ => .prim .int), (by intros; contradiction), (by intros; contradiction),
      none, (by intros; contradiction), [], some ⟨by intros; contradiction⟩⟩
  | br :: rest =>
      if hp : ctx.Pattern br.1 then
        let head ← walkScoped types slots ids rows caller (Δ ++ ctx.refine br.1) (ctx.extend br.1 env)
          (path ++ [.matchBranch index]) br.2 schemes expected
        let tail ← walkScopedBranches types slots ids rows caller Δ env ctx path rest (index + 1) schemes expected
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

/-- Compatibility result for the original free-only traversal. -/
abbrev Result (types : Nat → BoundsTy) := ScopedResult types BoundsTy.bvar

namespace Result
theorem shape {types ids rows caller Δ env e} (r : Result types ids rows caller Δ env e) :
    Synth.BoundsTy.toTy r.bounds = HMFoundView.ty types r.originalHM := by
  rw [← HMFoundView.scoped_identity_slots]
  exact ScopedResult.shape r
end Result

/-- Identity-slot view of the same executable traversal. -/
def walk (types : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) (path : CorePath)
    (e : Expr) (schemes : BinderSchemeMap) (expected : Option BoundsTy := none) :
    Except String (Result types ids rows caller Δ env e) :=
  walkScoped types BoundsTy.bvar ids rows caller Δ env path e schemes expected

structure LocatedResult {output path} (node : HMFoundView.AtNode output path)
    (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding) where
  typed : ScopedHMInterpretation.TypedChecked node types slots ids rows Δ env caller
  nodes : List Typed.NodeResult

/-- Traverse and certify the original RHS at an exact logical Core address.
    The lexical interface comes from the consuming declaration, not an invented
    inferred binder fact. This is not yet universal/group introduction. -/
def checkLocated {output path} (node : HMFoundView.AtNode output path)
    (types slots : Nat → BoundsTy) (ids : List Nat) (rows : Bindings)
    (caller : List Nat) (Δ : List Constraint) (env : List Binding)
    (schemes : BinderSchemeMap) (expected : Option BoundsTy := none) :
    Except String (LocatedResult node types slots ids rows caller Δ env) := do
  let walked ← walkScoped types slots ids rows caller Δ env path
    (.found node.original node.inner) schemes expected
  let derivation : ScopedDerives types slots ids rows Δ env node.inner.stripFound walked.bounds := by
    simpa only [Expr.stripFound] using walked.derivation
  let typed ← ScopedHMInterpretation.checkTyped node types slots ids rows Δ env caller walked.bounds derivation
    (by simpa only [Expr.stripFound] using walked.runtimeReady)
  pure ⟨typed, walked.nodes⟩

#print axioms checkLocated
#print axioms completeScopedSpine
#print axioms walkScoped
#print axioms walk

end FHM.Bounds.RecursiveHMWalk
