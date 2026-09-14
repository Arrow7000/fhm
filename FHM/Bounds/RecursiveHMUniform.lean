import FHM.Bounds.RecursiveHMCaller
import FHM.Bounds.HMDeclaredGroup
import FHM.Bounds.HMDeclaredCoordinates

/-! Every recursive RHS specializes through ONE uniform full group HM map.
Member counts specialize first. Checked common captures remove that count
transport from the environment; full HM insertion then changes all group vectors
uniformly, including slots unused by this member. Exact implementation and demand
bounds remain separate. The initial closed-group body slice below consumes
ordered generalized exports only after all universal member proofs exist. -/

namespace FHM.Bounds.RecursiveHMUniform

open RecursiveHMJudgement SchemeSpecialization CountSubstitution ScopedScheme

def actual {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    (counts : List Count) (f : Nat → BoundsTy) : BoundsTy :=
  mapFree f (bounds (s.counts.quantified.zip counts) cert.actual)

def demand {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    (counts : List Count) (f : Nat → BoundsTy) : BoundsTy :=
  mapFree f (bounds (s.counts.quantified.zip counts) cert.opening.bounds)

/-- A member reads precisely its own slots from the uniform group map. Counts
    in those full arguments are inserted after source telescope substitution. -/
theorem demand_instance {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    (counts : List Count) (f : Nat → BoundsTy)
    (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (fixed : ∀ i ∈ s.hm.body.freeVars, f i = .fvar i) :
    demand cert counts f = TypeSubstitution.combined (s.counts.quantified.zip counts)
      (SchemeUse.vector (cert.opening.ids.map f)) s.counts.body := by
  rw [demand, ← RecursiveHMContract.opaque_count_coherence cert.opening,
    RecursiveHMContract.map_combined s _ _ f lc fixed]
  simp only [RecursiveHMContract.fromOpaque, List.map_map, Function.comp_def, mapFree]

structure Result {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller)
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC) where
  typing : ScopedDerives
    (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
    (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceSlots i)))
    (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts)
    inst.premises (env.map (mapBinding f lc)) rhs (actual cert counts f)
  inclusion : SemanticSub inst.premises (actual cert counts f) (demand cert counts f)
  inScope : BoundsScoped caller (actual cert counts f)

/-- Unlike member-local HM vectors, `f` is the SAME function for every member
    of a group. Its full arguments are inserted only AFTER member count rows. -/
def fromCertified {s found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots)
    {counts caller} (inst : Instance s.counts counts caller)
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, BoundsScoped caller (f i))
    (captured : RecursiveHMEnvironment.Captured s.counts.captures env)
    (fixed : CapturesFixed f env) : Result cert inst f lc := by
  let rows := s.counts.quantified.zip counts
  have countKeep : CountCapturesFixed rows env := by
    intro c hc i hi
    apply lookup_none
    rw [List.map_fst_zip (Nat.le_of_eq inst.arity)]
    exact cert.countFresh c hc i hi
  have typeKeep : CapturesFixed f (env.map (mapCountBinding rows)) := by
    intro c hc i hi
    obtain ⟨original, ho, he⟩ := List.mem_map.mp hc
    cases original with
    | mono β => cases he
    | recursive original =>
        cases he
        exact fixed original ho i hi
  have hc := transportScopedCounts rows inst.finite caller
    (fun row hr => inst.argsScoped row.2 (List.of_mem_zip hr).2) cert.typing countKeep
  have ht := transportScopedTypes f lc caller scope hc typeKeep
  have envFixed := RecursiveHMEnvironment.instantiated inst captured
  have countScope : BoundsScoped caller (bounds rows cert.actual) := by
    apply bounds_scoped cert.actualScope
      (fun row hr => inst.argsScoped row.2 (List.of_mem_zip hr).2)
    intro i hi hn
    rcases List.mem_append.mp hi with hq | hcap
    · have absent := lookup_none_iff.mp hn
      rw [List.map_fst_zip (Nat.le_of_eq inst.arity)] at absent
      exact (absent hq).elim
    · exact inst.capturesScoped i hcap
  refine ⟨?_, SchemeSpecialization.subtype f (inst.subtype cert.inclusion), ?_⟩
  · simpa only [actual, rows, envFixed, CountAlgebra.compose, List.map_nil,
      List.nil_append, ScopedScheme.Instance.premises] using ht
  · exact HMInterpretation.scope_mono (HMInterpretation.map_scope countScope f scope)
      (fun _ hi => (List.mem_append.mp hi).elim id id)

def Result.assuming {s found typeCaptures env rhs sourceTypes sourceSlots}
    {cert : RecursiveHMUniversal.Certified s found typeCaptures env rhs sourceTypes sourceSlots}
    {counts caller} {inst : Instance s.counts counts caller} {f lc}
    (r : Result cert inst f lc) {Δ}
    (premises : inst.Usable Δ) :
    ScopedDerives
      (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
      (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceSlots i)))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts)
      Δ (env.map (mapBinding f lc)) rhs (actual cert counts f) ∧
    SemanticSub Δ (actual cert counts f) (demand cert counts f) :=
  ⟨r.typing.assuming premises, r.inclusion.assuming premises⟩

theorem Result.signature {annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises found typeCaptures env rhs sourceTypes sourceSlots)
    {counts caller} {inst : Instance cert.interface.scheme.counts counts caller} {f lc}
    (r : Result cert.implementation inst f lc)
    (fixed : ∀ i ∈ cert.interface.scheme.hm.body.freeVars, f i = .fvar i) :
    RecursiveHMSigned.BindingOK (quantified ++ captures) (quantified.zip counts)
      (cert.implementation.opening.ids.map f) inst.premises annotation (actual cert.implementation counts f) := by
  refine ⟨cert.interface.hmWF, ?_, cert.interface.source.annotation,
    cert.interface.source.decoded, ?_⟩
  · simpa using cert.implementation.opening.arity
  · change SemanticSub inst.premises (actual cert.implementation counts f)
      (TypeSubstitution.combined (cert.interface.scheme.counts.quantified.zip counts)
        (SchemeUse.vector (cert.implementation.opening.ids.map f)) cert.interface.scheme.counts.body)
    rw [← demand_instance cert.implementation counts f lc fixed]
    exact r.inclusion

def atNode {output path} (node : HMFoundView.AtNode output path)
    {s typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMUniversal.Certified s
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    {counts caller} {inst : Instance s.counts counts caller} {f lc}
    (r : Result cert inst f lc) :
    ScopedHMInterpretation.TypedChecked node
      (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceTypes i)))
      (fun i => mapFree f (bounds (s.counts.quantified.zip counts) (sourceSlots i)))
      (s.counts.quantified ++ s.counts.captures) (s.counts.quantified.zip counts)
      inst.premises (env.map (mapBinding f lc)) caller := by
  refine ⟨actual cert counts f, ⟨?_, r.inScope⟩, r.typing⟩
  rw [actual, HMFoundView.bounds_shape, bounds_shape, cert.shape]
  exact ScopedHMInterpretation.specialization f sourceTypes sourceSlots _ node.original

def atSignedNode {output path} (node : HMFoundView.AtNode output path)
    {annotation quantified captures premises typeCaptures env sourceTypes sourceSlots}
    (cert : RecursiveHMSigned.Certified annotation quantified captures premises
      (ScopedHMInterpretation.AtNode.view node sourceTypes sourceSlots) typeCaptures
      env node.inner.stripFound sourceTypes sourceSlots)
    {counts caller} {inst : Instance cert.interface.scheme.counts counts caller} {f lc}
    (r : Result cert.implementation inst f lc)
    (fixed : ∀ i ∈ cert.interface.scheme.hm.body.freeVars, f i = .fvar i) :
    RecursiveHMSigned.ScopedNodeChecked node
      (fun i => mapFree f (bounds (quantified.zip counts) (sourceTypes i)))
      (fun i => mapFree f (bounds (quantified.zip counts) (sourceSlots i)))
      (quantified ++ captures) (quantified.zip counts) inst.premises
      (env.map (mapBinding f lc)) caller annotation (cert.implementation.opening.ids.map f) :=
  ⟨atNode node cert.implementation r, r.signature cert fixed⟩

/-- Ordered ALL-member universal obligations have one common specialized
    recursive environment, not a family of independently mapped assumptions. -/
inductive Members {output metadata path captures premises typeCaptures env}
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, BoundsScoped caller (f i)) :
    {index : Nat} → {vectors : List (List Nat)} →
    {ps : HMDeclaredGroup.Interfaces output metadata path captures premises typeCaptures index vectors} →
    HMDeclaredGroup.CheckedMembers env ps → Type where
  | nil {index} : Members f lc scope (HMDeclaredGroup.CheckedMembers.nil (index := index))
  | cons {index ids rest}
      {p : HMDeclaredGroup.Member output metadata path index captures premises typeCaptures}
      {tail : HMDeclaredGroup.Interfaces output metadata path captures premises typeCaptures (index + 1) rest}
      {he : p.reconciled.signatureIds = ids}
      {head : HMDeclaredGroup.MemberChecked p env} {ms : HMDeclaredGroup.CheckedMembers env tail} :
      (∀ counts (inst : Instance head.certificate.interface.scheme.counts counts caller),
        Result head.certificate.implementation inst f lc) →
      Members f lc scope ms → Members f lc scope (.cons (he := he) head ms)

def allMembers {output metadata path captures premises typeCaptures env index vectors caller}
    {ps : HMDeclaredGroup.Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : HMDeclaredGroup.CheckedMembers env ps)
    (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
    (scope : ∀ i, BoundsScoped caller (f i)) (fixed : CapturesFixed f env) : Members f lc scope ms :=
  match ms with
  | .nil => .nil
  | .cons head rest =>
      .cons (fun _ inst => fromCertified head.certificate.implementation inst f lc scope head.captured fixed)
        (allMembers rest f lc scope fixed)

/-! The program body has generalized exit bindings, unlike the RHS judgement's
fixed recursive assumptions. Keep this boundary explicit: a body variable use
checks a full HM/count instance, while group introduction requires ALL actual
universal RHS obligations. These initial body rules stay in this assembly module
instead of introducing another parallel file family. -/

inductive BodyBinding where
  | mono (bounds : BoundsTy)
  | exported (scheme : HMCountScheme.Scheme)

/-- One branch path for List refinements and finite Bool coverage. Generalized
    exports remain in the environment behind any newly opened mono fields. -/
inductive BodyBranchContext where
  | list (lo hi : Count) (elem : BoundsTy)
  | bool

def BodyBranchContext.bounds : BodyBranchContext → BoundsTy
  | .list lo hi elem => .list lo hi elem
  | .bool => .custom boolTyName []

def BodyBranchContext.refine : BodyBranchContext → MatchPattern → List Constraint
  | .list lo hi _, p => RecursiveTyping.branchRefine p lo hi
  | .bool, _ => []

def BodyBranchContext.extend : BodyBranchContext → MatchPattern → List BodyBinding → List BodyBinding
  | .list lo hi elem, p, env =>
      if p = .named consCtorName 2 then
        .mono elem :: .mono (.list (.pred lo) (.pred hi) elem) :: env
      else env
  | .bool, _, env => env

def BodyBranchContext.Pattern : BodyBranchContext → MatchPattern → Prop
  | .list _ _ _, p => RecursiveTyping.ListPattern p
  | .bool, p => BoolBranches.Pattern p

instance (ctx : BodyBranchContext) (p : MatchPattern) : Decidable (ctx.Pattern p) := by
  cases ctx <;> unfold BodyBranchContext.Pattern <;> infer_instance

def BodyBranchContext.Covers (Δ : List Constraint) : BodyBranchContext → List (MatchPattern × Expr) → Prop
  | .list lo hi _, branches => ListBranches.Covers Δ ⟨lo, hi⟩ branches
  | .bool, branches => BoolBranches.Covers branches

def BodyBranchContext.checkCoverage (ctx : BodyBranchContext) (Δ : List Constraint)
    (branches : List (MatchPattern × Expr)) : Except String (PLift (ctx.Covers Δ branches)) :=
  match ctx with
  | .list lo hi _ => ListBranches.check Δ ⟨lo, hi⟩ branches
  | .bool => BoolBranches.check branches

private def bodyBranchContext (β : BoundsTy) :
    Except String (Σ ctx : BodyBranchContext, PLift (β = ctx.bounds)) :=
  match β with
  | .list lo hi elem => .ok ⟨.list lo hi elem, ⟨rfl⟩⟩
  | .custom name [] =>
      if hn : name = boolTyName then .ok ⟨.bool, ⟨by subst name; rfl⟩⟩
      else .error "bounds: generalized body match scrutinee is neither List nor Bool"
  | _ => .error "bounds: generalized body match scrutinee is neither List nor Bool"

inductive BodyDerives (ids : List Nat) (rows : Bindings) :
    List Constraint → List BodyBinding → Expr → BoundsTy → Prop where
  | literal {env p} : BodyDerives ids rows Δ env (.primLit p) (boundInfoOfPrimLit p)
  | primBinOp {env op} : BodyDerives ids rows Δ env (.primBinOp op) (Typed.primOpBounds op)
  | nil {env elem} : BodyDerives ids rows Δ env (.ctor nilCtorName) (.list (.lit 0) (.lit 0) elem)
  | boolCtor {env name} : BoolBranches.IsCtor name →
      BodyDerives ids rows Δ env (.ctor name) (.custom boolTyName [])
  | cons {env h t head elem lo hi} :
      BodyDerives ids rows Δ env h head → BodyDerives ids rows Δ env t (.list lo hi elem) →
      SemanticSub Δ head elem → BodyDerives ids rows Δ env (.app (.app (.ctor consCtorName) h) t)
        (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem)
  | varMono {env i β} : env[i]? = some (.mono β) → BodyDerives ids rows Δ env (.var i) β
  | varExported {env i s found caller} : env[i]? = some (.exported s) →
      (used : HMCountScheme.Use s Δ found caller) → BodyDerives ids rows Δ env (.var i) used.bounds
  | app {env f arg domain actual result} :
      BodyDerives ids rows Δ env f (.arrow domain result) → BodyDerives ids rows Δ env arg actual →
      SemanticSub Δ actual domain → BodyDerives ids rows Δ env (.app f arg) result
  | lambda {env ann body param result} :
      ScopedHMAnnotation.ParamOK BoundsTy.fvar BoundsTy.bvar ids rows Δ ann param →
      BodyDerives ids rows Δ (.mono param :: env) body result →
      BodyDerives ids rows Δ env (.lambda ann body) (.arrow param result)
  | letMono {env ann rhs body actual result} :
      ScopedHMAnnotation.BindingOK BoundsTy.fvar BoundsTy.bvar ids rows Δ ann actual →
      BodyDerives ids rows Δ env rhs actual → BodyDerives ids rows Δ (.mono actual :: env) body result →
      BodyDerives ids rows Δ env (.letIn ann rhs body) result
  | match_ {env scrut branches result} {ctx : BodyBranchContext} {actuals : Nat → BoundsTy} :
      BodyDerives ids rows Δ env scrut ctx.bounds → ctx.Covers Δ branches →
      (∀ br ∈ branches, ctx.Pattern br.1) →
      (∀ i br, branches[i]? = some br →
        BodyDerives ids rows (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2 (actuals i)) →
      (∀ i br, branches[i]? = some br → SemanticSub (Δ ++ ctx.refine br.1) (actuals i) result) →
      BodyDerives ids rows Δ env (.match_ scrut branches) result
  | letRec {output metadata path vectors captures premises bodyTypes bodyResult}
      (g : HMDeclaredGroup.Checked output metadata path vectors captures premises bodyTypes []) :
      (∀ caller (f : Nat → BoundsTy) (lc : ∀ i, (Synth.BoundsTy.toTy (f i)).IsLC)
        (scope : ∀ i, BoundsScoped caller (f i))
        (_fixed : CapturesFixed f (g.interfaces.contracts.map Binding.recursive ++ [])),
        Members f lc scope g.members) →
      BodyDerives ids rows Δ (g.exports.map BodyBinding.exported) g.body.stripFound bodyResult →
      BodyDerives ids rows Δ [] (.letRec g.annotations (g.rhss.map Expr.stripFound) g.body.stripFound) bodyResult

structure BodyResult (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BodyBinding) (e : Expr) where
  hm : Ty
  bounds : BoundsTy
  root : Typed.rootHM? e = some hm.eraseBounds
  shape : Synth.BoundsTy.toTy bounds = hm.eraseBounds
  typing : BodyDerives ids rows Δ env e.stripFound bounds
  inScope : BoundsScoped caller bounds
  nodes : List Typed.NodeResult

private def finishBody {ids rows caller Δ env e} (path : CorePath) (hm : Ty) (β : BoundsTy)
    (root : Typed.rootHM? e = some hm.eraseBounds) (typing : BodyDerives ids rows Δ env e.stripFound β)
    (children : List Typed.NodeResult) : Except String (BodyResult ids rows caller Δ env e) := do
  let shape ← match BinderBridge.equalTy (Synth.BoundsTy.toTy β) hm.eraseBounds with
    | some h => pure h | none => throw "bounds: generalized body result disagrees with original found payload"
  if h : boundsScopedBool caller β = true then
    pure ⟨hm, β, root, shape.down, typing, boundsScopedBool_sound h,
      ⟨path, hm.eraseBounds, some β⟩ :: children⟩
  else throw "bounds: generalized body result counts escape caller scope"

private structure BodyBranches (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BodyBinding) (ctx : BodyBranchContext)
    (branches : List (MatchPattern × Expr)) where
  actuals : Nat → BoundsTy
  typing : ∀ i br, branches[i]? = some br →
    BodyDerives ids rows (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2.stripFound (actuals i)
  patterns : ∀ br ∈ branches, ctx.Pattern br.1
  bounds : Option BoundsTy
  inclusions : ∀ i br, branches[i]? = some br →
    match bounds with | none => False | some β => SemanticSub (Δ ++ ctx.refine br.1) (actuals i) β
  nodes : List Typed.NodeResult

private def prependBodyBranches {ids rows caller Δ env br branches} {ctx : BodyBranchContext}
    (head : BodyResult ids rows caller (Δ ++ ctx.refine br.1) (ctx.extend br.1 env) br.2)
    (hp : ctx.Pattern br.1) (tail : BodyBranches ids rows caller Δ env ctx branches)
    (β : BoundsTy) (hh : SemanticSub (Δ ++ ctx.refine br.1) head.bounds β)
    (ht : ∀ i arm, branches[i]? = some arm → SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) β) :
    BodyBranches ids rows caller Δ env ctx (br :: branches) where
  actuals := fun i => match i with | 0 => head.bounds | i + 1 => tail.actuals i
  typing := by
    intro i arm h
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst arm; exact head.typing
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

private theorem body_match_typing {ids rows caller Δ env branches β} {ctx : BodyBranchContext} {scrut : Expr}
    (hs : BodyDerives ids rows Δ env scrut.stripFound ctx.bounds)
    (arms : BodyBranches ids rows caller Δ env ctx branches) (hb : arms.bounds = some β)
    (hc : ctx.Covers Δ (Expr.stripFoundBranches branches)) :
    BodyDerives ids rows Δ env (Expr.match_ scrut branches).stripFound β := by
  simp only [Expr.stripFound]
  apply BodyDerives.match_ (actuals := arms.actuals) hs hc
  · intro arm ha
    rw [RecursiveHMWalk.stripBranches] at ha
    rcases List.mem_map.mp ha with ⟨br, hm, rfl⟩
    exact arms.patterns br hm
  · intro i arm ha
    rcases RecursiveHMWalk.strip_index ha with ⟨br, hm, rfl⟩
    exact arms.typing i br hm
  · intro i arm ha
    rcases RecursiveHMWalk.strip_index ha with ⟨br, hm, rfl⟩
    simpa only [hb] using arms.inclusions i br hm

private theorem body_path_assuming (Δ Γ : List Constraint) :
    (⟨Δ ++ Γ, Δ⟩ : ForallProblem).Valid := fun _ h c hc => h c (List.mem_append_left Γ hc)

mutual
/-- Initial generalized body slice: literals, List origins, scalar operators,
    lambdas, mono locals and origin-backed single-argument exported calls.
    Generalized local lets, nested groups and deferred spines fail
    explicitly until their SAME-interface assembly rules are implemented. -/
def walkBody (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (env : List BodyBinding) (path : CorePath) (e : Expr) (schemes : BinderSchemeMap)
    (expected : Option BoundsTy := none) : Except String (BodyResult ids rows caller Δ env e) := do
  match e with
  | .found hm (.primLit p) =>
      finishBody path hm (boundInfoOfPrimLit p) rfl (by simpa only [Expr.stripFound] using BodyDerives.literal) []
  | .found hm (.primBinOp op) =>
      finishBody path hm (Typed.primOpBounds op) rfl (by simpa only [Expr.stripFound] using BodyDerives.primBinOp) []
  | .found hm (.ctor name) =>
      if hn : name = nilCtorName then
        match hm.eraseBounds with
        | .customTy n [a] =>
            if n = listTyName then
              let elem ← match expected with
                | some (.list _ _ elem) => pure elem
                | _ => Typed.shapeTop a
              finishBody path hm (.list (.lit 0) (.lit 0) elem) rfl
                (by subst name; simpa only [Expr.stripFound] using BodyDerives.nil) []
            else throw "bounds: generalized body Nil has a non-List found payload"
        | _ => throw "bounds: generalized body Nil has a non-List found payload"
      else if hb : BoolBranches.IsCtor name then
        finishBody path hm (.custom boolTyName []) rfl
          (by simpa only [Expr.stripFound] using BodyDerives.boolCtor hb) []
      else throw "bounds: unsupported standalone constructor in generalized body"
  | .found hm (.var i) =>
      match hv : env[i]? with
      | some (.mono β) =>
          finishBody path hm β rfl
            (by simpa only [Expr.stripFound] using BodyDerives.varMono hv) []
      | some (.exported s) =>
          if s.hm.paramCount == 0 && s.counts.quantified.isEmpty then
            let used ← HMCountScheme.check s Δ hm [] [] caller
            finishBody path hm used.bounds rfl
              (by simpa only [Expr.stripFound] using BodyDerives.varExported hv used) []
          else throw "bounds: exported polymorphic use needs origin-backed arguments"
      | none => throw "bounds: generalized body variable outside binding environment"
  | .found hm (.lambda ann body) =>
      match hm.eraseBounds with
      | .arrow paramHM _ =>
          let paramHint := match expected with | some (.arrow a _) => some a | _ => none
          let bodyHint := match expected with | some (.arrow _ b) => some b | _ => none
          let param ← RecursiveHMAnnotation.chooseScopedParam BoundsTy.fvar BoundsTy.bvar ids rows caller Δ ann paramHM paramHint
          let result ← walkBody ids rows caller Δ (.mono param.bounds :: env) (path ++ [.lambdaBody]) body schemes bodyHint
          finishBody path hm (.arrow param.bounds result.bounds) rfl
            (by simpa only [Expr.stripFound] using BodyDerives.lambda param.obligation result.typing) result.nodes
      | _ => throw "bounds: generalized body lambda has a non-arrow found payload"
  | .found hm (.app (.found partialHM (.app (.found ctorHM (.ctor name)) head)) tail) =>
      if hn : name = consCtorName then
        let headHint := match expected with | some (.list _ _ elem) => some elem | _ => none
        let h ← walkBody ids rows caller Δ env (path ++ [.appFun, .appArg]) head schemes headHint
        let t ← walkBody ids rows caller Δ env (path ++ [.appArg]) tail schemes
          (some (.list (.lit 0) .inf h.bounds))
        match ht : t.bounds with
        | .list lo hi elem =>
            let _ ← match BinderBridge.equalTy ctorHM.eraseBounds (.arrow h.hm.eraseBounds (.arrow t.hm.eraseBounds t.hm.eraseBounds)) with
              | some h => pure h | none => throw "bounds: generalized body Cons constructor payload mismatch"
            let _ ← match BinderBridge.equalTy partialHM.eraseBounds (.arrow t.hm.eraseBounds t.hm.eraseBounds) with
              | some h => pure h | none => throw "bounds: generalized body partial Cons payload mismatch"
            let sub ← Typed.subtype Δ h.bounds elem
            finishBody path hm (.list (.add lo (.lit 1)) (.add hi (.lit 1)) elem) rfl
              (by subst name; simpa only [Expr.stripFound] using
                BodyDerives.cons h.typing (by simpa only [ht] using t.typing) sub.down)
              (⟨path ++ [.appFun], partialHM.eraseBounds, none⟩ ::
                ⟨path ++ [.appFun, .appFun], ctorHM.eraseBounds, none⟩ :: h.nodes ++ t.nodes)
        | _ => throw "bounds: generalized body Cons tail is not a List"
      else throw "bounds: generalized body constructor application unsupported"
  | .found hm (.app (.found functionHM (.var i)) arg) =>
      match hv : env[i]? with
      | some (.exported s) =>
          match s.counts.body with
          | .arrow domain _ =>
              let actual ← walkBody ids rows caller Δ env (path ++ [.appArg]) arg schemes
              let types ← StructuralApplication.propose domain actual.bounds s.hm.paramCount
              let counts ← CountProposal.proposeArguments s.counts.quantified s.counts.body [actual.bounds]
              let used ← HMCountScheme.check s Δ functionHM counts types caller
              match hu : used.bounds with
              | .arrow param result =>
                  let sub ← Typed.subtype Δ actual.bounds param
                  let fn ← finishBody (ids := ids) (rows := rows) (caller := caller)
                    (Δ := Δ) (env := env) (e := .found functionHM (.var i))
                    (path ++ [.appFun]) functionHM used.bounds rfl
                    (by simpa only [Expr.stripFound] using BodyDerives.varExported hv used) []
                  finishBody path hm result rfl
                    (by simpa only [Expr.stripFound] using
                      BodyDerives.app (by simpa only [hu] using
                        (BodyDerives.varExported (ids := ids) (rows := rows) hv used)) actual.typing sub.down)
                    (fn.nodes ++ actual.nodes)
              | _ => throw "bounds: exported body use is not an arrow"
          | _ => throw "bounds: exported body application has a non-arrow contract"
      | _ =>
          let fn ← walkBody ids rows caller Δ env (path ++ [.appFun]) (.found functionHM (.var i)) schemes
          let actual ← walkBody ids rows caller Δ env (path ++ [.appArg]) arg schemes
          match hf : fn.bounds with
          | .arrow domain result =>
              let sub ← Typed.subtype Δ actual.bounds domain
              finishBody path hm result rfl
                (by simpa only [Expr.stripFound] using
                  (BodyDerives.app (by simpa only [Expr.stripFound, hf] using fn.typing) actual.typing sub.down))
                (fn.nodes ++ actual.nodes)
          | _ => throw "bounds: generalized body function is not an arrow"
  | .found hm (.app fn arg) =>
      let function ← walkBody ids rows caller Δ env (path ++ [.appFun]) fn schemes
      let actual ← walkBody ids rows caller Δ env (path ++ [.appArg]) arg schemes
      match hf : function.bounds with
      | .arrow domain result =>
          let sub ← Typed.subtype Δ actual.bounds domain
          finishBody path hm result rfl
            (by simpa only [Expr.stripFound] using
              (BodyDerives.app (by simpa only [hf] using function.typing) actual.typing sub.down))
            (function.nodes ++ actual.nodes)
      | _ => throw "bounds: generalized body function is not an arrow"
  | .found hm (.letIn ann rhs body) =>
      let hint ← RecursiveHMAnnotation.scopedBindingHint BoundsTy.fvar BoundsTy.bvar ids rows caller ann
      let actual ← walkBody ids rows caller Δ env (path ++ [.letRhs]) rhs schemes hint
      let _ ← RecursiveHMWalk.checkLocalInterface ann schemes (.letIn path) actual.hm
      let obligation ← RecursiveHMAnnotation.checkScopedBinding BoundsTy.fvar BoundsTy.bvar ids rows caller Δ ann actual.bounds
      let result ← walkBody ids rows caller Δ (.mono actual.bounds :: env) (path ++ [.letBody]) body schemes expected
      finishBody path hm result.bounds rfl
        (by simpa only [Expr.stripFound] using
          (BodyDerives.letMono obligation.down actual.typing result.typing))
        (actual.nodes ++ result.nodes)
  | .found hm (.match_ scrut branches) =>
      let input ← walkBody ids rows caller Δ env (path ++ [.matchScrut]) scrut schemes
      -- Equality of full bounds, not merely HM shape, connects scrutinee origins
      -- with constructor refinements and freshly opened field bindings.
      let ⟨ctx, hin⟩ ← bodyBranchContext input.bounds
      let coverage ← ctx.checkCoverage Δ (Expr.stripFoundBranches branches)
      let arms ← walkBodyBranches ids rows caller Δ env ctx path branches 0 schemes expected
      match hb : arms.bounds with
      | none => throw "bounds: generalized body match has no result-producing branch"
      | some β =>
          finishBody path hm β rfl
            (by simpa only [Expr.stripFound] using
              body_match_typing (by simpa only [hin.down] using input.typing) arms hb coverage.down)
            (input.nodes ++ arms.nodes)
  | .found _ (.letRec _ _ _) => throw "bounds: nested generalized recursive groups are not supported yet"
  | _ => throw "bounds: generalized body lacks an original found node"
termination_by (sizeOf e, 1)

private def walkBodyBranches (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List BodyBinding) (ctx : BodyBranchContext)
    (path : CorePath) (branches : List (MatchPattern × Expr)) (index : Nat)
    (schemes : BinderSchemeMap) (expected : Option BoundsTy) :
    Except String (BodyBranches ids rows caller Δ env ctx branches) := do
  match branches with
  | [] => pure ⟨(fun _ => .prim .int), (by intros; contradiction), (by intros; contradiction),
      none, (by intros; contradiction), []⟩
  | br :: rest =>
      if hp : ctx.Pattern br.1 then
        let head ← walkBody ids rows caller (Δ ++ ctx.refine br.1) (ctx.extend br.1 env)
          (path ++ [.matchBranch index]) br.2 schemes expected
        let tail ← walkBodyBranches ids rows caller Δ env ctx path rest (index + 1) schemes expected
        match expected with
        | some β =>
            let hs ← Typed.subtype (Δ ++ ctx.refine br.1) head.bounds β
            match ht : tail.bounds with
            | none => pure (prependBodyBranches head hp tail β hs.down (by
                intro i arm ha
                have impossible := tail.inclusions i arm ha
                simp only [ht] at impossible))
            | some τ =>
                let ts ← Typed.subtype Δ τ β
                pure (prependBodyBranches head hp tail β hs.down (by
                  intro i arm ha
                  have sub : SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) τ :=
                    by simpa only [ht] using tail.inclusions i arm ha
                  exact sub.trans (ts.down.assuming (body_path_assuming _ _))))
        | none =>
            match ht : tail.bounds with
            | none => pure (prependBodyBranches head hp tail head.bounds (SemanticSub.refl _ _) (by
                intro i arm ha
                have impossible := tail.inclusions i arm ha
                simp only [ht] at impossible))
            | some τ =>
                let ⟨β, merged⟩ ← BranchMerge.combine .upper head.bounds τ
                let subs := merged.down.sound Δ
                pure (prependBodyBranches head hp tail β (subs.1.assuming (body_path_assuming _ _)) (by
                  intro i arm ha
                  have sub : SemanticSub (Δ ++ ctx.refine arm.1) (tail.actuals i) τ :=
                    by simpa only [ht] using tail.inclusions i arm ha
                  exact sub.trans (subs.2.assuming (body_path_assuming _ _))))
      else throw "bounds: generalized body match has an unsupported pattern or constructor arity"
termination_by (sizeOf branches, 0)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (cases br; simp_all; omega)
end

private def memberNodes {output metadata path captures premises typeCaptures env index vectors}
    {ps : HMDeclaredGroup.Interfaces output metadata path captures premises typeCaptures index vectors}
    (ms : HMDeclaredGroup.CheckedMembers env ps) : List Typed.NodeResult :=
  match ms with
  | .nil => []
  | .cons head rest => head.rhs.located.nodes ++ memberNodes rest

/-- Closed-group vertical slice. Only after all universal RHSs accept do their
    generalized exit bindings become available to actual source body checking. -/
def checkBody {output metadata path vectors captures premises bodyTypes}
    (g : HMDeclaredGroup.Checked output metadata path vectors captures premises bodyTypes [])
    (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (schemes : BinderSchemeMap) (expected : Option BoundsTy := none) :
    Except String (BodyResult ids rows caller Δ []
      (.found g.originalHM (.letRec g.annotations g.rhss g.body))) := do
  let body ← walkBody ids rows caller Δ (g.exports.map BodyBinding.exported)
    (path ++ [.letRecBody]) g.body schemes expected
  finishBody path g.originalHM body.bounds rfl
    (by simpa only [Expr.stripFound] using
      BodyDerives.letRec g (fun _ f lc scope fixed => allMembers g.members f lc scope fixed) body.typing)
    (memberNodes g.members ++ body.nodes)

/-- A source-linked closed ROOT recursive program, not a general program-prefix
    or nested-group adapter. The body certificate is indexed by the exact input
    artifact, while retaining the actual all-member coordinate assembly. -/
structure ProgramResult (output : Expr) (metadata : Scope.Metadata) where
  assembled : HMDeclaredCoordinates.Result output metadata [] [] [] [] []
  body : BodyResult [] [] [] [] [] output

/-- No supplied opaque vectors, reconstructed RHSs or legacy fallback. Source
    annotations and real mono-local machine facts keep their distinct roles.
    `expected` is synthesis guidance, not an asserted result inclusion. -/
def checkClosedProgram (output : Expr) (metadata : Scope.Metadata)
    (schemes : BinderSchemeMap := []) (expected : Option BoundsTy := none) :
    Except String (ProgramResult output metadata) := do
  let assembled ← HMDeclaredCoordinates.check output metadata [] (schemes := schemes)
  let body ← checkBody assembled.checked [] [] [] [] schemes expected
  have sourceEq : output = .found assembled.checked.originalHM
      (.letRec assembled.checked.annotations assembled.checked.rhss assembled.checked.body) := by
    simpa only [Expr.atCorePath, Option.some.injEq] using assembled.checked.source
  pure ⟨assembled, by simpa only [sourceEq] using body⟩

#print axioms fromCertified
#print axioms demand_instance
#print axioms Result.assuming
#print axioms Result.signature
#print axioms atSignedNode
#print axioms allMembers
#print axioms walkBody
#print axioms checkBody
#print axioms checkClosedProgram

end FHM.Bounds.RecursiveHMUniform
