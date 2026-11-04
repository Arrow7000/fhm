import FHM.PatComp.Trace
import FHM.Surface.Span
import FHM.SurfaceBridge
import FHM.InferW

/-! # Construction-time Surface → Input provenance

Production lowering preserves partial annotations in `InferInput` and
carries provenance through `PatComp`'s shared emission trace. Source IDs are
assigned to the parser's span tree before lowering; the lowerer records both
directions of the term-path correspondence during construction.
`inferWithProvenance` calls the canonical worker once, retaining those paths to
join its editor maps and returning its exact completed Core payload. Source
spans identify artifacts; they do not allocate or identify anonymous type holes.
Successful construction is proved to produce exactly the shared structural
Surface lowerer's term, so its accepted payload has the canonical lowering
derivation. Metadata joins remain operational; the complete-Core safety
demonstration in `Headlines` is a separate specialization.
-/

open Surface.Span

namespace SurfaceBridge.Provenance

abbrev SourceId := Nat

structure SourceNode where
  id : SourceId
  span : Span
  authored : Bool := true
  deriving Repr, DecidableEq, BEq

instance : Inhabited SourceNode := ⟨⟨0, Span.empty, true⟩⟩

/-- The spanned parse mirror after a deterministic preorder ID pass. -/
inductive IdentifiedExpr where
  | leaf (source : SourceNode)
  | pair (source : SourceNode) (a b : IdentifiedExpr)
  | cons (source : SourceNode) (head tail : IdentifiedExpr)
  | list (source : SourceNode) (items : List IdentifiedExpr)
  | lambda (source : SourceNode) (body : IdentifiedExpr)
  | app (source : SourceNode) (fn arg : IdentifiedExpr)
  | letIn (source : SourceNode) (rhs body : IdentifiedExpr)
  | letRecIn (source : SourceNode) (rhss : List IdentifiedExpr) (body : IdentifiedExpr)
  | ife (source : SourceNode) (cond then_ else_ : IdentifiedExpr)
  | match_ (source : SourceNode) (scrut : IdentifiedExpr) (arms : List IdentifiedExpr)
  deriving Repr

instance : Inhabited IdentifiedExpr := ⟨.leaf default⟩

def IdentifiedExpr.source : IdentifiedExpr → SourceNode
  | .leaf n | .pair n .. | .cons n .. | .list n .. | .lambda n ..
  | .app n .. | .letIn n .. | .letRecIn n .. | .ife n .. | .match_ n .. => n

mutual
private def IdentifiedExpr.asGenerated : IdentifiedExpr → IdentifiedExpr
  | .leaf n => .leaf { n with authored := false }
  | .pair n a b => .pair { n with authored := false } a.asGenerated b.asGenerated
  | .cons n a b => .cons { n with authored := false } a.asGenerated b.asGenerated
  | .app n a b => .app { n with authored := false } a.asGenerated b.asGenerated
  | .letIn n a b => .letIn { n with authored := false } a.asGenerated b.asGenerated
  | .list n items => .list { n with authored := false } (generatedList items)
  | .lambda n body => .lambda { n with authored := false } body.asGenerated
  | .letRecIn n rhss body => .letRecIn { n with authored := false }
      (generatedList rhss) body.asGenerated
  | .ife n c t f => .ife { n with authored := false }
      c.asGenerated t.asGenerated f.asGenerated
  | .match_ n scrut arms => .match_ { n with authored := false }
      scrut.asGenerated (generatedList arms)

private def generatedList : List IdentifiedExpr → List IdentifiedExpr
  | [] => []
  | e :: es => e.asGenerated :: generatedList es
end

/-- Hide only an administrative expression root, retaining authored children. -/
def IdentifiedExpr.asGeneratedRoot : IdentifiedExpr → IdentifiedExpr
  | .leaf n => .leaf { n with authored := false }
  | .pair n a b => .pair { n with authored := false } a b
  | .cons n a b => .cons { n with authored := false } a b
  | .list n items => .list { n with authored := false } items
  | .lambda n body => .lambda { n with authored := false } body
  | .app n fn arg => .app { n with authored := false } fn arg
  | .letIn n rhs body => .letIn { n with authored := false } rhs body
  | .letRecIn n rhss body => .letRecIn { n with authored := false } rhss body
  | .ife n c t f => .ife { n with authored := false } c t f
  | .match_ n scrut arms => .match_ { n with authored := false } scrut arms

mutual
def identifyFrom (next : SourceId) : SpannedExpr → SourceId × IdentifiedExpr
  | .generated expr =>
      let (next, identified) := identifyFrom next expr
      (next, identified.asGenerated)
  | .generatedRoot expr =>
      let (next, identified) := identifyFrom next expr
      (next, identified.asGeneratedRoot)
  | .leaf span => (next + 1, .leaf ⟨next, span, true⟩)
  | .pair span a b =>
      let root := next
      let (next, a') := identifyFrom (next + 1) a
      let (next, b') := identifyFrom next b
      (next, .pair ⟨root, span, true⟩ a' b')
  | .cons span h t =>
      let root := next
      let (next, h') := identifyFrom (next + 1) h
      let (next, t') := identifyFrom next t
      (next, .cons ⟨root, span, true⟩ h' t')
  | .list span items =>
      let root := next
      let (next, items') := identifyListFrom (next + 1) items
      (next, .list ⟨root, span, true⟩ items')
  | .lambda span body =>
      let root := next
      let (next, body') := identifyFrom (next + 1) body
      (next, .lambda ⟨root, span, true⟩ body')
  | .app span fn arg =>
      let root := next
      let (next, fn') := identifyFrom (next + 1) fn
      let (next, arg') := identifyFrom next arg
      (next, .app ⟨root, span, true⟩ fn' arg')
  | .letIn span rhs body =>
      let root := next
      let (next, rhs') := identifyFrom (next + 1) rhs
      let (next, body') := identifyFrom next body
      (next, .letIn ⟨root, span, true⟩ rhs' body')
  | .letRecIn span rhss body =>
      let root := next
      let (next, rhss') := identifyListFrom (next + 1) rhss
      let (next, body') := identifyFrom next body
      (next, .letRecIn ⟨root, span, true⟩ rhss' body')
  | .ife span cond then_ else_ =>
      let root := next
      let (next, cond') := identifyFrom (next + 1) cond
      let (next, then') := identifyFrom next then_
      let (next, else') := identifyFrom next else_
      (next, .ife ⟨root, span, true⟩ cond' then' else')
  | .match_ span scrut arms =>
      let root := next
      let (next, scrut') := identifyFrom (next + 1) scrut
      let (next, arms') := identifyListFrom next arms
      (next, .match_ ⟨root, span, true⟩ scrut' arms')

def identifyListFrom (next : SourceId) : List SpannedExpr → SourceId × List IdentifiedExpr
  | [] => (next, [])
  | e :: es =>
      let (next, e') := identifyFrom next e
      let (next, es') := identifyListFrom next es
      (next, e' :: es')
end

/-- Assign IDs before lowering. IDs are deterministic preorder indices for one
    parsed snapshot; no claim is made that they survive arbitrary text edits. -/
def identify (s : SpannedExpr) : IdentifiedExpr := (identifyFrom 0 s).2

/-- A span-free mirror for diagnostic probes assembled from Surface syntax.
    Production editor requests use the parser's real span tree. -/
partial def diagnosticSpans (e : Surface.Expr) : SpannedExpr :=
  match e with
  | .pair a b => .pair .empty (diagnosticSpans a) (diagnosticSpans b)
  | .cons a b => .cons .empty (diagnosticSpans a) (diagnosticSpans b)
  | .list es => .list .empty (es.map diagnosticSpans)
  | .lambda _ _ b => .lambda .empty (diagnosticSpans b)
  | .app f a => .app .empty (diagnosticSpans f) (diagnosticSpans a)
  | .letIn _ _ _ _ r b => .letIn .empty (diagnosticSpans r) (diagnosticSpans b)
  | .letRecIn bs b => .letRecIn .empty (bs.map fun b => diagnosticSpans b.rhs) (diagnosticSpans b)
  | .ife c t f => .ife .empty (diagnosticSpans c) (diagnosticSpans t) (diagnosticSpans f)
  | .match_ s arms => .match_ .empty (diagnosticSpans s) (arms.map fun a => diagnosticSpans a.2)
  | _ => .leaf .empty

mutual
def IdentifiedExpr.nodes : IdentifiedExpr → List SourceNode
  | .leaf n => [n]
  | .pair n a b | .cons n a b | .app n a b | .letIn n a b =>
      n :: a.nodes ++ b.nodes
  | .list n items => n :: IdentifiedExpr.nodesList items
  | .lambda n body => n :: body.nodes
  | .letRecIn n rhss body => n :: IdentifiedExpr.nodesList rhss ++ body.nodes
  | .ife n c t f => n :: c.nodes ++ t.nodes ++ f.nodes
  | .match_ n scrut arms => n :: scrut.nodes ++ IdentifiedExpr.nodesList arms

def IdentifiedExpr.nodesList : List IdentifiedExpr → List SourceNode
  | [] => []
  | e :: es => e.nodes ++ IdentifiedExpr.nodesList es
end

inductive OriginAbsence where
  | eliminatedByPatternCompilation
  | unsupportedSurfaceForm
  deriving Repr, DecidableEq, BEq

inductive OriginTarget where
  | present (paths : List CorePath)
  | absent (reason : OriginAbsence)
  deriving Repr, DecidableEq, BEq

def OriginTarget.belowPath (pre : CorePath) : OriginTarget → OriginTarget
  | .present paths => .present (paths.map (pre ++ ·))
  | .absent reason => .absent reason

inductive GenerationReason where
  | pairCtor
  | pairPartialApp
  | consCtor
  | consPartialApp
  | listCtor (spineIndex : Nat)
  | listPartialApp (spineIndex : Nat)
  | listTailApp (spineIndex : Nat)
  | valueParamLambda (paramIndex : Nat)
  | patternBinding
  | patternLambdaScrutinee
  | patternCompilation (node : PatComp.GeneratedNode)
  deriving Repr, DecidableEq, BEq

inductive OriginKind where
  | authored
  | generated (reason : GenerationReason)
  deriving Repr, DecidableEq, BEq

structure Origin where
  source : SourceNode
  kind : OriginKind
  deriving Repr, DecidableEq, BEq

inductive SurfaceBinderSite where
  | lambda (owner : SourceId)
  | letIn (owner : SourceId)
  | letRec (owner : SourceId) (member : Nat)
  | letParam (owner : SourceId) (param : Nat)
  | letRecParam (owner : SourceId) (member param : Nat)
  | patCapture (owner : SourceId) (arm capture : Nat)
  deriving Repr, DecidableEq, BEq

/-- Binder correspondence records both compiler elimination and cloning. -/
inductive BinderOriginTarget where
  | present (sites : List CoreBinderSite)
  | absent (reason : OriginAbsence)
  deriving Repr, DecidableEq, BEq

def BinderOriginTarget.belowPath (pre : CorePath) : BinderOriginTarget → BinderOriginTarget
  | .present sites => .present (sites.map fun site => pre.foldr CoreBinderSite.below site)
  | .absent reason => .absent reason

abbrev SourceTargetMap := List (SourceId × OriginTarget)
abbrev CoreOriginMap := List (CorePath × Origin)
abbrev BinderTargetMap := List (SurfaceBinderSite × BinderOriginTarget)

structure Lowered (Term : Type := Expr) where
  expr : Term
  sourceNodes : List SourceNode
  sourceTargets : SourceTargetMap
  coreOrigins : CoreOriginMap
  binderTargets : BinderTargetMap

namespace Lowered

def belowPath {Term : Type} (pre : CorePath) (r : Lowered Term) : Lowered Term :=
  { r with
    sourceTargets := r.sourceTargets.map fun (id, target) => (id, target.belowPath pre)
    coreOrigins := r.coreOrigins.map fun (path, origin) => (pre ++ path, origin)
    binderTargets := r.binderTargets.map fun (source, target) =>
      (source, target.belowPath pre) }

def metadata {Term : Type} (expr : Term) (parts : List (Lowered Term)) : Lowered Term :=
  { expr
    sourceNodes := parts.flatMap (fun r => r.sourceNodes)
    sourceTargets := parts.flatMap (fun r => r.sourceTargets)
    coreOrigins := parts.flatMap (fun r => r.coreOrigins)
    binderTargets := parts.flatMap (fun r => r.binderTargets) }

/-- Completion changes annotation syntax while retaining construction-time
source paths. The expression payload changes only at this explicit boundary. -/
def mapExpr {Term Result : Type} (r : Lowered Term) (f : Term → Result) : Lowered Result :=
  { expr := f r.expr
    sourceNodes := r.sourceNodes
    sourceTargets := r.sourceTargets
    coreOrigins := r.coreOrigins
    binderTargets := r.binderTargets }

end Lowered

def authoredRoot {Term : Type} (source : SourceNode) (expr : Term) : Lowered Term :=
  { expr
    sourceNodes := [source]
    sourceTargets := [(source.id, .present [[]])]
    coreOrigins := [([], ⟨source, if source.authored then .authored else .generated .patternBinding⟩)]
    binderTargets := [] }

def generatedOrigin (source : SourceNode) (path : CorePath) (reason : GenerationReason) :
    CorePath × Origin :=
  (path, ⟨source, .generated reason⟩)

def combineAuthored {Term : Type} (source : SourceNode) (expr : Term) (parts : List (Lowered Term))
    (generated : CoreOriginMap := []) (binders : BinderTargetMap := []) : Lowered Term :=
  let children := Lowered.metadata expr parts
  { expr
    sourceNodes := source :: children.sourceNodes
    sourceTargets := (source.id, .present [[]]) :: children.sourceTargets
    coreOrigins := ([], ⟨source, if source.authored then .authored else .generated .patternBinding⟩) :: generated ++ children.coreOrigins
    binderTargets := binders ++ children.binderTargets }

mutual
def logicalCorePaths : Expr → List CorePath
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => [[]]
  | .lambda _ body => [] :: (logicalCorePaths body).map (.lambdaBody :: ·)
  | .app fn arg => [] ::
      (logicalCorePaths fn).map (.appFun :: ·) ++
      (logicalCorePaths arg).map (.appArg :: ·)
  | .letIn _ rhs body => [] ::
      (logicalCorePaths rhs).map (.letRhs :: ·) ++
      (logicalCorePaths body).map (.letBody :: ·)
  | .match_ scrut branches => [] ::
      (logicalCorePaths scrut).map (.matchScrut :: ·) ++
      logicalBranchPaths 0 branches
  | .letRec bindings body => [] ::
      logicalBindingPaths 0 bindings ++
      (logicalCorePaths body).map (.letRecBody :: ·)

def logicalBranchPaths (index : Nat) : List (MatchPattern × Expr) → List CorePath
  | [] => []
  | (_, body) :: rest =>
      (logicalCorePaths body).map (.matchBranch index :: ·) ++
        logicalBranchPaths (index + 1) rest

def logicalBindingPaths (member : Nat) : List CoreRecBinding → List CorePath
  | [] => []
  | binding :: rest =>
      (logicalCorePaths binding.rhs).map (.letRecRhs member :: ·) ++
        logicalBindingPaths (member + 1) rest
end

def exactlyOnce [BEq α] (xs ys : List α) : Bool :=
  xs.length == ys.length && xs.all fun x => (ys.filter fun y => y == x).length == 1

/-- Executable statement of Core-origin totality: every logical path has exactly
    one origin and the map contains no extra path. -/
def Lowered.coreOriginsTotal (r : Lowered) : Bool :=
  let sourceIds := r.sourceNodes.map (fun n => n.id)
  exactlyOnce (logicalCorePaths r.expr) (r.coreOrigins.map Prod.fst) &&
    r.coreOrigins.all fun (_, origin) => origin.source.id ∈ sourceIds

/-- Every preassigned source expression has exactly one target classification. -/
def Lowered.sourceTargetsTotal (r : Lowered) : Bool :=
  exactlyOnce (r.sourceNodes.map (fun n => n.id)) (r.sourceTargets.map Prod.fst) &&
    r.sourceTargets.all fun (_, target) =>
      match target with
      | .absent _ => true
      | .present paths =>
          !paths.isEmpty && exactlyOnce paths paths &&
            paths.all fun path => (r.expr.atCorePath path).isSome

/-- Every emitted Core binder target resolves in the same logical skeleton.
    `SurfaceBinderSite` is the stable structural join key for this slice; exact
    binder-token spans remain in the parser's existing `BinderSpan` sidecar and
    will be attached when that flat collector is replaced. -/
def Lowered.binderTargetsResolve (r : Lowered) : Bool :=
  exactlyOnce (r.binderTargets.map Prod.fst) (r.binderTargets.map Prod.fst) &&
    r.binderTargets.all fun (_, target) =>
      match target with
      | .absent _ => true
      | .present sites =>
          !sites.isEmpty && sites.all fun site =>
            !site.paths.isEmpty && site.paths.all fun path => (r.expr.atCorePath path).isSome

def Lowered.provenanceTotal (r : Lowered) : Bool :=
  r.coreOriginsTotal && r.sourceTargetsTotal && r.binderTargetsResolve

abbrev InputLowered := Lowered InferInput

/-- Failures in optional provenance metadata are separate from source rejection. -/
inductive ProvenanceFailureReason where
  | programGroups (index bindingGroups spanGroups : Nat)
  | programMembers (index bindings spans : Nat)
  | expressionShape
  | listShape (surfaceRemaining spansRemaining : Nat)
  | branchShape (surfaceRemaining spansRemaining : Nat)
  | bindingShape (surfaceRemaining spansRemaining : Nat)
  | missingSourceClassification (id : SourceId)
  | missingBinderClassification (site : SurfaceBinderSite)
  deriving Repr

structure ProvenanceFailure where
  source? : Option SourceNode := none
  reason : ProvenanceFailureReason
  deriving Repr

inductive ProvenanceLowerError where
  | sourceFailure (source : SourceNode) (error : LoweringError)
  | provenance (error : ProvenanceFailure)
  deriving Repr

def ProvenanceLowerError.mapSource (map : LoweringError → LoweringError) : ProvenanceLowerError → ProvenanceLowerError
  | .sourceFailure source error => .sourceFailure source (map error)
  | .provenance error => .provenance error

def ProvenanceLowerError.atSource (source : SourceNode) : ProvenanceLowerError → ProvenanceLowerError
  | .sourceFailure owner error => .sourceFailure owner error
  | .provenance error => .provenance { error with source? := error.source?.orElse (fun _ => some source) }

def wrapParamsWithProvenanceResult (ke : KindEnv) (tvs : List ValName) (owner : SourceNode)
    (site : Nat → SurfaceBinderSite) :
    Nat → List (ValName × Option Surface.Ty) → InputLowered → Except ProvenanceLowerError InputLowered
  | _, [], rhs => .ok rhs
  | index, (_name, ann) :: rest, rhs => do
      let inner ← wrapParamsWithProvenanceResult ke tvs owner site (index + 1) rest rhs
      let ann' ← (lowerTemplateAnnResult ke tvs ann).mapError fun error =>
        .sourceFailure owner (error.atSite (.parameterAnnotation index))
      let child := inner.belowPath [.lambdaBody]
      pure {
        expr := .lambda ann' inner.expr
        sourceNodes := child.sourceNodes
        sourceTargets := child.sourceTargets
        coreOrigins := generatedOrigin owner [] (.valueParamLambda index) :: child.coreOrigins
        binderTargets := (site index, .present [.lambda []]) :: child.binderTargets }

def wrapParamsWithProvenance (ke : KindEnv) (tvs : List ValName) (owner : SourceNode)
    (site : Nat → SurfaceBinderSite) (index : Nat) (params : List (ValName × Option Surface.Ty))
    (rhs : InputLowered) : Option InputLowered :=
  (wrapParamsWithProvenanceResult ke tvs owner site index params rhs).toOption

@[typed_result_projection] theorem wrapParamsWithProvenanceResult_toOption
    (ke : KindEnv) (tvs : List ValName) (owner : SourceNode) (site : Nat → SurfaceBinderSite)
    (index : Nat) (params : List (ValName × Option Surface.Ty)) (rhs : InputLowered) :
    (wrapParamsWithProvenanceResult ke tvs owner site index params rhs).toOption =
      wrapParamsWithProvenance ke tvs owner site index params rhs := rfl

def presentPathsFor (id : SourceId) (targets : SourceTargetMap) : List CorePath :=
  targets.flatMap fun (candidate, target) =>
    if candidate == id then
      match target with
      | .present paths => paths
      | .absent _ => []
    else []

def firstSourceAbsenceFor (id : SourceId) : SourceTargetMap → Option OriginAbsence
  | [] => none
  | (candidate, target) :: rest =>
      if candidate == id then
        match target with
        | .absent reason => some reason
        | .present _ => firstSourceAbsenceFor id rest
      else firstSourceAbsenceFor id rest

/-- Coalesce copies of source metadata after pattern compilation has cloned an
    arm. Missing classifications fail instead of being silently fabricated. -/
def mergeSourceTargetsResult (nodes : List SourceNode) (raw : SourceTargetMap) :
    Except ProvenanceLowerError SourceTargetMap :=
  nodes.mapM fun node =>
    let paths := (presentPathsFor node.id raw).dedup
    if paths.isEmpty then
      match firstSourceAbsenceFor node.id raw with
      | some reason => .ok (node.id, .absent reason)
      | none => .error (.provenance ⟨some node, .missingSourceClassification node.id⟩)
    else .ok (node.id, .present paths)

def mergeSourceTargets (nodes : List SourceNode) (raw : SourceTargetMap) : Option SourceTargetMap :=
  (mergeSourceTargetsResult nodes raw).toOption

@[typed_result_projection] theorem mergeSourceTargetsResult_toOption (nodes : List SourceNode) (raw : SourceTargetMap) :
    (mergeSourceTargetsResult nodes raw).toOption = mergeSourceTargets nodes raw := rfl

def presentBinderSitesFor (source : SurfaceBinderSite)
    (targets : BinderTargetMap) : List CoreBinderSite :=
  targets.flatMap fun (candidate, target) =>
    if candidate == source then
      match target with
      | .present sites => sites
      | .absent _ => []
    else []

def firstBinderAbsenceFor (source : SurfaceBinderSite) :
    BinderTargetMap → Option OriginAbsence
  | [] => none
  | (candidate, target) :: rest =>
      if candidate == source then
        match target with
        | .absent reason => some reason
        | .present _ => firstBinderAbsenceFor source rest
      else firstBinderAbsenceFor source rest

/-- Coalesce cloned binder sites and retain an explicit absence when their
    containing source arm was eliminated. -/
def mergeBinderTargetsResult (raw : BinderTargetMap) : Except ProvenanceLowerError BinderTargetMap :=
  raw.map Prod.fst |>.dedup |>.mapM fun source =>
    let rawSites := (presentBinderSitesFor source raw).dedup
    let sites := match source with
      | .patCapture _ _ capture =>
          let paths := rawSites.flatMap fun
            | .patCapture paths _ => paths
            | _ => []
          if paths.isEmpty then [] else [.patCapture paths.dedup capture]
      | _ => rawSites
    if sites.isEmpty then
      match firstBinderAbsenceFor source raw with
      | some reason => .ok (source, .absent reason)
      | none => .error (.provenance ⟨none, .missingBinderClassification source⟩)
    else .ok (source, .present sites)

def mergeBinderTargets (raw : BinderTargetMap) : Option BinderTargetMap :=
  (mergeBinderTargetsResult raw).toOption

@[typed_result_projection] theorem mergeBinderTargetsResult_toOption (raw : BinderTargetMap) :
    (mergeBinderTargetsResult raw).toOption = mergeBinderTargets raw := rfl

def absentSourceTargets {Term : Type} (reason : OriginAbsence) (r : Lowered Term) : SourceTargetMap :=
  r.sourceNodes.map fun node => (node.id, .absent reason)

def absentBinderTargets {Term : Type} (reason : OriginAbsence) (r : Lowered Term) : BinderTargetMap :=
  r.binderTargets.map fun (site, _target) => (site, .absent reason)

def traceArmRoots (act : Nat) (trace : PatComp.EmissionTrace) : List CorePath :=
  trace.armBodyRoots.filterMap fun (candidate, path) =>
    if candidate == act then some path else none

def clonedArmParts {Term : Type} (trace : PatComp.EmissionTrace)
    (arms : List (Lowered Term)) : List (Lowered Term) :=
  arms.mapIdx (fun act arm => (traceArmRoots act trace).map fun path => arm.belowPath path)
    |>.flatten

def patternCaptureAbsences (owner : SourceId)
    (pats : List Surface.Pattern) : BinderTargetMap :=
  pats.mapIdx (fun arm pat =>
    (patVars pat).mapIdx fun capture _ =>
      (.patCapture owner arm capture, .absent .eliminatedByPatternCompilation))
    |>.flatten

def traceCaptureTargets (owner : SourceId)
    (trace : PatComp.EmissionTrace) : BinderTargetMap :=
  trace.captureLets.map fun (act, capture, path) =>
    (.patCapture owner act capture, .present [.patCapture [path] capture])

/-- Translate PatComp's source-agnostic construction trace into the surface
    provenance vocabulary, merging duplicated arms and preserving elimination. -/
def lowerTracedMatchResult (source : SourceNode) (scrut : InputLowered)
    (pats : List Surface.Pattern) (arms : List InputLowered)
    (traced : PatComp.TracedLowering InferInput) : Except ProvenanceLowerError InputLowered := do
  let scrutPart := scrut.belowPath [.letRhs]
  let armParts := clonedArmParts traced.trace arms
  let nodes := source :: scrut.sourceNodes ++ arms.flatMap (fun arm => arm.sourceNodes)
  let rawSourceTargets : SourceTargetMap :=
    (source.id, .present [[]]) :: scrutPart.sourceTargets ++
      arms.flatMap (absentSourceTargets .eliminatedByPatternCompilation) ++
      armParts.flatMap (fun arm => arm.sourceTargets)
  let sourceTargets ← (mergeSourceTargetsResult nodes rawSourceTargets).mapError (.atSource source)
  let rawBinderTargets : BinderTargetMap :=
    scrutPart.binderTargets ++
      arms.flatMap (absentBinderTargets .eliminatedByPatternCompilation) ++
      patternCaptureAbsences source.id pats ++
      armParts.flatMap (fun arm => arm.binderTargets) ++
      traceCaptureTargets source.id traced.trace
  let binderTargets ← (mergeBinderTargetsResult rawBinderTargets).mapError (.atSource source)
  pure {
    expr := traced.expr
    sourceNodes := nodes
    sourceTargets
    coreOrigins :=
      traced.trace.generated.map (fun (path, node) =>
        generatedOrigin source path (.patternCompilation node)) ++
      scrutPart.coreOrigins ++ armParts.flatMap (fun arm => arm.coreOrigins)
    binderTargets }

def lowerTracedMatch (source : SourceNode) (scrut : InputLowered)
    (pats : List Surface.Pattern) (arms : List InputLowered)
    (traced : PatComp.TracedLowering InferInput) : Option InputLowered :=
  (lowerTracedMatchResult source scrut pats arms traced).toOption

@[typed_result_projection] theorem lowerTracedMatchResult_toOption
    (source : SourceNode) (scrut : InputLowered) (pats : List Surface.Pattern)
    (arms : List InputLowered) (traced : PatComp.TracedLowering InferInput) :
    (lowerTracedMatchResult source scrut pats arms traced).toOption =
      lowerTracedMatch source scrut pats arms traced := rfl

def lowerListWithProvenanceValue (owner : SourceNode) (index : Nat) (isRoot : Bool) :
    List InputLowered → InputLowered
  | [] =>
      let originKind := if isRoot then OriginKind.authored else .generated (.listCtor index)
      {
        expr := .ctor cNil
        sourceNodes := if isRoot then [owner] else []
        sourceTargets := if isRoot then [(owner.id, .present [[]])] else []
        coreOrigins := [([], ⟨owner, originKind⟩)]
        binderTargets := [] }
  | item :: rest =>
      let tail := lowerListWithProvenanceValue owner (index + 1) false rest
      let expr := .app (.app (.ctor cCons) item.expr) tail.expr
      let rootKind := if isRoot then OriginKind.authored else .generated (.listTailApp index)
      let ownNodes := if isRoot then [owner] else []
      let ownTargets := if isRoot then [(owner.id, .present [[]])] else []
      let item' := item.belowPath [.appFun, .appArg]
      let tail' := tail.belowPath [.appArg]
      {
        expr
        sourceNodes := ownNodes ++ item'.sourceNodes ++ tail'.sourceNodes
        sourceTargets := ownTargets ++ item'.sourceTargets ++ tail'.sourceTargets
        coreOrigins :=
          [([], ⟨owner, rootKind⟩),
           generatedOrigin owner [.appFun] (.listPartialApp index),
           generatedOrigin owner [.appFun, .appFun] (.listCtor index)] ++
          item'.coreOrigins ++ tail'.coreOrigins
        binderTargets := item'.binderTargets ++ tail'.binderTargets }
def lowerListWithProvenance (owner : SourceNode) (index : Nat) (isRoot : Bool)
    (items : List InputLowered) : Option InputLowered :=
  some (lowerListWithProvenanceValue owner index isRoot items)

@[typed_result_projection] theorem lowerListWithProvenanceValue_some
    (owner : SourceNode) (index : Nat) (isRoot : Bool) (items : List InputLowered) :
    some (lowerListWithProvenanceValue owner index isRoot items) =
      lowerListWithProvenance owner index isRoot items := rfl

mutual
def lowerIdentifiedExprResult (ke : KindEnv) (tvs vs : List ValName) :
    Surface.Expr → IdentifiedExpr → Except ProvenanceLowerError InputLowered
  | .primLit (.bool b), .leaf source =>
      .ok (authoredRoot source (.ctor (if b then cTrue else cFalse)))
  | .primLit .unit, .leaf source => .ok (authoredRoot source (.primLit .unit))
  | .primLit (.int n), .leaf source => .ok (authoredRoot source (.primLit (.int n)))
  | .primLit (.nat n), .leaf source => .ok (authoredRoot source (.primLit (.nat n)))
  | .primLit (.char c), .leaf source => .ok (authoredRoot source (.primLit (.char c)))
  | .primBinOp op, .leaf source => .ok (authoredRoot source (.primBinOp op))
  | .pair a b, .pair source sa sb => do
      let a' ← (lowerIdentifiedExprResult ke tvs vs a sa).mapError (.mapSource (LoweringError.below .pairLeft))
      let b' ← (lowerIdentifiedExprResult ke tvs vs b sb).mapError (.mapSource (LoweringError.below .pairRight))
      let expr := .app (.app (.ctor cPair) a'.expr) b'.expr
      pure (combineAuthored source expr
        [a'.belowPath [.appFun, .appArg], b'.belowPath [.appArg]]
        [generatedOrigin source [.appFun] .pairPartialApp,
         generatedOrigin source [.appFun, .appFun] .pairCtor])
  | .cons h t, .cons source sh st => do
      let h' ← (lowerIdentifiedExprResult ke tvs vs h sh).mapError (.mapSource (LoweringError.below .consHead))
      let t' ← (lowerIdentifiedExprResult ke tvs vs t st).mapError (.mapSource (LoweringError.below .consTail))
      let expr := .app (.app (.ctor cCons) h'.expr) t'.expr
      pure (combineAuthored source expr
        [h'.belowPath [.appFun, .appArg], t'.belowPath [.appArg]]
        [generatedOrigin source [.appFun] .consPartialApp,
         generatedOrigin source [.appFun, .appFun] .consCtor])
  | .list items, .list source sitems => do
      let items' ← (lowerIdentifiedListResult ke tvs vs items sitems).mapError (.atSource source)
      pure (lowerListWithProvenanceValue source 0 true items')
  | .lambda param paramAnn body, .lambda source sbody => do
      let ann' ← (lowerTemplateAnnResult ke tvs paramAnn).mapError fun error =>
        .sourceFailure source (error.atSite .lambdaAnnotation)
      match param with
      | .name name => do
          let body' ← (lowerIdentifiedExprResult ke tvs (name :: vs) body sbody).mapError (.mapSource (LoweringError.below .lambdaBody))
          pure (combineAuthored source (.lambda ann' body'.expr)
            [body'.belowPath [.lambdaBody]] []
            [(.lambda source.id, .present [.lambda []])])
      | .wildcard => do
          let body' ← (lowerIdentifiedExprResult ke tvs (.mk "_" :: vs) body sbody).mapError (.mapSource (LoweringError.below .lambdaBody))
          pure (combineAuthored source (.lambda ann' body'.expr)
            [body'.belowPath [.lambdaBody]] []
            [(.lambda source.id, .present [.lambda []])])
      | _ => do
          let body' ← (lowerIdentifiedExprResult ke tvs (patVars param ++ .mk "_" :: vs) body sbody).mapError (.mapSource (LoweringError.below .lambdaBody))
          let scrut : InputLowered := {
            expr := .var 0
            sourceNodes := []
            sourceTargets := []
            coreOrigins := [generatedOrigin source [] .patternLambdaScrutinee]
            binderTargets := [] }
          let traced := lowerInputMatchTrace scrut.expr [param]
            (fun i => [body'.expr].getD i (.ctor cNil))
          let matched ← lowerTracedMatchResult source scrut [param] [body'] traced
          let inner := { matched with
            sourceNodes := matched.sourceNodes.filter (fun n => n.id != source.id)
            sourceTargets := matched.sourceTargets.filter (fun entry => entry.1 != source.id) }
          pure (combineAuthored source (.lambda ann' matched.expr)
            [inner.belowPath [.lambdaBody]])
  | .app fn arg, .app source sfn sarg => do
      let fn' ← (lowerIdentifiedExprResult ke tvs vs fn sfn).mapError (.mapSource (LoweringError.below .appFun))
      let arg' ← (lowerIdentifiedExprResult ke tvs vs arg sarg).mapError (.mapSource (LoweringError.below .appArg))
      pure (combineAuthored source (.app fn'.expr arg'.expr)
        [fn'.belowPath [.appFun], arg'.belowPath [.appArg]])
  | .letIn name tyParams params ann rhs body, .letIn source srhs sbody => do
      let annF := finalizeInputAnn tyParams params ann
      let ann' ← (lowerInputLetAnnResult ke tvs annF).mapError fun error =>
        .sourceFailure source ((error.atSite .bindingAnnotation).inBinding name)
      let tvs' := letAnnTyPrefix tyParams annF ++ tvs
      let rhsCore ← (lowerIdentifiedExprResult ke tvs' (paramTermScope params vs) rhs srhs).mapError (.mapSource (fun error => (error.below .letRhs).inBinding name))
      let rhs' ← (wrapParamsWithProvenanceResult ke tvs' source
        (fun i => .letParam source.id i) 0 params rhsCore).mapError (.mapSource (.inBinding name))
      let body' ← (lowerIdentifiedExprResult ke tvs (name :: vs) body sbody).mapError (.mapSource (LoweringError.below .letBody))
      pure (combineAuthored source (.letIn ann' rhs'.expr body'.expr)
        [rhs'.belowPath [.letRhs], body'.belowPath [.letBody]] []
        [(.letIn source.id, .present [.letIn []])])
  | .letRecIn binds body, .letRecIn source srhss sbody => do
      let recScope := binds.map (fun b => b.name) ++ vs
      let bindings' ← lowerIdentifiedRecBindsResult ke tvs recScope source 0 binds srhss
      let body' ← (lowerIdentifiedExprResult ke tvs recScope body sbody).mapError (.mapSource (LoweringError.below .letRecBody))
      let inputBindings := bindings'.map fun binding =>
        { ann := binding.ann, rhs := binding.rhs.expr }
      let bindingParts := bindings'.mapIdx fun member binding =>
        binding.rhs.belowPath [.letRecRhs member]
      let groupBinders := binds.mapIdx fun member _ =>
        (.letRec source.id member, .present [.letRec [] member])
      pure (combineAuthored source (.letRec inputBindings body'.expr)
        (bindingParts ++ [body'.belowPath [.letRecBody]]) [] groupBinders
        )
  | .var name, .leaf source => do
      let index ← (resolveValueResult vs name).mapError (.sourceFailure source)
      pure (authoredRoot source (.var index))
  | .ctor name, .leaf source => .ok (authoredRoot source (.ctor name))
  | .ife cond then_ else_, .ife source scond sthen selse => do
      let cond' ← (lowerIdentifiedExprResult ke tvs vs cond scond).mapError (.mapSource (LoweringError.below .ifCondition))
      let then' ← (lowerIdentifiedExprResult ke tvs vs then_ sthen).mapError (.mapSource (LoweringError.below .ifThen))
      let else' ← (lowerIdentifiedExprResult ke tvs vs else_ selse).mapError (.mapSource (LoweringError.below .ifElse))
      let pats : List Surface.Pattern := [.ctor cTrue [], .ctor cFalse []]
      let arms := [then', else']
      let traced := lowerInputMatchTrace cond'.expr pats
        (fun i => (arms.map (fun arm => arm.expr)).getD i (.ctor cNil))
      lowerTracedMatchResult source cond' pats arms traced
  | .match_ scrut branches, .match_ source sscrut sarms => do
      let scrut' ← (lowerIdentifiedExprResult ke tvs vs scrut sscrut).mapError (.mapSource (LoweringError.below .matchScrut))
      let arms' ← (lowerIdentifiedBranchesResult ke tvs vs branches sarms).mapError (.atSource source)
      let pats := branches.map Prod.fst
      let traced := lowerInputMatchTrace scrut'.expr pats
        (fun i => (arms'.map (fun arm => arm.expr)).getD i (.ctor cNil))
      lowerTracedMatchResult source scrut' pats arms' traced
  | _, tree => .error (.provenance ⟨some tree.source, .expressionShape⟩)

termination_by surface _ => surfaceExprSize surface
decreasing_by all_goals simp only [surfaceExprSize, surfaceExprSizeList, surfaceExprSizeBranches, surfaceExprSizeLetRecBinds] <;> omega

def lowerIdentifiedListResult (ke : KindEnv) (tvs vs : List ValName) :
    List Surface.Expr → List IdentifiedExpr → Except ProvenanceLowerError (List InputLowered)
  | [], [] => .ok []
  | e :: es, se :: ses => do
      let e' ← (lowerIdentifiedExprResult ke tvs vs e se).mapError (.mapSource (LoweringError.below (.listItem 0)))
      let es' ← (lowerIdentifiedListResult ke tvs vs es ses).mapError (.mapSource LoweringError.nextListItem)
      pure (e' :: es')
  | exprs, trees => .error (.provenance ⟨none, .listShape exprs.length trees.length⟩)

termination_by surfaces _ => surfaceExprSizeList surfaces
decreasing_by all_goals simp only [surfaceExprSize, surfaceExprSizeList, surfaceExprSizeBranches, surfaceExprSizeLetRecBinds] <;> omega

def lowerIdentifiedBranchesResult (ke : KindEnv) (tvs vs : List ValName) :
    List (Surface.Pattern × Surface.Expr) → List IdentifiedExpr → Except ProvenanceLowerError (List InputLowered)
  | [], [] => .ok []
  | (pat, body) :: rest, sbody :: srest => do
      let body' ← (lowerIdentifiedExprResult ke tvs (patVars pat ++ vs) body sbody).mapError (.mapSource (LoweringError.below (.matchBranch 0)))
      let rest' ← (lowerIdentifiedBranchesResult ke tvs vs rest srest).mapError (.mapSource LoweringError.nextBranch)
      pure (body' :: rest')
  | branches, trees => .error (.provenance ⟨none, .branchShape branches.length trees.length⟩)

termination_by branches _ => surfaceExprSizeBranches branches
decreasing_by all_goals simp only [surfaceExprSize, surfaceExprSizeList, surfaceExprSizeBranches, surfaceExprSizeLetRecBinds] <;> omega

def lowerIdentifiedRecBindsResult (ke : KindEnv) (tvs recScope : List ValName)
    (owner : SourceNode) : Nat → List Surface.Binding → List IdentifiedExpr →
      Except ProvenanceLowerError (List (RecBinding BindingAnn InputLowered))
  | _, [], [] => .ok []
  | member, b :: rest, srhs :: srest => do
      let annF := finalizeInputAnn b.tyParams b.params b.ann
      let ann' ← (lowerInputLetAnnResult ke tvs annF).mapError fun error =>
        .sourceFailure owner (((error.atSite .bindingAnnotation).inBinding b.name).below (.letRecRhs member))
      let tvs' := letAnnTyPrefix b.tyParams annF ++ tvs
      let rhsCore ← (lowerIdentifiedExprResult ke tvs' (paramTermScope b.params recScope) b.rhs srhs).mapError (.mapSource (fun error => (error.below (.letRecRhs member)).inBinding b.name))
      let rhs' ← (wrapParamsWithProvenanceResult ke tvs' owner
        (fun i => .letRecParam owner.id member i) 0 b.params rhsCore).mapError
          (.mapSource (fun error => (error.inBinding b.name).below (.letRecRhs member)))
      let rest' ← lowerIdentifiedRecBindsResult ke tvs recScope owner (member + 1) rest srest
      pure ({ ann := ann', rhs := rhs' } :: rest')
  | _, bindings, trees => .error (.provenance ⟨some owner, .bindingShape bindings.length trees.length⟩)

termination_by _ bindings _ => surfaceExprSizeLetRecBinds bindings
decreasing_by all_goals simp only [surfaceExprSize, surfaceExprSizeList, surfaceExprSizeBranches, surfaceExprSizeLetRecBinds] <;> omega

end


def lowerIdentifiedExpr (ke : KindEnv) (tvs vs : List ValName)
    (surface : Surface.Expr) (tree : IdentifiedExpr) : Option InputLowered :=
  (lowerIdentifiedExprResult ke tvs vs surface tree).toOption

def lowerIdentifiedList (ke : KindEnv) (tvs vs : List ValName)
    (surfaces : List Surface.Expr) (trees : List IdentifiedExpr) : Option (List InputLowered) :=
  (lowerIdentifiedListResult ke tvs vs surfaces trees).toOption

def lowerIdentifiedBranches (ke : KindEnv) (tvs vs : List ValName)
    (branches : List (Surface.Pattern × Surface.Expr)) (trees : List IdentifiedExpr) : Option (List InputLowered) :=
  (lowerIdentifiedBranchesResult ke tvs vs branches trees).toOption

def lowerIdentifiedRecBinds (ke : KindEnv) (tvs recScope : List ValName) (owner : SourceNode)
    (member : Nat) (bindings : List Surface.Binding) (trees : List IdentifiedExpr) :
    Option (List (RecBinding BindingAnn InputLowered)) :=
  (lowerIdentifiedRecBindsResult ke tvs recScope owner member bindings trees).toOption

@[typed_result_projection] theorem lowerIdentifiedExprResult_toOption (ke : KindEnv) (tvs vs : List ValName) (surface : Surface.Expr) (tree : IdentifiedExpr) :
    (lowerIdentifiedExprResult ke tvs vs surface tree).toOption = lowerIdentifiedExpr ke tvs vs surface tree := rfl

@[typed_result_projection] theorem lowerIdentifiedListResult_toOption (ke : KindEnv) (tvs vs : List ValName) (surfaces : List Surface.Expr) (trees : List IdentifiedExpr) :
    (lowerIdentifiedListResult ke tvs vs surfaces trees).toOption = lowerIdentifiedList ke tvs vs surfaces trees := rfl

@[typed_result_projection] theorem lowerIdentifiedBranchesResult_toOption (ke : KindEnv) (tvs vs : List ValName) (branches : List (Surface.Pattern × Surface.Expr)) (trees : List IdentifiedExpr) :
    (lowerIdentifiedBranchesResult ke tvs vs branches trees).toOption = lowerIdentifiedBranches ke tvs vs branches trees := rfl

@[typed_result_projection] theorem lowerIdentifiedRecBindsResult_toOption (ke : KindEnv) (tvs vs : List ValName) (owner : SourceNode) (member : Nat) (bindings : List Surface.Binding) (trees : List IdentifiedExpr) :
    (lowerIdentifiedRecBindsResult ke tvs vs owner member bindings trees).toOption = lowerIdentifiedRecBinds ke tvs vs owner member bindings trees := rfl

/-- Construction-time lowering. The `SpannedExpr` must mirror the
    Surface tree; shape mismatches fail instead of silently corrupting paths. -/
def lowerWithProvenanceResult (ctors : CtorEnv) (surface : Surface.Expr)
    (spanned : SpannedExpr) : Except ProvenanceLowerError InputLowered := do
  let identified := identify spanned
  let lowered ← lowerIdentifiedExprResult (kindEnvOfCtors ctors) [] [] surface identified
  -- The ID pass, rather than the lowering recursion, is authoritative for the
  -- source domain. This makes an accidentally omitted source target observable
  -- to `sourceTargetsTotal` instead of letting both sides omit the same node.
  pure { lowered with sourceNodes := identified.nodes }

def lowerWithProvenance (ctors : CtorEnv) (surface : Surface.Expr)
    (spanned : SpannedExpr) : Option InputLowered :=
  (lowerWithProvenanceResult ctors surface spanned).toOption

@[typed_result_projection] theorem lowerWithProvenanceResult_toOption
    (ctors : CtorEnv) (surface : Surface.Expr) (spanned : SpannedExpr) :
    (lowerWithProvenanceResult ctors surface spanned).toOption = lowerWithProvenance ctors surface spanned := rfl

/-! Successful provenance construction agrees exactly with the shared structural
lowerer. The proofs quantify over arbitrary identified trees: mismatched metadata
may fail, but every accepted term has a lowering derivation independent of IDs.
-/


attribute [-typed_result_projection] Option.bind

theorem lowerTracedMatch_expr {source : SourceNode} {scrut : InputLowered}
    {pats : List Surface.Pattern} {arms : List InputLowered}
    {traced : PatComp.TracedLowering InferInput} {result : InputLowered}
    (h : lowerTracedMatch source scrut pats arms traced = some result) :
    result.expr = traced.expr := by
  rw [lowerTracedMatch, lowerTracedMatchResult] at h; simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨_, _, _, _, rfl⟩ := h
  rfl

theorem wrapParamsWithProvenance_project {ke : KindEnv} {tvs : List ValName}
    {owner : SourceNode} {site : Nat → SurfaceBinderSite} {index : Nat}
    {params : List (ValName × Option Surface.Ty)} {rhs result : InputLowered}
    (h : wrapParamsWithProvenance ke tvs owner site index params rhs = some result) :
    wrapInputParams ke tvs params rhs.expr = some result.expr := by
  induction params generalizing index result with
  | nil => cases h; rfl
  | cons param params ih =>
    rcases param with ⟨name, ann⟩
    rw [wrapParamsWithProvenance, wrapParamsWithProvenanceResult] at h; simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨inner, hinner, ann', hann, rfl⟩ := h
    have hp := ih hinner
    rw [wrapInputParams, LoweringOps.wrapParams_eq]
    change (do
      let annotation ← lowerTemplateAnn ke tvs ann
      let body ← wrapInputParams ke tvs params rhs.expr
      pure (Expr.lambda annotation body)) = some (Expr.lambda ann' inner.expr)
    simp only [typed_result_projection, hann, hp, bind, pure, Option.bind_some]

theorem lowerListWithProvenance_project {owner : SourceNode} {index : Nat} {isRoot : Bool}
    {items : List InputLowered} {result : InputLowered}
    (h : lowerListWithProvenance owner index isRoot items = some result) :
    result.expr = mkInputList (items.map (·.expr)) := by
  have valueExpr : ∀ (items : List InputLowered) (index : Nat) (isRoot : Bool),
      (lowerListWithProvenanceValue owner index isRoot items).expr = mkInputList (items.map (·.expr)) := by
    intro items
    induction items with
    | nil => intros; rfl
    | cons item rest ih =>
      intros
      simp only [lowerListWithProvenanceValue, mkInputList, LoweringOps.mkList,
        inputLoweringOps, List.map_cons, Lowered.belowPath]
      exact congrArg (fun tail => Expr.app (.app (.ctor cCons) item.expr) tail) (ih _ _)
  cases h
  exact valueExpr _ _ _

private theorem lowerRec_nil (ke) (tvs vs) (owner) (index) : lowerIdentifiedRecBinds ke tvs vs owner index [] [] = some [] := by
  rw [lowerIdentifiedRecBinds, lowerIdentifiedRecBindsResult.eq_def]
  rfl
private theorem lowerRec_cons (ke) (tvs vs) (owner) (index) (b : Surface.Binding) (rest) (srhs) (srest) :
 lowerIdentifiedRecBinds ke tvs vs owner index (b::rest) (srhs::srest) = (do
 let annF := finalizeInputAnn b.tyParams b.params b.ann
 let ann' ← lowerInputLetAnn ke tvs annF
 let tvs' := letAnnTyPrefix b.tyParams annF ++ tvs
 let rhs ← lowerIdentifiedExpr ke tvs' (paramTermScope b.params vs) b.rhs srhs
 let rhs' ← wrapParamsWithProvenance ke tvs' owner (fun i => .letRecParam owner.id index i) 0 b.params rhs
 let rest' ← lowerIdentifiedRecBinds ke tvs vs owner (index+1) rest srest
 pure ({ ann := ann', rhs := rhs' }::rest')) := by
  rw [lowerIdentifiedRecBinds, lowerIdentifiedRecBindsResult.eq_def]
  simp only [typed_result_projection]
  rfl

private theorem lowerRec_nil_cons (ke) (tvs vs) (owner) (index) (srhs) (srest) :
 lowerIdentifiedRecBinds ke tvs vs owner index [] (srhs::srest) = none := by
  rw [lowerIdentifiedRecBinds, lowerIdentifiedRecBindsResult.eq_def]
  rfl
private theorem lowerRec_cons_nil (ke) (tvs vs) (owner) (index) (b) (rest) :
 lowerIdentifiedRecBinds ke tvs vs owner index (b::rest) [] = none := by
  rw [lowerIdentifiedRecBinds, lowerIdentifiedRecBindsResult.eq_def]
  rfl

mutual
theorem lowerIdentifiedExpr_project {ke : KindEnv} {tvs vs : List ValName}
    {surface : Surface.Expr} {identified : IdentifiedExpr} {result : InputLowered}
    (h : lowerIdentifiedExpr ke tvs vs surface identified = some result) :
    lowerInputExpr ke tvs vs surface = some result.expr := by
  cases hs : surface with
  | primLit p =>
    cases p <;> cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    all_goals (cases h <;> rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, authoredRoot] <;> rfl)
  | primBinOp op =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    cases h
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, authoredRoot]
  | pair a b =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    have hpa := lowerIdentifiedExpr_project ha
    have hpb := lowerIdentifiedExpr_project hb
    simp only [typed_result_projection, lowerInputExpr, inputLoweringOps] at hpa hpb
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, hpa, hpb,
      bind, pure, Option.bind_some, combineAuthored]
    rfl
  | cons a b =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    have hpa := lowerIdentifiedExpr_project ha
    have hpb := lowerIdentifiedExpr_project hb
    simp only [typed_result_projection, lowerInputExpr, inputLoweringOps] at hpa hpb
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, hpa, hpb,
      bind, pure, Option.bind_some, combineAuthored]
    rfl
  | app a b =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a', ha, b', hb, rfl⟩ := h
    have hpa := lowerIdentifiedExpr_project ha
    have hpb := lowerIdentifiedExpr_project hb
    simp only [typed_result_projection, lowerInputExpr, inputLoweringOps] at hpa hpb
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, hpa, hpb,
      bind, pure, Option.bind_some, combineAuthored]
  | list items =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff] at h
    obtain ⟨items', hi, hl⟩ := h
    have hp := lowerIdentifiedList_project hi
    have he := lowerListWithProvenance_project hl
    simp only [typed_result_projection, lowerInputExprList, inputLoweringOps] at hp
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, hp, Option.map_some]
    exact congrArg some he.symm
  | lambda param ann body =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    cases param with
    | name name =>
      simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, rfl⟩ := h
      have hp := lowerIdentifiedExpr_project hb
      simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, inputEmissionOps] at hp
      rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, LoweringOps.lowerParamAnn, inputEmissionOps, ha, hp,
        bind, pure, Option.bind_some, combineAuthored]
    | wildcard =>
      simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, rfl⟩ := h
      have hp := lowerIdentifiedExpr_project hb
      simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, inputEmissionOps] at hp
      rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, LoweringOps.lowerParamAnn, inputEmissionOps, ha, hp,
        bind, pure, Option.bind_some, combineAuthored]
    | pair fst snd =>
      simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, matched, hm, rfl⟩ := h
      have hp := lowerIdentifiedExpr_project hb
      have he := lowerTracedMatch_expr hm
      simp only [typed_result_projection, lowerInputMatchTrace_expr] at he
      simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, inputEmissionOps] at hp
      rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, LoweringOps.lowerParamAnn, inputEmissionOps, ha, hp,
        bind, pure, Option.bind_some, LoweringOps.patternLambda, LoweringOps.match_,
        combineAuthored, inputEmissionOps]
      exact congrArg (fun e => some (Expr.lambda ann' e)) he.symm
    | ctor name pats =>
      simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, matched, hm, rfl⟩ := h
      have hp := lowerIdentifiedExpr_project hb
      have he := lowerTracedMatch_expr hm
      simp only [typed_result_projection, lowerInputMatchTrace_expr] at he
      simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, inputEmissionOps] at hp
      rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, LoweringOps.lowerParamAnn, inputEmissionOps, ha, hp,
        bind, pure, Option.bind_some, LoweringOps.patternLambda, LoweringOps.match_,
        combineAuthored, inputEmissionOps]
      exact congrArg (fun e => some (Expr.lambda ann' e)) he.symm
    | cons head tail =>
      simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, matched, hm, rfl⟩ := h
      have hp := lowerIdentifiedExpr_project hb
      have he := lowerTracedMatch_expr hm
      simp only [typed_result_projection, lowerInputMatchTrace_expr] at he
      simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, inputEmissionOps] at hp
      rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, LoweringOps.lowerParamAnn, inputEmissionOps, ha, hp,
        bind, pure, Option.bind_some, LoweringOps.patternLambda, LoweringOps.match_,
        combineAuthored, inputEmissionOps]
      exact congrArg (fun e => some (Expr.lambda ann' e)) he.symm
    | list items =>
      simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ann', ha, body', hb, matched, hm, rfl⟩ := h
      have hp := lowerIdentifiedExpr_project hb
      have he := lowerTracedMatch_expr hm
      simp only [typed_result_projection, lowerInputMatchTrace_expr] at he
      simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, inputEmissionOps] at hp
      rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, LoweringOps.lowerParamAnn, inputEmissionOps, ha, hp,
        bind, pure, Option.bind_some, LoweringOps.patternLambda, LoweringOps.match_,
        combineAuthored, inputEmissionOps]
      exact congrArg (fun e => some (Expr.lambda ann' e)) he.symm
  | letIn name tyParams params ann rhs body =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ann', ha, rhsCore, hr, rhs', hw, body', hb, rfl⟩ := h
    have hpr := lowerIdentifiedExpr_project hr
    have hpw := wrapParamsWithProvenance_project hw
    have hpb := lowerIdentifiedExpr_project hb
    simp only [typed_result_projection, lowerInputExpr, wrapInputParams, inputLoweringOps] at hpr hpw hpb
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, LoweringOps.lowerBindAnn, ha, hpr, hpw, hpb,
      bind, pure, Option.bind_some, combineAuthored]
  | letRecIn bindings body =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨bindings', hr, body', hb, rfl⟩ := h
    have hpr := lowerIdentifiedRecBinds_project hr
    have hpb := lowerIdentifiedExpr_project hb
    simp only [typed_result_projection, lowerInputExpr, lowerInputRecBinds, inputLoweringOps] at hpr hpb
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, hpr, hpb,
      bind, pure, Option.bind_some, combineAuthored]
  | var name =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨index, hi, rfl⟩ := h
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, hi, Option.map_some, authoredRoot]
    rfl
  | ctor name =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    cases h
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, lowerInputExpr, inputLoweringOps, authoredRoot]
    rfl
  | ife c t f =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff] at h
    obtain ⟨c', hc, t', ht, f', hf, hm⟩ := h
    have hpc := lowerIdentifiedExpr_project hc
    have hpt := lowerIdentifiedExpr_project ht
    have hpf := lowerIdentifiedExpr_project hf
    have he := lowerTracedMatch_expr hm
    simp only [typed_result_projection, lowerInputMatchTrace_expr] at he
    simp only [typed_result_projection, lowerInputExpr, inputLoweringOps] at hpc hpt hpf
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, hs, lowerInputExpr, inputLoweringOps, hpc, hpt, hpf,
      bind, pure, Option.bind_some, LoweringOps.match_, lowerInputMatch] at *
    exact congrArg some he.symm
  | match_ scrut branches =>
    cases identified <;> (rw [lowerIdentifiedExpr, lowerIdentifiedExprResult.eq_def] at h; simp only [hs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff] at h
    obtain ⟨scrut', hs, arms', hb, hm⟩ := h
    have hps := lowerIdentifiedExpr_project hs
    have hpb := lowerIdentifiedBranches_project hb
    have he := lowerTracedMatch_expr hm
    simp only [typed_result_projection, lowerInputMatchTrace_expr] at he
    simp only [typed_result_projection, lowerInputExpr, lowerInputBranches, inputLoweringOps] at hps hpb
    rw [lowerInputExpr, lowerExprWith_eq] <;> simp only [typed_result_projection, hs, lowerInputExpr, inputLoweringOps, hps, hpb,
      bind, pure, Option.bind_some, LoweringOps.match_, lowerInputMatch] at *
    exact congrArg some he.symm
termination_by sizeOf surface
decreasing_by all_goals (subst_vars; simp_wf) <;> omega

theorem lowerIdentifiedList_project {ke : KindEnv} {tvs vs : List ValName}
    {surfaces : List Surface.Expr} {identified : List IdentifiedExpr} {result : List InputLowered}
    (h : lowerIdentifiedList ke tvs vs surfaces identified = some result) :
    lowerInputExprList ke tvs vs surfaces = some (result.map (·.expr)) := by
  cases hss : surfaces with
  | nil =>
    cases identified <;> (rw [lowerIdentifiedList, lowerIdentifiedListResult.eq_def] at h; simp only [hss] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    cases h
    rw [lowerInputExprList, lowerExprListWith_eq] <;> simp only [typed_result_projection, lowerInputExprList, List.map_nil]
  | cons e es =>
    cases identified <;> (rw [lowerIdentifiedList, lowerIdentifiedListResult.eq_def] at h; simp only [hss] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨e', he, es', hes, rfl⟩ := h
    have hp := lowerIdentifiedExpr_project he
    have hps := lowerIdentifiedList_project hes
    simp only [typed_result_projection, lowerInputExpr, lowerInputExprList] at hp hps
    rw [lowerInputExprList, lowerExprListWith_eq] <;> simp only [typed_result_projection, lowerInputExprList, hp, hps, bind, pure, Option.bind_some, List.map_cons]
termination_by sizeOf surfaces
decreasing_by all_goals (subst_vars; simp_wf) <;> omega

theorem lowerIdentifiedBranches_project {ke : KindEnv} {tvs vs : List ValName}
    {branches : List (Surface.Pattern × Surface.Expr)} {identified : List IdentifiedExpr} {result : List InputLowered}
    (h : lowerIdentifiedBranches ke tvs vs branches identified = some result) :
    lowerInputBranches ke tvs vs branches = some (result.map (·.expr)) := by
  cases hbs : branches with
  | nil =>
    cases identified <;> (rw [lowerIdentifiedBranches, lowerIdentifiedBranchesResult.eq_def] at h; simp only [hbs] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    cases h
    rw [lowerInputBranches, lowerBranchesWith_eq] <;> simp only [typed_result_projection, lowerInputBranches, List.map_nil]
  | cons branch branches =>
    cases hbranch : branch
    rename_i pat body
    cases identified <;> (rw [lowerIdentifiedBranches, lowerIdentifiedBranchesResult.eq_def] at h; simp only [hbs, hbranch] at h; simp only [typed_result_projection, reduceCtorEq] at h)
    simp only [typed_result_projection, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b', hb, bs', hbs, rfl⟩ := h
    have hp := lowerIdentifiedExpr_project hb
    have hps := lowerIdentifiedBranches_project hbs
    simp only [typed_result_projection, lowerInputExpr, lowerInputBranches] at hp hps
    rw [lowerInputBranches, lowerBranchesWith_eq] <;> simp only [typed_result_projection, lowerInputBranches, hp, hps, bind, pure, Option.bind_some, List.map_cons]
termination_by sizeOf branches
decreasing_by all_goals (subst_vars; simp_wf) <;> omega

theorem lowerIdentifiedRecBinds_project {ke : KindEnv} {tvs vs : List ValName}
    {owner : SourceNode} {index : Nat} {bindings : List Surface.Binding}
    {identified : List IdentifiedExpr}
    {result : List (RecBinding BindingAnn InputLowered)}
    (h : lowerIdentifiedRecBinds ke tvs vs owner index bindings identified = some result) :
    lowerInputRecBinds ke tvs vs bindings = some (result.map fun binding =>
      { ann := binding.ann, rhs := binding.rhs.expr }) := by
  cases hbs : bindings with
  | nil =>
    cases identified <;> simp only [hbs, lowerRec_nil, lowerRec_nil_cons, reduceCtorEq] at h
    cases h
    rw [lowerInputRecBinds, lowerRecBindsWith_eq] <;> simp only [lowerInputRecBinds, List.map_nil]
  | cons b bindings =>
    cases hbnd : b
    rename_i name tyParams params ann rhs
    cases identified <;> simp only [hbs, hbnd, lowerRec_cons, lowerRec_cons_nil, reduceCtorEq] at h
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ann', ha, rhsCore, hr, rhs', hw, rest', hrest, rfl⟩ := h
    have hpr := lowerIdentifiedExpr_project hr
    have hpw := wrapParamsWithProvenance_project hw
    have hps := lowerIdentifiedRecBinds_project hrest
    simp only [lowerInputExpr, lowerInputRecBinds, wrapInputParams, inputLoweringOps] at hpr hpw hps
    rw [lowerInputRecBinds, lowerRecBindsWith_eq]
    simp only [typed_result_projection, inputLoweringOps, LoweringOps.lowerBindAnn, ha, hpr, hpw, hps,
      bind, pure, Option.bind_some, List.map_cons]
termination_by sizeOf bindings
decreasing_by all_goals (subst_vars; simp_wf) <;> omega
end
theorem lowerWithProvenance_project {ctors : CtorEnv} {surface : Surface.Expr}
    {spanned : Surface.Span.SpannedExpr} {result : InputLowered}
    (h : lowerWithProvenance ctors surface spanned = some result) :
    lowerInput ctors surface = some result.expr := by
  rw [lowerWithProvenance, lowerWithProvenanceResult] at h; simp only [typed_result_projection, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨lowered, hl, rfl⟩ := h
  exact lowerIdentifiedExpr_project (result := lowered) hl

/-- Native provenance success produces exactly the canonical structural term. -/
theorem lowerWithProvenanceResult_project {ctors : CtorEnv} {surface : Surface.Expr}
    {spanned : SpannedExpr} {result : InputLowered}
    (h : lowerWithProvenanceResult ctors surface spanned = .ok result) :
    lowerInputResult ctors surface = .ok result.expr := by
  apply TypedResult.toOption_eq_some.mp
  exact lowerWithProvenance_project (TypedResult.toOption_eq_some.mpr h)

/-- Every accepted identified term has the canonical structural lowering derivation. -/
theorem lowerIdentifiedExpr_sound {ctors : CtorEnv} {ke : KindEnv}
    {tvs vs : List ValName} {surface : Surface.Expr} {identified : IdentifiedExpr}
    {result : InputLowered}
    (h : lowerIdentifiedExpr ke tvs vs surface identified = some result) :
    InputLowersExpr ctors ke tvs vs surface result.expr :=
  lowerInputExpr_sound (lowerIdentifiedExpr_project h)

/-- Metadata construction certifies the exact term sent to canonical inference. -/
theorem lowerWithProvenance_sound {ctors : CtorEnv} {surface : Surface.Expr}
    {spanned : SpannedExpr} {result : InputLowered}
    (h : lowerWithProvenance ctors surface spanned = some result) :
    InputLowers ctors surface result.expr :=
  lowerInput_sound (lowerWithProvenance_project h)

def nodeTyAtCorePath (types : NodeTypeMap) (path : CorePath) : Option Ty :=
  (types.find? fun pair => pair.1 == path).map (·.2)

abbrev SourceTypeMap := List (SourceId × List (CorePath × Ty))
abbrev InferredSurfaceBinderSchemes := List (SurfaceBinderSite × PolyTy)
abbrev PatternBinderTypeMap := List (SurfaceBinderSite × List (CorePath × Ty))

/-- Input and completed Core share logical term paths; only annotations differ. -/
def inputAtCorePath : InferInput → CorePath → Option InferInput
  | input, [] => some input
  | .lambda _ body, .lambdaBody :: rest => inputAtCorePath body rest
  | .app fn _, .appFun :: rest => inputAtCorePath fn rest
  | .app _ arg, .appArg :: rest => inputAtCorePath arg rest
  | .letIn _ rhs _, .letRhs :: rest => inputAtCorePath rhs rest
  | .letIn _ _ body, .letBody :: rest => inputAtCorePath body rest
  | .match_ scrut _, .matchScrut :: rest => inputAtCorePath scrut rest
  | .match_ _ arms, .matchBranch index :: rest => do
      let (_, body) ← arms[index]?
      inputAtCorePath body rest
  | .letRec bindings _, .letRecRhs member :: rest => do
      let binding ← bindings[member]?
      inputAtCorePath binding.rhs rest
  | .letRec _ body, .letRecBody :: rest => inputAtCorePath body rest
  | _, _ => none
termination_by _ path => path.length

structure TypedLowered where
  /-- The declaration environment shared by lowering and HM inference. -/
  ctors : CtorEnv
  /-- Authored annotation modes before completion. -/
  input : InferInput
  lowering : InputLowered
  inference : InferenceResult
  sourceTypes : SourceTypeMap
  inferredBinderSchemes : InferredSurfaceBinderSchemes
  patternBinderTypes : PatternBinderTypeMap
  /-- Authored rigid names belonging to a surrounding recovered lexical scope. -/
  outerAliases : List (Nat × String) := []

structure SourceHover where
  source : SourceNode
  types : List (CorePath × Ty)

def TypedLowered.typesForSource (r : TypedLowered) (id : SourceId) :
    List (CorePath × Ty) :=
  (r.sourceTypes.find? fun pair => pair.1 == id).map (fun pair => pair.2) |>.getD []

/-- Smallest containing expression span, joined to the types found at its Core
    targets. This is the arbitrary-expression hover primitive for the slice. -/
def TypedLowered.hoverAt? (r : TypedLowered) (line col : Nat) : Option SourceHover :=
  let candidates := r.lowering.sourceNodes.filter fun node => node.span.contains line col
  match candidates with
  | [] => none
  | first :: rest =>
      let best := rest.foldl (fun best node =>
        if node.span.area < best.span.area then node else best) first
      some ⟨best, r.typesForSource best.id⟩

/-- Every present source target found exactly one inferred monotype at each of
    its Core paths. Absent targets intentionally contribute no type. -/
def TypedLowered.sourceTypesTotal (r : TypedLowered) : Bool :=
  r.lowering.sourceTargets.length == r.sourceTypes.length &&
    (r.lowering.sourceTargets.zip r.sourceTypes).all fun pair =>
      let ((sourceId, target), (typedId, types)) := pair
      sourceId == typedId && match target with
        | .absent _ => types.isEmpty
        | .present paths =>
            paths.length == types.length &&
              (paths.zip types).all fun (path, typedPath, _ty) => path == typedPath

/-- Inference emits exactly one monotype for every logical Core expression.
    This validates both totality and path uniqueness before editor consumers
    join source provenance against the side map. -/
def TypedLowered.nodeTypesTotal (r : TypedLowered) : Bool :=
  exactlyOnce (logicalCorePaths r.input.erase) (r.inference.nodeTypes.map Prod.fst)

def patternBinderTargets (targets : BinderTargetMap) : BinderTargetMap :=
  targets.filter fun (surface, _target) =>
    match surface with
    | .patCapture _ _ _ => true
    | _ => false

def captureRhsPaths : BinderOriginTarget → List CorePath
  | .absent _ => []
  | .present sites => sites.flatMap fun
      | .patCapture paths _ => paths.map (· ++ [.letRhs])
      | _ => []

/-- Pattern-binder monotypes are total over the structural capture domain:
    every surviving capture let has an inferred RHS type and eliminated captures
    have an explicit empty result. -/
def TypedLowered.patternBinderTypesTotal (r : TypedLowered) : Bool :=
  let targets := patternBinderTargets r.lowering.binderTargets
  targets.length == r.patternBinderTypes.length &&
    (targets.zip r.patternBinderTypes).all fun pair =>
      let ((site, target), (typedSite, types)) := pair
      let paths := captureRhsPaths target
      site == typedSite && paths.length == types.length &&
        (paths.zip types).all fun (path, typedPath, _ty) => path == typedPath

def typesAtTarget (nodeTypes : NodeTypeMap) : OriginTarget → List (CorePath × Ty)
  | .absent _ => []
  | .present paths => paths.filterMap fun path =>
      (nodeTyAtCorePath nodeTypes path).map fun ty => (path, ty)

def joinBinderSchemes (targets : BinderTargetMap) (schemes : BinderSchemeMap) :
    InferredSurfaceBinderSchemes :=
  targets.flatMap fun (surface, target) =>
    match target with
    | .absent _ => []
    | .present sites => sites.flatMap fun site =>
        -- Pattern captures are source-level monotypes, not generalisation sites.
        -- Their compiler-generated `letIn` facts therefore stay out of this map.
        match site with
        | .patCapture _ _ => []
        | _ =>
            match schemes.find? fun pair => pair.1 == site with
            | some pair => [(surface, pair.2)]
            | none => []

def patternBinderTypesAt (nodeTypes : NodeTypeMap) (targets : BinderTargetMap) : PatternBinderTypeMap :=
  targets.filterMap fun (surface, target) =>
    match surface, target with
    | .patCapture _ _ _, .present sites =>
        let types := sites.flatMap fun
          | .patCapture paths _ => paths.filterMap fun path =>
              let rhsPath := path ++ [.letRhs]
              (nodeTyAtCorePath nodeTypes rhsPath).map fun ty => (rhsPath, ty)
          | _ => []
        some (surface, types)
    | .patCapture _ _ _, .absent _ => some (surface, [])
    | _, _ => none

/-- Infer the lowered source once, retaining its emitted paths for all type
    and scheme joins. The original partial source remains the payload. -/
def inferWithProvenanceAtResult (K : List Nat) (frontier : Nat) (ctx : Ctx)
    (lowering : InputLowered) : Except InferError TypedLowered := do
  let result ← inferWithTypesResultCore K frontier ctx lowering.expr
  let inference : InferenceResult := {
    toInferResult := result.val.toInferResult
    nodeTypes := result.val.nodeTypes.toMap
    binderSchemes := result.val.binderSchemes.toMap }
  pure {
    ctors := ctx.ctors
    input := lowering.expr
    lowering
    inference
    sourceTypes := lowering.sourceTargets.map fun (id, target) =>
      (id, typesAtTarget inference.nodeTypes target)
    inferredBinderSchemes := joinBinderSchemes lowering.binderTargets inference.binderSchemes
    patternBinderTypes := patternBinderTypesAt inference.nodeTypes lowering.binderTargets }

/-- Contextual entry point for closed external schemes. -/
def inferWithProvenanceInResult (ctx : Ctx) (lowering : InputLowered) : Except InferError TypedLowered :=
  inferWithProvenanceAtResult lowering.expr.rigidVars lowering.expr.source_freshFloor ctx lowering

/-- Apply only subsequent successful constraints to already checked artifacts.
The recovery driver never supplies substitutions from a failed check. -/
def TypedLowered.onSubst (typed : TypedLowered) (subst : Subst) : TypedLowered :=
  let inference := { typed.inference with
    ty := subst.onTy typed.inference.ty
    subst := typed.inference.subst ++ subst
    nodeTypes := typed.inference.nodeTypes.map (fun (path, ty) => (path, subst.onTy ty))
    binderSchemes := typed.inference.binderSchemes.map (fun (site, scheme) => (site, subst.onPolyTy scheme)) }
  { typed with
    inference
    sourceTypes := typed.lowering.sourceTargets.map (fun (id, target) => (id, typesAtTarget inference.nodeTypes target))
    inferredBinderSchemes := joinBinderSchemes typed.lowering.binderTargets inference.binderSchemes
    patternBinderTypes := patternBinderTypesAt inference.nodeTypes typed.lowering.binderTargets }

/-- Closed-program entry point; editor recovery supplies only checked external
schemes to `inferWithProvenanceInResult` for each independent group. -/
def inferWithProvenanceResult (ctors : CtorEnv) (lowering : InputLowered) : Except InferError TypedLowered :=
  inferWithProvenanceInResult ⟨[], ctors⟩ lowering

/-- Compatibility projection of the native inference-and-provenance result. -/
def inferWithProvenance (ctors : CtorEnv) (lowering : InputLowered) : Option TypedLowered :=
  (inferWithProvenanceResult ctors lowering).toOption

end SurfaceBridge.Provenance

attribute [typed_result_projection] Option.bind
