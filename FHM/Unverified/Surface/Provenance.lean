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
This operational provenance layer is separate from the verified Core-lowering
safety demonstration in `Headlines`.
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

mutual
def identifyFrom (next : SourceId) : SpannedExpr → SourceId × IdentifiedExpr
  | .generated expr =>
      let (next, identified) := identifyFrom next expr
      (next, identified.asGenerated)
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
  | .letRec _ bindings body => [] ::
      logicalBindingPaths 0 bindings ++
      (logicalCorePaths body).map (.letRecBody :: ·)

def logicalBranchPaths (index : Nat) : List (MatchPattern × Expr) → List CorePath
  | [] => []
  | (_, body) :: rest =>
      (logicalCorePaths body).map (.matchBranch index :: ·) ++
        logicalBranchPaths (index + 1) rest

def logicalBindingPaths (member : Nat) : List Expr → List CorePath
  | [] => []
  | rhs :: rest =>
      (logicalCorePaths rhs).map (.letRecRhs member :: ·) ++
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

def wrapParamsWithProvenance (ke : KindEnv) (tvs : List ValName) (owner : SourceNode)
    (site : Nat → SurfaceBinderSite) :
    Nat → List (ValName × Option Surface.Ty) → InputLowered → Option InputLowered
  | _, [], rhs => some rhs
  | index, (_name, ann) :: rest, rhs => do
      let inner ← wrapParamsWithProvenance ke tvs owner site (index + 1) rest rhs
      let ann' ← lowerTemplateAnn ke tvs ann
      let child := inner.belowPath [.lambdaBody]
      pure {
        expr := .lambda ann' inner.expr
        sourceNodes := child.sourceNodes
        sourceTargets := child.sourceTargets
        coreOrigins := generatedOrigin owner [] (.valueParamLambda index) :: child.coreOrigins
        binderTargets := (site index, .present [.lambda []]) :: child.binderTargets }

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
def mergeSourceTargets (nodes : List SourceNode) (raw : SourceTargetMap) : Option SourceTargetMap :=
  nodes.mapM fun node =>
    let paths := (presentPathsFor node.id raw).dedup
    if paths.isEmpty then do
      let reason ← firstSourceAbsenceFor node.id raw
      pure (node.id, .absent reason)
    else
      some (node.id, .present paths)

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
def mergeBinderTargets (raw : BinderTargetMap) : Option BinderTargetMap :=
  raw.map Prod.fst |>.dedup |>.mapM fun source =>
    let rawSites := (presentBinderSitesFor source raw).dedup
    let sites := match source with
      | .patCapture _ _ capture =>
          let paths := rawSites.flatMap fun
            | .patCapture paths _ => paths
            | _ => []
          if paths.isEmpty then [] else [.patCapture paths.dedup capture]
      | _ => rawSites
    if sites.isEmpty then do
      let reason ← firstBinderAbsenceFor source raw
      pure (source, .absent reason)
    else
      some (source, .present sites)

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
def lowerTracedMatch (source : SourceNode) (scrut : InputLowered)
    (pats : List Surface.Pattern) (arms : List InputLowered)
    (traced : PatComp.TracedLowering InferInput) : Option InputLowered := do
  let scrutPart := scrut.belowPath [.letRhs]
  let armParts := clonedArmParts traced.trace arms
  let nodes := source :: scrut.sourceNodes ++ arms.flatMap (fun arm => arm.sourceNodes)
  let rawSourceTargets : SourceTargetMap :=
    (source.id, .present [[]]) :: scrutPart.sourceTargets ++
      arms.flatMap (absentSourceTargets .eliminatedByPatternCompilation) ++
      armParts.flatMap (fun arm => arm.sourceTargets)
  let sourceTargets ← mergeSourceTargets nodes rawSourceTargets
  let rawBinderTargets : BinderTargetMap :=
    scrutPart.binderTargets ++
      arms.flatMap (absentBinderTargets .eliminatedByPatternCompilation) ++
      patternCaptureAbsences source.id pats ++
      armParts.flatMap (fun arm => arm.binderTargets) ++
      traceCaptureTargets source.id traced.trace
  let binderTargets ← mergeBinderTargets rawBinderTargets
  pure {
    expr := traced.expr
    sourceNodes := nodes
    sourceTargets
    coreOrigins :=
      traced.trace.generated.map (fun (path, node) =>
        generatedOrigin source path (.patternCompilation node)) ++
      scrutPart.coreOrigins ++ armParts.flatMap (fun arm => arm.coreOrigins)
    binderTargets }

mutual
def lowerIdentifiedExpr (ke : KindEnv) (tvs vs : List ValName) :
    Surface.Expr → IdentifiedExpr → Option InputLowered
  | .primLit (.bool b), .leaf source =>
      some (authoredRoot source (.ctor (if b then cTrue else cFalse)))
  | .primLit .unit, .leaf source => some (authoredRoot source (.primLit .unit))
  | .primLit (.int n), .leaf source => some (authoredRoot source (.primLit (.int n)))
  | .primLit (.nat n), .leaf source => some (authoredRoot source (.primLit (.nat n)))
  | .primLit (.char c), .leaf source => some (authoredRoot source (.primLit (.char c)))
  | .primBinOp op, .leaf source => some (authoredRoot source (.primBinOp op))
  | .pair a b, .pair source sa sb => do
      let a' ← lowerIdentifiedExpr ke tvs vs a sa
      let b' ← lowerIdentifiedExpr ke tvs vs b sb
      let expr := .app (.app (.ctor cPair) a'.expr) b'.expr
      pure (combineAuthored source expr
        [a'.belowPath [.appFun, .appArg], b'.belowPath [.appArg]]
        [generatedOrigin source [.appFun] .pairPartialApp,
         generatedOrigin source [.appFun, .appFun] .pairCtor])
  | .cons h t, .cons source sh st => do
      let h' ← lowerIdentifiedExpr ke tvs vs h sh
      let t' ← lowerIdentifiedExpr ke tvs vs t st
      let expr := .app (.app (.ctor cCons) h'.expr) t'.expr
      pure (combineAuthored source expr
        [h'.belowPath [.appFun, .appArg], t'.belowPath [.appArg]]
        [generatedOrigin source [.appFun] .consPartialApp,
         generatedOrigin source [.appFun, .appFun] .consCtor])
  | .list items, .list source sitems => do
      let items' ← lowerIdentifiedList ke tvs vs items sitems
      lowerListWithProvenance source 0 true items'
  | .lambda param paramAnn body, .lambda source sbody => do
      let ann' ← lowerTemplateAnn ke tvs paramAnn
      match param with
      | .name name => do
          let body' ← lowerIdentifiedExpr ke tvs (name :: vs) body sbody
          pure (combineAuthored source (.lambda ann' body'.expr)
            [body'.belowPath [.lambdaBody]] []
            [(.lambda source.id, .present [.lambda []])])
      | .wildcard => do
          let body' ← lowerIdentifiedExpr ke tvs (.mk "_" :: vs) body sbody
          pure (combineAuthored source (.lambda ann' body'.expr)
            [body'.belowPath [.lambdaBody]] []
            [(.lambda source.id, .present [.lambda []])])
      | _ => do
          let body' ← lowerIdentifiedExpr ke tvs (patVars param ++ .mk "_" :: vs) body sbody
          let scrut : InputLowered := {
            expr := .var 0
            sourceNodes := []
            sourceTargets := []
            coreOrigins := [generatedOrigin source [] .patternLambdaScrutinee]
            binderTargets := [] }
          let traced := lowerInputMatchTrace scrut.expr [param]
            (fun i => [body'.expr].getD i (.ctor cNil))
          let matched ← lowerTracedMatch source scrut [param] [body'] traced
          let inner := { matched with
            sourceNodes := matched.sourceNodes.filter (fun n => n.id != source.id)
            sourceTargets := matched.sourceTargets.filter (fun entry => entry.1 != source.id) }
          pure (combineAuthored source (.lambda ann' matched.expr)
            [inner.belowPath [.lambdaBody]])
  | .app fn arg, .app source sfn sarg => do
      let fn' ← lowerIdentifiedExpr ke tvs vs fn sfn
      let arg' ← lowerIdentifiedExpr ke tvs vs arg sarg
      pure (combineAuthored source (.app fn'.expr arg'.expr)
        [fn'.belowPath [.appFun], arg'.belowPath [.appArg]])
  | .letIn name tyParams params ann rhs body, .letIn source srhs sbody => do
      let annF := finalizeInputAnn tyParams params ann
      let ann' ← lowerInputLetAnn ke tvs annF
      let tvs' := letAnnTyPrefix tyParams annF ++ tvs
      let rhsCore ← lowerIdentifiedExpr ke tvs' (paramTermScope params vs) rhs srhs
      let rhs' ← wrapParamsWithProvenance ke tvs' source
        (fun i => .letParam source.id i) 0 params rhsCore
      let body' ← lowerIdentifiedExpr ke tvs (name :: vs) body sbody
      pure (combineAuthored source (.letIn ann' rhs'.expr body'.expr)
        [rhs'.belowPath [.letRhs], body'.belowPath [.letBody]] []
        [(.letIn source.id, .present [.letIn []])])
  | .letRecIn binds body, .letRecIn source srhss sbody => do
      let recScope := binds.map (fun b => b.name) ++ vs
      let anns' ← binds.mapM fun b =>
        lowerInputLetAnn ke tvs (finalizeInputAnn b.tyParams b.params b.ann)
      let bindings' ← lowerIdentifiedRecBinds ke tvs recScope source 0 binds srhss
      let body' ← lowerIdentifiedExpr ke tvs recScope body sbody
      let bindingExprs := bindings'.map fun r => r.expr
      let bindingParts := bindings'.mapIdx fun member r => r.belowPath [.letRecRhs member]
      let groupBinders := binds.mapIdx fun member _ =>
        (.letRec source.id member, .present [.letRec [] member])
      pure (combineAuthored source (.letRec anns' bindingExprs body'.expr)
        (bindingParts ++ [body'.belowPath [.letRecBody]]) [] groupBinders
        )
  | .var name, .leaf source => do
      let index ← tvarIndex vs name
      pure (authoredRoot source (.var index))
  | .ctor name, .leaf source => some (authoredRoot source (.ctor name))
  | .ife cond then_ else_, .ife source scond sthen selse => do
      let cond' ← lowerIdentifiedExpr ke tvs vs cond scond
      let then' ← lowerIdentifiedExpr ke tvs vs then_ sthen
      let else' ← lowerIdentifiedExpr ke tvs vs else_ selse
      let pats : List Surface.Pattern := [.ctor cTrue [], .ctor cFalse []]
      let arms := [then', else']
      let traced := lowerInputMatchTrace cond'.expr pats
        (fun i => (arms.map (fun arm => arm.expr)).getD i (.ctor cNil))
      lowerTracedMatch source cond' pats arms traced
  | .match_ scrut branches, .match_ source sscrut sarms => do
      let scrut' ← lowerIdentifiedExpr ke tvs vs scrut sscrut
      let arms' ← lowerIdentifiedBranches ke tvs vs branches sarms
      let pats := branches.map Prod.fst
      let traced := lowerInputMatchTrace scrut'.expr pats
        (fun i => (arms'.map (fun arm => arm.expr)).getD i (.ctor cNil))
      lowerTracedMatch source scrut' pats arms' traced
  | _, _ => none

def lowerIdentifiedList (ke : KindEnv) (tvs vs : List ValName) :
    List Surface.Expr → List IdentifiedExpr → Option (List InputLowered)
  | [], [] => some []
  | e :: es, se :: ses => do
      let e' ← lowerIdentifiedExpr ke tvs vs e se
      let es' ← lowerIdentifiedList ke tvs vs es ses
      pure (e' :: es')
  | _, _ => none

def lowerIdentifiedBranches (ke : KindEnv) (tvs vs : List ValName) :
    List (Surface.Pattern × Surface.Expr) → List IdentifiedExpr → Option (List InputLowered)
  | [], [] => some []
  | (pat, body) :: rest, sbody :: srest => do
      let body' ← lowerIdentifiedExpr ke tvs (patVars pat ++ vs) body sbody
      let rest' ← lowerIdentifiedBranches ke tvs vs rest srest
      pure (body' :: rest')
  | _, _ => none

def lowerIdentifiedRecBinds (ke : KindEnv) (tvs recScope : List ValName)
    (owner : SourceNode) : Nat → List Surface.Binding → List IdentifiedExpr → Option (List InputLowered)
  | _, [], [] => some []
  | member, b :: rest, srhs :: srest => do
      let tvs' := letAnnTyPrefix b.tyParams
        (finalizeInputAnn b.tyParams b.params b.ann) ++ tvs
      let rhsCore ← lowerIdentifiedExpr ke tvs' (paramTermScope b.params recScope) b.rhs srhs
      let rhs' ← wrapParamsWithProvenance ke tvs' owner
        (fun i => .letRecParam owner.id member i) 0 b.params rhsCore
      let rest' ← lowerIdentifiedRecBinds ke tvs recScope owner (member + 1) rest srest
      pure (rhs' :: rest')
  | _, _, _ => none

def lowerListWithProvenance (owner : SourceNode) (index : Nat) (isRoot : Bool) :
    List InputLowered → Option InputLowered
  | [] =>
      let originKind := if isRoot then OriginKind.authored else .generated (.listCtor index)
      some {
        expr := .ctor cNil
        sourceNodes := if isRoot then [owner] else []
        sourceTargets := if isRoot then [(owner.id, .present [[]])] else []
        coreOrigins := [([], ⟨owner, originKind⟩)]
        binderTargets := [] }
  | item :: rest => do
      let tail ← lowerListWithProvenance owner (index + 1) false rest
      let expr := .app (.app (.ctor cCons) item.expr) tail.expr
      let rootKind := if isRoot then OriginKind.authored else .generated (.listTailApp index)
      let ownNodes := if isRoot then [owner] else []
      let ownTargets := if isRoot then [(owner.id, .present [[]])] else []
      let item' := item.belowPath [.appFun, .appArg]
      let tail' := tail.belowPath [.appArg]
      pure {
        expr
        sourceNodes := ownNodes ++ item'.sourceNodes ++ tail'.sourceNodes
        sourceTargets := ownTargets ++ item'.sourceTargets ++ tail'.sourceTargets
        coreOrigins :=
          [([], ⟨owner, rootKind⟩),
           generatedOrigin owner [.appFun] (.listPartialApp index),
           generatedOrigin owner [.appFun, .appFun] (.listCtor index)] ++
          item'.coreOrigins ++ tail'.coreOrigins
        binderTargets := item'.binderTargets ++ tail'.binderTargets }
end

/-- Construction-time lowering. The `SpannedExpr` must mirror the
    Surface tree; shape mismatches fail instead of silently corrupting paths. -/
def lowerWithProvenance (ctors : CtorEnv) (surface : Surface.Expr)
    (spanned : SpannedExpr) : Option InputLowered := do
  let identified := identify spanned
  let lowered ← lowerIdentifiedExpr (kindEnvOfCtors ctors) [] [] surface identified
  -- The ID pass, rather than the lowering recursion, is authoritative for the
  -- source domain. This makes an accidentally omitted source target observable
  -- to `sourceTargetsTotal` instead of letting both sides omit the same node.
  pure { lowered with sourceNodes := identified.nodes }

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
  | .letRec _ rhss _, .letRecRhs member :: rest => do
      let rhs ← rhss[member]?
      inputAtCorePath rhs rest
  | .letRec _ _ body, .letRecBody :: rest => inputAtCorePath body rest
  | _, _ => none
termination_by _ path => path.length

structure TypedLowered where
  /-- The declaration environment shared by lowering and HM inference. -/
  ctors : CtorEnv
  /-- Authored annotation modes before completion. -/
  input : InferInput
  lowering : Lowered
  inference : InferenceResult
  sourceTypes : SourceTypeMap
  inferredBinderSchemes : InferredSurfaceBinderSchemes
  patternBinderTypes : PatternBinderTypeMap

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
  exactlyOnce (logicalCorePaths r.lowering.expr) (r.inference.nodeTypes.map Prod.fst)

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

/-- Infer and complete the lowered input once, retaining its emitted paths for
    all type and scheme joins. The completed output is the runtime/Core payload. -/
def inferWithProvenance (ctors : CtorEnv) (lowering : InputLowered) : Option TypedLowered := do
  let inference ← inferWithTypes ctors lowering.expr
  pure {
    ctors
    input := lowering.expr
    lowering := lowering.mapExpr (fun _ => inference.completedExpr)
    inference
    sourceTypes := lowering.sourceTargets.map fun (id, target) =>
      (id, typesAtTarget inference.nodeTypes target)
    inferredBinderSchemes := joinBinderSchemes lowering.binderTargets inference.binderSchemes
    patternBinderTypes := patternBinderTypesAt inference.nodeTypes lowering.binderTargets }

end SurfaceBridge.Provenance
