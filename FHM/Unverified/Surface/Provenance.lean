import FHM.CorePath
import FHM.Surface.Span
import FHM.SurfaceBridge
import FHM.Unverified.Surface.CountScope

/-! # Construction-time Surface → Core provenance

This module carries construction-time provenance through ordinary lowering and
through `PatComp`'s compiler-owned emission trace. Source IDs are assigned to
the parser's span tree before lowering. The lowerer then emits the Core term and
both directions of the correspondence while it constructs the term; it never
tries to reconcile a finished Surface tree with finished Core.
-/

open Surface.Span

namespace SurfaceBridge.Provenance

open FHM.Bounds.Scope

abbrev SourceId := Nat

structure SourceNode where
  id : SourceId
  span : Span
  deriving Repr, DecidableEq, BEq

instance : Inhabited SourceNode := ⟨⟨0, Span.empty⟩⟩

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
def identifyFrom (next : SourceId) : SpannedExpr → SourceId × IdentifiedExpr
  | .leaf span => (next + 1, .leaf ⟨next, span⟩)
  | .pair span a b =>
      let root := next
      let (next, a') := identifyFrom (next + 1) a
      let (next, b') := identifyFrom next b
      (next, .pair ⟨root, span⟩ a' b')
  | .cons span h t =>
      let root := next
      let (next, h') := identifyFrom (next + 1) h
      let (next, t') := identifyFrom next t
      (next, .cons ⟨root, span⟩ h' t')
  | .list span items =>
      let root := next
      let (next, items') := identifyListFrom (next + 1) items
      (next, .list ⟨root, span⟩ items')
  | .lambda span body =>
      let root := next
      let (next, body') := identifyFrom (next + 1) body
      (next, .lambda ⟨root, span⟩ body')
  | .app span fn arg =>
      let root := next
      let (next, fn') := identifyFrom (next + 1) fn
      let (next, arg') := identifyFrom next arg
      (next, .app ⟨root, span⟩ fn' arg')
  | .letIn span rhs body =>
      let root := next
      let (next, rhs') := identifyFrom (next + 1) rhs
      let (next, body') := identifyFrom next body
      (next, .letIn ⟨root, span⟩ rhs' body')
  | .letRecIn span rhss body =>
      let root := next
      let (next, rhss') := identifyListFrom (next + 1) rhss
      let (next, body') := identifyFrom next body
      (next, .letRecIn ⟨root, span⟩ rhss' body')
  | .ife span cond then_ else_ =>
      let root := next
      let (next, cond') := identifyFrom (next + 1) cond
      let (next, then') := identifyFrom next then_
      let (next, else') := identifyFrom next else_
      (next, .ife ⟨root, span⟩ cond' then' else')
  | .match_ span scrut arms =>
      let root := next
      let (next, scrut') := identifyFrom (next + 1) scrut
      let (next, arms') := identifyListFrom next arms
      (next, .match_ ⟨root, span⟩ scrut' arms')

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

structure Lowered where
  expr : Expr
  sourceNodes : List SourceNode
  sourceTargets : SourceTargetMap
  coreOrigins : CoreOriginMap
  binderTargets : BinderTargetMap
  counts : Metadata := {}
  deriving Repr

namespace Lowered

def belowPath (pre : CorePath) (r : Lowered) : Lowered :=
  { r with
    sourceTargets := r.sourceTargets.map fun (id, target) => (id, target.belowPath pre)
    coreOrigins := r.coreOrigins.map fun (path, origin) => (pre ++ path, origin)
    binderTargets := r.binderTargets.map fun (source, target) =>
      (source, target.belowPath pre)
    counts := r.counts.below pre }

def metadata (expr : Expr) (parts : List Lowered) : Lowered :=
  { expr
    sourceNodes := parts.flatMap (fun r => r.sourceNodes)
    sourceTargets := parts.flatMap (fun r => r.sourceTargets)
    coreOrigins := parts.flatMap (fun r => r.coreOrigins)
    binderTargets := parts.flatMap (fun r => r.binderTargets)
    counts := Metadata.combine (parts.map (·.counts)) }

end Lowered

def authoredRoot (source : SourceNode) (expr : Expr) : Lowered :=
  { expr
    sourceNodes := [source]
    sourceTargets := [(source.id, .present [[]])]
    coreOrigins := [([], ⟨source, .authored⟩)]
    binderTargets := [] }

def generatedOrigin (source : SourceNode) (path : CorePath) (reason : GenerationReason) :
    CorePath × Origin :=
  (path, ⟨source, .generated reason⟩)

def combineAuthored (source : SourceNode) (expr : Expr) (parts : List Lowered)
    (generated : CoreOriginMap := []) (binders : BinderTargetMap := []) : Lowered :=
  let children := Lowered.metadata expr parts
  { expr
    sourceNodes := source :: children.sourceNodes
    sourceTargets := (source.id, .present [[]]) :: children.sourceTargets
    coreOrigins := ([], ⟨source, .authored⟩) :: generated ++ children.coreOrigins
    binderTargets := binders ++ children.binderTargets
    counts := children.counts }

mutual
def logicalCorePaths : Expr → List CorePath
  | .found _ inner => logicalCorePaths inner
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

def wrapParamsWithProvenance (ke : KindEnv) (tvs : List ValName) (owner : SourceNode)
    (site : Nat → SurfaceBinderSite) :
    Nat → List (ValName × Option Surface.Ty) → Lowered → (scope : Lexical := []) → Option Lowered
  | _, [], rhs, _ => some rhs
  | index, (_name, ann) :: rest, rhs, scope => do
      let inner ← wrapParamsWithProvenance ke tvs owner site (index + 1) rest rhs scope
      let ann' ← CountScope.lowerAnnScoped ke tvs scope ann
      let child := inner.belowPath [.lambdaBody]
      pure {
        expr := .lambda ann' inner.expr
        sourceNodes := child.sourceNodes
        sourceTargets := child.sourceTargets
        coreOrigins := generatedOrigin owner [] (.valueParamLambda index) :: child.coreOrigins
        binderTargets := (site index, .present [.lambda []]) :: child.binderTargets
        counts := Metadata.combine [CountScope.annotationMetadata (.lambda []) scope ann, child.counts] }

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

def absentSourceTargets (reason : OriginAbsence) (r : Lowered) : SourceTargetMap :=
  r.sourceNodes.map fun node => (node.id, .absent reason)

def absentBinderTargets (reason : OriginAbsence) (r : Lowered) : BinderTargetMap :=
  r.binderTargets.map fun (site, _target) => (site, .absent reason)

def traceArmRoots (act : Nat) (trace : PatComp.EmissionTrace) : List CorePath :=
  trace.armBodyRoots.filterMap fun (candidate, path) =>
    if candidate == act then some path else none

def clonedArmParts (trace : PatComp.EmissionTrace) (arms : List Lowered) : List Lowered :=
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
def lowerTracedMatch (source : SourceNode) (scrut : Lowered)
    (pats : List Surface.Pattern) (arms : List Lowered)
    (traced : PatComp.TracedLowering) : Option Lowered := do
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
    binderTargets
    counts := Metadata.combine (scrutPart.counts :: armParts.map (·.counts)) }

mutual
def lowerIdentifiedExpr (ke : KindEnv) (tvs vs : List ValName) :
    Surface.Expr → IdentifiedExpr → (scope : Lexical := []) → Option Lowered
  | .primLit (.bool b), .leaf source, _ =>
      some (authoredRoot source (.ctor (if b then cTrue else cFalse)))
  | .primLit .unit, .leaf source, _ => some (authoredRoot source (.primLit .unit))
  | .primLit (.int n), .leaf source, _ => some (authoredRoot source (.primLit (.int n)))
  | .primLit (.nat n), .leaf source, _ => some (authoredRoot source (.primLit (.nat n)))
  | .primLit (.char c), .leaf source, _ => some (authoredRoot source (.primLit (.char c)))
  | .primBinOp op, .leaf source, _ => some (authoredRoot source (.primBinOp op))
  | .pair a b, .pair source sa sb, scope => do
      let a' ← lowerIdentifiedExpr ke tvs vs a sa scope
      let b' ← lowerIdentifiedExpr ke tvs vs b sb scope
      let expr := .app (.app (.ctor cPair) a'.expr) b'.expr
      pure (combineAuthored source expr
        [a'.belowPath [.appFun, .appArg], b'.belowPath [.appArg]]
        [generatedOrigin source [.appFun] .pairPartialApp,
         generatedOrigin source [.appFun, .appFun] .pairCtor])
  | .cons h t, .cons source sh st, scope => do
      let h' ← lowerIdentifiedExpr ke tvs vs h sh scope
      let t' ← lowerIdentifiedExpr ke tvs vs t st scope
      let expr := .app (.app (.ctor cCons) h'.expr) t'.expr
      pure (combineAuthored source expr
        [h'.belowPath [.appFun, .appArg], t'.belowPath [.appArg]]
        [generatedOrigin source [.appFun] .consPartialApp,
         generatedOrigin source [.appFun, .appFun] .consCtor])
  | .list items, .list source sitems, scope => do
      let items' ← lowerIdentifiedList ke tvs vs items sitems scope
      lowerListWithProvenance source 0 true items'
  | .lambda param paramAnn body, .lambda source sbody, scope => do
      let ann' ← CountScope.lowerAnnScoped ke tvs scope paramAnn
      match param with
      | .name name => do
          let body' ← lowerIdentifiedExpr ke tvs (name :: vs) body sbody scope
          let result := combineAuthored source (.lambda ann' body'.expr)
            [body'.belowPath [.lambdaBody]] []
            [(.lambda source.id, .present [.lambda []])]
          pure { result with counts := Metadata.combine [
            CountScope.annotationMetadata (.lambda []) scope paramAnn, result.counts] }
      | .wildcard => do
          let body' ← lowerIdentifiedExpr ke tvs (.mk "_" :: vs) body sbody scope
          let result := combineAuthored source (.lambda ann' body'.expr)
            [body'.belowPath [.lambdaBody]] []
            [(.lambda source.id, .present [.lambda []])]
          pure { result with counts := Metadata.combine [
            CountScope.annotationMetadata (.lambda []) scope paramAnn, result.counts] }
      | _ => none
  | .app fn arg, .app source sfn sarg, scope => do
      let fn' ← lowerIdentifiedExpr ke tvs vs fn sfn scope
      let arg' ← lowerIdentifiedExpr ke tvs vs arg sarg scope
      pure (combineAuthored source (.app fn'.expr arg'.expr)
        [fn'.belowPath [.appFun], arg'.belowPath [.appArg]])
  | .letIn name tyParams params ann rhs body, .letIn source srhs sbody, scope => do
      let annF := finalizeAnn tyParams params ann
      let ann' ← CountScope.lowerPolyScoped ke scope annF
      let tvs' := letAnnTyPrefix tyParams annF ++ tvs
      let rhsCore ← lowerIdentifiedExpr ke tvs' (paramTermScope params vs) rhs srhs scope
      let rhs' ← wrapParamsWithProvenance ke tvs' source
        (fun i => .letParam source.id i) 0 params rhsCore scope
      let body' ← lowerIdentifiedExpr ke tvs (name :: vs) body sbody scope
      let result := combineAuthored source (.letIn ann' rhs'.expr body'.expr)
        [rhs'.belowPath [.letRhs], body'.belowPath [.letBody]] []
        [(.letIn source.id, .present [.letIn []])]
      pure { result with counts := Metadata.combine [
        CountScope.annotationMetadata (.letIn []) scope (annF.map (·.body)), result.counts] }
  | .letRecIn binds body, .letRecIn source srhss sbody, scope => do
      let recScope := binds.map (fun b => b.name) ++ vs
      let ownScopes := binds.mapIdx fun member b => telescope source.id member b.natBinders
      let anns' ← (binds.zip ownScopes).mapM fun (b, own) =>
        CountScope.lowerPolyScoped ke (own ++ scope) (finalizeAnn b.tyParams b.params b.ann)
      let countParts := (binds.zip ownScopes).mapIdx fun member (b, own) =>
        Metadata.combine [CountScope.telescopeMetadata (.letRec [] member) own,
          CountScope.annotationMetadata (.letRec [] member) (own ++ scope)
            ((finalizeAnn b.tyParams b.params b.ann).map (·.body))]
      let bindings' ← lowerIdentifiedRecBinds ke tvs recScope source 0 binds srhss scope
      let body' ← lowerIdentifiedExpr ke tvs recScope body sbody scope
      let bindingExprs := bindings'.map fun r => r.expr
      let bindingParts := bindings'.mapIdx fun member r => r.belowPath [.letRecRhs member]
      let groupBinders := binds.mapIdx fun member _ =>
        (.letRec source.id member, .present [.letRec [] member])
      let result := combineAuthored source (.letRec anns' bindingExprs body'.expr)
        (bindingParts ++ [body'.belowPath [.letRecBody]]) [] groupBinders
      pure { result with counts := Metadata.combine (result.counts :: countParts) }
  | .var name, .leaf source, _ => do
      let index ← tvarIndex vs name
      pure (authoredRoot source (.var index))
  | .ctor name, .leaf source, _ => some (authoredRoot source (.ctor name))
  | .ife cond then_ else_, .ife source scond sthen selse, scope => do
      let cond' ← lowerIdentifiedExpr ke tvs vs cond scond scope
      let then' ← lowerIdentifiedExpr ke tvs vs then_ sthen scope
      let else' ← lowerIdentifiedExpr ke tvs vs else_ selse scope
      let pats : List Surface.Pattern := [.ctor cTrue [], .ctor cFalse []]
      let arms := [then', else']
      let traced := PatComp.lowerMatchTrace cond'.expr pats
        (fun i => (arms.map (fun arm => arm.expr)).getD i (.ctor cNil))
      lowerTracedMatch source cond' pats arms traced
  | .match_ scrut branches, .match_ source sscrut sarms, scope => do
      let scrut' ← lowerIdentifiedExpr ke tvs vs scrut sscrut scope
      let arms' ← lowerIdentifiedBranches ke tvs vs branches sarms scope
      let pats := branches.map Prod.fst
      let traced := PatComp.lowerMatchTrace scrut'.expr pats
        (fun i => (arms'.map (fun arm => arm.expr)).getD i (.ctor cNil))
      lowerTracedMatch source scrut' pats arms' traced
  | _, _, _ => none

def lowerIdentifiedList (ke : KindEnv) (tvs vs : List ValName) :
    List Surface.Expr → List IdentifiedExpr → (scope : Lexical := []) → Option (List Lowered)
  | [], [], _ => some []
  | e :: es, se :: ses, scope => do
      let e' ← lowerIdentifiedExpr ke tvs vs e se scope
      let es' ← lowerIdentifiedList ke tvs vs es ses scope
      pure (e' :: es')
  | _, _, _ => none

def lowerIdentifiedBranches (ke : KindEnv) (tvs vs : List ValName) :
    List (Surface.Pattern × Surface.Expr) → List IdentifiedExpr → (scope : Lexical := []) → Option (List Lowered)
  | [], [], _ => some []
  | (pat, body) :: rest, sbody :: srest, scope => do
      let body' ← lowerIdentifiedExpr ke tvs (patVars pat ++ vs) body sbody scope
      let rest' ← lowerIdentifiedBranches ke tvs vs rest srest scope
      pure (body' :: rest')
  | _, _, _ => none

def lowerIdentifiedRecBinds (ke : KindEnv) (tvs recScope : List ValName)
    (owner : SourceNode) : Nat → List Surface.Binding → List IdentifiedExpr →
      (scope : Lexical := []) → Option (List Lowered)
  | _, [], [], _ => some []
  | member, b :: rest, srhs :: srest, scope => do
      let tvs' := bindingLowerTyScope b tvs
      let own := telescope owner.id member b.natBinders
      let rhsCore ← lowerIdentifiedExpr ke tvs' (paramTermScope b.params recScope) b.rhs srhs (own ++ scope)
      let rhs' ← wrapParamsWithProvenance ke tvs' owner
        (fun i => .letRecParam owner.id member i) 0 b.params rhsCore (own ++ scope)
      let rest' ← lowerIdentifiedRecBinds ke tvs recScope owner (member + 1) rest srest scope
      pure (rhs' :: rest')
  | _, _, _, _ => none

def lowerListWithProvenance (owner : SourceNode) (index : Nat) (isRoot : Bool) :
    List Lowered → Option Lowered
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
        binderTargets := item'.binderTargets ++ tail'.binderTargets
        counts := Metadata.combine [item'.counts, tail'.counts] }
end

/-- Construction-time lowering. The `SpannedExpr` must mirror the
    Surface tree; shape mismatches fail instead of silently corrupting paths. -/
def lowerWithProvenance (ctors : CtorEnv) (surface : Surface.Expr)
    (spanned : SpannedExpr) : Option Lowered := do
  let identified := identify spanned
  let lowered ← lowerIdentifiedExpr (kindEnvOfCtors ctors) [] [] surface identified
  -- The ID pass, rather than the lowering recursion, is authoritative for the
  -- source domain. This makes an accidentally omitted source target observable
  -- to `sourceTargetsTotal` instead of letting both sides omit the same node.
  pure { lowered with sourceNodes := identified.nodes }

def foundTyAtCorePath (e : Expr) (path : CorePath) : Option Ty := do
  let node ← e.atCorePath path
  match node with
  | .found ty _ => some ty
  | _ => none

abbrev SourceTypeMap := List (SourceId × List (CorePath × Ty))
abbrev InferredSurfaceBinderSchemes := List (SurfaceBinderSite × PolyTy)
abbrev PatternBinderTypeMap := List (SurfaceBinderSite × List (CorePath × Ty))

structure TypedLowered where
  lowering : Lowered
  inference : FoundResult
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
    every surviving capture let has a `.found` RHS type and eliminated captures
    have an explicit empty result. -/
def TypedLowered.patternBinderTypesTotal (r : TypedLowered) : Bool :=
  let targets := patternBinderTargets r.lowering.binderTargets
  targets.length == r.patternBinderTypes.length &&
    (targets.zip r.patternBinderTypes).all fun pair =>
      let ((site, target), (typedSite, types)) := pair
      let paths := captureRhsPaths target
      site == typedSite && paths.length == types.length &&
        (paths.zip types).all fun (path, typedPath, _ty) => path == typedPath

def typesAtTarget (output : Expr) : OriginTarget → List (CorePath × Ty)
  | .absent _ => []
  | .present paths => paths.filterMap fun path =>
      (foundTyAtCorePath output path).map fun ty => (path, ty)

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

def patternBinderTypesAt (output : Expr) (targets : BinderTargetMap) : PatternBinderTypeMap :=
  targets.filterMap fun (surface, target) =>
    match surface, target with
    | .patCapture _ _ _, .present sites =>
        let types := sites.flatMap fun
          | .patCapture paths _ => paths.filterMap fun path =>
              let rhsPath := path ++ [.letRhs]
              (foundTyAtCorePath output rhsPath).map fun ty => (rhsPath, ty)
          | _ => []
        some (surface, types)
    | .patCapture _ _ _, .absent _ => some (surface, [])
    | _, _ => none

/-- Infer exactly the lowered Core term, then join types and inferred schemes by
    the paths emitted during lowering. No Surface/Core structural zip occurs. -/
def inferWithProvenance (ctors : CtorEnv) (lowering : Lowered) : Option TypedLowered := do
  let inference ← inferFound ctors lowering.expr
  pure {
    lowering
    inference
    sourceTypes := lowering.sourceTargets.map fun (id, target) =>
      (id, typesAtTarget inference.output target)
    inferredBinderSchemes := joinBinderSchemes lowering.binderTargets inference.binderSchemes
    patternBinderTypes := patternBinderTypesAt inference.output lowering.binderTargets }

end SurfaceBridge.Provenance
