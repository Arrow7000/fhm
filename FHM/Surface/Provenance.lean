import FHM.CorePath
import FHM.Surface.Span
import FHM.SurfaceBridge

/-! # Construction-time Surface → Core provenance

This module is the first, deliberately match-free provenance slice. Source IDs
are assigned to the parser's span tree before lowering. The lowerer then emits
the Core term and both directions of the correspondence while it constructs the
term; it never tries to reconcile a finished Surface tree with finished Core.

`if` and `match` are rejected here because both pass through `PatComp`. They
need instrumentation inside the pattern compiler before this API can honestly
claim total provenance for them.
-/

open Surface.Span

namespace SurfaceBridge.Provenance

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
  deriving Repr, DecidableEq, BEq

abbrev SourceTargetMap := List (SourceId × OriginTarget)
abbrev CoreOriginMap := List (CorePath × Origin)
abbrev BinderTargetMap := List (SurfaceBinderSite × CoreBinderSite)

structure Lowered where
  expr : Expr
  sourceNodes : List SourceNode
  sourceTargets : SourceTargetMap
  coreOrigins : CoreOriginMap
  binderTargets : BinderTargetMap
  deriving Repr

namespace Lowered

def belowPath (pre : CorePath) (r : Lowered) : Lowered :=
  { r with
    sourceTargets := r.sourceTargets.map fun (id, target) => (id, target.belowPath pre)
    coreOrigins := r.coreOrigins.map fun (path, origin) => (pre ++ path, origin)
    binderTargets := r.binderTargets.map fun (source, target) =>
      (source, pre.foldr CoreBinderSite.below target) }

def metadata (expr : Expr) (parts : List Lowered) : Lowered :=
  { expr
    sourceNodes := parts.flatMap (fun r => r.sourceNodes)
    sourceTargets := parts.flatMap (fun r => r.sourceTargets)
    coreOrigins := parts.flatMap (fun r => r.coreOrigins)
    binderTargets := parts.flatMap (fun r => r.binderTargets) }

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
    binderTargets := binders ++ children.binderTargets }

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
  r.binderTargets.all fun (_, target) =>
    !target.paths.isEmpty && target.paths.all fun path => (r.expr.atCorePath path).isSome

def Lowered.provenanceTotal (r : Lowered) : Bool :=
  r.coreOriginsTotal && r.sourceTargetsTotal && r.binderTargetsResolve

def wrapParamsWithProvenance (ke : KindEnv) (tvs : List ValName) (owner : SourceNode)
    (site : Nat → SurfaceBinderSite) :
    Nat → List (ValName × Option Surface.Ty) → Lowered → Option Lowered
  | _, [], rhs => some rhs
  | index, (_name, ann) :: rest, rhs => do
      let inner ← wrapParamsWithProvenance ke tvs owner site (index + 1) rest rhs
      let ann' ← lowerAnn ke tvs ann
      let child := inner.belowPath [.lambdaBody]
      pure {
        expr := .lambda ann' inner.expr
        sourceNodes := child.sourceNodes
        sourceTargets := child.sourceTargets
        coreOrigins := generatedOrigin owner [] (.valueParamLambda index) :: child.coreOrigins
        binderTargets := (site index, .lambda []) :: child.binderTargets }

mutual
def lowerIdentifiedExpr (ke : KindEnv) (tvs vs : List ValName) :
    Surface.Expr → IdentifiedExpr → Option Lowered
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
      let ann' ← lowerAnn ke tvs paramAnn
      match param with
      | .name name => do
          let body' ← lowerIdentifiedExpr ke tvs (name :: vs) body sbody
          pure (combineAuthored source (.lambda ann' body'.expr)
            [body'.belowPath [.lambdaBody]] []
            [(.lambda source.id, .lambda [])])
      | .wildcard => do
          let body' ← lowerIdentifiedExpr ke tvs (.mk "_" :: vs) body sbody
          pure (combineAuthored source (.lambda ann' body'.expr)
            [body'.belowPath [.lambdaBody]] []
            [(.lambda source.id, .lambda [])])
      | _ => none
  | .app fn arg, .app source sfn sarg => do
      let fn' ← lowerIdentifiedExpr ke tvs vs fn sfn
      let arg' ← lowerIdentifiedExpr ke tvs vs arg sarg
      pure (combineAuthored source (.app fn'.expr arg'.expr)
        [fn'.belowPath [.appFun], arg'.belowPath [.appArg]])
  | .letIn name tyParams params ann rhs body, .letIn source srhs sbody => do
      let annF := finalizeAnn tyParams params ann
      let ann' ← lowerPolyAnn ke annF
      let tvs' := letAnnTyPrefix tyParams annF ++ tvs
      let rhsCore ← lowerIdentifiedExpr ke tvs' (paramTermScope params vs) rhs srhs
      let rhs' ← wrapParamsWithProvenance ke tvs' source
        (fun i => .letParam source.id i) 0 params rhsCore
      let body' ← lowerIdentifiedExpr ke tvs (name :: vs) body sbody
      pure (combineAuthored source (.letIn ann' rhs'.expr body'.expr)
        [rhs'.belowPath [.letRhs], body'.belowPath [.letBody]] []
        [(.letIn source.id, .letIn [])])
  | .letRecIn binds body, .letRecIn source srhss sbody => do
      let recScope := binds.map (fun b => b.name) ++ vs
      let anns' ← lowerAnnList ke (binds.map fun b => finalizeAnn b.tyParams b.params b.ann)
      let bindings' ← lowerIdentifiedRecBinds ke tvs recScope source 0 binds srhss
      let body' ← lowerIdentifiedExpr ke tvs recScope body sbody
      let bindingExprs := bindings'.map fun r => r.expr
      let bindingParts := bindings'.mapIdx fun member r => r.belowPath [.letRecRhs member]
      let groupBinders := binds.mapIdx fun member _ =>
        (.letRec source.id member, .letRec [] member)
      pure (combineAuthored source (.letRec anns' bindingExprs body'.expr)
        (bindingParts ++ [body'.belowPath [.letRecBody]]) [] groupBinders)
  | .var name, .leaf source => do
      let index ← tvarIndex vs name
      pure (authoredRoot source (.var index))
  | .ctor name, .leaf source => some (authoredRoot source (.ctor name))
  | .ife _ _ _, .ife _ _ _ _ => none
  | .match_ _ _, .match_ _ _ _ => none
  | _, _ => none

def lowerIdentifiedList (ke : KindEnv) (tvs vs : List ValName) :
    List Surface.Expr → List IdentifiedExpr → Option (List Lowered)
  | [], [] => some []
  | e :: es, se :: ses => do
      let e' ← lowerIdentifiedExpr ke tvs vs e se
      let es' ← lowerIdentifiedList ke tvs vs es ses
      pure (e' :: es')
  | _, _ => none

def lowerIdentifiedRecBinds (ke : KindEnv) (tvs recScope : List ValName)
    (owner : SourceNode) : Nat → List Surface.Binding → List IdentifiedExpr → Option (List Lowered)
  | _, [], [] => some []
  | member, b :: rest, srhs :: srest => do
      let tvs' := bindingLowerTyScope b tvs
      let rhsCore ← lowerIdentifiedExpr ke tvs' (paramTermScope b.params recScope) b.rhs srhs
      let rhs' ← wrapParamsWithProvenance ke tvs' owner
        (fun i => .letRecParam owner.id member i) 0 b.params rhsCore
      let rest' ← lowerIdentifiedRecBinds ke tvs recScope owner (member + 1) rest srest
      pure (rhs' :: rest')
  | _, _, _ => none

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
        binderTargets := item'.binderTargets ++ tail'.binderTargets }
end

/-- Match-free construction-time lowering. The `SpannedExpr` must mirror the
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

structure TypedLowered where
  lowering : Lowered
  inference : FoundResult
  sourceTypes : SourceTypeMap
  inferredBinderSchemes : InferredSurfaceBinderSchemes

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

def typesAtTarget (output : Expr) : OriginTarget → List (CorePath × Ty)
  | .absent _ => []
  | .present paths => paths.filterMap fun path =>
      (foundTyAtCorePath output path).map fun ty => (path, ty)

def joinBinderSchemes (targets : BinderTargetMap) (schemes : BinderSchemeMap) :
    InferredSurfaceBinderSchemes :=
  targets.filterMap fun (surface, core) =>
    (schemes.find? fun pair => pair.1 == core).map fun pair => (surface, pair.2)

/-- Infer exactly the lowered Core term, then join types and inferred schemes by
    the paths emitted during lowering. No Surface/Core structural zip occurs. -/
def inferWithProvenance (ctors : CtorEnv) (lowering : Lowered) : Option TypedLowered := do
  let inference ← inferFound ctors lowering.expr
  pure {
    lowering
    inference
    sourceTypes := lowering.sourceTargets.map fun (id, target) =>
      (id, typesAtTarget inference.output target)
    inferredBinderSchemes := joinBinderSchemes lowering.binderTargets inference.binderSchemes }

end SurfaceBridge.Provenance
