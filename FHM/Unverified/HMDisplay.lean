import FHM.Unverified.HMArtifacts

/-! Human-facing HM type names. No inference or checking is changed here.
Source signature names are preserved; synthesized variables receive compact
alpha names rather than the worker's debug IDs. This is unverified presentation.
-/

namespace FHM.Unverified.HMDisplay

open Surface.Span SurfaceBridge SurfaceBridge.Provenance FHM.Unverified.HMArtifacts

structure Context where
  boundNames : List String := []
  aliases : List (Nat × String) := []
  freeIds : List Nat := []
  deriving Inhabited

def alphaName (n : Nat) : String :=
  String.singleton (Char.ofNat (97 + n % 26)) ++
    (if n < 26 then "" else toString (n / 26))

def freeName (ctx : Context) (n : Nat) : String :=
  match ctx.aliases.find? (fun p => p.1 == n) with
  | some (_, name) => name
  | none =>
      let reserved := ctx.boundNames ++ ctx.aliases.map (·.2)
      let names := (List.range (ctx.freeIds.length + reserved.length + 1)).map alphaName
        |>.filter (fun name => !(reserved.contains name))
      names[ctx.freeIds.idxOf n]?.getD "a"

mutual
def prettyAux (ctx : Context) (prec : Nat) : Ty → String
  | .prim p => prettyPrimTy p
  | .bvar n => ctx.boundNames[n]?.getD (alphaName n)
  | .fvar n => freeName ctx n
  | .arrow a b => prettyParenIf (prec ≥ 1) (prettyAux ctx 1 a ++ " → " ++ prettyAux ctx 0 b)
  | .customTy (.mk "Pair") [a, b] => "(" ++ prettyAux ctx 0 a ++ ", " ++ prettyAux ctx 0 b ++ ")"
  | .customTy (.mk name) [] => name
  | .customTy (.mk name) args =>
      prettyParenIf (prec ≥ 2) (name ++ " " ++ String.intercalate " " (prettyArgs ctx args))

def prettyArgs (ctx : Context) : List Ty → List String
  | [] => []
  | t :: ts => prettyAux ctx 2 t :: prettyArgs ctx ts
end

def pretty (ctx : Context) (ty : Ty) : String :=
  prettyAux { ctx with freeIds := (ctx.freeIds ++ ty.freeVars).eraseDups } 0 ty

def scheme (ctx : Context) (names : List String) (sig : PolyTy) : String :=
  let reserved := ctx.boundNames ++ ctx.aliases.map (·.2)
  let names := if names.length == sig.paramCount then names else
    (List.range (sig.paramCount + reserved.length)).map alphaName
      |>.filter (fun name => !(reserved.contains name)) |>.take sig.paramCount
  let body := pretty { ctx with boundNames := names ++ ctx.boundNames } sig.body
  if names.isEmpty then body else "∀ " ++ String.intercalate " " names ++ ". " ++ body

structure Scope where
  path : CorePath
  names : List String
  aliases : List (Nat × String)
  freeIds : List Nat

/- Only bijective variable-to-variable correspondences supply display names.
    Composite specialization and identified independent variables are NOT
    projected into the inferred RHS type. In particular, unused parameters
    remain independently synthesized variables, not guessed signature domains. -/
mutual
partial def matchNames (names : List String) : Ty → Ty → List (Nat × String)
  | .fvar n, .bvar i => (names[i]?).toList.map (fun name => (n, name))
  | .arrow a b, .arrow x y => matchNames names a x ++ matchNames names b y
  | .customTy a args, .customTy b targets =>
      if a == b then matchNameArgs names args targets else []
  | _, _ => []

partial def matchNameArgs (names : List String) : List Ty → List Ty → List (Nat × String)
  | a :: args, b :: targets => matchNames names a b ++ matchNameArgs names args targets
  | _, _ => []
end

def rhsPath (typed : TypedLowered) (site : SurfaceBinderSite) : Option CorePath := do
  let (_, target) ← typed.lowering.binderTargets.find? (fun p => p.1 == site)
  let sites ← match target with | .present s => some s | .absent _ => none
  match ← sites.head? with
  | .letIn path => some (path ++ [.letRhs])
  | .letRec path member => some (path ++ [.letRecRhs member])
  | _ => none

def scopes (typed : TypedLowered) (locations : Locations) : List Scope :=
  locations.displays.filterMap fun display => do
    let path ← rhsPath typed display.site
    let rootTy ← nodeTyAtCorePath typed.inference.nodeTypes path
    let candidates := match declaredScheme typed display.site with
      | some sig => matchNames display.names rootTy sig.body
      | none => []
    let aliases := candidates.filter fun (n, name) => candidates.all fun (m, other) =>
      (m != n || other == name) && (other != name || m == n)
    let freeIds := (rootTy.freeVars ++ typed.sourceTypes.flatMap (fun (_, facts) =>
      facts.flatMap fun (p, ty) => if path.isPrefixOf p then ty.freeVars else [])).eraseDups
    pure ⟨path, display.names, aliases.eraseDups, freeIds⟩

def context (scopes : List Scope) (path : CorePath) (ty : Ty) : Context :=
  let enclosing := (scopes.filter fun s => s.path.isPrefixOf path).mergeSort
    (fun a b => a.path.length ≥ b.path.length)
  let aliases := enclosing.flatMap (·.aliases)
  let freeIds := ((enclosing.head?.map (·.freeIds)).getD [] ++ ty.freeVars).eraseDups
    |>.filter (fun n => !(aliases.any fun p => p.1 == n))
  ⟨enclosing.flatMap (·.names), aliases, freeIds⟩

def sourceType (typed : TypedLowered) (scopes : List Scope) (id : SourceId) : Option String := do
  let (path, ty) ← (typed.typesForSource id).head?
  pure (pretty (context scopes path ty) ty)

def binderType (typed : TypedLowered) (scopes : List Scope) (locations : Locations)
    (site : SurfaceBinderSite) : Option String :=
  let names := ((locations.displays.find? fun d => d.site == site).map (·.names)).getD []
  match declaredScheme typed site with
  | some sig =>
      let path := (rhsPath typed site).getD []
      -- The declaration introduces its own quantifiers; do not add them twice.
      let outerScopes := scopes.filter fun s => s.path != path
      some (scheme (context outerScopes path sig.body) names sig)
  | none =>
      match typed.inferredBinderSchemes.find? (fun p => p.1 == site) with
      | some (_, sig) =>
          let path := (rhsPath typed site).getD []
          some (scheme (context scopes path sig.body) [] sig)
      | none => do
          let (_, target) ← typed.lowering.binderTargets.find? (fun p => p.1 == site)
          match site, target with
          | .patCapture _ _ _, _ =>
              let (_, types) ← typed.patternBinderTypes.find? (fun p => p.1 == site)
              let (path, ty) ← types.head?
              pure (pretty (context scopes path ty) ty)
          | _, .present sites =>
              let .lambda path ← sites.head? | none
              let .arrow ty _ ← nodeTyAtCorePath typed.inference.nodeTypes path | none
              pure (pretty (context scopes path ty) ty)
          | _, _ => none

structure HoleDisplay where
  span : Span
  types : List String

/- Preserve one slot per written hole even if a presentation lookup fails. -/
mutual
partial def holeParts : Surface.Ty → Option Ty → List (Option Ty)
  | .hole, ty => [ty]
  | .arrow a b, ty =>
      let pair := ty.bind fun t => match t with | .arrow x y => some (x, y) | _ => none
      holeParts a (pair.map (·.1)) ++ holeParts b (pair.map (·.2))
  | .pair a b, ty =>
      let pair := ty.bind fun t => match t with
        | .customTy (.mk "Pair") [x, y] => some (x, y)
        | _ => none
      holeParts a (pair.map (·.1)) ++ holeParts b (pair.map (·.2))
  | .customTy name args, ty =>
      let targets := ty.bind fun t => match t with
        | .customTy n ts => if n == name then some ts else none
        | _ => none
      holeArgParts args (targets.getD [])
  | _, _ => []

partial def holeArgParts : List Surface.Ty → List Ty → List (Option Ty)
  | [], _ => []
  | a :: args, targets =>
      holeParts a targets.head? ++ holeArgParts args targets.tail
end

def binderMonotypes (typed : TypedLowered) (site : SurfaceBinderSite) : List (CorePath × Ty) :=
  let target : Option BinderOriginTarget := (typed.lowering.binderTargets.find? fun p => p.1 == site).map (·.2)
  match target with
  | some (.present sites) => sites.filterMap fun
      | .lambda path => do
          let .arrow domain _ ← nodeTyAtCorePath typed.inference.nodeTypes path | none
          pure (path, domain)
      | _ => none
  | _ => []

def completedSchemes (typed : TypedLowered) (site : SurfaceBinderSite) : List (CorePath × PolyTy) :=
  let target : Option BinderOriginTarget := (typed.lowering.binderTargets.find? fun p => p.1 == site).map (·.2)
  match target with
  | some (.present sites) => sites.filterMap fun
      | .letIn path => do
          let .letIn (some sig) _ _ ← typed.lowering.expr.atCorePath path | none
          pure (path ++ [.letRhs], sig)
      | .letRec path member => do
          let .letRec anns _ _ ← typed.lowering.expr.atCorePath path | none
          let some sig ← anns[member]? | none
          pure (path ++ [.letRecRhs member], sig)
      | _ => none
  | _ => []

def dropDomains : Nat → Ty → Option Ty
  | 0, ty => some ty
  | n + 1, .arrow _ body => dropDomains n body
  | _, _ => none

abbrev HoleValues := List (CorePath × Ty × List String)

def annotationParts (annotation : Surface.Ty) (facts : HoleValues) : List HoleValues :=
  let count := (holeParts annotation none).length
  (List.range count).map fun i => facts.filterMap fun (path, ty, names) => do
    let some part ← (holeParts annotation (some ty))[i]? | none
    pure (path, part, names)

def headerHoles (refs : List NameReference) (scopes : List Scope)
    (header bodyStart : Span) (parts : List HoleValues) : List HoleDisplay :=
  let holes := refs.filter fun r => r.kind == .typeHole && inside r.span header && before r.span bodyStart
  (holes.zip parts).map fun (ref, facts) =>
    let types := facts.map fun (path, ty, names) =>
      let ctx := context (if names.isEmpty then scopes else scopes.filter (fun s => s.path != path)) path ty
      pretty { ctx with boundNames := names ++ ctx.boundNames } ty
    ⟨ref.span, types.eraseDups⟩

def bindingHoleParts (typed : TypedLowered) (site : SurfaceBinderSite)
    (paramSite : Nat → SurfaceBinderSite) (tyParams : List ValName)
    (params : List (ValName × Option Surface.Ty)) (ann : Option Surface.PolyTy) : List HoleValues :=
  let paramParts := (params.mapIdx fun i (_, annotation) => match annotation with
    | none => []
    | some annotation => annotationParts annotation
        ((binderMonotypes typed (paramSite i)).map fun (p, t) => (p, t, []))).flatten
  let sigParts := match ann with
    | none => []
    | some sig =>
        let finalized := finalizeAnn tyParams params ann
        let writtenNames := displayNames finalized
        let facts := (completedSchemes typed site).filterMap fun (path, scheme) => do
          let body ← dropDomains (if (paramsToArrows params sig.body).isSome then params.length else 0) scheme.body
          let names := if writtenNames.length == scheme.paramCount then writtenNames
            else (List.range scheme.paramCount).map alphaName
          pure (path, body, names)
        annotationParts sig.body facts
  paramParts ++ sigParts

/- Join annotation tokens to their owner and the already inferred artifacts.
    Copied source arms may have several types; source locations never allocate
    or identify inference variables. -/
mutual
partial def holeDisplays (typed : TypedLowered) (scopes : List Scope)
    (bs : List BinderSpan) (refs : List NameReference) :
    Surface.Expr → IdentifiedExpr → List HoleDisplay
  | .lambda _ ann body, .lambda owner sb =>
      let parts := match ann with
        | none => []
        | some annotation => annotationParts annotation ((typed.typesForSource owner.id).filterMap fun (p, t) =>
            match t with | .arrow domain _ => some (p, domain, []) | _ => none)
      headerHoles refs scopes owner.span sb.source.span parts ++ holeDisplays typed scopes bs refs body sb
  | .letIn name tyParams params ann rhs body, .letIn owner sr sb =>
      let locations := locate bs (.letIn owner.id) name .val owner.span sb.source.span sr.source.span
      let header := match locations with
        | v :: _ => { owner.span with startLine := v.span.startLine, startCol := v.span.startCol }
        | [] => owner.span
      headerHoles refs scopes header sr.source.span
        (bindingHoleParts typed (.letIn owner.id) (.letParam owner.id) tyParams params ann) ++
        holeDisplays typed scopes bs refs rhs sr ++ holeDisplays typed scopes bs refs body sb
  | .letRecIn bindings body, .letRecIn owner rhss sb =>
      bindingHoleDisplays typed scopes bs refs owner 0 bindings rhss ++ holeDisplays typed scopes bs refs body sb
  | .pair a b, .pair _ sa sb | .cons a b, .cons _ sa sb | .app a b, .app _ sa sb =>
      holeDisplays typed scopes bs refs a sa ++ holeDisplays typed scopes bs refs b sb
  | .list es, .list _ ss => listHoleDisplays typed scopes bs refs es ss
  | .ife c t f, .ife _ sc st sf =>
      holeDisplays typed scopes bs refs c sc ++ holeDisplays typed scopes bs refs t st ++ holeDisplays typed scopes bs refs f sf
  | .match_ s arms, .match_ _ ss bodies =>
      holeDisplays typed scopes bs refs s ss ++ listHoleDisplays typed scopes bs refs (arms.map (·.2)) bodies
  | _, _ => []

partial def listHoleDisplays (typed : TypedLowered) (scopes : List Scope)
    (bs : List BinderSpan) (refs : List NameReference) :
    List Surface.Expr → List IdentifiedExpr → List HoleDisplay
  | e :: es, s :: ss => holeDisplays typed scopes bs refs e s ++ listHoleDisplays typed scopes bs refs es ss
  | _, _ => []

partial def bindingHoleDisplays (typed : TypedLowered) (scopes : List Scope)
    (bs : List BinderSpan) (refs : List NameReference) (owner : SourceNode) :
    Nat → List Surface.Binding → List IdentifiedExpr → List HoleDisplay
  | i, b :: bindings, r :: rhss =>
      let locations := bindingLocations bs owner i b r owner.span
      let header := match locations with
        | v :: _ => { owner.span with startLine := v.span.startLine, startCol := v.span.startCol }
        | [] => owner.span
      headerHoles refs scopes header r.source.span
        (bindingHoleParts typed (.letRec owner.id i) (.letRecParam owner.id i) b.tyParams b.params b.ann) ++
        holeDisplays typed scopes bs refs b.rhs r ++ bindingHoleDisplays typed scopes bs refs owner (i + 1) bindings rhss
  | _, _, _ => []
end

end FHM.Unverified.HMDisplay
