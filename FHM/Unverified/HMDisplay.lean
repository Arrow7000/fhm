import FHM.Unverified.HMArtifacts

/-! Human-facing HM type names. No inference or checking is changed here.
Source signature names are preserved; synthesized variables receive compact
alpha names rather than the worker's debug IDs. This is unverified presentation.
-/

namespace FHM.Unverified.HMDisplay

open SurfaceBridge SurfaceBridge.Provenance FHM.Unverified.HMArtifacts

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
  | .bl _ _ e => prettyParenIf (prec ≥ 2) ("List " ++ prettyAux ctx 2 e)
  | .customTy (.mk "Pair") [a, b] => "(" ++ prettyAux ctx 0 a ++ ", " ++ prettyAux ctx 0 b ++ ")"
  | .customTy (.mk name) [] => name
  | .customTy (.mk name) args =>
      prettyParenIf (prec ≥ 2) (name ++ " " ++ String.intercalate " " (prettyArgs ctx args))

def prettyArgs (ctx : Context) : List Ty → List String
  | [] => []
  | t :: ts => prettyAux ctx 2 t :: prettyArgs ctx ts
end

def pretty (ctx : Context) (ty : Ty) : String :=
  prettyAux { ctx with freeIds := (ctx.freeIds ++ ty.freeVars).eraseDups } 0 ty.eraseBounds

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
    let rootTy ← foundTyAtCorePath typed.inference.output path
    let candidates := match declaredScheme typed display.site with
      | some sig => matchNames display.names rootTy.eraseBounds sig.body.eraseBounds
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
              let .arrow ty _ ← foundTyAtCorePath typed.inference.output path | none
              pure (pretty (context scopes path ty) ty)
          | _, _ => none

end FHM.Unverified.HMDisplay
