import FHM.Unverified.Surface.Provenance
import FHM.Pretty

/-!
Unverified presentation joins for the HM editor. Types come exclusively from
`inferWithProvenance`; this module supplies source names and token locations.
The parser-side tree is traversed, never reconciled with an inferred Core tree.
-/

namespace FHM.Unverified.HMArtifacts

open Surface.Span SurfaceBridge SurfaceBridge.Provenance

structure BinderLocation where
  site : SurfaceBinderSite
  name : String
  kind : BinderKind
  span : Span
  scope : Span

structure Occurrence where
  id : SourceId
  name : String
  kind : String

structure BindingDisplay where
  site : SurfaceBinderSite
  names : List String

structure Locations where
  binders : List BinderLocation := []
  occurrences : List Occurrence := []
  displays : List BindingDisplay := []
  deriving Inhabited

def Locations.append (a b : Locations) : Locations :=
  ⟨a.binders ++ b.binders, a.occurrences ++ b.occurrences, a.displays ++ b.displays⟩

def Locations.withExpr (a : Locations) (source : SourceNode) : Locations :=
  { a with occurrences := ⟨source.id, "expression", "expr"⟩ :: a.occurrences }

def displayNames (ann : Option Surface.PolyTy) : List String :=
  (ann.map (fun a => a.foralls.map (fun | .mk s => s))).getD []

def before (a b : Span) : Bool :=
  a.endLine < b.startLine || (a.endLine == b.startLine && a.endCol ≤ b.startCol)

/-- Slice one source line using the lexer/editor's UTF-16 columns. -/
def spanText (src : String) (span : Span) : String :=
  let line := (src.splitOn "\n")[span.startLine - 1]?.getD ""
  let (_, chars) := line.toList.foldl (fun (col, chars) c =>
    let next := col + if c.toNat > 0xFFFF then 2 else 1
    (next, if span.startCol ≤ col && col < span.endCol then c :: chars else chars)) (1, [])
  String.ofList chars.reverse

def inside (a b : Span) : Bool :=
  (b.startLine < a.startLine || (b.startLine == a.startLine && b.startCol ≤ a.startCol)) &&
  (a.endLine < b.endLine || (a.endLine == b.endLine && a.endCol ≤ b.endCol))

/-- Header tokens precede their RHS/body. Taking the last matching token keeps
    earlier same-name declarations out of nested and SCC-reordered bindings. -/
def locate (bs : List BinderSpan) (site : SurfaceBinderSite) (name : ValName)
    (kind : BinderKind) (header scope : Span) (bodyStart : Span) : List BinderLocation :=
  let name := match name with | .mk s => s
  let candidates := bs.filter fun b => b.name == name && b.kind == kind &&
    b.scope?.isNone && inside b.span header && before b.span bodyStart
  match candidates.getLast? with
  | none => []
  | some b => [⟨site, name, kind, b.span, scope⟩]

def bindingLocations (bs : List BinderSpan) (owner : SourceNode) (member : Nat)
    (b : Surface.Binding) (rhs : IdentifiedExpr) (scope : Span) : List BinderLocation :=
  let vals := locate bs (.letRec owner.id member) b.name .val owner.span scope rhs.source.span
  let header := match vals with
    | v :: _ => { owner.span with startLine := v.span.startLine, startCol := v.span.startCol }
    | [] => owner.span
  vals ++ (b.params.mapIdx fun i (name, _) =>
    locate bs (.letRecParam owner.id member i) name .param header rhs.source.span rhs.source.span).flatten

mutual
partial def collect (bs : List BinderSpan) : Surface.Expr → IdentifiedExpr → Locations
  | .var name, .leaf n => ⟨[], [⟨n.id, (match name with | .mk s => s), "val"⟩], []⟩
  | .ctor name, .leaf n => ⟨[], [⟨n.id, (match name with | .mk s => s), "ctor"⟩], []⟩
  | .primLit _, .leaf n => ⟨[], [⟨n.id, "literal", "lit"⟩], []⟩
  | .primBinOp _, .leaf n => ⟨[], [⟨n.id, "operator", "op"⟩], []⟩
  | .pair a b, .pair n sa sb | .cons a b, .cons n sa sb | .app a b, .app n sa sb =>
      ((collect bs a sa).append (collect bs b sb)).withExpr n
  | .list es, .list n ses => (collectList bs es ses).withExpr n
  | .lambda pat _ body, .lambda owner sbody =>
      let binders := match pat with
        | .name name => locate bs (.lambda owner.id) name .param owner.span sbody.source.span sbody.source.span
        | _ => []
      ((⟨binders, [], []⟩ : Locations).append (collect bs body sbody)).withExpr owner
  | .letIn name tyParams params ann rhs body, .letIn owner srhs sbody =>
      let vals := locate bs (.letIn owner.id) name .val owner.span sbody.source.span srhs.source.span
      let header := match vals with
        | v :: _ => { owner.span with startLine := v.span.startLine, startCol := v.span.startCol }
        | [] => owner.span
      let heads := (params.mapIdx fun i (n, _) =>
        locate bs (.letParam owner.id i) n .param header srhs.source.span srhs.source.span).flatten
      let display := ⟨.letIn owner.id, displayNames (finalizeAnn tyParams params ann)⟩
      ((⟨vals ++ heads, [], [display]⟩ : Locations).append ((collect bs rhs srhs).append (collect bs body sbody))).withExpr owner
  | .letRecIn bindings body, .letRecIn owner rhss sbody =>
      ((collectBindings bs owner 0 bindings rhss sbody.source.span).append (collect bs body sbody)).withExpr owner
  | .ife c t f, .ife n sc st sf =>
      ((collect bs c sc).append ((collect bs t st).append (collect bs f sf))).withExpr n
  | .match_ scrut arms, .match_ owner sscrut sarms =>
      ((collect bs scrut sscrut).append (collectArms bs owner 0 sscrut.source.span arms sarms)).withExpr owner
  | _, _ => {}

partial def collectList (bs : List BinderSpan) : List Surface.Expr → List IdentifiedExpr → Locations
  | e :: es, se :: ses => (collect bs e se).append (collectList bs es ses)
  | _, _ => {}

partial def collectBindings (bs : List BinderSpan) (owner : SourceNode) (member : Nat) :
    List Surface.Binding → List IdentifiedExpr → Span → Locations
  | b :: rest, rhs :: rhss, scope =>
      let own := bindingLocations bs owner member b rhs (owner.span.union scope)
      let display := ⟨.letRec owner.id member, displayNames (finalizeAnn b.tyParams b.params b.ann)⟩
      (⟨own, [], [display]⟩ : Locations).append ((collect bs b.rhs rhs).append
        (collectBindings bs owner (member + 1) rest rhss scope))
  | _, _, _ => {}

partial def collectArms (bs : List BinderSpan) (owner : SourceNode) (arm : Nat) (previous : Span) :
    List (Surface.Pattern × Surface.Expr) → List IdentifiedExpr → Locations
  | (pat, body) :: rest, sbody :: srest =>
      let header := { owner.span with startLine := previous.endLine, startCol := previous.endCol }
      let names := patVars pat
      let binders := (names.mapIdx fun capture name =>
        locate bs (.patCapture owner.id arm capture) name .pat header sbody.source.span sbody.source.span).flatten
      (⟨binders, [], []⟩ : Locations).append ((collect bs body sbody).append
        (collectArms bs owner (arm + 1) sbody.source.span rest srest))
  | _, _ => {}
end

/-- Recreate just the parser-side wrappers used by `Program.term`. The RHS
    sidecars are already SCC-aligned by the parser. Synthetic wrappers receive
    no occurrence hover; their IDs still identify group-exit schemes. -/
def programSpanned (p : Surface.Program) (sp : SpannedProgram) (scope : Span) : Option SpannedExpr :=
  let rec go : List (List Surface.Binding) → List (List SpannedExpr) → Option SpannedExpr
    | [], [] => some sp.body
    | g :: gs, rhs :: rhss => do
        if g.length != rhs.length then none else do
          let body ← go gs rhss
          pure (if g.isEmpty then body else .letRecIn scope rhs body)
    | _, _ => none
  go p.groups sp.groups

/-- Program-level SCC wrappers are lowering scaffolding, not authored
    expression-hover targets. Nested authored recursive lets are retained. -/
def programWrapperIds : List (List Surface.Binding) → IdentifiedExpr → List SourceId
  | [], _ => []
  | group :: rest, tree =>
      if group.isEmpty then programWrapperIds rest tree
      else match tree with
        | .letRecIn owner _ body => owner.id :: programWrapperIds rest body
        | _ => []

/-- Authored schemes are carried declarations, deliberately absent from the
    inferred-scheme map. They have nevertheless passed the HM ceiling check. -/
def declaredScheme (typed : TypedLowered) (site : SurfaceBinderSite) : Option PolyTy := do
  let (_, target) ← typed.lowering.binderTargets.find? (fun p => p.1 == site)
  let sites ← match target with
    | .present sites => some sites
    | .absent _ => none
  let core ← sites.head?
  match core with
  | .letIn path =>
      let node ← typed.lowering.expr.atCorePath path
      match node with
      | .letIn ann _ _ => ann
      | _ => none
  | .letRec path member =>
      let node ← typed.lowering.expr.atCorePath path
      match node with
      | .letRec anns _ _ => (anns[member]?).join
      | _ => none
  | _ => none

def binderType (typed : TypedLowered) (site : SurfaceBinderSite) : Option String :=
  match typed.inferredBinderSchemes.find? (fun p => p.1 == site) with
  | some (_, scheme) => some scheme.eraseBounds.pretty
  | none =>
      match declaredScheme typed site with
      | some scheme => some scheme.eraseBounds.pretty
      | none => do
          match site with
          | .patCapture _ _ _ =>
              let (_, types) ← typed.patternBinderTypes.find? (fun p => p.1 == site)
              let (_, ty) ← types.head?
              pure ty.eraseBounds.pretty
          | _ =>
              let (_, target) ← typed.lowering.binderTargets.find? (fun p => p.1 == site)
              let sites ← match target with
                | .present sites => some sites
                | .absent _ => none
              let .lambda path ← sites.head? | none
              let .arrow domain _ ← foundTyAtCorePath typed.inference.output path | none
              pure domain.eraseBounds.pretty

end FHM.Unverified.HMArtifacts
