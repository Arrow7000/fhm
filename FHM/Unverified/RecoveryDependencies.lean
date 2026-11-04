import FHM.SurfaceBridge
import FHM.Surface.Span

/-! Source dependencies used only by editor recovery. Namespace distinctions
remain explicit; recovery causes never stand in for inference types. -/
namespace FHM.Unverified.RecoveryDependencies

inductive Cause where
  | binding (name : ValName)
  | localBinding (name : ValName) (span : Surface.Span.Span)
  | declaration (name : TyName)
  | expression (span : Surface.Span.Span)
  | syntax (span : Surface.Span.Span)
  deriving Repr, BEq

/-- Names excluded by a preceding recovery stage. These carry failure identity,
not kinds or schemes. The parser can withhold a malformed authored header. -/
structure Seed where
  values : List (ValName × List Cause) := []
  types : List (TyName × List Cause) := []
  constructors : List (CtorName × List Cause) := []
  body : List Cause := []

structure Uses where
  types : List TyName := []
  constructors : List CtorName := []
  deriving Repr, Inhabited

def Uses.append (a b : Uses) : Uses :=
  ⟨a.types ++ b.types, a.constructors ++ b.constructors⟩

mutual
def typeNames : Surface.Ty → List TyName
  | .prim .bool => [⟨"Bool"⟩]
  | .pair a b => ⟨"Pair"⟩ :: typeNames a ++ typeNames b
  | .arrow a b => typeNames a ++ typeNames b
  | .customTy name args => name :: typeNamesList args
  | _ => []
def typeNamesList : List Surface.Ty → List TyName
  | [] => []
  | ty :: rest => typeNames ty ++ typeNamesList rest
end

private def annotation (ann : Option Surface.PolyTy) : Uses :=
  ⟨(ann.map (fun scheme => typeNames scheme.body)).getD [], []⟩
private def parameters (params : List (ValName × Option Surface.Ty)) : Uses :=
  ⟨params.flatMap (fun (_, ann) => (ann.map typeNames).getD []), []⟩

mutual
def patternUses : Surface.Pattern → Uses
  | .name _ | .wildcard => {}
  | .pair a b => (⟨[⟨"Pair"⟩], [⟨"Pair"⟩]⟩ : Uses) |>.append (patternUses a) |>.append (patternUses b)
  | .ctor name pats => (⟨[], [name]⟩ : Uses) |>.append (patternListUses pats)
  | .cons head tail => (⟨[⟨"List"⟩], [⟨"Cons"⟩]⟩ : Uses) |>.append (patternUses head) |>.append (patternUses tail)
  | .list pats => (⟨[⟨"List"⟩], [⟨"Cons"⟩, ⟨"Nil"⟩]⟩ : Uses) |>.append (patternListUses pats)
def patternListUses : List Surface.Pattern → Uses
  | [] => {}
  | pat :: rest => (patternUses pat).append (patternListUses rest)
end

mutual
def expression : Surface.Expr → Uses
  | .primLit (.bool value) => ⟨[⟨"Bool"⟩], [if value then ⟨"True"⟩ else ⟨"False"⟩]⟩
  | .primLit _ | .primBinOp _ | .var _ => {}
  | .ctor name => ⟨[], [name]⟩
  | .pair a b => (⟨[⟨"Pair"⟩], [⟨"Pair"⟩]⟩ : Uses) |>.append (expression a) |>.append (expression b)
  | .cons head tail => (⟨[⟨"List"⟩], [⟨"Cons"⟩]⟩ : Uses) |>.append (expression head) |>.append (expression tail)
  | .list items => (⟨[⟨"List"⟩], [⟨"Cons"⟩, ⟨"Nil"⟩]⟩ : Uses) |>.append (expressions items)
  | .lambda pat ann body =>
      (⟨(ann.map typeNames).getD [], []⟩ : Uses) |>.append (patternUses pat) |>.append (expression body)
  | .app fn arg => (expression fn).append (expression arg)
  | .letIn _ _ params ann rhs body =>
      (parameters params).append (annotation ann) |>.append (expression rhs) |>.append (expression body)
  | .letRecIn binds body => (bindings binds).append (expression body)
  | .ife cond yes no => (⟨[⟨"Bool"⟩], [⟨"True"⟩, ⟨"False"⟩]⟩ : Uses)
      |>.append (expression cond) |>.append (expression yes) |>.append (expression no)
  | .match_ scrut arms => (expression scrut).append (branches arms)
def expressions : List Surface.Expr → Uses
  | [] => {}
  | expr :: rest => (expression expr).append (expressions rest)
def bindings : List Surface.Binding → Uses
  | [] => {}
  | binding :: rest => (parameters binding.params).append (annotation binding.ann)
      |>.append (expression binding.rhs) |>.append (bindings rest)
def branches : List (Surface.Pattern × Surface.Expr) → Uses
  | [] => {}
  | (pat, body) :: rest => (patternUses pat).append (expression body) |>.append (branches rest)
end

def declaration (decl : Surface.DataDecl) : List TyName :=
  decl.ctors.flatMap (fun (_, fields) => typeNamesList fields)

/-- SCCs with dependencies first. Shared-name conflicts can be represented by
bidirectional edges so recovery never chooses an arbitrary duplicate definition. -/
def components (items : List α) (depends : α → α → Bool) : List (List α) :=
  let table : Array (List Nat) := Array.ofFn fun (i : Fin items.length) =>
    items.zipIdx.filterMap fun (item, j) => if depends (items.get i) item then some j else none
  let graph : Scc.Digraph (Fin items.length) := {
    succ := fun i => ((table[i.val]?.getD []).filterMap fun j =>
      if h : j < items.length then some ⟨j, h⟩ else none).toFinset }
  let groups := (Scc.kosaraju graph).map (fun group => group.map Fin.val)
  let order := SurfaceBridge.kahnTopo groups.length
    (SurfaceBridge.sccBeforeEdges (fun i => table[i]?.getD []) groups)
  order.filterMap (groups[·]?) |>.map (fun group => group.filterMap (items[·]?))

end FHM.Unverified.RecoveryDependencies
