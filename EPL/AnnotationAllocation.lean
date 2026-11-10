import EPL.Unification

namespace EPL

def Template.names : Template → List String
  | .fixed _ | .hole => []
  | .named name => [name]
  | .arrow domain codomain => domain.names ++ codomain.names

def namedHoleTable (names : List String) (frontier : Nat) : HoleAssignment :=
  let keys := names.dedup
  keys.zip ((List.range keys.length).map fun offset => .mvar (frontier + offset))

/-- Resolve a template after its complete local named-hole table has been
allocated. `frontier` is reserved for anonymous holes only. -/
def Template.allocateWith (holes : HoleAssignment) : Nat → Template → Nat × Ty
  | frontier, .fixed ty => (frontier, ty)
  | frontier, .hole => (frontier + 1, .mvar frontier)
  | frontier, .named name =>
      (frontier, (holes.lookup name).getD (.mvar frontier))
  | frontier, .arrow domain codomain =>
      let domainResult := domain.allocateWith holes frontier
      let codomainResult := codomain.allocateWith holes domainResult.1
      (codomainResult.1, .arrow domainResult.2 codomainResult.2)

structure Template.Allocation where
  next : Nat
  ty : Ty
  holes : HoleAssignment
  deriving Repr

/-- Allocate one metavariable per distinct local name, followed by one fresh
metavariable for each anonymous occurrence. Every call starts a new name table. -/
def Template.allocate (frontier : Nat) (template : Template) : Template.Allocation :=
  let keys := template.names.dedup
  let holes := namedHoleTable keys frontier
  let resolved := template.allocateWith holes (frontier + keys.length)
  ⟨resolved.1, resolved.2, holes⟩

end EPL
