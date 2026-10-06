import FHM.Unverified.Surface.Provenance
import FHM.Pretty

/-!
# Missing-case examples for editors and the CLI

Explore the existing compiled decision tree under inferred occurrence types.
Each path to `fail` records constructor choices; untested fields stay wildcards.
These are diagnostic examples only: the proved exhaustiveness checker still
controls acceptance. Enumeration stops after five examples, allowing callers
to display four and say when more remain.
-/

namespace FHM.Unverified.CoverageDiagnostics

open PatComp SurfaceBridge SurfaceBridge.Provenance Surface.Span

abbrev Choices := List (Occ × (CtorName × Nat))

/-- Follow only real, visible constructors at each switch. Defaults are taken
    only for constructor tags absent from the explicit cases. Fuel bounds the
    tree path, not the source program's evaluation. -/
def uncovered (ctors : CtorEnv) : Nat → DTree → OccCtx → Choices → Nat → List Choices
  | _, _, _, _, 0 => []
  | 0, _, _, _, _ => []
  | _ + 1, .fail, _, choices, _ => [choices]
  | _ + 1, .leaf .., _, _, _ => []
  | fuel + 1, .switch occ cases dflt, octx, choices, limit =>
      match LookupList.get? octx occ with
      | some (.customTy T args) => Id.run do
          let mut missing := []
          for name in (ctors.map (·.1)).eraseDups do
            if missing.length >= limit then break
            match LookupList.get? ctors name with
            | some ctor =>
              if ctor.tyName == T then
                let arity := ctor.contents.length
                let child := ((cases.find? fun (c, a, _) => c == name && a == arity).map
                  (fun (_, _, t) => t)).getD dflt
                let fields := instFieldTys ctors name args
                missing := missing ++ uncovered ctors fuel child
                  (OccCtx.extend octx occ fields) ((occ, name, arity) :: choices)
                  (limit - missing.length)
            | none => pure ()
          return missing
      | _ => []

/-- Reassemble choices into source pattern syntax. At most `choices.length`
    constructor choices can occur on any path, so that is enough fuel. -/
def materialize (choices : Choices) : Nat → Occ → Surface.Pattern
  | 0, _ => .wildcard
  | fuel + 1, occ =>
      match choices.find? fun entry => entry.1 == occ with
      | none => .wildcard
      | some (_, name, arity) =>
          let fields := (subOccs occ arity).map (materialize choices fuel)
          match name, fields with
          | ⟨"Pair"⟩, [a, b] => .pair a b
          | ⟨"Nil"⟩, [] => .list []
          | ⟨"Cons"⟩, [h, t] => .cons h t
          | _, _ => .ctor name fields

mutual
private def treeDepth : DTree → Nat
  | .fail | .leaf .. => 1
  | .switch _ cases dflt => 1 + max (casesDepth cases) (treeDepth dflt)

private def casesDepth : List (CtorName × Nat × DTree) → Nat
  | [] => 0
  | (_, _, t) :: rest => max (treeDepth t) (casesDepth rest)
end

structure Missing where
  patterns : List Surface.Pattern
  more : Bool := false

/-- Inference supplies the scrutinee type, including nested parameter types.
    The depth of the tree bounds every path to a failure leaf. -/
def examples (ctors : CtorEnv) (scrutTy : Ty) (ps : List Surface.Pattern) : Missing :=
  let tree := compile [[]] (initMatrix ps)
  let paths := uncovered ctors (treeDepth tree) tree [([], scrutTy)] [] 5
  { patterns := (paths.take 4).map fun choices => materialize choices (choices.length + 1) []
    more := paths.length > 4 }

structure Failure where
  span : Span
  missing : Missing

/-- Find the same first failing match as the pipeline, using source IDs to
    recover its scrutinee's inferred type even inside recursive definitions or
    matches cloned by pattern compilation. -/
partial def firstFailure (typed : TypedLowered) : Surface.Expr → IdentifiedExpr → Option Failure
  | .pair a b, .pair _ sa sb | .cons a b, .cons _ sa sb | .app a b, .app _ sa sb =>
      firstFailure typed a sa <|> firstFailure typed b sb
  | .list es, .list _ ses => firstIn (es.zip ses)
  | .lambda _ _ body, .lambda _ sbody => firstFailure typed body sbody
  | .letIn _ _ _ _ rhs body, .letIn _ srhs sbody =>
      firstFailure typed rhs srhs <|> firstFailure typed body sbody
  | .letRecIn binds body, .letRecIn _ rhss sbody =>
      firstIn ((binds.map (·.rhs)).zip rhss) <|> firstFailure typed body sbody
  | .ife c t f, .ife _ sc st sf => firstIn [(c, sc), (t, st), (f, sf)]
  | .match_ scrut arms, .match_ source sscrut sarms =>
      let alone := Surface.Expr.match_ (.primLit .unit)
        (arms.map fun (p, _) => (p, .primLit .unit))
      firstFailure typed scrut sscrut <|>
        (if checkExhaustive typed.ctors alone then none else
          let missing := match (typed.typesForSource sscrut.source.id).head? with
            | some (_, ty) => examples typed.ctors ty (arms.map (·.1))
            | none => { patterns := [] }
          some { span := source.span, missing }) <|>
        firstIn ((arms.map (·.2)).zip sarms)
  | _, _ => none
where
  firstIn : List (Surface.Expr × IdentifiedExpr) → Option Failure
    | [] => none
    | (e, se) :: rest => firstFailure typed e se <|> firstIn rest

end FHM.Unverified.CoverageDiagnostics
