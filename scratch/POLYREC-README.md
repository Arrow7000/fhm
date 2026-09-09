# Damas--Milner recursion smoke tests (`scratch/polyrec-*`)

`PolyRecTest.lean` is the executable specification for recursive typing on the
erased branch. Run it from the repository root:

```console
lake env lean --run scratch/PolyRecTest.lean
```

The driver uses the current pipeline directly:

```text
parse -> erase surface bounds -> lower -> infer -> exhaustiveness
      -> erase Core annotations -> evaluate
```

Successful programs must reach a specific value. Negative programs must get as
far as lowering and then be rejected specifically by Infer; a parse/lower error
does not count as a successful negative test.

## Semantic boundary pinned by the matrix

D2 is ordinary Damas--Milner recursion:

- Every member of an SCC has one monotype while that SCC is checked.
- Members are generalised after the SCC exits and can then be instantiated
  independently at later call sites.
- An annotation does not grant per-call-site polymorphism inside an SCC.
- Unannotated polymorphic recursion remains uninferable.

Complete head-binder/scoped-type-variable support is separately parked. Its
negative test records a current implementation limitation, not an additional
claim about the Damas--Milner boundary.

## Test matrix

| file | expected | contract |
|---|---:|---|
| `polyrec-ordinary-recursion.fhm` | pass, `15` | ordinary recursion at one monotype |
| `polyrec-generalize-after-scc.fhm` | pass, `(1, True)` | a recursive binding is polymorphic after SCC exit |
| `polyrec-mixed-fixed-instantiation.fhm` | pass, `[5, 5, 5]` | mutually recursive members share a fixed in-SCC instantiation |
| `polyrec-inner-poly-calls.fhm` | Infer rejects | an annotated member is called at two types inside its SCC |
| `polyrec-mixed-group.fhm` | Infer rejects | the same two-instantiation conflict in a mixed SCC |
| `polyrec-mixed-conflict-must-fail.fhm` | Infer rejects | a recursive monotype is forced to equal its own list type |
| `polyrec-unannotated-must-fail.fhm` | Infer rejects | canonical unannotated polymorphic recursion |
| `polyrec-inner-poly-unannotated-must-fail.fhm` | Infer rejects | two in-SCC instantiations without an annotation |
| `polyrec-nested.fhm` | Infer rejects | canonical annotated polymorphic recursion is outside D2 |
| `polyrec-groups-nested.fhm` | Infer rejects | annotations do not restore polyrec in a larger multi-SCC program |
| `polyrec-head-binder-scoped-must-fail.fhm` | Infer rejects | current parked complete head-binder/scoped-tyvar form |

The historical `polyrec-skolem-leak-must-fail.fhm` fixture was renamed to
`polyrec-mixed-fixed-instantiation.fhm`: the program uses only one recursive
instantiation and is accepted under D2, evaluating to `[5, 5, 5]`. Calling it a
required rejection encoded the superseded polymorphic-recursion design.

## Parser notes

- Top-level mutual groups are formed by SCC analysis; explicit sibling syntax
  exists only inside `let ... in`.
- The parser accepts one infix operator per expression, so chains such as
  `a + b + c` need parentheses.
