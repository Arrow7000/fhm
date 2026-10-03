# Erased annotated-polymorphic-recursion smoke tests (`scratch/polyrec-*`)

`PolyRecTest.lean` is the executable specification for recursive typing on the
erased branch. Run it from the repository root:

```console
lake env lean --run scratch/PolyRecTest.lean
```

The driver uses the current pipeline directly:

```text
parse -> lower -> infer -> exhaustiveness -> erase Core annotations -> evaluate
```

Successful programs must reach a specific value. Negative programs must get as
far as lowering and then be rejected specifically by Infer; a parse/lower error
does not count as a successful typing-negative test. The unsupported head-binder
syntax case separately expects a parse error.

## Semantic boundary pinned by the matrix

The checker uses a mixed recursive group:

- An unannotated member has one monotype while its SCC is checked and is
  generalized only after the SCC exits.
- A completely annotated member is checked against its declared scheme and can
  be instantiated independently at recursive call sites inside the SCC.
- Its scoped annotation variables are rigid while its body is checked; they
  cannot escape through an unannotated sibling's shared monotype.
- Unannotated polymorphic recursion remains uninferable.
- All runtime annotations are erased; checking introduces no type-passing terms.

Head-binder sugar remains unsupported; explicit lambda RHSs support scoped type
variables. The syntax negative records that distinction, not a typing restriction.
The `.fhm` files retain historical names/comments from the former D2 policy;
the current matrix and executable driver are authoritative.

## Test matrix

| file | expected | contract |
|---|---:|---|
| `polyrec-ordinary-recursion.fhm` | pass, `15` | ordinary recursion at one monotype |
| `polyrec-generalize-after-scc.fhm` | pass, `(1, True)` | a recursive binding is polymorphic after SCC exit |
| `polyrec-mixed-fixed-instantiation.fhm` | Infer rejects | a rigid annotation variable escapes into an unannotated sibling |
| `polyrec-inner-poly-calls.fhm` | pass, `(4, 4)` | an annotated member is called at two types inside its SCC |
| `polyrec-mixed-group.fhm` | pass, `(1, 2)` | an unannotated sibling independently instantiates an annotated member |
| `polyrec-mixed-conflict-must-fail.fhm` | Infer rejects | a recursive monotype is forced to equal its own list type |
| `polyrec-unannotated-must-fail.fhm` | Infer rejects | canonical unannotated polymorphic recursion |
| `polyrec-inner-poly-unannotated-must-fail.fhm` | Infer rejects | two in-SCC instantiations without an annotation |
| `polyrec-nested.fhm` | pass, `7` | annotated polymorphic recursion over a nested datatype |
| `polyrec-groups-nested.fhm` | pass, `7` | annotated polyrec in a larger multi-SCC program |
| `polyrec-head-binder-scoped-must-fail.fhm` | Parse rejects | head-binder sugar remains unsupported |

The historical `polyrec-skolem-leak-must-fail.fhm` fixture was renamed to
`polyrec-mixed-fixed-instantiation.fhm`: the former D2 checker accepted this
program by solving the shared monotypes first. In the mixed annotation-directed
checker, checking `f` at rigid `a` would put that `a` into unannotated `g`'s
monotype, so the program is rejected. Annotating `g` too is the intended remedy;
the corresponding core fixture is in `FHM/Examples.lean`.

## Parser notes

- Top-level mutual groups are formed by SCC analysis; explicit sibling syntax
  exists only inside `let ... in`.
- The parser accepts one infix operator per expression, so chains such as
  `a + b + c` need parentheses.
