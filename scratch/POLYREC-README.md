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

- Complete annotations are dependency cuts. Their schemes are assumed while
  the unannotated sub-group is inferred.
- Unannotated members each have one monotype while that sub-group is inferred;
  after it is solved, they are generalized.
- A completely annotated member is checked against its declared scheme and can
  be instantiated independently at recursive call sites inside the SCC. Its RHS
  is checked only after inferred siblings have their final schemes.
- Its scoped annotation variables are rigid while its body is checked; they
  cannot be unified away, but may pass through an inferred sibling by ordinary
  instantiation of that sibling's generalized scheme.
- Unannotated polymorphic recursion remains uninferable.
- All runtime annotations are erased; checking introduces no type-passing terms.

Head-binder sugar remains unsupported; explicit lambda RHSs support scoped type
variables. The syntax negative records that distinction, not a typing restriction.
The matrix and executable driver are authoritative.

## Test matrix

| file | expected | contract |
|---|---:|---|
| `polyrec-ordinary-recursion.fhm` | pass, `15` | ordinary recursion at one monotype |
| `polyrec-generalize-after-scc.fhm` | pass, `(1, True)` | a recursive binding is polymorphic after SCC exit |
| `polyrec-mixed-fixed-instantiation.fhm` | pass, `[5, 5, 5]` | an inferred sibling is generalized before the signed RHS is checked |
| `polyrec-inner-poly-calls.fhm` | pass, `(4, 4)` | an annotated member is called at two types inside its SCC |
| `polyrec-mixed-group.fhm` | pass, `(1, 2)` | an unannotated sibling independently instantiates an annotated member |
| `polyrec-mixed-conflict-must-fail.fhm` | Infer rejects | a recursive monotype is forced to equal its own list type |
| `polyrec-unannotated-must-fail.fhm` | Infer rejects | canonical unannotated polymorphic recursion |
| `polyrec-inner-poly-unannotated-must-fail.fhm` | Infer rejects | two in-SCC instantiations without an annotation |
| `polyrec-nested.fhm` | pass, `7` | annotated polymorphic recursion over a nested datatype |
| `polyrec-groups-nested.fhm` | pass, `7` | annotated polyrec in a larger multi-SCC program |
| `polyrec-head-binder-scoped-must-fail.fhm` | Parse rejects | head-binder sugar remains unsupported |

The historical `polyrec-skolem-leak-must-fail.fhm` fixture was renamed to
`polyrec-mixed-fixed-instantiation.fhm`. The earlier simultaneous checker rejected
it because checking `f` first tried to put rigid `a` into unannotated `g`'s shared
monotype. Contract stratification removes that accidental order dependence: infer
and generalize `g` against `f`'s declared contract, then check `f` using `g`'s final
scheme. The program is therefore accepted without runtime type passing.

## Parser notes

- Top-level mutual groups are formed by SCC analysis; explicit sibling syntax
  exists only inside `let ... in`.
- The parser accepts one infix operator per expression, so chains such as
  `a + b + c` need parentheses.
