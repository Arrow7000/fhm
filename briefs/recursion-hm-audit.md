# Recursive bindings: HM/D2 audit

Audited 2026-09-13 against `.lake/build/bin/fhm`.

## Contract observed

An SCC is checked with one monotype per member.  A member's annotation is
validated against its inferred type, but is not instantiated at individual
uses while the SCC is being checked.  After the SCC exits, members are
generalised and may be instantiated independently.  This is ordinary
Damas--Milner recursion, not polymorphic recursion.

## Scratch matrix

| fixture | observed result | classification |
|---|---|---|
| `polyrec-ordinary-recursion.fhm` | accepts, evaluates to `15` | expected |
| `polyrec-generalize-after-scc.fhm` | accepts, evaluates to `(1, True)` | expected; recursive binding is polymorphic after its SCC |
| `polyrec-mixed-fixed-instantiation.fhm` | accepts, evaluates to `[5, 5, 5]` | expected; mutual members use one in-SCC instance |
| `polyrec-inner-poly-calls.fhm` | Infer error in `g`, line 20 | expected; annotated `f` is used at two in-SCC instances |
| `polyrec-mixed-group.fhm` | Infer error in `g`, line 16 | expected; mixed SCC still has one instance per member |
| `polyrec-mixed-conflict-must-fail.fhm` | Infer error in `h`, line 12 | expected occurs-check-style conflict |
| `polyrec-unannotated-must-fail.fhm` | Infer error in `bad`, lines 11--14 | expected; unannotated polyrec is not inferred |
| `polyrec-inner-poly-unannotated-must-fail.fhm` | Infer error in `g`, line 12 | expected |
| `polyrec-nested.fhm` | Infer error in `size`, lines 12--15 | expected; annotation does not enable polyrec |
| `polyrec-groups-nested.fhm` | Infer error in `size`, lines 14--17 | expected; outer groups do not alter the boundary |
| `polyrec-head-binder-scoped-must-fail.fhm` | Infer error in `id1`, line 5 | expected parked head-binder/scoped-tyvar limitation |

`lake env lean --run scratch/PolyRecTest.lean` also reports all 11 cases as
specified.  No fixture changes were needed.  In particular, the head-binder
fixture remains deliberately negative rather than being rewritten to lambda
syntax, so it continues to cover the known scoped-type-variable seam.

## Targeted probes

An annotated mutual SCC such as:

```fhm
let f : {a} a -> a =
  \x -> if True then x else g x
let g =
  \y -> f y
(f 1, f True)
```

is accepted: the group exits with both `f` and `g` at `forall a. a -> a`, and
the two uses of `f` are `Int -> Int` and `Bool -> Bool`.  Replacing `g`'s RHS
with `\y -> (f y, f [y])` is rejected in `g`: those calls happen *inside* the
SCC and must share the member monotype.  A one-way dependency (`a = \x -> b x`
then `b = \y -> y`) also accepts and permits polymorphic later uses of `a`,
consistent with SCC ordering.

## Hover observation

Successful diagnostics retain final schemes at declarations and final
instances at uses outside the SCC, for example `same : forall a. a -> a`, then
`same : Int -> Int` and `same : Bool -> Bool`.  Inference-time symbols inside
an RHS are rendered with raw metavariables instead: `?c` for `same`'s
parameter/recursive occurrence and `?t16` for `f`/`g`'s shared parameter in
the mixed SCC. This was observed before the parent display repair, independently
of the D2 typing result. `HMDisplay` now uses compact alpha names, retaining
authored signature names when their correspondence is valid and genuine nested
let skolems' names. No recursive checking/generalisation rule was changed.
Failed programs currently return diagnostics with no symbols.
