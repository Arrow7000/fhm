# Implementation brief: `.found` typing output and lowering provenance

**Status:** approved direction; implementation not started
**Date:** 2026-09-09
**Related:** [`design-memo-dm-erased-shadow.md`](design-memo-dm-erased-shadow.md) (D4, D7, D8)

## Outcome

Inference returns a typed Core term using the existing `Expr` with:

```lean
| found (ty : Ty) (expr : Expr)
```

There is exactly one `.found` wrapper for every logical Core expression node. Its payload is that node's inferred **monotype**. Generalised binder schemes and source provenance are separate outputs with different owners:

| fact | representation | producer |
|---|---|---|
| Per-expression inferred monotype | `.found Ty Expr` | inference |
| Generalised type shown for a binder | `BinderSite → PolyTy` result/index | inference at generalisation points |
| Surface identity/span and generated-node origin | `CorePath → Origin` map | lowering |

User annotations remain in their existing term slots. Machine-inferred binder schemes must not overwrite or masquerade as user annotations.

## Why provenance is not another `.found` payload

Inference receives Core only. By then lowering has compiled matches, introduced capture/scrutinee lets, and discarded the surface tree's identity as an explicit input. Moreover, the approved constructor contains only `Ty` and `Expr`; it has no place for a source ID or span. Inference therefore cannot naturally recover source identity while creating `.found` nodes. Doing so would require either changing the constructor again or reconstructing surface correspondence after the fact, recreating the positional-zip failure.

Assign a stable `SourceId` to each surface expression/binder before lowering, with its span as metadata. Lowering is then the point where both sides of the relationship are known, so it must emit provenance while constructing Core. Use paths in the **logical Core skeleton** (child selectors with `.found` treated as transparent), not equality or hashes of `Expr`, because identical subexpressions can occur more than once. A suitable result shape is:

```lean
structure Lowered where
  expr       : Expr
  provenance : CorePath → Option Origin
```

`Origin` must distinguish a direct surface node from a generated node and, for generated nodes, retain the originating surface ID/span and generation reason. Multiple Core paths may legitimately share one surface origin. This is construction-time provenance, not a later structural reconciliation.

`BinderSite` should be based on the same logical `CorePath` plus a binder slot, since one `letRec` node owns several binders. This gives the LSP a stable join between binder schemes, `.found` node types, and source provenance without placing source metadata in `Expr`.

## Required invariants

1. **Clean input:** parser/lowering output is `.found`-free.
2. **Shape preservation:** `stripFound typedExpr = lowered.expr`.
3. **One fact per node:** every logical Core node has exactly one `.found`, and `.found` introduces no additional logical path component.
4. **Final substitution:** every stored monotype has the inference run's final substitution applied. Stored binder schemes are generalised from the final solved monotype/context and are stable under that substitution.
5. **Typing coherence:** each `.found τ e` agrees with the declarative subderivation for the corresponding stripped node; the root payload agrees with the program result type.
6. **Separate schemes:** every generalisation site returns its inferred `PolyTy` under a `BinderSite`; nongeneralising binders may use the corresponding trivial scheme when tooling requires one.
7. **Total Core provenance:** every logical Core path has an `Origin`, including PatComp-generated nodes. Generated origins are marked rather than presented as user-authored expressions.
8. **Strip before runtime:** evaluation and operational semantics never consume `.found`. The runtime input is `stripFound typedExpr` passed through the branch's existing erasure boundary; no `Step` rule for `.found` is required.

BL consumes the same typed output. It maps or analyses `.found` payloads; it must not add a second layer of `.found` wrappers.

## Match provenance and staging

A v1 vertical slice may cover literals, variables, applications, lambdas, ordinary lets, and internal binder hover before match provenance is complete. That is an implementation staging choice only: it must be reported as partial and must not become the final LSP contract.

The final product must support surface match expressions and pattern-bound variables. PatComp must record which generated decision-tree/capture nodes came from each surface match/pattern, identify a primary hover/report target where several Core nodes share one origin, and guarantee that every hoverable surface match/pattern ID has at least one target. Positional walking of the finished surface and Core trees is not an acceptable substitute.

## Suggested checkpoint sequence

1. Define `.found`, `FoundFree`, `stripFound`, logical `CorePath`, `BinderSite`, and `Origin`; prove the basic strip/path laws.
2. Change relational and executable inference outputs together so they build one wrapper per node and apply the final substitution across the completed output.
3. Return generalised binder schemes separately and prove their agreement with the corresponding solved monotypes/generalisation premises.
4. Make lowering return total provenance for the non-match fragment; join it with `.found` and binder schemes for internal hover.
5. Run one small program through `.found` → internal hover → BL report as the first vertical checkpoint.
6. Extend provenance through PatComp and add match/pattern hover tests before declaring LSP/BL parity complete.

Keep R1 (`Expr.erase` removal), full head-binder support, and polymorphic recursion out of these checkpoints.
