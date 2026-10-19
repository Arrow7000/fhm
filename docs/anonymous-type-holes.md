# Anonymous annotation milestone

This branch contains a verified **Core-shaped input elaborator**, not a parser or editor feature yet. `Anonymous.Input` records partial annotation syntax; `Anonymous.inferCore` returns ordinary `Expr` output with completed annotations. `TypeOfHM` and runtime semantics are unchanged.

Supported partial syntax is the lambda/application/ordinary-let spine. Templates contain fixed types, independent anonymous holes, arrows, and datatype applications. A whole `_` has the same independent typing meaning as an omitted lambda or ordinary-let annotation (`Typing.lambda_hole_iff` / `Typing.let_hole_iff`). Eligible unsolved variables generalize; variables reachable through the context and written rigid variables do not. An enclosing let synthesizes a complete scheme and closes its RHS annotations under those same ordered binders.

Whole completed subtrees delegate once to the existing verified inferer. This preserves complete signatures, matches, and polymorphic recursion inside such subtrees. Partial explicit-forall signatures, complete signatures whose RHS contains partial syntax, and partial match/recursive spines currently fail explicitly. In particular, a partial recursive signature never becomes a polymorphic-recursion dependency cut.

Checked results include:

- ordinary Core output typing (`Infer.sourceSound`), exact runtime erasure (`Infer.erase`), and annotation completion/fidelity (`Infer.completes`);
- successful elaboration implies the independent partial-input rules (`Infer.inputSound`);
- residual result/context principality against independent `Typing P`, with independently quantified protected set `P` (`Infer.principal`);
- concrete producer completeness (`inferCore_complete`) and exact closed-input acceptance (`inferCore_empty_accepts_iff`).

Principality here concerns the result type and flexible context. It does not assert most-general fillings for every unused hole or expose per-hole editor metadata.

`FHM/AnonymousExamples.lean` executes the polymorphic identity with a hole in its lambda parameter, structured let templates, independent holes at Bool/Int uses, occurs-check rejection, context-sensitive generalization, rigid-variable protection, unused-hole generalization, and complete polymorphic-recursion preservation. Run `lake build FHM.AnonymousExamples`.

The examples also cover independent copied input visits and a lowered partial scrutinee followed by a completed matcher. The original copied fallback with holes in match branches remains unsupported; these tests are not a source pattern-compilation compatibility proof. Supporting that case requires a focused branch/lowering extension before any broader frontend migration. No global hole identities, ownership tables, or named-hole machinery is introduced.
