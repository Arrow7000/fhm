<!-- Written 2026-07-14: compile-time partial evaluation / constant folding idea. Not started. -->

# Idea brief: compile-time simplification (`simplify` pass)

**Status: NOT STARTED — parked for a future session.** Captured from the audit-session discussion.

## The landscape (why this is cleaner than "messy heuristics")

- **Soundness is free.** Any *finite prefix* of the verified `SmallStep.Step` relation preserves typing and
  meaning (that's `TypeOfElabHM.preservation` / `preservation_star`). So "simplify = take some `Step`s and
  stop" is *always* correct for any number of steps. The halting problem only limits *how far* you can go,
  never *whether a reduction was valid*.
- **Firm, always-terminating rules** (theorem-backed, not guesswork):
  1. **Constant folding:** saturated primops on literals (`1 + 3 → 4`) — one δ-step.
  2. **Case-of-known-constructor:** `match (Just 5) with …` → selected branch — terminates.
  3. **Full normalization of the `letRec`-free fragment:** any subterm with **no `letRec`** is *strongly
     normalizing* (HM typing rules out self-application like `x x`, so without explicit recursion you cannot
     loop). ⇒ such subterms can be reduced *completely*, guaranteed to terminate. This is the cool one.
- **Only the recursive fragment is undecidable** → fall back to fuel (`evaluate`) or leave it.

## Proposed shape

```lean
def simplify : Expr → Expr := …   -- fold primops; fire known matches; normalize letRec-free subterms; else leave
```
Theorems to author (statement author = parent; proofs = subagent):
- **Meaning/type preservation:** `TypeOfElabHM ctx e τ → TypeOfElabHM ctx (simplify e) τ`, and
  `Relation.ReflTransGen Step e (simplify e)` (simplify only takes real steps) — so it's sound *by construction*.
- **"It actually does something" (user's idea):** progress lemmas keyed on *what `e` contains* — e.g.
  "if `e` contains a saturated primop-on-literals redex / a case-of-known-ctor / a `letRec`-free non-value,
  then `(simplify e).sizeOf < e.sizeOf`" (or a well-founded measure decreases). This is the witness that the
  pass is non-trivial on the terminating fragment, and it doubles as the termination measure for iterating
  `simplify` to a fixpoint on that fragment.
- **Normalization on the SN fragment:** `NoLetRec e → IsNormalForm (simplify e)` (i.e. full evaluation of
  recursion-free subterms terminates at a normal form).

Compose with the safe pipeline (see audit-followups brief): `simplify` on a `Safe ctors` term yields another
`Safe ctors` term (preservation of both `WellTyped` and `AllMatchesExhaustive`) — an optimization pass that
slots into the Lego chain.
