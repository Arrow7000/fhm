# Elm 0.19.1: scoped type variables in nested helpers (Feature "C")

**Question.** Can a nested helper (a `let`-bound function inside an outer *annotated*
function) have a type annotation that references the OUTER function's type variable —
Haskell-style `ScopedTypeVariables` — and does Elm support this? And if it "works", is
it **(a) genuine sharing** of the outer scope's type variable, or **(b) best-effort
re-quantification** of a fresh, independent variable that merely *looks* like it works?

**Short answer.** Elm 0.19.1 has **genuine, name-based scoped type variables** for nested
helpers — interpretation **(a)**. A type variable in a nested annotation that shares its
*name* with a type variable bound by an enclosing **annotated** binding **is the same
rigid variable** as the outer one. A nested-annotation variable whose name does **not**
match any enclosing annotation variable is a fresh, independently generalized variable.
The choice is a **deterministic lexical rule keyed on the variable name**, decided up
front — **not** a best-effort, usage-driven re-quantification. Hypothesis (b) is
**refuted**: Elm does not silently re-quantify a fresh variable to make a tricky program
typecheck; when the names match it commits to sharing (and stays monomorphic), and when
they differ it commits to non-sharing (and errors). This matches Haskell's
`ScopedTypeVariables` semantics, except it is **on by default** and needs no explicit
`forall` (Elm quantifies each name at the *outermost* annotation in the lexical scope
chain that mentions it).

All claims below are verified empirically with `elm make` (Elm 0.19.1, via the project's
`shell.nix`).

---

## The rule Elm actually implements

For a type-variable **name** `n` appearing in one or more annotations along a lexical
scope chain (outer function down through nested `let` helpers):

1. `n` is **quantified once**, at the **outermost annotation** in that chain that mentions
   `n`. Every occurrence of `n` (inner annotations included) refers to **that one
   variable**.
2. Inside the body where that outer annotation is in force, `n` is **rigid** (the caller
   chooses it), so any inner helper annotated with `n` is **monomorphic in `n`** — it is
   *not* re-generalized at the inner `let`.
3. A nested-annotation name that does **not** occur in any enclosing annotation is
   quantified at the **inner binding itself** → it is an ordinary, independently
   generalized (polymorphic) `let` binding.
4. The sharing anchor must be an **annotated** enclosing binder. (See the unannotated-
   outer edge case below.)

This single rule predicts every result in the matrix. There is no point at which Elm
inspects how the helper is *used* and then "decides" where to put the `forall`.

---

## Evidence matrix

Two contrasting pairs do the decisive work. Within each pair the ONLY difference is the
**name** of the inner helper's type variable (`a`, which collides with the outer
`outer : a -> ...`, vs `z`, which does not). The name alone flips the result — that is
the signature of genuine name-based sharing.

| # | File | Outer ann.? | Inner var | What it forces | Result | Interpretation |
|---|---|---|---|---|---|---|
| C-1 | `ScopedTyVarShare.elm` | `a -> a` | `b -> a` | helper body returns outer `x:a` (escape) | ✅ compiles | inner `a` **is** outer `a` → returning `x` is legal |
| C-2 | `ScopedTyVarShareRenamed.elm` | `a -> a` | `b -> z` | same body, non-matching name | ❌ type mismatch | inner `z` ≠ outer `a` → `x:a` can't be `z` |
| C-3 | `ScopedTyVarReQuant.elm` | `a -> Int` | `a -> a` | helper used at `Bool` **and** `String` | ❌ type mismatch | inner `a` = outer **rigid** `a` → monomorphic, can't take `Bool` |
| C-4 | `ScopedTyVarReQuantRenamed.elm` | `a -> Int` | `z -> z` | same two uses, non-matching name | ✅ compiles | inner `z` independently generalized → polymorphic |
| C-5 | `ScopedTyVarOpaque.elm` | `a -> a` | `a -> a` | opaque, consistent use only | ✅ compiles | **non-distinguishing trap** (fine under both (a) and (b)) |
| C-6 | `ScopedTyVarMutual.elm` | `a -> a` (mutual `f`/`g`) | `b -> a` | escape, inside a mutual SCC | ✅ compiles | sharing behaves identically inside a recursive group |
| C-7 | `ScopedTyVarNoOuterAnn.elm` | *(none)* | `b -> a` | escape, no enclosing annotation | 💥 compiler crash | rank bug; Elm does **not** re-quantify to recover |
| C-8 | `ScopedTyVarNoOuterAnnRenamed.elm` | *(none)* | `b -> z` | escape, no enclosing annotation | 💥 compiler crash | same crash regardless of name |
| C-9 | `ScopedTyVarNoOuterAnnOpaque.elm` | *(none)* | `a -> a` | opaque, no enclosing annotation | ✅ compiles | crash is tied to the *escape*, not to inner annotations per se |

### Why each pair is decisive (not just "it passed")

- **Pair C-1 vs C-2** (escape direction). The bodies are identical (`helper _ = x`); only
  the inner return-type *name* changes. With `a` it compiles; with `z` it fails with an
  error that literally says the two names are different variables (see below). The body
  returning `x : a` can only satisfy the inner annotation if the inner variable **is** the
  outer `a`. Compiles ⟺ name matches ⟺ sharing. This rules out (b): a re-quantified fresh
  variable could never be satisfied by returning the specific value `x`.

- **Pair C-3 vs C-4** (polymorphism direction — controls for "annotations are just rigid").
  One might object that an annotated helper `a -> a` is rigid *anyway*, so C-3 failing on
  `helper True` proves nothing. **C-4 is the control that defuses this**: the identical
  program with the helper named `z -> z` **compiles** and uses the helper at both `Bool`
  and `String`. So an annotated helper *can* be polymorphic at its use sites (it gets its
  own `forall`). The ONLY reason the `a`-named helper in C-3 is *not* polymorphic is that
  its `a` was **captured by / shared with the outer rigid `a`** and therefore not
  re-generalized at the inner `let`. Again: name flips monomorphic↔polymorphic ⟺ sharing.

- **C-5** is included precisely as the **trap**: an opaque, consistent use compiles under
  both interpretations and therefore proves nothing on its own. Reporting only C-5 would be
  the classic "a test passing is not enough" mistake.

- **C-6** shows the rule is unchanged when the annotated outer is a member of a
  mutually-recursive group (`f`/`g` cross-call; helper nested in `f` shares `f`'s `a`).

- **C-7/C-8/C-9** probe the mechanism: sharing is anchored on an **annotated** enclosing
  binder. With no outer annotation there is no properly-ranked rigid variable to share
  with; the "escape" cases (C-7, C-8) hit a **rank-handling bug** in the constraint solver
  (`a [rank = 2]` / `z [rank = 2]`, `Type/Solve.hs:206`), while the opaque case (C-9)
  compiles. Crucially, Elm **crashes rather than re-quantifying** — additional evidence
  against the best-effort hypothesis (b).

### Hypothesis signatures (how the matrix discriminates)

| Hypothesis | C-1 | C-2 | C-3 | C-4 |
|---|---|---|---|---|
| **(a) genuine name-based sharing** | ✅ | ❌ | ❌ | ✅ |
| (b) always re-quantify (never share) | ❌ | ❌ | ✅ | ✅ |
| always share regardless of name | ✅ | ✅ | ❌ | ❌ |
| best-effort (share/re-quant to make it pass) | ✅ | ✅ | ✅ | ✅ |

**Observed: ✅ ❌ ❌ ✅ → exactly hypothesis (a).** The "best-effort" hypothesis (b/the one
we set out to test) predicts everything passes; it does not. Elm is principled.

---

## Minimal examples + exact compiler output

### C-1 `ScopedTyVarShare.elm` — sharing makes the escape legal (✅)

```elm
outer : a -> a
outer x =
    let
        helper : b -> a   -- `a` here IS outer's `a`
        helper _ = x      -- returning x : a is therefore legal
    in
    helper 0
```

> `Success! Compiled 1 module.`

### C-2 `ScopedTyVarShareRenamed.elm` — rename `a`→`z` breaks it (❌)

```elm
outer : a -> a
outer x =
    let
        helper : b -> z   -- `z` is a DIFFERENT variable from outer's `a`
        helper _ = x      -- x : a cannot be z
    in
    helper 0
```

```
-- TYPE MISMATCH ------------------------------- src/ScopedTyVarShareRenamed.elm

Something is off with the body of the `helper` definition:

25|             x
                ^
This `x` value is a:

    a

But the type annotation on `helper` says it should be:

    z

Hint: Your type annotation uses `a` and `z` as separate type variables. Your
code seems to be saying they are the same though. Maybe they should be the same
in your type annotation? Maybe your code uses them in a weird way?
```

The hint is an explicit statement of Elm's model: **same name = same variable; different
names = different variables.**

### C-3 `ScopedTyVarReQuant.elm` — shared `a` is rigid/monomorphic (❌)

```elm
outer : a -> Int
outer x =
    let
        helper : a -> a   -- `a` = outer's RIGID `a`, so helper is NOT polymorphic
        helper y = y
    in
    (if helper True then 1 else 0) + String.length (helper "hi")
```

```
-- TYPE MISMATCH ------------------------------------ src/ScopedTyVarReQuant.elm

The 1st argument to `helper` is not what I expect:

27|     (if helper True then 1 else 0) + String.length (helper "hi")
                   ^^^^
This `True` value is a:

    Bool

But `helper` needs the 1st argument to be:

    a

Hint: Your type annotation uses type variable `a` which means ANY type of value
can flow through, but your code is saying it specifically wants a `Bool` value.
```

`helper`'s parameter type is reported as `a` (the outer variable), and it refuses `Bool`.

### C-4 `ScopedTyVarReQuantRenamed.elm` — rename `a`→`z` makes it polymorphic (✅)

```elm
outer : a -> Int
outer x =
    let
        helper : z -> z   -- fresh name → independently generalized → polymorphic
        helper y = y
    in
    (if helper True then 1 else 0) + String.length (helper "hi")
```

> `Success! Compiled 1 module.`

Same body and same two incompatible uses as C-3; the only change is the variable name, and
that alone makes the helper polymorphic. This is the linchpin of the whole argument.

### C-7 / C-8 `ScopedTyVarNoOuterAnn(.elm/Renamed)` — unannotated outer crashes (💥)

```elm
outer x =                 -- NO annotation on outer
    let
        helper : b -> a    -- (C-8 uses `b -> z`)
        helper _ = x
    in
    helper 0
```

```
elm: You ran into a compiler bug. Here are some details for the developers:

    a [rank = 2]        -- (C-8 prints `z [rank = 2]`)

CallStack (from HasCallStack):
  error, called at compiler/src/Type/Solve.hs:206:15 in main:Type.Solve
...
>   thread blocked indefinitely in an MVar operation
elm: thread blocked indefinitely in an MVar operation
```

C-9 (the same shape but with an **opaque** helper, `helper y = y` applied to `x`) compiles
cleanly, so the crash is specifically the *escape* (returning the outer parameter into an
inner annotated rigid variable) when there is no enclosing annotation to anchor the rank.

---

## Reproduce

Project: `elm-letrec-test/` (self-contained, has its own `shell.nix`). Elm 0.19.1.

In this environment `nix` was not on `PATH`; prepend the default profile bin dir, then run
inside `nix-shell`.

```bash
cd elm-letrec-test
export PATH="/nix/var/nix/profiles/default/bin:$PATH"

nix-shell --run 'elm make src/ScopedTyVarShare.elm            --output=/dev/null'  # ✅
nix-shell --run 'elm make src/ScopedTyVarShareRenamed.elm     --output=/dev/null'  # ❌ type mismatch (a vs z)
nix-shell --run 'elm make src/ScopedTyVarReQuant.elm          --output=/dev/null'  # ❌ type mismatch (a not Bool)
nix-shell --run 'elm make src/ScopedTyVarReQuantRenamed.elm   --output=/dev/null'  # ✅
nix-shell --run 'elm make src/ScopedTyVarOpaque.elm           --output=/dev/null'  # ✅ (non-distinguishing)
nix-shell --run 'elm make src/ScopedTyVarMutual.elm           --output=/dev/null'  # ✅
nix-shell --run 'elm make src/ScopedTyVarNoOuterAnn.elm       --output=/dev/null'  # 💥 compiler crash (rank bug)
nix-shell --run 'elm make src/ScopedTyVarNoOuterAnnRenamed.elm --output=/dev/null' # 💥 compiler crash (rank bug)
nix-shell --run 'elm make src/ScopedTyVarNoOuterAnnOpaque.elm --output=/dev/null'  # ✅
```

(Tried plain `elm` first: not on `PATH` in this environment; the `nix-shell` form works and
reports `elm --version` = `0.19.1`.)

---

## Bottom line for a type-system implementer

- **Yes, Elm supports scoped type variables in nested helpers, and it is genuine (a),
  name-based sharing — not best-effort re-quantification (b).**
- The rule is purely lexical: **each type-variable name is quantified once, at the
  outermost annotation in the scope chain that mentions it.** Inner annotations reusing
  that name reference the *same* (rigid, monomorphic-in-the-body) variable; inner
  annotations introducing a *new* name get their own `forall` (ordinary let
  generalization). Elm never decides quantification by looking at how the helper is used,
  so it cannot "silently re-quantify when tricky": the `a`-vs-`z` rename flips the result
  deterministically in both directions (C-1↔C-2 and C-3↔C-4).
- This is Haskell `ScopedTypeVariables` semantics, but **on by default and `forall`-free**,
  because Elm's quantification site for a name is fixed to the outermost annotation rather
  than requiring an explicit binder.
- The sharing is anchored on an **annotated** enclosing binder. If the enclosing function
  is unannotated and an inner annotation tries to "escape" the outer parameter into a rigid
  variable, Elm 0.19.1 does not gracefully re-quantify — it hits a **constraint-solver rank
  bug and crashes** (`a [rank = 2]`, `Type/Solve.hs:206`). Practically: to use scoped type
  variables in a helper, the enclosing function must carry the annotation that introduces
  the shared name.
- Consistent with the existing `FINDINGS.md`: annotations drive the polymorphism story.
  There, annotations enable mutual (but not self) polymorphic recursion; here, annotations
  are also what fix where each type variable is quantified, giving genuine scoped type
  variables. The scoped-tyvar behaviour is unchanged inside a mutually-recursive group
  (C-6).
```
