# Elm 0.19.1: polymorphism of (mutually) recursive `let` / top-level bindings

**Question:** Does Elm allow mutually recursive bindings to be polymorphic when they have type annotations?

**Short answer:** Yes — with type annotations, members of a (mutually) recursive group can call *each other* polymorphically (mutual polymorphic recursion). **But a binding's reference to *itself* is always monomorphic, even when annotated** — so direct self polymorphic recursion is rejected (occurs-check / infinite type). `let` and top-level behave identically.

All claims below are verified empirically with `elm make` (Elm 0.19.1).

## The rule

1. A reference to **another** annotated binding in the same recursive group instantiates that binding's **declared polymorphic scheme** fresh at each use site.
2. A binding's reference to **itself** is bound to the **monomorphic** in-progress type (the rigid annotation skeleton). It does *not* get its own scheme back, so a self-call at a different type forces `a = F a` → infinite type error.
3. Rule 2 holds even inside an otherwise-fine mutual group: a member may call its *sibling* polymorphically but never *itself*.
4. The cross-member polymorphism requires the annotation. Without annotations the group is one monomorphic SCC, generalized only *after* the group (ordinary HM let-generalization — a separate, weaker thing from polymorphic recursion).

> Practical workaround for self polymorphic recursion: split the function into two mutually recursive functions so the "recursive" call goes through an annotated *sibling* instead of the binding itself.

## Evidence matrix

| Test file | Bindings | Annotated? | Exercises | Result |
|---|---|---|---|---|
| `Body.elm` | mutual `f`/`g` | yes | use group polymorphically *in the let body* | ✅ |
| `NoAnnMutual.elm` | mutual `f`/`g` | no | same, no annotations | ✅ |
| `SelfRec.elm` | single `deep` | yes | **self** poly-recursion (`deep [xs]` at `List (List a)`) | ❌ infinite type |
| `MutualRec.elm` | mutual `even2`/`odd2` | yes | **mutual** poly-recursion (cross-calls at different types) | ✅ |
| `MutualMultiUse.elm` | mutual `f`/`g` | yes | sibling `g` used at `List a` **and** `(a,a)` in one body | ✅ |
| `MutualMultiUseNoAnn.elm` | mutual `f`/`g` | no | same, no annotations | ❌ type mismatch |
| `SelfInMutual.elm` | mutual `p`/`q` | yes | `p` cross-calls `q` (ok) **and** self-calls `p [xs]` | ❌ only on the self-call |
| `TopSelfRec.elm` | top-level single | yes | top-level version of `SelfRec` | ❌ infinite type |
| `TopMutualRec.elm` | top-level mutual | yes | top-level version of `MutualRec` | ✅ |

Key contrasts:
- `MutualRec` ✅ vs `SelfRec` ❌ → mutual works, self doesn't.
- `MutualMultiUse` ✅ vs `MutualMultiUseNoAnn` ❌ → the annotation is what enables it.
- `SelfInMutual` fails **only** on `p [ xs ]`, not on the `p`↔`q` cross-calls → self is monomorphic even inside a healthy mutual group.
- `Body`/`NoAnnMutual` ✅ regardless of annotations → ordinary "generalize-after-the-group" let-polymorphism is orthogonal to polymorphic recursion.

## Minimal examples

Works — mutual polymorphic recursion via annotated siblings (`MutualMultiUse.elm`). `g` is genuinely polymorphic: used at two incompatible types in one body.

```elm
let
    f : a -> Int
    f x =
        g [ x ] + g ( x, x )   -- g used at (List a) and (a, a)

    g : b -> Int
    g y =
        f y
in
f 0
```

Fails — direct self polymorphic recursion, even with annotation (`SelfRec.elm`):

```elm
let
    deep : List a -> Int
    deep xs =
        case xs of
            [] -> 0
            _ :: _ -> 1 + deep [ xs ]   -- deep at List (List a) → infinite type
in
deep [ 1, 2, 3 ]
```

Elm's error for the failing case:

```
The 1st argument to `deep` is not what I expect:
    1 + deep [ xs ]
            ^^^^^^
This argument is a list of type:  List (List a)
But `deep` needs the 1st argument to be:  List a
```

## Reproduce

Project: `elm-letrec-test/` (self-contained, has its own `shell.nix`). Elm 0.19.1.

Note: in this environment `nix` was not on `PATH`; prepend the default profile bin dir.

```bash
cd elm-letrec-test
export PATH="/nix/var/nix/profiles/default/bin:$PATH"

nix-shell --run 'elm make src/MutualRec.elm           --output=/dev/null'   # ✅
nix-shell --run 'elm make src/MutualMultiUse.elm       --output=/dev/null'   # ✅
nix-shell --run 'elm make src/SelfRec.elm             --output=/dev/null'   # ❌
nix-shell --run 'elm make src/SelfInMutual.elm        --output=/dev/null'   # ❌ (self-call only)
nix-shell --run 'elm make src/MutualMultiUseNoAnn.elm --output=/dev/null'   # ❌
```

## One-line takeaway for a type-system implementer

Elm's annotated-letrec rule: **siblings see each other's full polymorphic scheme; a binding never sees its own scheme polymorphically** (self-references are monomorphic). Annotations enable mutual polymorphic recursion but not self polymorphic recursion.
