# Versioned database values: design notes

Exploration notes (started 2026-11-20). Nothing here is implemented yet
except where marked.

## Goal

```
import db from Schema                   -- db : Db v0
let person = db.Person.find(pred)       -- person : Person v0
let! db1 = db.persist(newCarDraft)      -- db is consumed; db1 : Db v1
let other = db1.Car.find(pred2)         -- other : Car v1
car == other                            -- type error: Car v0 vs Car v1
```

* A database value is **affine**: a mutation consumes it and returns a new
  one. Reads do not consume it.
* Entities carry the **version** of the db they were read from. Entities of
  different versions have different types, so they cannot be compared. This
  removes the reference-vs-value equality question: within one version, two
  entities with the same id are equal in every respect, so `==` can be
  implemented as an id comparison. Across versions, the only meaningful
  question is "same row?", asked explicitly with `a.id == b.id`.
* Columns and links (`.name` vs `.wife`) are not distinguished, in either
  the surface or the core language.

## Decisions so far

1. **Versions are brands, not counts.** What matters is *which* snapshot an
   entity came from, not how many writes happened. Counting (`v(n+1)`) breaks
   on conditional writes (`if c then persist db x else db`), loops, helpers
   whose number of writes changes, and two independent dbs (both `v(0)`), and
   needs arithmetic in unification. A version is just a type variable:
   `Db v`, `Person v` are ordinary phantom type parameters, and comparability
   is ordinary type equality. This already works in EPL today.
2. **A mutation mints a fresh brand via an existential constructor.**
   `type AnyDb = MkAnyDb {w} (Db w)`, `persist : {v t} Db v -> Draft t -> AnyDb`
   (rank 1). Matching on `MkAnyDb db` introduces `w` as a fresh rigid type
   variable; the match's result type must not mention it (escape check).
   `let! db1 = e in rest` is sugar for `match e with MkAnyDb db1 -> rest`:
   a bind whose continuation must work for every version. This avoids both
   rank-n types and impredicativity (`AnyDb` is an ordinary type, so it can
   instantiate `foldr`'s `b`).
3. **Entities of a consumed db can't be read.** Field access on a
   `Person v` requires a live `Db v` in scope: `p0.name` is sugar for a read
   through `db0`. After `let! db1 = persist db0 ...`, there is no live
   `Db v0`, so `p0.name` is an error (with a quick fix: read it before the
   write). This rejects "time travel" queries such as
   `p0.friends.filter(.firstname == p1.firstname)` without any dependency
   analysis. An entity value is just `(id, brand)`, so `.id` needs no db and
   works anywhere: `p0.id == p1.id` is the explicit cross-version identity
   check. Primitive results (`String`, `Int`, ...) are unbranded and survive.
4. **Hoisting.** `p0.name` *means* "the name as of v0", so reading it before
   the write is its correct implementation. Start with the consistent error
   plus an editor quick fix; implicit hoisting can come later as sugar (it
   breaks down at lambdas and function boundaries).
5. **Backend: current state only.** As-of queries (system-versioned tables,
   Datomic-style) would let v0 entities live forever, but Postgres has no
   built-in support and history across schema changes is painful. A possible
   later upgrade: if a program's db values are one `REPEATABLE READ`
   transaction, the runtime could keep undo images of its own writes and
   answer as-of-v0 queries itself. The error in (3) would then turn into a
   feature without breaking any program.

## Background

* **Existentials, Haskell-style.** `data T = forall w. C (F w)`: the payload
  is fully usable after a match; only *which type* `w` is stays hidden.
  Unlike Lean's `∃` in `Prop` (no eliminating into data at all, forced by
  proof irrelevance), anything whose type doesn't mention `w` can be
  returned. The constructor's type is rank 1 (`C : {w} F w -> T`); the rank-2
  part is built into the `match` typing rule (Läufer & Odersky 1994).
* **The escape check** in the declarative rules is a scoping condition: the
  branch is typed one rigid level deeper, and the result type must be well
  formed at the outer level. In inference, Rémy levels already reject
  outer metavariables being solved to inner rigids (EPL does this today for
  annotations: "a type variable would escape its scope").
* **Impredicative** = instantiating a type variable with a quantified type.
  Hindley–Milner is predicative; wrapping the quantifier in a data type
  keeps it that way.
* **Precedents:** `runST` (Launchbury & Peyton Jones 1994), GhostCell
  (invariant brands), Ghosts of Departed Proofs; Wadler's `let!` in "Linear
  types can change the world!" (1990) and Odersky's "Observers for linear
  types" (1992) for read-only use of a linear value; Rust's `&'a Db` with
  `Person<'a>` (a borrow plus a projection; lifetimes give liveness, not
  distinctness, because of subtyping); Clean's uniqueness types (threading
  style: `usize :: *{#e} -> (Int, *{#e})`).

## Plan

1. **Existential type variables in constructors** (done 2026-11-23, proved):
   `type Pack a = MkPack {s} s (s -> a)`. Matching on such a constructor makes
   its variables fresh rigids one level deeper, and the result must be well
   formed at the outer level. A pattern may name the hidden types,
   `MkPack {t} x f`; otherwise they can't be named in the arm (messages and
   hover show the declaration's name, primed if it is taken).
2. `let!` sugar in the surface language.
3. Affine `Db` and the "live `Db v` in scope" rule for field access.
