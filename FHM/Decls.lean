import FHM.Core

/-! # Type declarations → `CtorEnv`  (well-formedness SPEC)

The surface language lets users declare algebraic data types (`type Maybe a =
Just a | Nothing`). After name resolution they arrive here as `DataDecl`s — with
type params already turned into de Bruijn `bvar`s (matching `Ctor.paramCount`) —
which are validated and elaborated into the `CtorEnv` that `Core`'s typing rules
(`ctor`, `match_`, the comparison primops) consult.

**Nothing new is needed in `Core`.** `Ctor`/`CtorEnv` already exist, and every
Core theorem is `∀ ctors`, so a well-formed declaration group is simply a
well-formed `CtorEnv` the existing metatheory already covers. This module is the
front-end that *produces* such an env.

This file contains ONLY the declarative spec — the `DataDecl` AST and the
predicates that say what a *well-formed* declaration group is. The decidable
checker and the elaborator into `CtorEnv` are deliberately **not here yet** (see
the "Deferred" note at the bottom); they will be written against this spec.

## The two passes (why the spec is shaped this way)

Types may reference each other out of order and mutually (`type Tree a = Node a
(Forest a)` / `type Forest a = …`). So well-formedness is stated in two stages,
mirroring how the checker will run:

1. **Collect** a `KindEnv` — every declared type name with its arity
   (`DataDecls.kindEnv`). This is a pure "names first" pass.
2. **Check** each constructor's field types against that `KindEnv`
   (`Ty.WellKinded`): type applications reference only declared types at the
   right arity, own-params are in range, and there are no free type variables. -/


/-- A resolved algebraic data-type declaration: a type constructor `name` of
    arity `paramCount`, with data constructors each carrying a list of field
    types. A field type may reference this type's own params via `.bvar i`
    (`i < paramCount`) and any declared type via `.customTy`; it carries no
    `.fvar`s. (This is the *post-name-resolution* form — the surface syntax with
    named params/fields resolves down to this.) -/
structure DataDecl where
  name : TyName
  paramCount : Nat
  ctors : List (CtorName × List Ty)
  deriving Repr


/-- The kinding environment for a declaration group: each declared type name
    mapped to its arity. Produced by the "names first" pass so that constructor
    bodies may reference types declared out of order or mutually. -/
abbrev KindEnv := LookupList TyName Nat


/-- **Kinding of a field type**, relative to a kind env `ke` and the declaring
    type's arity `pc`. This single predicate bundles the three obligations a
    `Ctor` field must meet — and, being an inductive over `Ty`, it *is* the
    "kind-checking logic":

    * **type applications** (`customTy T args`) reference a *declared* type `T`
      at its *declared arity* (`get? ke T = some args.length`), recursively;
    * **bound type vars** are in range (`bvar i` with `i < pc`) — the declaring
      type's own parameters, nothing else;
    * **closedness**: no `fvar` (note the deliberate absence of an `fvar` case).

    Consequently `WellKinded ke pc ty` implies both `ContainsBvarsUpTo pc ty`
    (the `Ctor.bound` obligation) and `NoFreeVars ty` (the `Ctor.closed`
    obligation) — so the elaborator can discharge a `Ctor`'s side-conditions
    straight from this. -/
inductive Ty.WellKinded (ke : KindEnv) (pc : Nat) : Ty → Prop
  | prim {p} :
      Ty.WellKinded ke pc (.prim p)
  | bvar {i} :
      i < pc →
      Ty.WellKinded ke pc (.bvar i)
  | arrow {a b} :
      Ty.WellKinded ke pc a →
      Ty.WellKinded ke pc b →
      Ty.WellKinded ke pc (.arrow a b)
  | customTy {T args} :
      LookupList.get? ke T = some args.length →
      (∀ arg ∈ args, Ty.WellKinded ke pc arg) →
      Ty.WellKinded ke pc (.customTy T args)


/-- Pass 1: the kind env induced by a declaration group (names + arities). -/
def DataDecls.kindEnv (decls : List DataDecl) : KindEnv :=
  decls.map (fun d => (d.name, d.paramCount))


/-- A single declaration is well-formed against a kind env when every field type
    of every constructor is well-kinded at the declaration's arity. -/
def DataDecl.WF (ke : KindEnv) (d : DataDecl) : Prop :=
  ∀ c ∈ d.ctors, ∀ ty ∈ c.2, Ty.WellKinded ke d.paramCount ty


/-- **A declaration group is well-formed** when, against the group's own kind env:
    every declaration's fields are well-kinded, and both the type names and the
    (group-wide) constructor names are distinct (the `CtorEnv` is keyed by ctor
    name, so ctor names must be globally unique). -/
structure DataDecls.WF (decls : List DataDecl) : Prop where
  /-- every declaration's constructor fields are well-kinded against the group env -/
  fields : ∀ d ∈ decls, DataDecl.WF (DataDecls.kindEnv decls) d
  /-- declared type names are distinct -/
  tyNamesNodup : (decls.map (·.name)).Nodup
  /-- constructor names are distinct across the whole group -/
  ctorNamesNodup : (decls.flatMap (fun d => d.ctors.map Prod.fst)).Nodup


/-! ## Deferred to the next step (functions — held for review of the spec above)

Once the spec is agreed, the executable side is:

* `Ty.decWellKinded : KindEnv → Nat → Ty → Bool` (or a `Decidable` instance) with
  a reflection lemma `= true ↔ Ty.WellKinded …`, plus
  `WellKinded → ContainsBvarsUpTo pc ty` and `WellKinded → NoFreeVars ty`
  (to feed a `Ctor`'s `bound`/`closed` fields — generalising `Examples.mkCtor`).
* `elabDecls : List DataDecl → Option CtorEnv` — the two-pass elaborator: build
  the `KindEnv`, check `DataDecls.WF` decidably, and on success emit one `Ctor`
  per constructor (`toTy` builds the uniform ADT result type automatically), as a
  `LookupList CtorName Ctor`; `none` on any violation.
* soundness: `elabDecls decls = some env → DataDecls.WF decls` (and vice-versa),
  so the produced env is well-formed by construction.
* a fixed **prelude** `CtorEnv` built via `elabDecls` (`Bool`, `List`, …),
  retiring the ad-hoc `Examples.demoCtors`. -/
