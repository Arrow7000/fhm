import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Card
import FHM.Bounds.Kernel

/-- Name of a type -/
inductive TyName
  | mk (str : String)
  deriving DecidableEq, Repr

/-- Name of a type constructor -/
inductive CtorName
  | mk (str : String)
  deriving DecidableEq, Repr

/-- Name of a value binding (or type variable) -/
inductive ValName
  | mk (str : String)
  deriving DecidableEq, Repr







abbrev LookupList (key : Type) (value : Type) := List (key × value)

namespace LookupList

def get? {k v} [DecidableEq k] (l : LookupList k v) (key : k) :=
  match l with
  | [] => none
  | ⟨key', val⟩ :: rest =>
    if key = key' then some val else get? rest key

/-- Proof that lookup list `l` contains the given key -/
inductive HasKey {k v : Type} (key : k) : (l : LookupList k v) → Prop
  | here : HasKey key (⟨key, val⟩ :: rest)
  | there : HasKey key l → HasKey key (⟨key', val⟩ :: l)

/-- Proof that lookup list `l` contains the given value at the specified key -/
inductive Has {k v : Type} (key : k) (val : v) : (l : LookupList k v) → Prop
  | here : Has key val (⟨key, val⟩ :: rest)
  | there : Has key val l → Has key val (⟨key', val'⟩ :: l)

end LookupList










inductive PrimTy
  | unit
  | int
  | nat
  | char
  deriving DecidableEq, Repr


/-- Prelude List ADT name (Nil/Cons). Bare `List t` is `customTy listTyName [t]`. -/
def listTyName : TyName := ⟨"List"⟩

inductive Ty
  | prim : PrimTy → Ty
  | arrow : (from_ to_ : Ty) → Ty
  /-- Bound var – only makes sense within the context of a polytype -/
  | bvar : Nat → Ty
  /-- Free var – unbound var. In spec-land this signifies an unconstrained variable. In algorithm-land this is a unification variable. -/
  | fvar : Nat → Ty
  /-- A custom type with its type params -/
  | customTy : TyName → List Ty → Ty
  /-- Bounded list `BL lo hi elem`. Length intervals are part of the type.
  Not the List ADT (`customTy listTyName […]`); see `bareListTy`. -/
  | bl : (lo hi : FHM.Bounds.CountSlot) → (elem : Ty) → Ty
  deriving Repr

/-- Bare HM list (no length demand): user `List t` or Infer-filled list shape. -/
def bareListTy (α : Ty) : Ty :=
  .customTy listTyName [α]

mutual
/-- Drop BL intervals for an HM view (`bl _ _ α` → bare `List α`). Pure function.
    Mutual with list walker so equations are definitional (`rfl` simp lemmas). -/
def Ty.eraseBounds : Ty → Ty
  | .prim p => .prim p
  | .arrow a b => .arrow (Ty.eraseBounds a) (Ty.eraseBounds b)
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .customTy n as => .customTy n (TyList.eraseBounds as)
  | .bl _ _ α => bareListTy (Ty.eraseBounds α)
def TyList.eraseBounds : List Ty → List Ty
  | [] => []
  | a :: as => Ty.eraseBounds a :: TyList.eraseBounds as
end

@[simp] theorem Ty.eraseBounds_bl (lo hi : FHM.Bounds.CountSlot) (α : Ty) :
    Ty.eraseBounds (.bl lo hi α) = bareListTy (Ty.eraseBounds α) := rfl

@[simp] theorem Ty.eraseBounds_bareList (α : Ty) :
    Ty.eraseBounds (bareListTy α) = bareListTy (Ty.eraseBounds α) := rfl

@[simp] theorem Ty.eraseBounds_prim (p : PrimTy) :
    Ty.eraseBounds (.prim p) = .prim p := rfl

@[simp] theorem Ty.eraseBounds_arrow (a b : Ty) :
    Ty.eraseBounds (.arrow a b) = .arrow (Ty.eraseBounds a) (Ty.eraseBounds b) := rfl

@[simp] theorem Ty.eraseBounds_fvar (i : Nat) :
    Ty.eraseBounds (.fvar i) = .fvar i := rfl

@[simp] theorem Ty.eraseBounds_bvar (i : Nat) :
    Ty.eraseBounds (.bvar i) = .bvar i := rfl

@[simp] theorem Ty.eraseBounds_customTy (n : TyName) (as : List Ty) :
    Ty.eraseBounds (.customTy n as) = .customTy n (TyList.eraseBounds as) := rfl

@[simp] theorem TyList.eraseBounds_nil : TyList.eraseBounds [] = [] := rfl

@[simp] theorem TyList.eraseBounds_cons (a : Ty) (as : List Ty) :
    TyList.eraseBounds (a :: as) = Ty.eraseBounds a :: TyList.eraseBounds as := rfl

theorem TyList.eraseBounds_eq_map (as : List Ty) :
    TyList.eraseBounds as = as.map Ty.eraseBounds := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [ih]

structure PolyTy where
  paramCount : Nat
  /-- May reference params by `.bvar`s in range of `paramCount`  -/
  body : Ty
  -- TODO(bounds-preserving Phase 1 follow-up): Nat/count telescope for schemes
  -- like `{n : Nat, a} BL n n a → …`. Surface already has `natBinders` on
  -- bindings; Infer must ignore count binders. Do not leave length polymorphism
  -- only in a sidecar forever — extend PolyTy when monotype `Ty.bl` is green.

/-- Make a polytype with no type vars -/
def PolyTy.mkTrivial (bodyTy : Ty) : PolyTy :=
  { paramCount := 0, body := bodyTy }





/-- `ty` can only contain `bvar`s that are lower than `n`. If `n = 0` `ty` contains no `bvar`s at all. -/
inductive ContainsBvarsUpTo (n : Nat) : (ty : Ty) → Prop
  | prim :
    ContainsBvarsUpTo n (.prim p)

  | arrow :
    ContainsBvarsUpTo n fst →
    ContainsBvarsUpTo n snd →
    ContainsBvarsUpTo n (.arrow fst snd)

  | fvar :
    ContainsBvarsUpTo n (.fvar i)

  | customTy :
    (∀ ty ∈ tys, ContainsBvarsUpTo n ty) →
    ContainsBvarsUpTo n (.customTy name tys)

  | bl :
    ContainsBvarsUpTo n elem →
    ContainsBvarsUpTo n (.bl lo hi elem)

  | bvar :
    i < n →
    ContainsBvarsUpTo n (.bvar i)



/-- ty contains no `fvar`s at all -/
inductive NoFreeVars : (ty : Ty) → Prop
  | prim :
    NoFreeVars (.prim p)

  | arrow :
    NoFreeVars fst →
    NoFreeVars snd →
    NoFreeVars (.arrow fst snd)

  | customTy :
    (∀ ty ∈ tys, NoFreeVars ty) →
    NoFreeVars (.customTy name tys)

  | bl :
    NoFreeVars elem →
    NoFreeVars (.bl lo hi elem)

  | bvar :
    NoFreeVars (.bvar i)







/-- A constructor for a type. E.g. `Result.Ok`, `Maybe.Some`, `Maybe.None` -/
structure Ctor where
  /-- How many type params the type has -/
  paramCount : Nat
  /-- The name of the type this is a constructor for -/
  tyName : TyName
  /-- What this constructor actually contains.
      Can reference `.bvar`s in range of `paramCount` -/
  contents : List Ty
  /-- Proof that all tys are appropriately bound -/
  bound : ∀ ty ∈ contents, ContainsBvarsUpTo paramCount ty
  /-- Contains no free vars -/
  closed : ∀ ty ∈ contents, NoFreeVars ty

/-- Which type constructors exist -/
abbrev CtorEnv := LookupList CtorName Ctor





/-- Maps from de Bruijn index of value bindings to their types -/
abbrev Env := List PolyTy










/-- Primitive literals -/
inductive PrimLitExpr
  | unit : PrimLitExpr
  | int : Int → PrimLitExpr
  | nat : Nat → PrimLitExpr
  | char : Char → PrimLitExpr


/-- Primitive binary operators: built-in, monomorphic, curried 2-argument
    functions. Each has a fixed type (the typing rules assign it explicitly) and
    a δ-rule in `SmallStep.Step` that fires on a *saturated* application to
    literal operands.     Arithmetic ops (`intAdd`/`intSub`) return `int`
    unconditionally; the comparison ops `intLt`/`charLt` return `Bool` and so are
    only well-typed relative to an env providing `Bool` (see
    `TypeOfElabHM.primBinOpIntLt`). -/
inductive PrimBinOp
  | intAdd
  | intSub
  | intLt
  | charLt
  deriving DecidableEq, Repr

/-- Type of a primitive literal (`TypeOfHM` / `TypeOfElabHM` primLit rules). -/
def PrimLitExpr.ty : PrimLitExpr → Ty
  | .unit => .prim .unit
  | .int _ => .prim .int
  | .nat _ => .prim .nat
  | .char _ => .prim .char

/-- Nullary `Bool` constructor shape (matches `Ctor.isBoolCtor` in InferW). -/
def Ctor.isNullaryBool (c : Ctor) : Bool :=
  c.tyName == ⟨"Bool"⟩ && c.paramCount == 0 && c.contents.isEmpty

/-- Type of a primitive binary op. Comparison ops need `True`/`False` Bool
    ctors in `ctors` (same gate as `inferCore`). -/
def PrimBinOp.ty (ctors : CtorEnv) : PrimBinOp → Option Ty
  | .intAdd =>
      some (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | .intSub =>
      some (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))
  | .intLt =>
      match LookupList.get? ctors ⟨"True"⟩, LookupList.get? ctors ⟨"False"⟩ with
      | some tc, some fc =>
        if tc.isNullaryBool && fc.isNullaryBool then
          some (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))
        else none
      | _, _ => none
  | .charLt =>
      match LookupList.get? ctors ⟨"True"⟩, LookupList.get? ctors ⟨"False"⟩ with
      | some tc, some fc =>
        if tc.isNullaryBool && fc.isNullaryBool then
          some (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))
        else none
      | _, _ => none

inductive MatchPattern
  /-- `contents` is basically just a binding range. i.e. if 2 this means we've bound 2 new "names" to the context -/
  | named (ctor : CtorName) (contents : Nat)
  | wildcard
  deriving DecidableEq, Repr

/-- How many variables a branch pattern binds: a `named` ctor binds its
    `contents`-many fields; `wildcard` binds nothing. -/
def MatchPattern.bindCount : MatchPattern → Nat
  | .named _ n => n
  | .wildcard  => 0

/-- Does this branch pattern fire for constructor `name` of the given `arity`?
    A `named` pattern matches its exact ctor+arity; `wildcard` matches anything. -/
def MatchPattern.matchesCtor : MatchPattern → CtorName → Nat → Bool
  | .named c n, name, arity => c == name && n == arity
  | .wildcard,  _,    _     => true


/-- An expression in our language -/
inductive Expr
  | primLit (prim : PrimLitExpr)
  /-- A primitive binary operator (e.g. `intAdd`). A leaf naming a built-in,
      curried, monomorphic 2-argument function, applied via ordinary `app`. Its
      type is fixed (see the `primBinOp*` rules of `TypeOfElabHM`/`TypeOfHM`); a
      *saturated* application to literal operands reduces by a δ-rule in
      `SmallStep.Step`, while a partial application `app (primBinOp op) v` is a
      value (a stuck function). -/
  | primBinOp (op : PrimBinOp)
  /-- A lambda. `paramAnn` is an optional type ascription on the parameter
      (surface `λ(x : T). body`); `none` means the param type is inferred. -/
  | lambda (paramAnn : Option Ty) (body : Expr)
  | app (f input : Expr)
  /-- A let binding. `ann` is an optional scheme ascription on the bound
      expression (surface `let x : σ = e in body`); `none` means the scheme is
      generalised by inference. -/
  | letIn (ann : Option PolyTy) (bindingExpr body : Expr)
  /-- A variable use (de Bruijn index into the term-variable environment).
      Type-erased: no type arguments are stored — the machine relation
      (`TypeOfHM.var`) instantiates the bound scheme existentially, so reduction
      never computes with types. -/
  | var (deBruijnIndex : Nat)
  /-- A type constructor -/
  | ctor (name : CtorName)
  | match_ (scrutinee : Expr) (branches : List (MatchPattern × Expr))
  /-- A (mutually) recursive binding group with **per-binding optional scheme
      annotations** (mirroring `letIn`'s `ann`). The `bindings` (the RHSs
      `e₀ … e_{n-1}`) AND `body` are all in scope of the `n = bindings.length`
      group binders, with binding `j` at de Bruijn index `j`. `n = 1` is `fix`.

      `anns` carries one `Option PolyTy` per binding (PARALLEL to `bindings`;
      the length invariant lives in the typing rule, not the constructor).
      An UNANNOTATED member (`none`) is typed at a shared monotype linked
      through the group's gen-var pool and generalised only for the `body`
      (Damas–Milner monomorphic recursion). An ANNOTATED member (`some σ`) is
      in scope at its FULL declared scheme in both the RHSs and the `body`, so
      recursive occurrences may instantiate `σ` at different types (Pottier's
      `LetRecPoly` — decidable polymorphic recursion); its binding is stored
      scheme-relatively (its own scheme's variables at `bvar`s, opened fresh by
      the typing rule). The all-`none` and all-`some` groups are exactly the
      historical `letRec` / `letRecAnn` nodes. -/
  | letRec (anns : List (Option PolyTy)) (bindings : List Expr) (body : Expr)







/-- Build `[.bvar start, .bvar (start+1), ..., .bvar (start+count-1)]`. -/
def Ty.bvarRangeFrom (start : Nat) : Nat → List Ty
  | 0     => []
  | n + 1 => .bvar start :: bvarRangeFrom (start + 1) n


/-- Build `[.bvar 0, .bvar 1, ..., .bvar (count-1)]`. -/
def Ty.bvarRange : Nat → List Ty :=
  Ty.bvarRangeFrom 0


/-- Wrap a list of argument types in right-nested arrows ending at a result type:

    `[a₁, a₂, ..., aₙ]`, `r` ↦ `a₁ → a₂ → ... → aₙ → r`. -/
def Ty.wrapArrows (result : Ty) : List Ty → Ty
  | []          => result
  | arg :: rest => .arrow arg (wrapArrows result rest)

/--
  Convert a constructor entry to its polytype.

  E.g. for `Result.ok`:
    `{ paramCount := 2, tyName := Result, contents := [.bvar 1] }`

  produces the polytype `∀ e t. t → Result e t`:
    `{ paramCount := 2,
       body       := .arrow (.bvar 1)
                            (.customTy Result [.bvar 0, .bvar 1]) }`. -/
def Ctor.toTy (ctor : Ctor) : PolyTy :=
  let resultTy :=
    Ty.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)

  let body := Ty.wrapArrows resultTy ctor.contents
  { paramCount := ctor.paramCount, body }












/-- Full context. Contains both bindings and type constructors maps. -/
structure Ctx where
  /-- Value bindings -/
  env : Env
  /-- Which type constructors exist here -/
  ctors : CtorEnv




mutual

/-- Get all the `.fvar`s from the `Ty`, deduped -/
def Ty.freeVars : Ty → List Nat
  | .prim _ => []
  | .arrow a b => (a.freeVars ++ b.freeVars).dedup
  | .fvar n => [n]
  | .bvar _ => []
  | .customTy _ tys => TyList.freeVars tys
  | .bl _ _ e => e.freeVars

def TyList.freeVars : List Ty → List Nat
  | [] => []
  | head :: tail => (head.freeVars ++ TyList.freeVars tail).dedup

end


mutual
/-- A *closed monotype*: no free **and** no bound type variables. This is the
    decidable check used to validate parameter annotations (`λ(x : T). …`),
    which must be closed (`Ty.isClosed_iff`: `↔ NoFreeVars ∧ ContainsBvarsUpTo 0`). -/
def Ty.isClosed : Ty → Bool
  | .prim _          => true
  | .arrow a b       => a.isClosed && b.isClosed
  | .fvar _          => false
  | .bvar _          => false
  | .customTy _ tys  => TyList.isClosed tys
  | .bl _ _ e        => e.isClosed
def TyList.isClosed : List Ty → Bool
  | []      => true
  | t :: ts => t.isClosed && TyList.isClosed ts
end

theorem TyList.isClosed_iff_forall (tys : List Ty) :
    TyList.isClosed tys = true ↔ ∀ t ∈ tys, t.isClosed = true := by
  induction tys with
  | nil => simp [TyList.isClosed]
  | cons hd tl ih =>
    simp only [TyList.isClosed, Bool.and_eq_true, List.mem_cons]
    rw [ih]
    constructor
    · rintro ⟨hhd, htl⟩ t (rfl | ht)
      · exact hhd
      · exact htl t ht
    · intro h
      exact ⟨h hd (Or.inl rfl), fun t ht => h t (Or.inr ht)⟩



def Env.freeVars : Env → List Nat
  | [] => []
  | polyTy :: tail =>
    (polyTy.body.freeVars ++ freeVars tail).dedup


mutual

/-- For every `.fvar i`, if `i < vars.length`, replace the `.fvar` with `.bvar vars[i]`.

In other words, remove the given free vars and bind them back up. I.e. close them up, to make a polytype with `vars.length` binders ✨ -/
def Ty.closeOver (vars : List Nat) : Ty → Ty
  | .prim p          => .prim p
  | .arrow a b       => .arrow (a.closeOver vars) (b.closeOver vars)
  | .bvar i          => .bvar i
  | .customTy nm tys => .customTy nm (TyList.closeOver vars tys)
  | .bl lo hi e      => .bl lo hi (e.closeOver vars)
  | .fvar n          =>
      match vars.idxOf? n with
      | some i => .bvar i
      | none   => .fvar n


def TyList.closeOver (vars : List Nat) : List Ty → List Ty
  | []        => []
  | hd :: tl  => hd.closeOver vars :: TyList.closeOver vars tl

end

private lemma List.findIdx?_go_lt {p : α → Bool} {l : List α} {n i : Nat}
    (h : List.findIdx?.go p l n = some i) : i - n < l.length := by
  induction l generalizing n with
  | nil => simp [List.findIdx?.go] at h
  | cons hd tl ih =>
    simp [List.findIdx?.go] at h
    split at h
    · simp at h;
      subst h
      simp
    · have := ih h; simp; omega

private lemma List.idxOf?_lt_length {a : α} [BEq α] {l : List α} {i : Nat}
    (h : l.idxOf? a = some i) : i < l.length := by
  have := List.findIdx?_go_lt (n := 0) h
  omega

/--
Strong induction principle for `Ty` that gives a useful IH for the `customTy`
case: `(∀ t ∈ tys, motive t)`, rather than the bare `motive tys` you'd get from
the auto-generated recursor (which doesn't recurse into the embedded `List Ty`).

Usage:
```
theorem some_property : ∀ ty : Ty, P ty := by
  intro ty
  induction ty using Ty.rec_strong
  case prim p           => ...
  case arrow a b iha ihb => ...
  case bvar n           => ...
  case fvar n           => ...
  case customTy nm tys ih => ...   -- ih : ∀ t ∈ tys, P t
```
-/
@[elab_as_elim]
def Ty.rec_strong.{u} {motive : Ty → Sort u}
    (prim     : ∀ p, motive (.prim p))
    (arrow    : ∀ a b, motive a → motive b → motive (.arrow a b))
    (bvar     : ∀ n, motive (.bvar n))
    (fvar     : ∀ n, motive (.fvar n))
    (customTy : ∀ nm tys, (∀ t ∈ tys, motive t) → motive (.customTy nm tys))
    (bl       : ∀ lo hi e, motive e → motive (.bl lo hi e)) :
    (ty : Ty) → motive ty
  | .prim p          => prim p
  | .arrow a b       =>
      arrow a b
        (Ty.rec_strong prim arrow bvar fvar customTy bl a)
        (Ty.rec_strong prim arrow bvar fvar customTy bl b)
  | .bvar n          => bvar n
  | .fvar n          => fvar n
  | .customTy nm tys =>
      customTy nm tys
        (fun t _ht => Ty.rec_strong prim arrow bvar fvar customTy bl t)
  | .bl lo hi e      =>
      bl lo hi e (Ty.rec_strong prim arrow bvar fvar customTy bl e)
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem _ht; omega)

/-- Erasing intervals twice is idempotent. -/
@[simp] theorem Ty.eraseBounds_idem (τ : Ty) :
    Ty.eraseBounds (Ty.eraseBounds τ) = Ty.eraseBounds τ := by
  induction τ using Ty.rec_strong with
  | prim p => rfl
  | arrow a b iha ihb => simp only [Ty.eraseBounds, iha, ihb]
  | bvar i => rfl
  | fvar i => rfl
  | customTy nm tys ih =>
    simp only [Ty.eraseBounds]
    refine congrArg (Ty.customTy nm) ?_
    induction tys with
    | nil => rfl
    | cons hd tl ih_tl =>
      simp only [TyList.eraseBounds, List.cons.injEq]
      exact ⟨ih hd List.mem_cons_self, ih_tl fun t ht => ih t (List.mem_cons_of_mem _ ht)⟩
  | bl lo hi e ih =>
    simp only [bareListTy, Ty.eraseBounds, TyList.eraseBounds, ih]

/-- Erase monotype body of a scheme (param count unchanged). -/
def PolyTy.eraseBounds (σ : PolyTy) : PolyTy :=
  ⟨σ.paramCount, Ty.eraseBounds σ.body⟩

@[simp] theorem PolyTy.eraseBounds_mkTrivial (τ : Ty) :
    PolyTy.eraseBounds (PolyTy.mkTrivial τ) = PolyTy.mkTrivial (Ty.eraseBounds τ) :=
  rfl

@[simp] theorem PolyTy.eraseBounds_paramCount (σ : PolyTy) :
    (PolyTy.eraseBounds σ).paramCount = σ.paramCount :=
  rfl

@[simp] theorem PolyTy.eraseBounds_body (σ : PolyTy) :
    (PolyTy.eraseBounds σ).body = Ty.eraseBounds σ.body :=
  rfl

@[simp] theorem PolyTy.eraseBounds_idem (σ : PolyTy) :
    PolyTy.eraseBounds (PolyTy.eraseBounds σ) = PolyTy.eraseBounds σ := by
  cases σ with | mk n b => simp [PolyTy.eraseBounds, Ty.eraseBounds_idem]

/-- Path R projection: map type annotations through `eraseBounds`. Term structure
    is unchanged; only type-shaped payloads (binder anns, var tyArgs) are erased.
    Pipeline Infer/bounds never call this — residual HM bridge theorems only.

    Termination is structural on `Expr` via `sizeOf` (match uses pair projection
    so the recursive arg stays under list membership). -/
def Expr.eraseBounds : Expr → Expr
  | .primLit p => .primLit p
  | .primBinOp op => .primBinOp op
  | .lambda ann body => .lambda (ann.map Ty.eraseBounds) body.eraseBounds
  | .app f arg => .app f.eraseBounds arg.eraseBounds
  | .letIn ann rhs body =>
      .letIn (ann.map PolyTy.eraseBounds) rhs.eraseBounds body.eraseBounds
  | .var i => .var i
  | .ctor c => .ctor c
  | .match_ scrut brs =>
      .match_ scrut.eraseBounds (brs.map fun pe => (pe.1, pe.2.eraseBounds))
  | .letRec anns bindings body =>
      .letRec (anns.map (Option.map PolyTy.eraseBounds))
        (bindings.map Expr.eraseBounds) body.eraseBounds
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := List.sizeOf_lt_of_mem ‹_›; omega)
    | (have h := List.sizeOf_lt_of_mem ‹_›
       have : sizeOf pe.2 < sizeOf pe := by
         cases pe; simp only [Prod.mk.sizeOf_spec]; omega
       omega)





/-- Pointwise erase of schemes in a value environment. -/
def Env.eraseBounds (env : Env) : Env := env.map PolyTy.eraseBounds

@[simp] theorem Env.eraseBounds_nil : Env.eraseBounds [] = [] := rfl

@[simp] theorem Env.eraseBounds_cons (σ : PolyTy) (env : Env) :
    Env.eraseBounds (σ :: env) = PolyTy.eraseBounds σ :: Env.eraseBounds env := rfl

theorem Env.eraseBounds_getElem? (env : Env) (i : Nat) :
    (Env.eraseBounds env)[i]? = (env[i]?).map PolyTy.eraseBounds := by
  simp only [Env.eraseBounds, List.getElem?_map]

/-- `eraseBounds` preserves bvar structure (BL → bare List keeps the element). -/
theorem ContainsBvarsUpTo.eraseBounds {n : Nat} {τ : Ty}
    (h : ContainsBvarsUpTo n τ) : ContainsBvarsUpTo n (Ty.eraseBounds τ) := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | fvar => exact .fvar
  | customTy hall ih =>
    simp only [Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map]
    refine .customTy ?_
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact ih t₀ ht₀
  | bl he ih =>
    simp only [Ty.eraseBounds_bl, bareListTy]
    refine .customTy ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ih
  | bvar hlt =>
    exact .bvar hlt

/-- Converse: bvars in `τ` are exactly those of `erase τ` (erase never drops bvars). -/
theorem ContainsBvarsUpTo.of_eraseBounds {n : Nat} {τ : Ty}
    (h : ContainsBvarsUpTo n (Ty.eraseBounds τ)) : ContainsBvarsUpTo n τ := by
  induction τ using Ty.rec_strong generalizing n with
  | prim _ => exact .prim
  | arrow a b iha ihb =>
    simp only [Ty.eraseBounds_arrow] at h
    cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    simp only [Ty.eraseBounds_bvar] at h
    cases h with | bvar hlt => exact .bvar hlt
  | fvar _ => exact .fvar
  | customTy nm tys ih =>
    simp only [Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map] at h
    cases h with
    | customTy hall =>
      refine .customTy ?_
      intro t ht
      have ht' : Ty.eraseBounds t ∈ tys.map Ty.eraseBounds :=
        List.mem_map_of_mem (f := Ty.eraseBounds) ht
      exact ih t ht (hall _ ht')
  | bl lo hi e ih =>
    simp only [Ty.eraseBounds_bl, bareListTy] at h
    cases h with
    | customTy hall =>
      have he : ContainsBvarsUpTo n (Ty.eraseBounds e) :=
        hall _ (by simp only [List.mem_singleton])
      exact .bl (ih he)

/-- `eraseBounds` preserves freeness of type variables (BL → List keeps the element). -/
theorem NoFreeVars.eraseBounds {τ : Ty} (h : NoFreeVars τ) :
    NoFreeVars (Ty.eraseBounds τ) := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | customTy hall ih =>
    simp only [Ty.eraseBounds_customTy, TyList.eraseBounds_eq_map]
    refine .customTy ?_
    intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    exact ih t₀ ht₀
  | bl he ih =>
    simp only [Ty.eraseBounds_bl, bareListTy]
    exact .customTy (by
      intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ih)
  | bvar => exact .bvar

/-- Path R: project intervals out of constructor field types (and thus `toTy`). -/
def Ctor.eraseBounds (c : Ctor) : Ctor where
  paramCount := c.paramCount
  tyName := c.tyName
  contents := c.contents.map Ty.eraseBounds
  bound := by
    intro ty hty
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hty
    exact ContainsBvarsUpTo.eraseBounds (c.bound t ht)
  closed := by
    intro ty hty
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hty
    exact NoFreeVars.eraseBounds (c.closed t ht)

/-- Pointwise erase of every constructor's field types. -/
def CtorEnv.eraseBounds (ctors : CtorEnv) : CtorEnv :=
  ctors.map fun p => (p.1, Ctor.eraseBounds p.2)

/-- Path R residual context: erase schemes **and** ctor field types.
    (Earlier "ctors unchanged; prelude/NoBL assumed" made residual `TypeOf*`
    false when a field carries `BL` — structural `InstantiatesBy` cannot
    relate a BL template to an erased List instance.) -/
def Ctx.eraseBounds (ctx : Ctx) : Ctx :=
  { env := ctx.env.eraseBounds, ctors := ctx.ctors.eraseBounds }

@[simp] theorem Ctor.eraseBounds_paramCount (c : Ctor) :
    (Ctor.eraseBounds c).paramCount = c.paramCount := rfl

@[simp] theorem Ctor.eraseBounds_tyName (c : Ctor) :
    (Ctor.eraseBounds c).tyName = c.tyName := rfl

@[simp] theorem Ctor.eraseBounds_contents (c : Ctor) :
    (Ctor.eraseBounds c).contents = c.contents.map Ty.eraseBounds := rfl

@[simp] theorem CtorEnv.eraseBounds_nil : CtorEnv.eraseBounds [] = [] := rfl

@[simp] theorem CtorEnv.eraseBounds_cons (name : CtorName) (c : Ctor) (rest : CtorEnv) :
    CtorEnv.eraseBounds ((name, c) :: rest) =
      (name, Ctor.eraseBounds c) :: CtorEnv.eraseBounds rest := rfl

@[simp] theorem Ctx.eraseBounds_mk (env : Env) (ctors : CtorEnv) :
    Ctx.eraseBounds ⟨env, ctors⟩ = ⟨Env.eraseBounds env, CtorEnv.eraseBounds ctors⟩ := rfl

theorem CtorEnv.eraseBounds_get? (ctors : CtorEnv) (name : CtorName) :
    LookupList.get? (CtorEnv.eraseBounds ctors) name =
      (LookupList.get? ctors name).map Ctor.eraseBounds := by
  induction ctors with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with | mk n c =>
    simp only [CtorEnv.eraseBounds_cons, LookupList.get?]
    by_cases h : name = n
    · simp only [h, ↓reduceIte, Option.map_some]
    · simp only [h, ↓reduceIte, ih]

/-- Closing doesn't add any more bvars than it is expected to -/
theorem Ty.closeOver_preserves_bvars : ContainsBvarsUpTo 0 ty → ContainsBvarsUpTo vars.length (ty.closeOver vars) := by
  intro prem
  induction ty using Ty.rec_strong with
  | prim p => exact .prim
  | arrow a b iha ihb =>
    cases prem with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    cases prem with | bvar h => exact .bvar (by omega)
  | fvar n =>
    -- After `bl` was added, the fvar equation is `closeOver.eq_6`.
    rw [Ty.closeOver.eq_6]
    cases h : vars.idxOf? n with
    | some i => exact .bvar (List.idxOf?_lt_length h)
    | none => exact .fvar
  | customTy nm tys ih =>
    cases prem with
    | customTy hall =>
      have hmap : ∀ l, TyList.closeOver vars l = l.map (Ty.closeOver vars) := by
        intro l; induction l with
        | nil => rfl
        | cons hd tl ihl => simp [TyList.closeOver, ihl]
      simp only [Ty.closeOver]
      rw [hmap]
      exact .customTy (fun t ht => by
        obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
        exact ih t0 ht0 (hall t0 ht0))
  | bl lo hi e ih =>
    cases prem with | bl he => exact .bl (ih he)


theorem Ty.isClosed_iff (t : Ty) :
    t.isClosed = true ↔ NoFreeVars t ∧ ContainsBvarsUpTo 0 t := by
  induction t using Ty.rec_strong with
  | prim p => exact iff_of_true rfl ⟨.prim, .prim⟩
  | fvar n =>
    refine iff_of_false (by simp [Ty.isClosed]) ?_
    rintro ⟨hnfv, _⟩; cases hnfv
  | bvar i =>
    refine iff_of_false (by simp [Ty.isClosed]) ?_
    rintro ⟨_, hbv⟩; cases hbv with | bvar h => omega
  | arrow a b iha ihb =>
    simp only [Ty.isClosed, Bool.and_eq_true]
    rw [iha, ihb]
    constructor
    · rintro ⟨⟨na, ca⟩, nb, cb⟩; exact ⟨.arrow na nb, .arrow ca cb⟩
    · rintro ⟨hn, hc⟩
      cases hn with | arrow na nb => cases hc with | arrow ca cb => exact ⟨⟨na, ca⟩, nb, cb⟩
  | customTy name tys ih =>
    show TyList.isClosed tys = true ↔ _
    rw [TyList.isClosed_iff_forall]
    constructor
    · intro h
      refine ⟨.customTy fun t ht => ((ih t ht).mp (h t ht)).1,
              .customTy fun t ht => ((ih t ht).mp (h t ht)).2⟩
    · rintro ⟨hn, hc⟩ t ht
      cases hn with
      | customTy hn' => cases hc with
        | customTy hc' => exact (ih t ht).mpr ⟨hn' t ht, hc' t ht⟩
  | bl lo hi e ih =>
    simp only [Ty.isClosed]
    rw [ih]
    constructor
    · intro ⟨nf, cb⟩; exact ⟨.bl nf, .bl cb⟩
    · rintro ⟨hn, hc⟩
      cases hn with | bl nf => cases hc with | bl cb => exact ⟨nf, cb⟩


/--
Strong induction principle for `Expr` that gives a useful IH for the `match_`
case: `(∀ pat e, (pat, e) ∈ branches → motive e)`, rather than the bare
`motive branches` you'd get from the auto-generated recursor (which doesn't
recurse into the embedded `List (MatchPattern × Expr)`).

Usage:
```
theorem some_property : ∀ e : Expr, P e := by
  intro e
  induction e using Expr.rec_strong
  case primLit p                       => ...
  case lambda paramAnn body ih         => ...
  case app f input ihf ihi             => ...
  case letIn ann be body ihbe ihbo     => ...
  case var n                           => ...
  case ctor nm                         => ...
  case match_ scrutinee branches ihs ihbs => ...
    -- ihbs : ∀ pat e, (pat, e) ∈ branches → P e
```
-/
@[elab_as_elim]
def Expr.rec_strong.{u} {motive : Expr → Sort u}
    (primLit    : ∀ p, motive (.primLit p))
    (primBinOp  : ∀ op, motive (.primBinOp op))
    (lambda     : ∀ paramAnn body, motive body → motive (.lambda paramAnn body))
    (app        : ∀ f input, motive f → motive input → motive (.app f input))
    (letIn      : ∀ ann bindingExpr body,
                    motive bindingExpr → motive body →
                    motive (.letIn ann bindingExpr body))
    (var        : ∀ n, motive (.var n))
    (ctor       : ∀ nm, motive (.ctor nm))
    (match_     : ∀ scrutinee branches,
                    motive scrutinee →
                    (∀ pat e, (pat, e) ∈ branches → motive e) →
                    motive (.match_ scrutinee branches))
    (letRec     : ∀ anns bindings body,
                    (∀ e ∈ bindings, motive e) →
                    motive body →
                    motive (.letRec anns bindings body)) :
    (e : Expr) → motive e
  | .primLit p          => primLit p
  | .primBinOp op       => primBinOp op
  | .lambda paramAnn body        =>
      lambda paramAnn body
        (Expr.rec_strong primLit primBinOp lambda app letIn var ctor match_ letRec body)
  | .app f input        =>
      app f input
        (Expr.rec_strong primLit primBinOp lambda app letIn var ctor match_ letRec f)
        (Expr.rec_strong primLit primBinOp lambda app letIn var ctor match_ letRec input)
  | .letIn ann be body      =>
      letIn ann be body
        (Expr.rec_strong primLit primBinOp lambda app letIn var ctor match_ letRec be)
        (Expr.rec_strong primLit primBinOp lambda app letIn var ctor match_ letRec body)
  | .var n => var n
  | .ctor nm            => ctor nm
  | .match_ scrutinee branches =>
      match_ scrutinee branches
        (Expr.rec_strong primLit primBinOp lambda app letIn var ctor match_ letRec scrutinee)
        (fun _pat e _hb =>
          Expr.rec_strong primLit primBinOp lambda app letIn var ctor match_ letRec e)
  | .letRec anns bindings body =>
      letRec anns bindings body
        (fun e _hb =>
          Expr.rec_strong primLit primBinOp lambda app letIn var ctor match_ letRec e)
        (Expr.rec_strong primLit primBinOp lambda app letIn var ctor match_ letRec body)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := List.sizeOf_lt_of_mem _hb
       simp only [Prod.mk.sizeOf_spec] at h
       omega)




mutual

/-- Replace all `.bvar`s with some other `Ty` -/
def Ty.instantiate (subst : Nat → Ty) : Ty → Ty
  | .prim p => .prim p
  | .arrow a b => .arrow (a.instantiate subst) (b.instantiate subst)
  | .bvar n => subst n
  | .fvar n => .fvar n
  | .customTy name tys => .customTy name (TyList.instantiate subst tys)
  | .bl lo hi e => .bl lo hi (e.instantiate subst)

def TyList.instantiate (subst : Nat → Ty) : List Ty → List Ty
  | [] => []
  | head :: tail => head.instantiate subst :: TyList.instantiate subst tail

end





/-- Resulting type is the input type with the `.bvar i`s swapped out for the `i`th item in `tyArgs`.

Cannot be produced for a `bvar` whose index is out of range of `tyArgs`. Thus if tyArgs doesn't contain any `bvar`s, neither does the output.

This Ty-level relation is the recursive ENGINE (it must recurse into arbitrary
subterms, and the match rule uses it on `ctor.contents` — naked field types, not
schemes). Scheme-instantiation sites use the `PolyTy.InstantiatesTo` wrapper
below, which is the semantically honest PolyTy → Ty face of instantiation. -/
inductive InstantiatesBy (tyArgs : List Ty) : Ty → Ty → Prop
  | prim :
    InstantiatesBy tyArgs (.prim p) (.prim p)

  | arrow :
    InstantiatesBy tyArgs fst instFst →
    InstantiatesBy tyArgs snd instSnd →
    InstantiatesBy tyArgs (.arrow fst snd) (.arrow instFst instSnd)

  | fvar :
    InstantiatesBy tyArgs (.fvar n) (.fvar n)

  | customTy :
    List.Forall₂ (InstantiatesBy tyArgs) tys instTys →
    InstantiatesBy tyArgs (.customTy name tys) (.customTy name instTys)

  | bl :
    InstantiatesBy tyArgs elem instElem →
    InstantiatesBy tyArgs (.bl lo hi elem) (.bl lo hi instElem)

  | bvar :
    tyArgs[i]? = some ty →
    InstantiatesBy tyArgs (.bvar i) ty

/-- `σ` instantiates to `τ` at the type arguments `tyArgs`: `τ` is `σ`'s body
    with `σ`'s bound variables replaced by the corresponding `tyArgs`. THE
    scheme-instantiation judgment (used by the `var`/`ctor` typing rules).

    Deliberately says nothing about `tyArgs.length` vs `σ.paramCount`: the
    decoration-blind `TypeOfHM.var` (textbook HM) instantiates by *any* witness
    list, while the type-passing `TypeOfElabHM.var` pins the arity with a
    separate `Ty.AreLC` premise. Scheme well-formedness (`PolyTy.WF`) is likewise
    a separate concern. -/
def PolyTy.InstantiatesTo (σ : PolyTy) (tyArgs : List Ty) (τ : Ty) : Prop :=
  InstantiatesBy tyArgs σ.body τ








/-! ## Small-step operational semantics

Call-by-value reduction on closed terms. Uses de Bruijn *indices* for term-level
variables: `var 0` is the innermost binder. Substitution is the standard
"substitute-and-eliminate" variant that shifts other vars to account for the
disappearing binder.

The machine here is independent of type checking — it would run on any
syntactically well-formed `Expr`. Type soundness (progress + preservation) is
the bridge between this and `TypeOfElabHM`. -/

mutual

/--
Shift all `.var i` `i ≥ threshold` up by `n`. Traverses into binders with
`threshold` incremented by the number of new bindings introduced.

Used by `substN`: when a value is inserted at substitution depth `k`, it has
to pass under `k` new binders, which shifts its free vars up by `k`.
-/
def Expr.shiftFrom (threshold : Nat) (n : Nat) : Expr → Expr
  | .var i => if i < threshold then .var i else .var (i + n)
  | .primLit p         => .primLit p
  | .primBinOp op      => .primBinOp op
  | .lambda ann body   => .lambda ann (body.shiftFrom (threshold + 1) n)
  | .app f arg         => .app (f.shiftFrom threshold n) (arg.shiftFrom threshold n)
  | .letIn ann rhs body =>
      .letIn ann (rhs.shiftFrom threshold n) (body.shiftFrom (threshold + 1) n)
  | .ctor c            => .ctor c
  | .match_ scrut branches =>
      .match_ (scrut.shiftFrom threshold n)
        (BranchList.shiftFrom threshold n branches)
  | .letRec anns bindings body =>
      -- anns are types, untouched by term-var shifting; the `bindings.length`
      -- group binders are in scope in every RHS and the body
      .letRec anns (RecGroup.shiftFrom (threshold + bindings.length) n bindings)
        (body.shiftFrom (threshold + bindings.length) n)

private def BranchList.shiftFrom (threshold : Nat) (n : Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, body.shiftFrom (threshold + pat.bindCount) n)
        :: BranchList.shiftFrom threshold n rest

/-- Shift every binding of a `letRec` group at a single (already group-adjusted)
    threshold. -/
def RecGroup.shiftFrom (threshold : Nat) (n : Nat) : List Expr → List Expr
  | []        => []
  | e :: rest => e.shiftFrom threshold n :: RecGroup.shiftFrom threshold n rest

end

/-! ### Type-beta (type-passing): instantiate a scheme's variables through a
    term's annotations.

`Ty.openTyFrom d Ts ty` substitutes the *outermost* (depth-`d`) scheme's type
variables: `bvar (d+i) ↦ Ts[i]`, leaving `bvar < d` (bound by inner schemes) and
out-of-range `bvar`s untouched. `Expr.instTyAux d Ts` pushes this through every
annotation in a term, with `d`-bookkeeping identical to `Expr.openTyVarsAux` (a
TERM binder leaves `d` unchanged; an annotated `let`'s bound expression sits under
`σ.paramCount` extra type binders, so `d` grows there). With `Ts = Xs.map Ty.fvar`
this coincides with `openTyVarsAux d Xs` (see `instTyAux_fvar_eq_openTyVarsAux`),
which ties type-beta to the static scoped-variable opening. `instTy Ts e` is
type-beta at the outermost scheme (depth 0). -/
/-- Shift every `bvar` of a type up by `d`. `Ty` has no internal binders (the `∀`
    lives at `PolyTy`), so an unconditional shift is correct and capture-free. -/
def Ty.shiftBvarsBy (d : Nat) (ty : Ty) : Ty :=
  ty.instantiate (fun n => .bvar (n + d))

@[simp] theorem Ty.shiftBvarsBy_fvar (d n : Nat) : Ty.shiftBvarsBy d (.fvar n) = .fvar n := rfl

@[simp] theorem Ty.shiftBvarsBy_zero (ty : Ty) : Ty.shiftBvarsBy 0 ty = ty := by
  unfold Ty.shiftBvarsBy
  have : (fun n => Ty.bvar (n + 0)) = (fun n => Ty.bvar n) := by funext n; rw [Nat.add_zero]
  rw [this]
  induction ty using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar n => rfl
  | arrow a b iha ihb => simp only [Ty.instantiate, Ty.arrow.injEq]; exact ⟨iha, ihb⟩
  | customTy nm tys ih =>
    simp only [Ty.instantiate, Ty.customTy.injEq, true_and]
    induction tys with
    | nil => rfl
    | cons hd tl ih_tl =>
      simp only [TyList.instantiate, List.cons.injEq]
      exact ⟨ih hd List.mem_cons_self, ih_tl (fun t ht => ih t (List.mem_cons_of_mem _ ht))⟩
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Ty.bl.injEq, true_and]; exact ih

def Ty.openTyFrom (d : Nat) (Ts : List Ty) (ty : Ty) : Ty :=
  ty.instantiate (fun i =>
    if i < d then .bvar i else ((Ts[i - d]?).map (Ty.shiftBvarsBy d)).getD (.bvar i))

@[simp] theorem Ty.openTyFrom_arrow {d : Nat} {Ts : List Ty} {a b : Ty} :
    Ty.openTyFrom d Ts (.arrow a b)
      = .arrow (Ty.openTyFrom d Ts a) (Ty.openTyFrom d Ts b) := rfl

@[simp] theorem Ty.openTyFrom_customTy {d : Nat} {Ts : List Ty} {nm : TyName} {tys : List Ty} :
    Ty.openTyFrom d Ts (.customTy nm tys)
      = .customTy nm (tys.map (Ty.openTyFrom d Ts)) := by
  unfold Ty.openTyFrom
  simp only [Ty.instantiate, Ty.customTy.injEq, true_and]
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp only [TyList.instantiate, List.map_cons]; rw [ih]

@[simp] theorem Ty.openTyFrom_bl {d : Nat} {Ts : List Ty} {lo hi : FHM.Bounds.CountSlot} {e : Ty} :
    Ty.openTyFrom d Ts (.bl lo hi e) = .bl lo hi (Ty.openTyFrom d Ts e) := rfl

/-- The type-binder count a recursion-group annotation contributes: an annotated
    member's binding (and scheme body) sits under its scheme's `paramCount` extra
    type binders; an unannotated member's under none. -/
def RecAnn.params : Option PolyTy → Nat
  | none   => 0
  | some σ => σ.paramCount

/-- Type-beta through a recursion group's SCHEME-ANNOTATION BODIES: each present
    `σⱼ.body` is descended at `d + σⱼ.paramCount` (shielding `σⱼ`'s own quantified
    variables), mirroring the `σ.body` descent in the `letIn (some σ)` case and
    `RecGroup.openAnns`. A no-op on self-contained schemes and on `none` entries. -/
def RecGroup.instAnns (d : Nat) (Ts : List Ty) (anns : List (Option PolyTy)) :
    List (Option PolyTy) :=
  anns.map (Option.map (fun σ => { σ with body := Ty.openTyFrom (d + σ.paramCount) Ts σ.body }))

mutual
/-- Type-beta through a term's annotations at the depth-`d` scheme. Mirrors
    `Expr.openTyVarsAux`'s structure (so it coincides with it on `fvar`
    arguments), but substitutes arbitrary `Ts` via `Ty.openTyFrom`. -/
def Expr.instTyAux (d : Nat) (Ts : List Ty) : Expr → Expr
  | .primLit p          => .primLit p
  | .primBinOp op       => .primBinOp op
  | .lambda ann body    => .lambda (ann.map (Ty.openTyFrom d Ts)) (body.instTyAux d Ts)
  | .app f arg          => .app (f.instTyAux d Ts) (arg.instTyAux d Ts)
  | .letIn (some σ) rhs body =>
      -- `σ` introduces `σ.paramCount` inner type binders over `σ.body` and `rhs`,
      -- but **not** over the continuation `body` (mirrors `openTyVarsAux`).
      .letIn (some { σ with body := Ty.openTyFrom (d + σ.paramCount) Ts σ.body })
        (rhs.instTyAux (d + σ.paramCount) Ts)
        (body.instTyAux d Ts)
  | .letIn none rhs body =>
      .letIn none (rhs.instTyAux d Ts) (body.instTyAux d Ts)
  | .var i => .var i
  | .ctor c             => .ctor c
  | .match_ scrut branches =>
      .match_ (scrut.instTyAux d Ts) (BranchList.instTyAux d Ts branches)
  | .letRec anns bindings body =>
      -- Each PRESENT annotation `σⱼ` introduces `σⱼ.paramCount` inner type binders
      -- over BOTH its own `σⱼ.body` and binding `j`, so both are SHIELDED at
      -- `d + σⱼ.paramCount` (exactly mirroring the `letIn (some σ)` case);
      -- unannotated members introduce no binders (depth stays `d`); the **body**
      -- recurses at `d`. This keeps a re-wrapped recursion group's annotated
      -- members polymorphic across `instTy` (subject reduction for mutual
      -- own-variable polymorphic recursion) while letting a scheme body
      -- reference an enclosing scope's type variable.
      .letRec (RecGroup.instAnns d Ts anns)
        (RecGroup.instTyAux d Ts anns bindings) (body.instTyAux d Ts)

private def BranchList.instTyAux (d : Nat) (Ts : List Ty) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest => (pat, body.instTyAux d Ts) :: BranchList.instTyAux d Ts rest

/-- Type-beta through a recursion group's bindings: each binding is descended at
    `d + RecAnn.params aⱼ` (shielding its own scheme's variables when annotated),
    the anns consumed in lockstep. When the anns are exhausted the depth stays
    `d` (a totality default; well-typed groups have matching lengths). -/
private def RecGroup.instTyAux (d : Nat) (Ts : List Ty) :
    List (Option PolyTy) → List Expr → List Expr
  | _,       []        => []
  | [],      e :: rest => e.instTyAux d Ts :: RecGroup.instTyAux d Ts [] rest
  | a :: as, e :: rest =>
      e.instTyAux (d + RecAnn.params a) Ts :: RecGroup.instTyAux d Ts as rest
end

/-- Type-beta at the outermost scheme (depth 0). -/
def Expr.instTy (Ts : List Ty) (e : Expr) : Expr := e.instTyAux 0 Ts

private theorem BranchList.instTyAux_eq_map (d : Nat) (Ts : List Ty)
    (brs : List (MatchPattern × Expr)) :
    BranchList.instTyAux d Ts brs = brs.map (fun pb => (pb.1, pb.2.instTyAux d Ts)) := by
  induction brs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨p, b⟩ := hd; simp only [BranchList.instTyAux, List.map_cons, ih]

/-- The per-binding type-depth offsets of a recursion group: binding `j` is
    descended at `d + RecAnn.params aⱼ` (or `d` once the anns are exhausted — a
    totality default, never hit for well-typed groups). The list has length
    `bs.length`, so zipping `bs` against it loses no binding. Both
    `RecGroup.instTyAux`/`openTyVarsAux` and `TyBvarBounded.RecGroup` are
    characterised by this list (see the `_eq_zip` / `_iff` lemmas). -/
def RecGroup.shieldDepths (d : Nat) : List (Option PolyTy) → List Expr → List Nat
  | _,       []        => []
  | [],      _ :: rest => d :: RecGroup.shieldDepths d [] rest
  | a :: as, _ :: rest => (d + RecAnn.params a) :: RecGroup.shieldDepths d as rest

theorem RecGroup.shieldDepths_length (d : Nat) (anns : List (Option PolyTy)) (bs : List Expr) :
    (RecGroup.shieldDepths d anns bs).length = bs.length := by
  induction bs generalizing anns with
  | nil => cases anns <;> rfl
  | cons hd tl ih =>
    cases anns with
    | nil => simp only [RecGroup.shieldDepths, List.length_cons, ih]
    | cons a as => simp only [RecGroup.shieldDepths, List.length_cons, ih]

/-- `shieldDepths` only inspects the *length* of the bindings, so it is unchanged
    by any structural map over the bindings. -/
theorem RecGroup.shieldDepths_map (d : Nat) (anns : List (Option PolyTy)) (f : Expr → Expr)
    (bs : List Expr) :
    RecGroup.shieldDepths d anns (bs.map f) = RecGroup.shieldDepths d anns bs := by
  induction bs generalizing anns with
  | nil => cases anns <;> rfl
  | cons hd tl ih =>
    cases anns with
    | nil => simp only [List.map_cons, RecGroup.shieldDepths, ih]
    | cons a as => simp only [List.map_cons, RecGroup.shieldDepths, ih]

/-- Projecting the bindings back out of `bs.zip (shieldDepths …)` recovers `bs`
    (the depth list is exactly as long as `bs`). -/
theorem RecGroup.zip_shieldDepths_map_fst (d : Nat) (anns : List (Option PolyTy))
    (bs : List Expr) :
    (bs.zip (RecGroup.shieldDepths d anns bs)).map Prod.fst = bs := by
  induction bs generalizing anns with
  | nil => rfl
  | cons hd tl ih =>
    cases anns with
    | nil => simp only [RecGroup.shieldDepths, List.zip_cons_cons, List.map_cons, ih]
    | cons a as => simp only [RecGroup.shieldDepths, List.zip_cons_cons, List.map_cons, ih]

private theorem RecGroup.instTyAux_eq_zip (d : Nat) (Ts : List Ty)
    (anns : List (Option PolyTy)) (bs : List Expr) :
    RecGroup.instTyAux d Ts anns bs
      = (bs.zip (RecGroup.shieldDepths d anns bs)).map (fun p => p.1.instTyAux p.2 Ts) := by
  induction bs generalizing anns with
  | nil => cases anns <;> rfl
  | cons hd tl ih =>
    cases anns with
    | nil =>
      simp only [RecGroup.instTyAux, RecGroup.shieldDepths, List.zip_cons_cons,
        List.map_cons, ih]
    | cons a as =>
      simp only [RecGroup.instTyAux, RecGroup.shieldDepths, List.zip_cons_cons,
        List.map_cons, ih]

/-- Type-beta with the empty argument list is the identity (no scheme variable to
    substitute). -/
theorem Ty.openTyFrom_nil (d : Nat) (ty : Ty) : Ty.openTyFrom d [] ty = ty := by
  unfold Ty.openTyFrom
  have hsub : (fun i => if i < d then Ty.bvar i
      else (([] : List Ty)[i - d]?.map (Ty.shiftBvarsBy d)).getD (Ty.bvar i))
      = (fun i => Ty.bvar i) := by funext i; simp
  rw [hsub]
  induction ty using Ty.rec_strong with
  | prim p => rfl
  | bvar i => rfl
  | fvar n => rfl
  | arrow a b iha ihb => simp only [Ty.instantiate, Ty.arrow.injEq]; exact ⟨iha, ihb⟩
  | customTy nm tys ih =>
    simp only [Ty.instantiate, Ty.customTy.injEq, true_and]
    induction tys with
    | nil => rfl
    | cons hd tl ih_tl =>
      simp only [TyList.instantiate, List.cons.injEq]
      exact ⟨ih hd List.mem_cons_self, ih_tl (fun t ht => ih t (List.mem_cons_of_mem _ ht))⟩
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Ty.bl.injEq, true_and]; exact ih

/-- Type-beta with empty arguments is the identity on group annotations. -/
theorem RecGroup.instAnns_nil (d : Nat) (anns : List (Option PolyTy)) :
    RecGroup.instAnns d [] anns = anns := by
  simp only [RecGroup.instAnns, Ty.openTyFrom_nil]
  conv_rhs => rw [← List.map_id anns]
  exact List.map_congr_left (fun a _ => by cases a <;> rfl)

theorem Expr.instTyAux_nil : ∀ (e : Expr) (d : Nat), e.instTyAux d [] = e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d; rfl
  | primBinOp op => intro d; rfl
  | ctor nm => intro d; rfl
  | var n => intro d; rfl
  | app f arg ihf iharg => intro d; simp only [Expr.instTyAux, ihf, iharg]
  | lambda ann body ih =>
    intro d; simp only [Expr.instTyAux, ih]
    cases ann with
    | none => rfl
    | some t => simp only [Option.map_some, Ty.openTyFrom_nil]
  | letIn ann rhs body ihr ihb =>
    intro d
    cases ann with
    | none => simp only [Expr.instTyAux, ihr, ihb]
    | some σ =>
      simp only [Expr.instTyAux, ihr, ihb, Ty.openTyFrom_nil]
  | match_ scrut branches ihs ihbs =>
    intro d
    simp only [Expr.instTyAux, BranchList.instTyAux_eq_map, Expr.match_.injEq]
    refine ⟨ihs d, ?_⟩
    conv_rhs => rw [← List.map_id branches]
    apply List.map_congr_left
    rintro ⟨p, b⟩ hpb
    simp only [ihbs p b hpb d, id_eq]
  | letRec anns bindings body ihbs ihb =>
    intro d
    simp only [Expr.instTyAux, Expr.letRec.injEq]
    refine ⟨RecGroup.instAnns_nil d anns, ?_, ihb d⟩
    rw [RecGroup.instTyAux_eq_zip]
    rw [List.map_congr_left (g := Prod.fst)
        (fun p hp => ihbs p.1 (List.of_mem_zip hp).1 p.2)]
    exact RecGroup.zip_shieldDepths_map_fst d anns bindings

theorem Expr.instTy_nil (e : Expr) : e.instTy [] = e := Expr.instTyAux_nil e 0

mutual

/--
Capture-avoiding multi-substitution under de Bruijn *indices* (innermost = 0).

Replaces `.var (k + j)` `(vs[j]).shiftFrom 0 k` for `j ∈ [0, vs.length)`,
and shifts higher indices down by `vs.length`. The `shiftFrom 0 k` accounts
for the `k` binders the substitution has traversed into.

When traversing into a binder, `k` is incremented by the number of binders
introduced (1 for `lambda`/`letIn`, `pat.contents` for each match branch body).

Used to implement beta, let-reduction, and match-reduction in one uniform
operation.

Replaces `.var`s that are `≥ k` with their corresponding item in `vs`. If the var index is higher than `k+vs.length`, just shift it down by `vs.length`.

In other words, this replaces a bunch of specific vars with their values and leaves other one untouched.
-/
def Expr.substN (k : Nat) (vs : List Expr) : Expr → Expr
  | .var i =>
      if i < k then .var i
      else if h : i - k < vs.length then (vs[i - k]).shiftFrom 0 k
      else .var (i - vs.length)
  | .primLit p         => .primLit p
  | .primBinOp op      => .primBinOp op
  | .lambda ann body   => .lambda ann (body.substN (k + 1) vs)
  | .app f arg         => .app (f.substN k vs) (arg.substN k vs)
  | .letIn ann rhs body =>
      .letIn ann (rhs.substN k vs) (body.substN (k + 1) vs)
  | .ctor n            => .ctor n
  | .match_ scrut branches =>
      .match_ (scrut.substN k vs) (BranchList.substN k vs branches)
  | .letRec anns bindings body =>
      -- anns are types, untouched by term-var substitution; the `bindings.length`
      -- group binders are in scope in every RHS and the body
      .letRec anns (RecGroup.substN (k + bindings.length) vs bindings)
        (body.substN (k + bindings.length) vs)

private def BranchList.substN (k : Nat) (vs : List Expr) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, body.substN (k + pat.bindCount) vs)
        :: BranchList.substN k vs rest

def RecGroup.substN (k : Nat) (vs : List Expr) : List Expr → List Expr
  | []        => []
  | e :: rest => e.substN k vs :: RecGroup.substN k vs rest

end

/-- Single-var substitution. Beta-reduces `(λ. body) v` to `body.subst1 0 v`.

In other words, replaces all references to `.var k` value `v`. This could be either during function application or replacing a let binding with its referent value. It also shifts all `.var`s up or down where appropriate so things stay well-indexed. -/
def Expr.subst1 (k : Nat) (v : Expr) : Expr → Expr :=
  Expr.substN k [v]




namespace SmallStep

mutual

/-- A fully-reduced expression: a value of one of the built-in or user-defined types. -/
inductive IsValue : Expr → Prop
  | primLit (p) :
      IsValue (.primLit p)
  | lambda ann body :
      IsValue (.lambda ann body)
  | ctor (name) :
      IsValue (.ctor name)
  | ctorApp {f v} :
      IsCtorChain f → IsValue v →
      IsValue (.app f v)
  /-- A bare primitive operator is a value (a stuck built-in function). -/
  | primBinOp (op) :
      IsValue (.primBinOp op)
  /-- A *partially* applied binary primop (one argument short of saturation) is
      a value — a stuck function awaiting its second operand. A *saturated*
      application `app (app (primBinOp op) v₁) v₂` is deliberately NOT a value
      (it reduces by a δ-rule), so this covers exactly the one-argument case. -/
  | primBinOpPartial {op v} :
      IsValue v →
      IsValue (.app (.primBinOp op) v)

/-- A constructor optionally applied to zero or more *values*. Both `.ctor c`
    (zero args) and `.app (.app (.ctor c) v₁) v₂` (multiple args) qualify. -/
inductive IsCtorChain : Expr → Prop
  | ctor (name) :
      IsCtorChain (.ctor name)
  | app {f v} :
      IsCtorChain f → IsValue v →
      IsCtorChain (.app f v)

end

/-- Decompose a ctor chain into its ctor name and the list of applied args
    in *application order* (first applied arg first). -/
inductive CtorAppliedTo : Expr → CtorName → List Expr → Prop
  | base (name) :
      CtorAppliedTo (.ctor name) name []
  | step {f arg name args} :
      CtorAppliedTo f name args →
      CtorAppliedTo (.app f arg) name (args ++ [arg])




/-- `(pat, body)` is the *first* branch in `branches` whose pattern matches the
    given constructor name and arity. Mirrors `findMatchingBranch`. -/
inductive FirstMatchingBranch (name : CtorName) (arity : Nat) :
    List (MatchPattern × Expr) → MatchPattern → Expr → Prop
  | here :
    pat.matchesCtor name arity = true →
    FirstMatchingBranch name arity ((pat, body) :: rest) pat body
  | there :
    pat'.matchesCtor name arity = false →
    FirstMatchingBranch name arity rest pat body →
    FirstMatchingBranch name arity ((pat', body') :: rest) pat body


/-- Call-by-value small-step reduction. Left-to-right evaluation order. -/
inductive Step : Expr → Expr → Prop

  -- ─── reduction rules ────────────────────────────────────────────────

  /-- Beta. (NB: `body.substN 0 [v]` substitutes the argument `v` into `body`;
      written via `substN` rather than `subst1` because `_.subst1 0 v` misfires
      under dot notation — `subst1`'s first `Expr` parameter is `v`, not the
      target.) -/
  | beta {ann body v} :
      IsValue v →
      Step (.app (.lambda ann body) v) (body.substN 0 [v])

  /-- Let reduction (call-by-name: a `let` binds its rhs without first reducing it).
      This is the genuine type-passing semantics — we never reduce *under* the
      implicit `Λ` of a polymorphic binding, so a scheme's type binders are always
      consumed outside-in and `instTy` only ever instantiates in-range type `bvar`s.
      Sound here because the language is pure (no effects). -/
  | letReduce {ann rhs body} :
      Step (.letIn ann rhs body) (body.substN 0 [rhs])

  /-- Match reduction. The scrutinee must be a fully-evaluated ctor chain
      whose ctor name matches the *first* applicable branch pattern. -/
  | matchReduce {scrut branches name args pat body} :
      IsValue scrut →
      CtorAppliedTo scrut name args →
      FirstMatchingBranch name args.length branches pat body →
      Step (.match_ scrut branches) (body.substN 0 (args.take pat.bindCount))

  /-- Wildcard match reduction. When the scrutinee is a value that is *not* a
      constructor chain (e.g. an `Int` or a function), it can only be matched by
      a wildcard. By typing such a match's first branch is a wildcard, so reduce
      to that branch's body (a wildcard binds nothing). -/
  | matchWildReduce {scrut body rest} :
      IsValue scrut →
      ¬ IsCtorChain scrut →
      Step (.match_ scrut ((.wildcard, body) :: rest)) body

  /-- Recursive-group unfolding. Substitute, for each group variable `j` in `body`,
      the term `letRec anns bindings eⱼ` ("binding `j`, re-wrapped — carrying the
      `anns` — so its own recursive references stay resolved, at the right scheme
      when annotated"). For `n = 1` this is the `fix f → f (fix f)` unfolding.
      `letRec` is never a value and always steps (so progress is trivial); a
      degenerate binding like `letRec [none] [var 0] (var 0)` loops, as it should. -/
  | letRecUnfold {anns bindings body} :
      Step (.letRec anns bindings body)
        (body.substN 0 (bindings.map (fun e => Expr.letRec anns bindings e)))

  /-- δ-reduction for `intAdd`: a saturated application on integer literals
      computes the sum. The operands are already literals because the CBV
      congruence rules reduce them first, and canonical forms guarantees a
      value of type `int` is an `int` literal. -/
  | deltaIntAdd {m n : Int} :
      Step (.app (.app (.primBinOp .intAdd) (.primLit (.int m))) (.primLit (.int n)))
        (.primLit (.int (m + n)))

  /-- δ-reduction for `intSub`. -/
  | deltaIntSub {m n : Int} :
      Step (.app (.app (.primBinOp .intSub) (.primLit (.int m))) (.primLit (.int n)))
        (.primLit (.int (m - n)))

  /-- δ-reduction for `intLt`: emit the prelude `Bool` constructor. The result is
      well-typed because the `primBinOpIntLt` typing premise supplies
      `True`/`False : Bool` (so preservation reads it straight off). -/
  | deltaIntLt {m n : Int} :
      Step (.app (.app (.primBinOp .intLt) (.primLit (.int m))) (.primLit (.int n)))
        (.ctor (if m < n then ⟨"True"⟩ else ⟨"False"⟩))

  /-- δ-reduction for `charLt` (character ordering by codepoint). -/
  | deltaCharLt {a b : Char} :
      Step (.app (.app (.primBinOp .charLt) (.primLit (.char a))) (.primLit (.char b)))
        (.ctor (if a.toNat < b.toNat then ⟨"True"⟩ else ⟨"False"⟩))

  -- ─── congruence rules (enforce left-to-right CBV) ─────────────────

  /-- Reduce the function position of an application. -/
  | appFn {f f' arg} :
      Step f f' →
      Step (.app f arg) (.app f' arg)

  /-- Once the function is a value, reduce the argument. -/
  | appArg {v arg arg'} :
      IsValue v → Step arg arg' →
      Step (.app v arg) (.app v arg')

  /-- Reduce the scrutinee of a match. -/
  | matchScrut {scrut scrut' branches} :
      Step scrut scrut' →
      Step (.match_ scrut branches) (.match_ scrut' branches)



/-! ### Decidable value / ctor-chain checks -/

mutual

def isValue : Expr → Bool
  | .primLit _ => true
  | .lambda _ _ => true
  | .ctor _ => true
  | .primBinOp _ => true
  | .app (.primBinOp _) v => isValue v
  | .app f v => isCtorChain f && isValue v
  | _ => false

def isCtorChain : Expr → Bool
  | .ctor _ => true
  | .app f v => isCtorChain f && isValue v
  | _ => false

end

/-! ### Ctor-chain decomposition -/

def getCtorArgs : Expr → Option (CtorName × List Expr)
  | .ctor name => some (name, [])
  | .app f arg => do
    let (name, args) ← getCtorArgs f
    return (name, args ++ [arg])
  | _ => none

def findMatchingBranch (name : CtorName) (args : List Expr) :
    List (MatchPattern × Expr) → Option Expr
  | [] => none
  | (pat, body) :: rest =>
    if pat.matchesCtor name args.length then
      some (body.substN 0 (args.take pat.bindCount))
    else
      findMatchingBranch name args rest

/-! ### Small-step evaluation function -/

/-- Compute one step of CBV reduction, returning `none` if the expression is
    already a value or is stuck (ill-typed / open term). -/
def step : Expr → Option Expr
  | .app f arg =>
    if isValue f then
      if isValue arg then
        match f with
        | .lambda _ body => some (body.substN 0 [arg])
        | .app (.primBinOp op) v =>
          -- saturated binary primop: δ-reduce when both operands are int literals
          match op, v, arg with
          | .intAdd, .primLit (.int m), .primLit (.int n) => some (.primLit (.int (m + n)))
          | .intSub, .primLit (.int m), .primLit (.int n) => some (.primLit (.int (m - n)))
          | .intLt, .primLit (.int m), .primLit (.int n) =>
              some (.ctor (if m < n then ⟨"True"⟩ else ⟨"False"⟩))
          | .charLt, .primLit (.char a), .primLit (.char b) =>
              some (.ctor (if a.toNat < b.toNat then ⟨"True"⟩ else ⟨"False"⟩))
          | _, _, _ => none
        | _ => none
      else do let arg' ← step arg; return .app f arg'
    else do let f' ← step f; return .app f' arg

  | .letIn _ rhs body =>
    -- call-by-name: bind the rhs without reducing it first
    some (body.substN 0 [rhs])

  | .match_ scrut branches =>
    if isValue scrut then
      match getCtorArgs scrut with
      | some (name, args) => findMatchingBranch name args branches
      | none =>
        match branches with
        | (.wildcard, body) :: _ => some body
        | _ => none
    else do let scrut' ← step scrut; return .match_ scrut' branches

  | .letRec anns bindings body =>
    some (body.substN 0 (bindings.map (fun e => Expr.letRec anns bindings e)))

  | _ => none

/-- Multi-step evaluator with fuel. Returns `some v` when a value is reached,
    `none` if stuck or out of fuel. -/
def evaluate : Nat → Expr → Option Expr
  | 0, e => if isValue e then some e else none
  | n + 1, e =>
    if isValue e then some e
    else match step e with
    | some e' => evaluate n e'
    | none => none

/-! ### Bool ↔ Prop correspondence for IsValue / IsCtorChain -/

private theorem isValue_isCtorChain_correct (e : Expr) :
    (isValue e = true ↔ IsValue e) ∧ (isCtorChain e = true ↔ IsCtorChain e) := by
  induction e using Expr.rec_strong with
  | primLit p => exact ⟨⟨fun _ => .primLit p, fun _ => rfl⟩, ⟨nofun, nofun⟩⟩
  | primBinOp op => exact ⟨⟨fun _ => .primBinOp op, fun _ => rfl⟩, ⟨nofun, nofun⟩⟩
  | lambda ann body _ => exact ⟨⟨fun _ => .lambda ann body, fun _ => rfl⟩, ⟨nofun, nofun⟩⟩
  | ctor name => exact ⟨⟨fun _ => .ctor name, fun _ => rfl⟩, ⟨fun _ => .ctor name, fun _ => rfl⟩⟩
  | app f arg ihf iharg =>
    refine ⟨⟨fun hv => ?_, fun h => ?_⟩, ?_⟩
    · -- isValue (f.app arg) = true → IsValue (f.app arg)
      cases f with
      | primBinOp op => exact .primBinOpPartial (iharg.1.mp (by simpa only [isValue] using hv))
      | lambda a b => simp [isValue, isCtorChain] at hv
      | primLit p => simp [isValue, isCtorChain] at hv
      | var a => simp [isValue, isCtorChain] at hv
      | letIn a b c => simp [isValue, isCtorChain] at hv
      | match_ a b => simp [isValue, isCtorChain] at hv
      | letRec a b c => simp [isValue, isCtorChain] at hv
      | ctor c =>
        have ha : isValue arg = true := by simpa only [isValue, isCtorChain, Bool.true_and] using hv
        exact .ctorApp (.ctor c) (iharg.1.mp ha)
      | app f1 f2 =>
        have hv' : isCtorChain (f1.app f2) = true ∧ isValue arg = true := by
          simpa only [isValue, Bool.and_eq_true] using hv
        exact .ctorApp (ihf.2.mp hv'.1) (iharg.1.mp hv'.2)
    · -- IsValue (f.app arg) → isValue (f.app arg) = true
      cases h with
      | ctorApp hc hvv =>
        have hcf := ihf.2.mpr hc
        have hva := iharg.1.mpr hvv
        cases f <;> simp_all [isValue, isCtorChain]
      | primBinOpPartial hvv => exact iharg.1.mpr hvv
    · -- isCtorChain (f.app arg) = true ↔ IsCtorChain (f.app arg)
      simp only [isCtorChain, Bool.and_eq_true]
      exact ⟨fun ⟨hf, ha⟩ => .app (ihf.2.mp hf) (iharg.1.mp ha),
             fun h => by cases h with | app hc hv => exact ⟨ihf.2.mpr hc, iharg.1.mpr hv⟩⟩
  | var _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | letIn _ _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | match_ _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | letRec _ _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩

theorem isValue_iff_IsValue {e : Expr} : isValue e = true ↔ IsValue e :=
  (isValue_isCtorChain_correct e).1


/-! ### Helper lemmas -/

private theorem CtorAppliedTo_of_getCtorArgs {e name args}
    (h : getCtorArgs e = some (name, args)) :
    CtorAppliedTo e name args := by
  induction e using Expr.rec_strong generalizing name args with
  | ctor n =>
    simp [getCtorArgs] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .base n
  | app f arg ih _ =>
    unfold getCtorArgs at h
    match hf : getCtorArgs f with
    | .none => simp [hf] at h
    | .some ⟨n, as⟩ =>
      simp [hf] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .step (ih hf)
  | _ => simp [getCtorArgs] at h

private theorem getCtorArgs_of_CtorAppliedTo {e name args}
    (h : CtorAppliedTo e name args) : getCtorArgs e = some (name, args) := by
  induction h with
  | base => simp [getCtorArgs]
  | step _ ih => simp [getCtorArgs, ih]

/-- Every constructor chain is a constructor applied to some arguments. Proved by
    structural induction on the expression (`IsCtorChain` is mutual with `IsValue`,
    so we cannot induct on the proof directly). -/
private theorem CtorAppliedTo_of_IsCtorChain :
    ∀ {e : Expr}, IsCtorChain e → ∃ name args, CtorAppliedTo e name args := by
  intro e
  induction e using Expr.rec_strong with
  | ctor nm => intro _; exact ⟨nm, [], .base nm⟩
  | app f v ihf _ =>
    intro h
    cases h with
    | app hf _ =>
      obtain ⟨name, args, hca⟩ := ihf hf
      exact ⟨name, args ++ [v], .step hca⟩
  | primLit p => intro h; cases h
  | primBinOp op => intro h; cases h
  | lambda a b _ => intro h; cases h
  | var n => intro h; cases h
  | letIn a be b _ _ => intro h; cases h
  | match_ s br _ _ => intro h; cases h
  | letRec _ _ _ _ _ => intro h; cases h

/-- A constructor chain always decomposes via `getCtorArgs`; contrapositively, a
    `getCtorArgs = none` term is not a constructor chain. -/
private theorem getCtorArgs_ne_none_of_IsCtorChain {e : Expr}
    (h : IsCtorChain e) : getCtorArgs e ≠ none := by
  obtain ⟨name, args, hca⟩ := CtorAppliedTo_of_IsCtorChain h
  rw [getCtorArgs_of_CtorAppliedTo hca]; exact nofun

private theorem not_IsCtorChain_of_getCtorArgs_none {e : Expr}
    (h : getCtorArgs e = none) : ¬ IsCtorChain e :=
  fun hcc => getCtorArgs_ne_none_of_IsCtorChain hcc h

private theorem findMatchingBranch_to_FirstMatch {name args branches e'}
    (h : findMatchingBranch name args branches = some e') :
    ∃ pat body, FirstMatchingBranch name args.length branches pat body ∧
      e' = body.substN 0 (args.take pat.bindCount) := by
  induction branches with
  | nil => simp [findMatchingBranch] at h
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [findMatchingBranch] at h
    split at h
    · rename_i hm
      simp at h
      exact ⟨pat, body, .here hm, h.symm⟩
    · rename_i hnm
      obtain ⟨p, b, hfirst, heq⟩ := ih h
      exact ⟨p, b, .there ((Bool.not_eq_true _).mp hnm) hfirst, heq⟩

private theorem FirstMatch_to_findMatchingBranch {name : CtorName} {arity : Nat}
    {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : FirstMatchingBranch name arity branches pat body)
    {args : List Expr} (hlen : arity = args.length) :
    findMatchingBranch name args branches = some (body.substN 0 (args.take pat.bindCount)) := by
  induction h with
  | here hm =>
    subst hlen
    simp [findMatchingBranch, hm]
  | there hnot _ ih =>
    subst hlen
    unfold findMatchingBranch
    rw [if_neg ((Bool.not_eq_true _).mpr hnot)]
    exact ih

private theorem isCtorChain_imp_isValue {e : Expr}
    (h : isCtorChain e = true) : isValue e = true := by
  cases e with
  | app f v => cases f <;> simp_all [isValue, isCtorChain]
  | ctor c => rfl
  | primLit p => simp [isCtorChain] at h
  | primBinOp op => simp [isCtorChain] at h
  | lambda a b => simp [isCtorChain] at h
  | var a => simp [isCtorChain] at h
  | letIn a b c => simp [isCtorChain] at h
  | match_ a b => simp [isCtorChain] at h
  | letRec a b c => simp [isCtorChain] at h

private theorem isValue_step_none {e : Expr} (hv : isValue e = true) :
    step e = none := by
  cases e with
  | primLit _ => rfl
  | lambda _ _ => rfl
  | ctor _ => rfl
  | primBinOp _ => rfl
  | var _ => simp [isValue] at hv
  | letIn _ _ _ => simp [isValue] at hv
  | match_ _ _ => simp [isValue] at hv
  | letRec _ _ _ => simp [isValue] at hv
  | app f arg =>
    cases f with
    | primBinOp op =>
      have ha : isValue arg = true := by simpa only [isValue] using hv
      simp [step, ha]
    | lambda _ _ => simp [isValue, isCtorChain] at hv
    | primLit _ => simp [isValue, isCtorChain] at hv
    | var _ => simp [isValue, isCtorChain] at hv
    | letIn _ _ _ => simp [isValue, isCtorChain] at hv
    | match_ _ _ => simp [isValue, isCtorChain] at hv
    | letRec _ _ _ => simp [isValue, isCtorChain] at hv
    | ctor c =>
      have ha : isValue arg = true := by simpa only [isValue, isCtorChain, Bool.true_and] using hv
      simp [step, ha]
    | app f1 f2 =>
      have hv' : isCtorChain (f1.app f2) = true ∧ isValue arg = true := by
        simpa only [isValue, Bool.and_eq_true] using hv
      have hvf : isValue (f1.app f2) = true := isCtorChain_imp_isValue hv'.1
      cases f1 with
      | primBinOp op => simp [isCtorChain] at hv'
      | ctor c => simp [step, hvf, hv'.2]
      | app g1 g2 => simp [step, hvf, hv'.2]
      | lambda _ _ => simp [isCtorChain] at hv'
      | primLit _ => simp [isCtorChain] at hv'
      | var _ => simp [isCtorChain] at hv'
      | letIn _ _ _ => simp [isCtorChain] at hv'
      | match_ _ _ => simp [isCtorChain] at hv'
      | letRec _ _ _ => simp [isCtorChain] at hv'

private theorem step_some_not_isValue {e e' : Expr}
    (h : step e = some e') : isValue e = false := by
  cases hv : isValue e with
  | false => rfl
  | true => exact absurd h (by rw [isValue_step_none hv]; nofun)

/-! ### Soundness of `step` w.r.t. the `Step` relation -/

theorem step_sound {e e' : Expr} (h : step e = some e') : Step e e' := by
  induction e using Expr.rec_strong generalizing e' with
  | primLit _ | primBinOp _ | lambda _ _ _ | ctor _ | var _ => simp [step] at h
  | app f arg ihf iharg =>
    unfold step at h
    split at h
    · rename_i hvf
      split at h
      · rename_i hvarg
        split at h
        · simp at h; subst h
          exact .beta (isValue_iff_IsValue.mp hvarg)
        · split at h
          · simp at h; subst h; exact .deltaIntAdd
          · simp at h; subst h; exact .deltaIntSub
          · simp at h; subst h; exact .deltaIntLt
          · simp at h; subst h; exact .deltaCharLt
          · exact nomatch h
        · exact nomatch h
      · match harg : step arg with
        | .none => simp [harg] at h
        | .some arg' =>
          simp [harg] at h; subst h; exact .appArg (isValue_iff_IsValue.mp hvf) (iharg harg)
    · match hf : step f with
      | .none => simp [hf] at h
      | .some f' => simp [hf] at h; subst h; exact .appFn (ihf hf)
  | letIn ann rhs body _ _ =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact .letReduce
  | match_ scrut branches ihscrut _ =>
    unfold step at h
    split at h
    · rename_i hvscrut
      revert h
      cases hga : getCtorArgs scrut with
      | none =>
        intro h
        match branches, h with
        | (.wildcard, body) :: rest, h =>
          obtain rfl := Option.some.inj h
          exact .matchWildReduce (isValue_iff_IsValue.mp hvscrut)
            (not_IsCtorChain_of_getCtorArgs_none hga)
        | [], h => exact nomatch h
        | (.named c n, body) :: rest, h => exact nomatch h
      | some p =>
        obtain ⟨name, args⟩ := p
        intro h
        obtain ⟨pat, body, hfirst, rfl⟩ := findMatchingBranch_to_FirstMatch h
        exact .matchReduce (isValue_iff_IsValue.mp hvscrut)
          (CtorAppliedTo_of_getCtorArgs hga) hfirst
    · match hscrut : step scrut with
      | .none => simp [hscrut] at h
      | .some scrut' =>
        simp [hscrut] at h; subst h; exact .matchScrut (ihscrut hscrut)
  | letRec anns bindings body _ _ =>
    simp only [step, Option.some.injEq] at h
    subst h
    exact .letRecUnfold

/-! ### Completeness of `step` w.r.t. the `Step` relation -/

theorem step_complete {e e' : Expr} (h : Step e e') : step e = some e' := by
  induction h with
  | beta hval =>
    have := isValue_iff_IsValue.mpr hval
    unfold step; simp [isValue, this]
  | letReduce =>
    unfold step; rfl
  | matchReduce hval hctor hfirst =>
    have := isValue_iff_IsValue.mpr hval
    have := getCtorArgs_of_CtorAppliedTo hctor
    have := FirstMatch_to_findMatchingBranch hfirst rfl
    unfold step; simp [*]
  | matchWildReduce hval hnc =>
    rename_i scrut body rest
    have hv := isValue_iff_IsValue.mpr hval
    have hga : getCtorArgs scrut = none := by
      cases hval with
      | primLit _ => rfl
      | lambda _ _ => rfl
      | primBinOp op => rfl
      | primBinOpPartial hvv => rfl
      | ctor name => exact absurd (.ctor name) hnc
      | ctorApp hch hvv => exact absurd (.app hch hvv) hnc
    unfold step; simp [hv, hga]
  | appFn _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | appArg hval _ ih =>
    have hvf := isValue_iff_IsValue.mpr hval
    have hva := step_some_not_isValue ih
    unfold step; simp [hvf, hva, ih]
  | matchScrut _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | letRecUnfold => rfl
  | deltaIntAdd => unfold step; simp [isValue]
  | deltaIntSub => unfold step; simp [isValue]
  | deltaIntLt => unfold step; simp [isValue]
  | deltaCharLt => unfold step; simp [isValue]

theorem step_deterministic {e e₁ e₂ : Expr}
    (h₁ : Step e e₁) (h₂ : Step e e₂) : e₁ = e₂ := by
  have := step_complete h₁
  have := step_complete h₂
  simp_all




end SmallStep




/-! ## Well-scopedness

`WellScopedUnder n e` means every `.var i` `e` satisfies `i < n`. Under de
Bruijn indices with the cons-on-binder convention, the typing relation maintains
the invariant that any well-typed expression is well-scoped under
`ctx.env.length`.

Lambda/let/match introduce 1, 1, or `pat.contents` new levels respectively,
raising the scope bound inside their body. -/

mutual

inductive Expr.WellScopedUnder : Nat → Expr → Prop
  | primLit {n p}            : Expr.WellScopedUnder n (.primLit p)
  | ctor    {n c}            : Expr.WellScopedUnder n (.ctor c)
  | var     {n i}     : i < n → Expr.WellScopedUnder n (.var i)
  | lambda  {n ann body}       :
      Expr.WellScopedUnder (n + 1) body →
      Expr.WellScopedUnder n (.lambda ann body)
  | app     {n f arg}        :
      Expr.WellScopedUnder n f → Expr.WellScopedUnder n arg →
      Expr.WellScopedUnder n (.app f arg)
  | letIn   {n ann rhs body}   :
      Expr.WellScopedUnder n rhs →
      Expr.WellScopedUnder (n + 1) body →
      Expr.WellScopedUnder n (.letIn ann rhs body)
  | match_  {n scrut branches} :
      Expr.WellScopedUnder n scrut →
      Expr.BranchListWellScoped n branches →
      Expr.WellScopedUnder n (.match_ scrut branches)
  | letRec  {n anns bindings body} :
      (∀ e ∈ bindings, Expr.WellScopedUnder (n + bindings.length) e) →
      Expr.WellScopedUnder (n + bindings.length) body →
      Expr.WellScopedUnder n (.letRec anns bindings body)

inductive Expr.BranchListWellScoped : Nat → List (MatchPattern × Expr) → Prop
  | nil  {n}          : Expr.BranchListWellScoped n []
  | cons {n pat body rest} :
      Expr.WellScopedUnder (n + pat.bindCount) body →
      Expr.BranchListWellScoped n rest →
      Expr.BranchListWellScoped n ((pat, body) :: rest)

end


/-- Instantation doesn't add more bvars than are in `tyArgs` -/
theorem InstantiatesBy.preserves_bvars : (∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg) → InstantiatesBy tyArgs polyTy ty → ContainsBvarsUpTo 0 ty := by
  intro prem hinst
  cases hinst with
  | prim => constructor
  | arrow a b =>
    expose_names
    constructor
    · exact a.preserves_bvars prem
    · exact b.preserves_bvars prem
  | fvar => refine .fvar
  | bvar hin =>
    have : ty ∈ tyArgs := by grind
    exact prem ty this
  | customTy rels =>
    expose_names
    constructor
    intro ty tyin
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp tyin
    have hlen := rels.length_eq
    have := List.Forall₂.get rels (by omega) hi
    exact this.preserves_bvars prem
  | bl h =>
    exact .bl (h.preserves_bvars prem)











/-! ### Env helpers used by `weaken_env` and `subst_lemma`. -/

/-- An element is in an env's freeVars iff some polytype in env mentions it. -/
theorem Env.mem_freeVars_iff {env : Env} {x : Nat} :
    x ∈ env.freeVars ↔ ∃ pt ∈ env, x ∈ pt.body.freeVars := by
  induction env with
  | nil => simp [Env.freeVars]
  | cons hd tl ih =>
    simp only [Env.freeVars, List.mem_dedup, List.mem_append]
    rw [ih]
    constructor
    · rintro (h | ⟨pt, hmem, h⟩)
      · exact ⟨hd, List.mem_cons_self, h⟩
      · exact ⟨pt, List.mem_cons_of_mem _ hmem, h⟩
    · rintro ⟨pt, hmem, h⟩
      cases hmem with
      | head _ => exact .inl h
      | tail _ h' => exact .inr ⟨pt, h', h⟩

/-- Freshness for an env's free vars is preserved when passing to a sub-env (one
    whose polytypes are all present in the larger env). Used to weaken the
    `letRec` generalisation premise when the substitution lemmas *shrink* the
    environment (dropping the substituted scheme block). -/
theorem Env.not_mem_freeVars_of_sub {x : Nat} {env₁ env₂ : Env}
    (hsub : ∀ pt ∈ env₁, pt ∈ env₂) (h : x ∉ env₂.freeVars) : x ∉ env₁.freeVars := by
  intro hc
  obtain ⟨pt, hmem, hx⟩ := Env.mem_freeVars_iff.mp hc
  exact h (Env.mem_freeVars_iff.mpr ⟨pt, hsub pt hmem, hx⟩)


/-! ## Canonical forms

Inversion lemmas that say "if a value has such-and-such a type, it has such-and-
such a syntactic form". Used in progress to conclude that the next step exists
when we see a value in a particular type position.

Note the asymmetry vs. simpler languages: a value of arrow type can be either
a `lambda` *or* a partial ctor application (since constructors are curried). -/

/-- Instantiation preserves the `wrapArrows ... (customTy ...)` shape: if you
    instantiate a type of that shape, you get back a type of the same shape with
    the same `customTy` name and the same number of arrow wrappers. -/
private lemma InstantiatesBy.wrapArrows_customTy_form
    {name : TyName} {args tys : List Ty} {τ : Ty}
    (h : InstantiatesBy env (Ty.wrapArrows (.customTy name args) tys) τ) :
    ∃ instArgs instTys, τ = Ty.wrapArrows (.customTy name instArgs) instTys := by
  induction tys generalizing τ with
  | nil =>
    cases h with
    | customTy _ => exact ⟨_, [], rfl⟩
  | cons _ rest ih =>
    cases h with
    | arrow _ h_rest =>
      expose_names
      obtain ⟨instArgs, instRest, h_eq⟩ := ih h_rest
      refine ⟨instArgs, instFst :: instRest, ?_⟩
      simp [Ty.wrapArrows, h_eq]


/-! ## Progress -/

namespace SmallStep

mutual

/-- Every match expression (transitively) inside `e` is exhaustive: for each
    match node, every constructor of the matched type `tyName` has a
    corresponding branch.  The `tyName` at each match node is existentially
    quantified — when *building* the proof the caller picks the type that the
    match covers (typically from the typing derivation). -/
inductive AllMatchesExhaustive : CtorEnv → Expr → Prop where
  | primLit : AllMatchesExhaustive ctors (.primLit p)
  | primBinOp : AllMatchesExhaustive ctors (.primBinOp op)
  | var : AllMatchesExhaustive ctors (.var n)
  | ctor : AllMatchesExhaustive ctors (.ctor name)
  | lambda :
    AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.lambda ann body)
  | app :
    AllMatchesExhaustive ctors f → AllMatchesExhaustive ctors arg →
    AllMatchesExhaustive ctors (.app f arg)
  | letIn :
    AllMatchesExhaustive ctors rhs → AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.letIn ann rhs body)
  /-- Exhaustiveness for match: every constructor in the ctor env whose type
      matches `tyName` has a corresponding branch. The `tyName` is existentially
      quantified — the caller picks it (typically from the typing derivation) —
      but it is pinned to the branches: every branch's pattern must be a
      constructor of `tyName`, so a bogus ctor-less type cannot be chosen. -/
  | match_ {tyName : TyName} :
    AllMatchesExhaustive ctors scrut →
    AllBranchBodiesExhaustive ctors branches →
    (∀ c n body, (MatchPattern.named c n, body) ∈ branches →
       ∃ ctor, LookupList.get? ctors c = some ctor ∧ ctor.tyName = tyName) →
    (∀ (ctorName : CtorName) (ctor : Ctor),
      LookupList.get? ctors ctorName = some ctor →
      ctor.tyName = tyName →
      ∃ pat body, (pat, body) ∈ branches ∧
        pat.matchesCtor ctorName ctor.contents.length = true) →
    AllMatchesExhaustive ctors (.match_ scrut branches)
  /-- A `letRec` group is exhaustive iff every binding and the body are. -/
  | letRec :
    (∀ e ∈ bindings, AllMatchesExhaustive ctors e) →
    AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.letRec anns bindings body)

/-- All branch bodies are recursively exhaustive. -/
inductive AllBranchBodiesExhaustive : CtorEnv → List (MatchPattern × Expr) → Prop where
  | nil : AllBranchBodiesExhaustive ctors []
  | cons :
    AllMatchesExhaustive ctors body →
    AllBranchBodiesExhaustive ctors rest →
    AllBranchBodiesExhaustive ctors ((pat, body) :: rest)

end


/-- If a matching branch exists in the list, `findMatchingBranch` succeeds. -/
theorem findMatchingBranch_of_exists {name : CtorName} {args : List Expr}
    {branches : List (MatchPattern × Expr)}
    (h : ∃ pat body, (pat, body) ∈ branches ∧
         pat.matchesCtor name args.length = true) :
    ∃ e', findMatchingBranch name args branches = some e' := by
  induction branches with
  | nil => obtain ⟨_, _, hmem, _⟩ := h; exact nomatch hmem
  | cons hd tl ih =>
    obtain ⟨pat, body, hmem, hcov⟩ := h
    unfold findMatchingBranch
    split
    · exact ⟨_, rfl⟩
    · rename_i hnm
      cases hmem with
      | head _ => exact absurd hcov hnm
      | tail _ hmem' => exact ih ⟨pat, body, hmem', hcov⟩


end SmallStep


/-! ## Type inference: locally-nameless + cofinite quantification

### Design source

Faithful port of Chargueraud's mini-ML formalisation
(`charguer/formalmetacoq/ln/ML_{Definitions,Infrastructure,Soundness}.v`), the
canonical application of Aydemir et al.'s "Engineering Formal Metatheory"
(POPL 2008) to Hindley-Milner with let-polymorphism.

### The core idea: cofinite quantification

The let rule must generalise the type variables of the bound expression that
aren't fixed by the environment. The subtle part is formalising "a fresh choice
of those variables" so that it survives induction.

The naive **exists-fresh** phrasing — pick one concrete `ftvs ⊆ FV(τ) \ FV(Γ)`
(what an earlier `Generalise` relation, since removed, did) — fails: a
derivation commits to one choice, and when the environment grows in a recursive
`subst_lemma`/`weaken_env` call those particular vars may now clash, with no way
to renege.

The **cofinite** phrasing flips the quantifier: the rule says the body checks
**for every** opening by names `Xs` avoiding some *finite* set `L`. The
induction hypothesis is then *universal* in the choice of fresh names — when the
environment grows we just re-instantiate it at names fresh for the bigger env.
This is the "rename to dodge clashes" move baked into the rule, rather than
bolted on as a separate equivariance lemma. The payoff: `weaken_env` and
`subst_lemma` need **no** environment-freshness side conditions.

### Variable encodings (three distinct things)

- `Ty.bvar i` — a type variable bound by a scheme; de Bruijn *index* scoped
  within one `PolyTy` (`i < paramCount`).
- `Ty.fvar n` — a free type variable; a locally-nameless *name* (`Nat`).
  Declaratively these are abstract/rigid type variables; they become
  unification variables only in the algorithmic phase.
- `Expr.var i` — a term variable; de Bruijn *index* into the environment.

Because term variables are de Bruijn indices (not locally-nameless names), the
*term*-side cofinite quantifier from Chargueraud vanishes for us; only the
*type*-side cofinite quantification (in `letIn`) remains.

### The pieces

- `Ty.substFvar`/`substFvars`, `Env.substFvar` — type-variable substitution
  (`[Z ↦ U]`), used by `typ_subst_preservation`.
- `Ty.openVars Xs` — open a scheme body's bvars with fresh *names*;
  `Ty.openWith Vs` — open them with arbitrary *types* (instantiation,
  generalising `InstantiatesBy`).
- `Ty.IsLC` (`= ContainsBvarsUpTo 0`) — locally-closed (no bvars).
- `PolyTy.WF M` — well-formed scheme (`M.body`'s bvars are `< M.paramCount`).
- `FreshNames L n Xs` — `n` distinct names avoiding `L`.
- `HasSchemeVars` / `HasScheme` — "types at every fresh opening" / "types at
  every concrete instantiation", bridged by `HasScheme.fromHasSchemeVars`.

No value restriction: the language is pure, so let-generalising arbitrary
expressions is sound (plain Damas-Milner). -/

mutual

/-- `[Z ↦ U] · ty` — replace every `.fvar Z` in `ty` with `U`.

    NOTE the explicit (non-dot) recursive call style: dot notation
    (`a.substFvar Z U`) would pick `U` for the `Ty` slot since it's the first
    `Ty`-typed positional arg, causing both an argument-order bug and a
    termination-check failure. -/
def Ty.substFvar (Z : Nat) (U : Ty) : Ty → Ty
  | .prim p          => .prim p
  | .arrow a b       => .arrow (Ty.substFvar Z U a) (Ty.substFvar Z U b)
  | .bvar n          => .bvar n
  | .fvar n          => if n = Z then U else .fvar n
  | .customTy nm tys => .customTy nm (TyList.substFvar Z U tys)
  | .bl lo hi e      => .bl lo hi (Ty.substFvar Z U e)

private def TyList.substFvar (Z : Nat) (U : Ty) : List Ty → List Ty
  | []        => []
  | hd :: tl  => Ty.substFvar Z U hd :: TyList.substFvar Z U tl

end

/-- Iterated `substFvar`: apply a list of `(Z, U)` substitutions left-to-right. -/
def Ty.substFvars : List (Nat × Ty) → Ty → Ty
  | []              , ty => ty
  | (Z, U) :: rest  , ty => Ty.substFvars rest (Ty.substFvar Z U ty)

/-- Open a scheme body's bvars with named fvars: `.bvar i ↦ .fvar (Xs.get i)`. -/
def Ty.openVars (Xs : List Nat) (ty : Ty) : Ty :=
  ty.instantiate (fun i => (Xs[i]?).elim (.bvar i) .fvar)

/-- Open a scheme body's bvars with arbitrary LC types. -/
def Ty.openWith (Vs : List Ty) (ty : Ty) : Ty :=
  ty.instantiate (fun i => (Vs[i]?).getD (.bvar i))

def PolyTy.substFvar (Z : Nat) (U : Ty) (pt : PolyTy) : PolyTy :=
  -- NOTE: explicit (non-dot) call: `pt.body.substFvar Z U` would misfire because
  -- `Ty.substFvar` has two `Ty` args and dot notation fills the wrong one.
  { paramCount := pt.paramCount, body := Ty.substFvar Z U pt.body }

def PolyTy.openVars (Xs : List Nat) (pt : PolyTy) : Ty := pt.body.openVars Xs

def PolyTy.openWith (Vs : List Ty) (pt : PolyTy) : Ty := pt.body.openWith Vs

def Env.substFvar (Z : Nat) (U : Ty) (env : Env) : Env :=
  env.map (PolyTy.substFvar Z U)

/-! ### Type-variable operations on terms

Pushing type-level substitution / opening through the *type annotations* embedded
in a term (`lambda` param annotations and `letIn` scheme annotations). These are
the term-level analogues of `Ty.substFvar` / `Ty.openVars`, and they exist to
support **scoped type variables**: an annotation inside a `let`-bound expression
may mention the type variables bound by an enclosing `let`'s scheme. -/

mutual
/-- Substitute a free type variable `Z ↦ U` through every annotation in a term.
    Free type variables are global names, so (unlike opening) this needs no
    binder-depth bookkeeping. Used by `typ_subst_preservation`. -/
def Expr.substTyFvar (Z : Nat) (U : Ty) : Expr → Expr
  | .primLit p          => .primLit p
  | .primBinOp op       => .primBinOp op
  | .lambda ann body    => .lambda (ann.map (Ty.substFvar Z U)) (body.substTyFvar Z U)
  | .app f arg          => .app (f.substTyFvar Z U) (arg.substTyFvar Z U)
  | .letIn ann rhs body =>
      .letIn (ann.map (PolyTy.substFvar Z U)) (rhs.substTyFvar Z U) (body.substTyFvar Z U)
  | .var i => .var i
  | .ctor c             => .ctor c
  | .match_ scrut branches =>
      .match_ (scrut.substTyFvar Z U) (BranchList.substTyFvar Z U branches)
  | .letRec anns bindings body =>
      -- anns are kept type annotations: push `[Z ↦ U]` through them too. Free
      -- type variables are global names, so no shield-depth bookkeeping needed.
      .letRec (anns.map (Option.map (PolyTy.substFvar Z U)))
        (RecGroup.substTyFvar Z U bindings) (body.substTyFvar Z U)

private def BranchList.substTyFvar (Z : Nat) (U : Ty) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest => (pat, body.substTyFvar Z U) :: BranchList.substTyFvar Z U rest

private def RecGroup.substTyFvar (Z : Nat) (U : Ty) : List Expr → List Expr
  | []        => []
  | e :: rest => e.substTyFvar Z U :: RecGroup.substTyFvar Z U rest
end

/-- Iterated `Expr.substTyFvar` (left-to-right), mirroring `Ty.substFvars`. -/
def Expr.substTyFvars : List (Nat × Ty) → Expr → Expr
  | []             , e => e
  | (Z, U) :: rest , e => Expr.substTyFvars rest (Expr.substTyFvar Z U e)

/-- Iterated `PolyTy.substFvar` (left-to-right), mirroring `Expr.substTyFvars`.
    Used to push a block of type-fvar substitutions through a kept `letRecAnn`
    scheme. -/
def PolyTy.substFvars : List (Nat × Ty) → PolyTy → PolyTy
  | []             , σ => σ
  | (Z, U) :: rest , σ => PolyTy.substFvars rest (PolyTy.substFvar Z U σ)

/-- Open the `bvar (d + i)` of a type (offset `d`) to `.fvar (Xs[i])`, leaving
    `bvar`s `< d` (those bound by *inner* schemes) untouched. `d = 0` coincides
    with `Ty.openVars`. -/
def Ty.openVarsFrom (d : Nat) (Xs : List Nat) (t : Ty) : Ty :=
  t.instantiate (fun i => if i < d then .bvar i else (Xs[i - d]?).elim (.bvar i) .fvar)

/-- Open scoped type variables through a recursion group's SCHEME-ANNOTATION
    BODIES: each present `σⱼ.body` is descended at `d + σⱼ.paramCount` (shielding
    `σⱼ`'s own quantified variables), so a scheme may reference an enclosing
    scope's type variable. A no-op on self-contained schemes (all `bvar`s
    `< σⱼ.paramCount`) and on `none` entries. Mirrors the `σ.body` descent in the
    `letIn (some σ)` case. -/
def RecGroup.openAnns (d : Nat) (Xs : List Nat) (anns : List (Option PolyTy)) :
    List (Option PolyTy) :=
  anns.map (Option.map (fun σ => { σ with body := Ty.openVarsFrom (d + σ.paramCount) Xs σ.body }))

mutual
/-- Open the scoped type variables of an enclosing scheme inside a term's
    annotations: replace the `bvar`s referencing that scheme by `.fvar (Xs[i])`.
    `d` tracks how many *type*-binder levels (introduced by annotated polymorphic
    `let`s) we've descended through, so only the targeted scheme's vars are
    opened. Term binders (`lambda`, match patterns) and a `let`'s *continuation*
    bind no type variables, so they leave `d` unchanged. -/
def Expr.openTyVarsAux (d : Nat) (Xs : List Nat) : Expr → Expr
  | .primLit p          => .primLit p
  | .primBinOp op       => .primBinOp op
  | .lambda ann body    => .lambda (ann.map (Ty.openVarsFrom d Xs)) (body.openTyVarsAux d Xs)
  | .app f arg          => .app (f.openTyVarsAux d Xs) (arg.openTyVarsAux d Xs)
  | .letIn (some σ) rhs body =>
      -- `σ` introduces `σ.paramCount` inner type binders over `σ.body` and `rhs`
      -- (the signature scopes over the bound expression), but **not** over the
      -- continuation `body`.
      .letIn (some { σ with body := Ty.openVarsFrom (d + σ.paramCount) Xs σ.body })
        (rhs.openTyVarsAux (d + σ.paramCount) Xs)
        (body.openTyVarsAux d Xs)
  | .letIn none rhs body =>
      .letIn none (rhs.openTyVarsAux d Xs) (body.openTyVarsAux d Xs)
  | .var i => .var i
  | .ctor c             => .ctor c
  | .match_ scrut branches =>
      .match_ (scrut.openTyVarsAux d Xs) (BranchList.openTyVarsAux d Xs branches)
  | .letRec anns bindings body =>
      -- Each PRESENT annotation `σⱼ` introduces `σⱼ.paramCount` inner type binders
      -- over BOTH its own `σⱼ.body` and binding `j` (the binding is scheme-relative
      -- to `σⱼ`), but **not** over the continuation `body`. So both the scheme
      -- bodies and the annotated bindings are SHIELDED at `d + σⱼ.paramCount`
      -- (mirroring `letIn (some σ)`), letting a scheme body reference an enclosing
      -- scope's type variable; unannotated bindings and the **body** recurse at `d`.
      .letRec (RecGroup.openAnns d Xs anns)
        (RecGroup.openTyVarsAux d Xs anns bindings)
        (body.openTyVarsAux d Xs)

def BranchList.openTyVarsAux (d : Nat) (Xs : List Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest => (pat, body.openTyVarsAux d Xs) :: BranchList.openTyVarsAux d Xs rest

/-- Open scoped type variables through a recursion group's bindings: each binding
    is descended at `d + RecAnn.params aⱼ` (shielding its own scheme's variables
    when annotated), the anns consumed in lockstep. Mirrors `RecGroup.instTyAux`. -/
def RecGroup.openTyVarsAux (d : Nat) (Xs : List Nat) :
    List (Option PolyTy) → List Expr → List Expr
  | _,       []        => []
  | [],      e :: rest => e.openTyVarsAux d Xs :: RecGroup.openTyVarsAux d Xs [] rest
  | a :: as, e :: rest =>
      e.openTyVarsAux (d + RecAnn.params a) Xs :: RecGroup.openTyVarsAux d Xs as rest
end

/-- The `RecGroup.*` structural helpers for `letRec` bindings are all just
    `List.map` of the corresponding single-`Expr` operation. Stating this lets the
    `letRec` cases of the structural lemmas reuse the generic `List.map` lemmas
    (membership, length, `map_map`) exactly as the `BranchList.*_eq_map` lemmas
    do for `match_`. -/
theorem RecGroup.shiftFrom_eq_map (threshold n : Nat) (bs : List Expr) :
    RecGroup.shiftFrom threshold n bs = bs.map (·.shiftFrom threshold n) := by
  induction bs with
  | nil => rfl
  | cons hd tl ih => simp only [RecGroup.shiftFrom, List.map_cons, ih]

theorem RecGroup.substN_eq_map (k : Nat) (vs : List Expr) (bs : List Expr) :
    RecGroup.substN k vs bs = bs.map (·.substN k vs) := by
  induction bs with
  | nil => rfl
  | cons hd tl ih => simp only [RecGroup.substN, List.map_cons, ih]

private theorem RecGroup.substTyFvar_eq_map (Z : Nat) (U : Ty) (bs : List Expr) :
    RecGroup.substTyFvar Z U bs = bs.map (·.substTyFvar Z U) := by
  induction bs with
  | nil => rfl
  | cons hd tl ih => simp only [RecGroup.substTyFvar, List.map_cons, ih]

private theorem RecGroup.openTyVarsAux_eq_zip (d : Nat) (Xs : List Nat)
    (anns : List (Option PolyTy)) (bs : List Expr) :
    RecGroup.openTyVarsAux d Xs anns bs
      = (bs.zip (RecGroup.shieldDepths d anns bs)).map (fun p => p.1.openTyVarsAux p.2 Xs) := by
  induction bs generalizing anns with
  | nil => cases anns <;> rfl
  | cons hd tl ih =>
    cases anns with
    | nil =>
      simp only [RecGroup.openTyVarsAux, RecGroup.shieldDepths, List.zip_cons_cons,
        List.map_cons, ih]
    | cons a as =>
      simp only [RecGroup.openTyVarsAux, RecGroup.shieldDepths, List.zip_cons_cons,
        List.map_cons, ih]

theorem RecGroup.openTyVarsAux_length (d : Nat) (Xs : List Nat)
    (anns : List (Option PolyTy)) (bs : List Expr) :
    (RecGroup.openTyVarsAux d Xs anns bs).length = bs.length := by
  rw [RecGroup.openTyVarsAux_eq_zip, List.length_map, List.length_zip,
    RecGroup.shieldDepths_length, Nat.min_self]

/-- **Type-beta coincides with scoped-variable opening on `fvar` arguments.**
    `Ty.openTyFrom d (Xs.map Ty.fvar)` substitutes `bvar (d+i) ↦ fvar Xs[i]`,
    which is exactly `Ty.openVarsFrom d Xs`. -/
theorem Ty.openTyFrom_fvar_eq_openVarsFrom (d : Nat) (Xs : List Nat) (ty : Ty) :
    Ty.openTyFrom d (Xs.map Ty.fvar) ty = Ty.openVarsFrom d Xs ty := by
  unfold Ty.openTyFrom Ty.openVarsFrom
  congr 1
  funext i
  by_cases hi : i < d
  · simp only [if_pos hi]
  · simp only [if_neg hi, List.getElem?_map]
    cases Xs[i - d]? with
    | none => rfl
    | some x => simp only [Option.map_some, Ty.shiftBvarsBy_fvar, Option.getD_some, Option.elim]

/-! ### Scheme-body descent helpers for recursion-group annotations.
    `RecGroup.openAnns`/`instAnns` descend into each present `σⱼ.body` at
    `d + σⱼ.paramCount` (letting a scheme reference an enclosing scope's type var);
    these lemmas mirror the corresponding binding-level facts. -/

@[simp] theorem RecGroup.openAnns_length (d : Nat) (Xs : List Nat)
    (anns : List (Option PolyTy)) :
    (RecGroup.openAnns d Xs anns).length = anns.length := by
  simp [RecGroup.openAnns]

@[simp] theorem RecGroup.instAnns_length (d : Nat) (Ts : List Ty)
    (anns : List (Option PolyTy)) :
    (RecGroup.instAnns d Ts anns).length = anns.length := by
  simp [RecGroup.instAnns]

/-- Type-beta at `fvar` arguments coincides with scoped-variable opening on
    annotation bodies (the ann-list analogue of `Ty.openTyFrom_fvar_eq_openVarsFrom`). -/
theorem RecGroup.instAnns_fvar_eq_openAnns (d : Nat) (Xs : List Nat)
    (anns : List (Option PolyTy)) :
    RecGroup.instAnns d (Xs.map Ty.fvar) anns = RecGroup.openAnns d Xs anns := by
  simp only [RecGroup.instAnns, RecGroup.openAnns]
  exact List.map_congr_left (fun a _ => by
    cases a with
    | none => rfl
    | some σ => simp only [Option.map_some, Ty.openTyFrom_fvar_eq_openVarsFrom])

/-- The term-level coincidence: `instTyAux` at `fvar` arguments is exactly the
    scoped-variable opener `openTyVarsAux` (both have identical `d`-bookkeeping). -/
theorem Expr.instTyAux_fvar_eq_openTyVarsAux (Xs : List Nat) :
    ∀ (e : Expr) (d : Nat), e.instTyAux d (Xs.map Ty.fvar) = e.openTyVarsAux d Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d; rfl
  | primBinOp op => intro d; rfl
  | ctor nm => intro d; rfl
  | var n => intro d; rfl
  | app f arg ihf iharg => intro d; simp only [Expr.instTyAux, Expr.openTyVarsAux, ihf, iharg]
  | lambda ann body ih =>
    intro d
    simp only [Expr.instTyAux, Expr.openTyVarsAux, ih]
    cases ann with
    | none => rfl
    | some t => simp only [Option.map_some, Ty.openTyFrom_fvar_eq_openVarsFrom]
  | letIn ann rhs body ihr ihb =>
    intro d
    cases ann with
    | none => simp only [Expr.instTyAux, Expr.openTyVarsAux, ihr, ihb]
    | some σ =>
      simp only [Expr.instTyAux, Expr.openTyVarsAux, ihr, ihb,
        Ty.openTyFrom_fvar_eq_openVarsFrom]
  | match_ scrut branches ihs ihbs =>
    intro d
    simp only [Expr.instTyAux, Expr.openTyVarsAux]
    rw [ihs d]
    congr 1
    revert ihbs
    induction branches with
    | nil => intro _; rfl
    | cons hd tl ihtl =>
      intro ihbs
      obtain ⟨p, b⟩ := hd
      simp only [BranchList.instTyAux, BranchList.openTyVarsAux, List.cons.injEq,
        Prod.mk.injEq, true_and]
      exact ⟨ihbs p b List.mem_cons_self d,
        ihtl (fun p' b' hm => ihbs p' b' (List.mem_cons_of_mem _ hm))⟩
  | letRec anns bindings body ihbs ihb =>
    intro d
    simp only [Expr.instTyAux, Expr.openTyVarsAux, RecGroup.instTyAux_eq_zip,
      RecGroup.openTyVarsAux_eq_zip, Expr.letRec.injEq]
    exact ⟨RecGroup.instAnns_fvar_eq_openAnns d Xs anns,
      List.map_congr_left (fun p hp => ihbs p.1 (List.of_mem_zip hp).1 p.2), ihb d⟩

/-- A member of `(l.map f).zip r` reflects to a member of `l.zip r`: the
    `letRec` typing rule's `bindings.zip τs` premise must be reconstructed after a
    structural transform `f` is mapped over the bindings. -/
theorem List.mem_zip_map_left {α β γ : Type _} {f : α → γ} :
    ∀ {l : List α} {r : List β} {p : γ × β},
      p ∈ (l.map f).zip r → ∃ a b, a ∈ l ∧ (a, b) ∈ l.zip r ∧ p = (f a, b) := by
  intro l
  induction l with
  | nil => intro r p h; simp at h
  | cons hd tl ih =>
    intro r p h
    cases r with
    | nil => simp at h
    | cons rhd rtl =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
      cases h with
      | inl heq => exact ⟨hd, rhd, List.mem_cons_self, List.mem_cons_self, heq⟩
      | inr h' =>
        obtain ⟨a, b, ha, hmem, heq⟩ := ih h'
        exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hmem, heq⟩

/-- A member of `l.zip (r.map g)` reflects to a member of `l.zip r` (the RIGHT
    analogue of `mem_zip_map_left`): the fused `letRec` rule's `bindings.zip specs`
    premise must be reconstructed from a `bindings.zip anns` member, where
    `anns = specs.map RecSpec.ann`. -/
private theorem List.mem_zip_map_right_ex {α β γ : Type _} {g : β → γ} :
    ∀ {l : List α} {r : List β} {p : α × γ},
      p ∈ l.zip (r.map g) → ∃ a b, (a, b) ∈ l.zip r ∧ p = (a, g b) := by
  intro l
  induction l with
  | nil => intro r p h; simp at h
  | cons hd tl ih =>
    intro r p h
    cases r with
    | nil => simp at h
    | cons rhd rtl =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
      cases h with
      | inl heq => exact ⟨hd, rhd, List.mem_cons_self, heq⟩
      | inr h' =>
        obtain ⟨a, b, hmem, heq⟩ := ih h'
        exact ⟨a, b, List.mem_cons_of_mem _ hmem, heq⟩

/-- Open an enclosing scheme's scoped type variables throughout a (bound) term:
    the term-level analogue of `PolyTy.openVars`. -/
def Expr.openTyVars (Xs : List Nat) (e : Expr) : Expr := e.openTyVarsAux 0 Xs

/-- Top-level coincidence (`d = 0`): type-beta at fresh `fvar`s is scoped opening. -/
theorem Expr.instTy_fvar_eq_openTyVars (Xs : List Nat) (e : Expr) :
    e.instTy (Xs.map Ty.fvar) = e.openTyVars Xs :=
  Expr.instTyAux_fvar_eq_openTyVarsAux Xs e 0

/-- The bound-expression form used by the `let` typing rule's cofinite premise:
    open the bound expression's scoped type variables at `Xs` **iff** the `let`
    carries a scheme annotation (the annotation is what binds those variables).
    An unannotated `let` introduces no scoped type variables, so its bound
    expression is typed unchanged. -/
def Expr.openBoundTyVars : Option PolyTy → List Nat → Expr → Expr
  | none,   _,  e => e
  | some _, Xs, e => e.openTyVars Xs

/-! ### Type erasure (`erase`)

The uniform erasure of the erasure-on-`Step` migration
(`briefs/design-memo-erasure-migration.md` §3.1): drop ALL type annotations and
type-passing decorations — `lambda (some t)` → `lambda none`, `letIn (some σ)` →
`letIn none`, `letRec anns` → `letRec (all none)`, `var i _` → `var i []` (the
`tyArgs` are zeroed, not passed through). Structural elsewhere. `erase e` is the
term the machine (`SmallStep.Step`) runs, typed by the declarative `TypeOfHM`; the
soundness of the source checker against it is `Infer.sound`. -/
def Expr.erase : Expr → Expr
  | .primLit p          => .primLit p
  | .primBinOp op       => .primBinOp op
  | .lambda _ body      => .lambda none body.erase
  | .app f arg          => .app f.erase arg.erase
  | .letIn _ rhs body   => .letIn none rhs.erase body.erase
  | .var i => .var i
  | .ctor c             => .ctor c
  | .match_ scrut branches =>
      .match_ scrut.erase (branches.map fun pe => (pe.1, pe.2.erase))
  | .letRec _ bindings body =>
      .letRec (bindings.map (fun _ => none)) (bindings.map Expr.erase) body.erase
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := List.sizeOf_lt_of_mem ‹_›; omega)
    | (have h := List.sizeOf_lt_of_mem ‹_›
       have : sizeOf pe.2 < sizeOf pe := by
         cases pe; simp only [Prod.mk.sizeOf_spec]; omega
       omega)

@[simp] theorem Expr.erase_lambda (ann : Option Ty) (body : Expr) :
    (Expr.lambda ann body).erase = Expr.lambda none body.erase := by
  simp only [Expr.erase]

@[simp] theorem Expr.erase_app (f arg : Expr) :
    (Expr.app f arg).erase = Expr.app f.erase arg.erase := by
  simp only [Expr.erase]

@[simp] theorem Expr.erase_letIn (ann : Option PolyTy) (rhs body : Expr) :
    (Expr.letIn ann rhs body).erase = Expr.letIn none rhs.erase body.erase := by
  simp only [Expr.erase]

@[simp] theorem Expr.erase_var (i : Nat) :
    (Expr.var i).erase = Expr.var i := by
  simp only [Expr.erase]

@[simp] theorem Expr.erase_match (scrut : Expr) (branches : List (MatchPattern × Expr)) :
    (Expr.match_ scrut branches).erase =
      Expr.match_ scrut.erase (branches.map fun pe => (pe.1, pe.2.erase)) := by
  simp only [Expr.erase]

@[simp] theorem Expr.erase_letRec (anns : List (Option PolyTy)) (bindings : List Expr) (body : Expr) :
    (Expr.letRec anns bindings body).erase =
      Expr.letRec (bindings.map (fun _ => none)) (bindings.map Expr.erase) body.erase := by
  simp only [Expr.erase]

/-! Erasure commutes with scoped-type-variable opening (depth-generalised). -/

/-- `List.map (fun _ => none)` agrees on lists of equal length. -/
private theorem List.map_const_none_eq_of_length {α : Type u} {l₁ l₂ : List α}
    (h : l₁.length = l₂.length) :
    l₁.map (fun _ : α => (none : Option PolyTy)) = l₂.map (fun _ : α => (none : Option PolyTy)) := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons _ _ => simp at h
  | cons _ tl ihtl =>
      cases l₂ with
      | nil => simp at h
      | cons _ t2 =>
          simp only [List.map_cons]
          have hlen : tl.length = t2.length := by
            exact Nat.add_one_inj.mp (by simpa using h)
          rw [ihtl (l₂ := t2) hlen]

/-- For a branch list, erasing after `openTyVarsAux` equals erasing directly, given
    the pointwise depth-`d` erasure-opening fact on each branch body. -/
private theorem BranchList.erase_openTyVarsAux (d : Nat) (Xs : List Nat)
    (brs : List (MatchPattern × Expr))
    (h : ∀ pb ∈ brs, (pb.2.openTyVarsAux d Xs).erase = pb.2.erase) :
    (BranchList.openTyVarsAux d Xs brs).map (fun pb => (pb.1, pb.2.erase)) =
      brs.map (fun pb => (pb.1, pb.2.erase)) := by
  induction brs with
  | nil => rfl
  | cons hd tl ihtl =>
      obtain ⟨p, b⟩ := hd
      simp only [BranchList.openTyVarsAux, List.map_cons]
      rw [h (p, b) (List.mem_cons_self ..)]
      congr 1
      exact ihtl (fun pb hpb => h pb (List.mem_cons_of_mem (p, b) hpb))

/-- For a recursion group, erasing after `openTyVarsAux` equals erasing directly,
    given the per-binding depth-generalised erasure-opening fact. -/
private theorem RecGroup.erase_openTyVarsAux (d : Nat) (Xs : List Nat)
    (anns : List (Option PolyTy)) (bindings : List Expr)
    (h : ∀ b ∈ bindings, ∀ d Xs, (b.openTyVarsAux d Xs).erase = b.erase) :
    (RecGroup.openTyVarsAux d Xs anns bindings).map Expr.erase = bindings.map Expr.erase := by
  revert h
  induction bindings generalizing anns with
  | nil => intro _; cases anns <;> rfl
  | cons hd tl ihtl =>
      intro h
      cases anns with
      | nil =>
          simp only [RecGroup.openTyVarsAux, List.map_cons]
          rw [h hd (List.mem_cons_self ..) d Xs,
              ihtl [] (fun b hb => h b (List.mem_cons_of_mem hd hb))]
      | cons a as =>
          simp only [RecGroup.openTyVarsAux, List.map_cons]
          rw [h hd (List.mem_cons_self ..) (d + RecAnn.params a) Xs,
              ihtl as (fun b hb => h b (List.mem_cons_of_mem hd hb))]

/-- `erase` drops every annotation, so opening scoped type variables first has no
    effect on the erasure — at ANY depth `d` (the `letIn (some σ)` / `letRec` cases
    descend bindings at `d + paramCount`, so the depth-0 instance alone is not
    enough). This is the "erasure ∘ opening = erasure" fact the opened-RHS cases of
    `Infer.sound` rely on. -/
theorem Expr.erase_openTyVarsAux (Xs : List Nat) :
    ∀ (e : Expr) (d : Nat), (e.openTyVarsAux d Xs).erase = e.erase := by
  intro e
  induction e using Expr.rec_strong generalizing Xs with
  | primLit p => intro d; simp [Expr.openTyVarsAux, Expr.erase]
  | primBinOp op => intro d; simp [Expr.openTyVarsAux, Expr.erase]
  | ctor nm => intro d; simp [Expr.openTyVarsAux, Expr.erase]
  | var n => intro d; simp [Expr.openTyVarsAux]
  | lambda ann body ih =>
      intro d
      simp [Expr.openTyVarsAux, ih Xs d]
  | app f arg ihf iharg =>
      intro d
      simp [Expr.openTyVarsAux, ihf Xs d, iharg Xs d]
  | letIn ann rhs body ihr ihb =>
      intro d
      cases ann with
      | none => simp [Expr.openTyVarsAux, ihr Xs d, ihb Xs d]
      | some σ => simp [Expr.openTyVarsAux, ihr Xs (d + σ.paramCount), ihb Xs d]
  | match_ scrut branches ihs ihbs =>
      intro d
      simp only [Expr.openTyVarsAux, Expr.erase_match, ihs Xs d]
      congr 1
      exact BranchList.erase_openTyVarsAux d Xs branches (fun pb hpb => ihbs pb.1 pb.2 hpb Xs d)
  | letRec anns bindings body ihbs ihb =>
      intro d
      simp only [Expr.openTyVarsAux, Expr.erase_letRec, ihb Xs d]
      congr 1
      · exact List.map_const_none_eq_of_length (RecGroup.openTyVarsAux_length d Xs anns bindings)
      · exact RecGroup.erase_openTyVarsAux d Xs anns bindings (fun b hb d' Xs' => ihbs b hb Xs' d')

theorem Expr.erase_openTyVars (Xs : List Nat) (e : Expr) :
    (e.openTyVars Xs).erase = e.erase := by
  simpa [Expr.openTyVars] using Expr.erase_openTyVarsAux Xs e 0

/-- Erasure is a no-op on `openBoundTyVars` (the cofinite `letIn` opening): whether
    or not the `let` carries an annotation, erasing the opened bound expression is
    erasing the stored one. -/
theorem Expr.erase_openBoundTyVars (ann : Option PolyTy) (Xs : List Nat) (e : Expr) :
    (Expr.openBoundTyVars ann Xs e).erase = e.erase := by
  cases ann <;> simp [Expr.openBoundTyVars, Expr.erase_openTyVars]

/-! ### Erasure is a no-op under scoped-variable opening (image of `erase`).

The CEK leaf's `Expr.openTyVars_eq_self_of_erased` (`CekMachine.lean`) stated
"opening is a no-op" for the *selective* `IsErased` predicate, which keeps
`letIn`/`letRec` annotations. The `Step` dynamics needs the analogous fact for
the *image* of the uniform `Expr.erase`: an erased term has `none`/all-`none`/
`tyArgs = []` in every annotation slot, so `openTyVarsAux` has nothing to open. -/

/-- For a branch list, opening is a no-op on the erasures of each branch body. -/
private theorem BranchList.openTyVarsAux_eq_self_of_erase_image (d : Nat) (Xs : List Nat)
    (brs : List (MatchPattern × Expr))
    (h : ∀ pb ∈ brs, pb.2.erase.openTyVarsAux d Xs = pb.2.erase) :
    BranchList.openTyVarsAux d Xs (brs.map (fun pb => (pb.1, pb.2.erase))) =
      brs.map (fun pb => (pb.1, pb.2.erase)) := by
  induction brs with
  | nil => rfl
  | cons hd tl ihtl =>
      obtain ⟨p, b⟩ := hd
      simp only [BranchList.openTyVarsAux, List.map_cons]
      rw [h (p, b) (List.mem_cons_self ..),
          ihtl (fun pb hpb => h pb (List.mem_cons_of_mem (p, b) hpb))]

/-- For a recursion group whose bindings are already erased, opening is a no-op on
    `bindings.map Expr.erase` (the all-`none` annotations descend each binding at
    `d + RecAnn.params none`, which the depth-general hypothesis covers). -/
private theorem RecGroup.openTyVarsAux_eq_self_of_erase_image (d : Nat) (Xs : List Nat)
    (bindings : List Expr)
    (h : ∀ b ∈ bindings, ∀ d Xs, b.erase.openTyVarsAux d Xs = b.erase) :
    RecGroup.openTyVarsAux d Xs (bindings.map (fun _ => none)) (bindings.map Expr.erase) =
      bindings.map Expr.erase := by
  induction bindings with
  | nil => rfl
  | cons hd tl ihtl =>
      simp only [RecGroup.openTyVarsAux, List.map_cons]
      rw [h hd (List.mem_cons_self ..) (d + RecAnn.params none) Xs,
          ihtl (fun b hb => h b (List.mem_cons_of_mem hd hb))]

/-- Opening scoped type variables is a no-op on a term in the image of `Expr.erase`
    (erasure already blanked every annotation slot, so there is nothing to open),
    depth-generalised. -/
theorem Expr.openTyVarsAux_eq_self_of_erase_image (e : Expr) :
    ∀ (d : Nat) (Xs : List Nat), e.erase.openTyVarsAux d Xs = e.erase := by
  induction e using Expr.rec_strong with
  | primLit p => intro d Xs; simp [Expr.openTyVarsAux, Expr.erase]
  | primBinOp op => intro d Xs; simp [Expr.openTyVarsAux, Expr.erase]
  | ctor nm => intro d Xs; simp [Expr.openTyVarsAux, Expr.erase]
  | var n => intro d Xs; simp [Expr.openTyVarsAux]
  | lambda ann body ih =>
      intro d Xs
      simp [Expr.openTyVarsAux, ih d Xs]
  | app f arg ihf iharg =>
      intro d Xs
      simp [Expr.openTyVarsAux, ihf d Xs, iharg d Xs]
  | letIn ann rhs body ihr ihb =>
      intro d Xs
      simp [Expr.openTyVarsAux, ihr d Xs, ihb d Xs]
  | match_ scrut branches ihs ihbs =>
      intro d Xs
      simp only [Expr.openTyVarsAux, Expr.erase_match, ihs d Xs]
      congr 1
      exact BranchList.openTyVarsAux_eq_self_of_erase_image d Xs branches
        (fun pb hpb => ihbs pb.1 pb.2 hpb d Xs)
  | letRec anns bindings body ihbs ihb =>
      intro d Xs
      simp only [Expr.openTyVarsAux, Expr.erase_letRec, ihb d Xs]
      congr 1
      · simp [RecGroup.openAnns]
      · exact RecGroup.openTyVarsAux_eq_self_of_erase_image d Xs bindings
          (fun b hb d' Xs' => ihbs b hb d' Xs')

/-- Opening scoped type variables is a no-op on an erased term (depth 0). -/
theorem Expr.openTyVars_eq_self_of_erase_image (e : Expr) (Xs : List Nat) :
    e.erase.openTyVars Xs = e.erase := by
  simpa [Expr.openTyVars] using Expr.openTyVarsAux_eq_self_of_erase_image e 0 Xs

/-- `Expr.erase` is idempotent (an erased term is a fixed point of `erase`). -/
theorem Expr.erase_idem (e : Expr) : e.erase.erase = e.erase := by
  induction e using Expr.rec_strong with
  | primLit p => simp [Expr.erase]
  | primBinOp op => simp [Expr.erase]
  | ctor nm => simp [Expr.erase]
  | var n => simp [Expr.erase_var]
  | lambda ann body ih => simp [Expr.erase_lambda, ih]
  | app f arg ihf iharg => simp [Expr.erase_app, ihf, iharg]
  | letIn ann rhs body ihr ihb => simp [Expr.erase_letIn, ihr, ihb]
  | match_ scrut branches ihs ihbs =>
      simp only [Expr.erase_match, ihs]
      congr 1
      rw [List.map_map]
      exact List.map_congr_left (fun pe hpe => by
        cases pe with
        | mk p b => simp [ihbs p b hpe])
  | letRec anns bindings body ihbs ihb =>
      simp only [Expr.erase_letRec, ihb]
      congr 1
      · exact List.map_const_none_eq_of_length (by simp)
      · rw [List.map_map]
        exact List.map_congr_left (fun b hb => ihbs b hb)

/-! ### Path R: `Expr.eraseBounds` commutation

Residual soundness needs erase to pass through Infer's type-spine rewrites.
Placed after `substTyFvars` / `openTyVars` / `openBoundTyVars`. -/

theorem Expr.eraseBounds_idem (e : Expr) :
    e.eraseBounds.eraseBounds = e.eraseBounds := by
  induction e using Expr.rec_strong with
  | primLit _ | primBinOp _ | ctor _ | var _ => simp [Expr.eraseBounds]
  | app _ _ ihf iharg => simp [Expr.eraseBounds, ihf, iharg]
  | lambda ann body ih =>
    simp [Expr.eraseBounds, ih]
    cases ann <;> simp [Ty.eraseBounds_idem]
  | letIn ann rhs body ihr ihb =>
    simp [Expr.eraseBounds, ihr, ihb]
    cases ann <;> simp [PolyTy.eraseBounds_idem]
  | match_ scrut branches ihs ihbs =>
    simp [Expr.eraseBounds, ihs]
    intro p b hpb
    exact ihbs p b hpb
  | letRec anns bindings body ihbs ihb =>
    simp [Expr.eraseBounds, ihb]
    refine And.intro ?_ ihbs
    intro a ha
    cases a <;> simp [PolyTy.eraseBounds_idem]

/-- Local (pre-`Ty.eraseBounds_substFvar`) helper for Path R term commutation. -/
private theorem eraseBounds_substFvar_ty (Z : Nat) (U : Ty) (τ : Ty) :
    Ty.eraseBounds (Ty.substFvar Z U τ) =
      Ty.substFvar Z (Ty.eraseBounds U) (Ty.eraseBounds τ) := by
  induction τ using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b iha ihb =>
    simp only [Ty.substFvar, Ty.eraseBounds_arrow, iha, ihb]
  | bvar i => rfl
  | fvar n =>
    by_cases hn : n = Z
    · simp only [Ty.substFvar, if_pos hn, Ty.eraseBounds_fvar]
    · simp only [Ty.substFvar, if_neg hn, Ty.eraseBounds_fvar]
  | customTy nm tys ih =>
    simp only [Ty.substFvar, Ty.eraseBounds_customTy]
    refine congrArg (Ty.customTy nm) ?_
    have hsub (V : Ty) (ts : List Ty) :
        TyList.substFvar Z V ts = ts.map (Ty.substFvar Z V) := by
      induction ts with
      | nil => rfl
      | cons hd tl iht => simp only [TyList.substFvar, List.map_cons, iht]
    rw [hsub, TyList.eraseBounds_eq_map, TyList.eraseBounds_eq_map, hsub, List.map_map,
      List.map_map]
    exact List.map_congr_left fun t ht => ih t ht
  | bl lo hi e ih =>
    simp only [Ty.substFvar, Ty.eraseBounds_bl, bareListTy, TyList.substFvar, ih]

private theorem eraseBounds_substFvar_poly (Z : Nat) (U : Ty) (σ : PolyTy) :
    PolyTy.eraseBounds (PolyTy.substFvar Z U σ) =
      PolyTy.substFvar Z (Ty.eraseBounds U) (PolyTy.eraseBounds σ) := by
  cases σ with
  | mk n b =>
    simp only [PolyTy.eraseBounds, PolyTy.substFvar, eraseBounds_substFvar_ty]

private theorem BranchList.substTyFvar_eq_map_local (Z : Nat) (U : Ty)
    (brs : List (MatchPattern × Expr)) :
    BranchList.substTyFvar Z U brs = brs.map (fun pb => (pb.1, pb.2.substTyFvar Z U)) := by
  induction brs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [BranchList.substTyFvar, List.map_cons, ih]

theorem Expr.eraseBounds_substTyFvar (Z : Nat) (U : Ty) (e : Expr) :
    (e.substTyFvar Z U).eraseBounds =
      e.eraseBounds.substTyFvar Z (Ty.eraseBounds U) := by
  induction e using Expr.rec_strong with
  | primLit _ | primBinOp _ | ctor _ => simp [Expr.eraseBounds, Expr.substTyFvar]
  | var n => simp [Expr.eraseBounds, Expr.substTyFvar]
  | app _ _ ihf iharg => simp [Expr.eraseBounds, Expr.substTyFvar, ihf, iharg]
  | lambda ann body ih =>
    simp [Expr.eraseBounds, Expr.substTyFvar, ih]
    cases ann with
    | none => rfl
    | some t =>
      simp only [Option.map_some, Option.some.injEq]
      exact eraseBounds_substFvar_ty Z U t
  | letIn ann rhs body ihr ihb =>
    simp [Expr.eraseBounds, Expr.substTyFvar, ihr, ihb]
    cases ann with
    | none => rfl
    | some σ =>
      simp only [Option.map_some, Option.some.injEq]
      exact eraseBounds_substFvar_poly Z U σ
  | match_ scrut branches ihs ihbs =>
    simp only [Expr.eraseBounds, Expr.substTyFvar, ihs,
      BranchList.substTyFvar_eq_map_local, List.map_map]
    simp [Expr.match_.injEq]
    intro p b hpb
    exact ihbs p b hpb
  | letRec anns bindings body ihbs ihb =>
    simp only [Expr.eraseBounds, Expr.substTyFvar, ihb,
      RecGroup.substTyFvar_eq_map, List.map_map]
    simp [Expr.letRec.injEq]
    constructor
    · intro a ha
      cases a with
      | none => rfl
      | some σ =>
        simp only [Option.map_some, Function.comp_def, Option.some.injEq]
        exact eraseBounds_substFvar_poly Z U σ
    · exact ihbs

theorem Expr.eraseBounds_substTyFvars (pairs : List (Nat × Ty)) (e : Expr) :
    (e.substTyFvars pairs).eraseBounds =
      e.eraseBounds.substTyFvars (pairs.map fun p => (p.1, Ty.eraseBounds p.2)) := by
  induction pairs generalizing e with
  | nil => simp only [Expr.substTyFvars, List.map_nil]
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, List.map_cons]
    -- LHS: erase (substFvars tl (substTyFvar Z U e))
    --     = substFvars (map erase tl) (erase (substTyFvar Z U e))   [ih]
    --     = substFvars (map erase tl) (substTyFvar Z (erase U) (erase e))
    rw [ih, Expr.eraseBounds_substTyFvar]

/-- `eraseBounds` fixes the bvar/fvar-only payload of `openVarsFrom`. -/
private theorem eraseBounds_openVarsFrom_ty (d : Nat) (Xs : List Nat) (τ : Ty) :
    Ty.eraseBounds (Ty.openVarsFrom d Xs τ) =
      Ty.openVarsFrom d Xs (Ty.eraseBounds τ) := by
  unfold Ty.openVarsFrom
  induction τ using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b iha ihb =>
    simp only [Ty.instantiate, Ty.eraseBounds_arrow, iha, ihb]
  | bvar i =>
    simp only [Ty.instantiate, Ty.eraseBounds_bvar]
    by_cases hi : i < d
    · simp only [if_pos hi, Ty.eraseBounds_bvar]
    · simp only [if_neg hi]
      cases Xs[i - d]? with
      | none => rfl
      | some _ => rfl
  | fvar n => rfl
  | customTy nm tys ih =>
    simp only [Ty.instantiate, Ty.eraseBounds_customTy]
    refine congrArg (Ty.customTy nm) ?_
    have hinst (σ : Nat → Ty) (ts : List Ty) :
        TyList.instantiate σ ts = ts.map (Ty.instantiate σ) := by
      induction ts with
      | nil => rfl
      | cons hd tl iht => simp only [TyList.instantiate, List.map_cons, iht]
    rw [hinst, TyList.eraseBounds_eq_map, TyList.eraseBounds_eq_map, hinst, List.map_map,
      List.map_map]
    exact List.map_congr_left fun t ht => ih t ht
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Ty.eraseBounds_bl, bareListTy, TyList.instantiate, ih]

private theorem RecAnn.params_eraseBounds (a : Option PolyTy) :
    RecAnn.params (Option.map PolyTy.eraseBounds a) = RecAnn.params a := by
  cases a with
  | none => rfl
  | some σ => simp only [RecAnn.params, Option.map_some, PolyTy.eraseBounds_paramCount]

private theorem RecGroup.shieldDepths_eraseBounds (d : Nat) (anns : List (Option PolyTy))
    (bs : List Expr) :
    RecGroup.shieldDepths d (anns.map (Option.map PolyTy.eraseBounds)) bs =
      RecGroup.shieldDepths d anns bs := by
  induction bs generalizing anns with
  | nil => cases anns <;> rfl
  | cons hd tl ih =>
    cases anns with
    | nil => simp only [List.map_nil, RecGroup.shieldDepths]
    | cons a as =>
      simp only [List.map_cons, RecGroup.shieldDepths, RecAnn.params_eraseBounds, ih]

private theorem RecGroup.openAnns_eraseBounds (d : Nat) (Xs : List Nat)
    (anns : List (Option PolyTy)) :
    (RecGroup.openAnns d Xs anns).map (Option.map PolyTy.eraseBounds) =
      RecGroup.openAnns d Xs (anns.map (Option.map PolyTy.eraseBounds)) := by
  simp only [RecGroup.openAnns, List.map_map]
  apply List.map_congr_left
  intro a _
  cases a with
  | none => rfl
  | some σ =>
    simp only [Option.map_some, Function.comp_def, PolyTy.eraseBounds,
      eraseBounds_openVarsFrom_ty]

private theorem BranchList.openTyVarsAux_eq_map_local (d : Nat) (Xs : List Nat)
    (brs : List (MatchPattern × Expr)) :
    BranchList.openTyVarsAux d Xs brs =
      brs.map (fun pb => (pb.1, pb.2.openTyVarsAux d Xs)) := by
  induction brs with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [BranchList.openTyVarsAux, List.map_cons, ih]

private theorem Expr.eraseBounds_openTyVarsAux (Xs : List Nat) :
    ∀ (e : Expr) (d : Nat),
      (e.openTyVarsAux d Xs).eraseBounds = e.eraseBounds.openTyVarsAux d Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit _ | primBinOp _ | ctor _ => intro d; simp [Expr.eraseBounds, Expr.openTyVarsAux]
  | var n => intro d; simp [Expr.eraseBounds, Expr.openTyVarsAux]
  | app _ _ ihf iharg =>
    intro d; simp [Expr.eraseBounds, Expr.openTyVarsAux, ihf d, iharg d]
  | lambda ann body ih =>
    intro d
    simp [Expr.eraseBounds, Expr.openTyVarsAux, ih d]
    cases ann with
    | none => rfl
    | some t =>
      simp only [Option.map_some, Option.some.injEq]
      exact eraseBounds_openVarsFrom_ty d Xs t
  | letIn ann rhs body ihr ihb =>
    intro d
    cases ann with
    | none =>
      simp [Expr.eraseBounds, Expr.openTyVarsAux, ihr d, ihb d]
    | some σ =>
      simp only [Expr.eraseBounds, Expr.openTyVarsAux, Option.map_some,
        ihr (d + σ.paramCount), ihb d]
      -- residual goal is scheme-body equality (paramCount preserved by erase)
      cases σ with
      | mk n b =>
        simp only [PolyTy.eraseBounds, eraseBounds_openVarsFrom_ty]
  | match_ scrut branches ihs ihbs =>
    intro d
    simp only [Expr.eraseBounds, Expr.openTyVarsAux, ihs d,
      BranchList.openTyVarsAux_eq_map_local, List.map_map]
    simp [Expr.match_.injEq]
    intro p b hpb
    exact ihbs p b hpb d
  | letRec anns bindings body ihbs ihb =>
    intro d
    simp only [Expr.eraseBounds, Expr.openTyVarsAux, ihb d,
      RecGroup.openTyVarsAux_eq_zip, RecGroup.shieldDepths_map,
      RecGroup.shieldDepths_eraseBounds, List.map_map]
    simp only [Expr.letRec.injEq]
    refine ⟨?anns, ?binds, trivial⟩
    case anns =>
      exact RecGroup.openAnns_eraseBounds d Xs anns
    case binds =>
      -- (map erase bindings).zip depths = map (Prod.map erase id) (bindings.zip depths)
      rw [List.zip_map_left]
      simp only [List.map_map]
      apply List.map_congr_left
      intro p hp
      obtain ⟨e, de⟩ := p
      have he : e ∈ bindings := (List.of_mem_zip hp).1
      -- erase (open de Xs e) = open de Xs (erase e)
      simpa [Function.comp_def, Prod.map_apply] using ihbs e he de

theorem Expr.eraseBounds_openTyVars (Xs : List Nat) (e : Expr) :
    (e.openTyVars Xs).eraseBounds = e.eraseBounds.openTyVars Xs :=
  Expr.eraseBounds_openTyVarsAux Xs e 0

theorem Expr.eraseBounds_openBoundTyVars (ann : Option PolyTy) (Xs : List Nat) (e : Expr) :
    (Expr.openBoundTyVars ann Xs e).eraseBounds =
      Expr.openBoundTyVars (ann.map PolyTy.eraseBounds) Xs e.eraseBounds := by
  cases ann with
  | none => simp only [Expr.openBoundTyVars, Option.map_none]
  | some σ =>
    simp only [Expr.openBoundTyVars, Option.map_some]
    exact Expr.eraseBounds_openTyVars Xs e

theorem Expr.eraseBounds_lambda (ann : Option Ty) (body : Expr) :
    (Expr.lambda ann body).eraseBounds =
      .lambda (ann.map Ty.eraseBounds) body.eraseBounds := by
  simp only [Expr.eraseBounds]

theorem Expr.eraseBounds_letIn (ann : Option PolyTy) (rhs body : Expr) :
    (Expr.letIn ann rhs body).eraseBounds =
      .letIn (ann.map PolyTy.eraseBounds) rhs.eraseBounds body.eraseBounds := by
  simp only [Expr.eraseBounds]

theorem Expr.eraseBounds_app (f arg : Expr) :
    (Expr.app f arg).eraseBounds = .app f.eraseBounds arg.eraseBounds := by
  simp only [Expr.eraseBounds]

theorem Expr.eraseBounds_var (i : Nat) :
    (Expr.var i).eraseBounds = .var i := by
  simp only [Expr.eraseBounds]

/-! ### Locally-closed-ness. -/

/-- Locally-closed monotype: no `.bvar`s. Existing `ContainsBvarsUpTo 0`. -/
abbrev Ty.IsLC (ty : Ty) : Prop := ContainsBvarsUpTo 0 ty

/-- All types in the list are LC, AND the list has the expected length. -/
def Ty.AreLC (n : Nat) (Vs : List Ty) : Prop :=
  Vs.length = n ∧ ∀ V ∈ Vs, V.IsLC

/-- A well-formed scheme: every bound variable in the body is within the
    declared arity (`< paramCount`).

    Intuition: this is exactly the condition that makes `M` a *real* `∀`-scheme
    — equivalently, opening it with any `paramCount`-many names yields a
    locally-closed type (no dangling bvars escape). We use this elementary
    *syntactic* form (rather than the "opening is always LC" semantic form)
    because it's what the proofs actually consume, and it's trivially preserved
    by the operations we perform on schemes. -/
def PolyTy.WF (M : PolyTy) : Prop :=
  ContainsBvarsUpTo M.paramCount M.body

theorem Ty.IsLC.eraseBounds {τ : Ty} (h : τ.IsLC) : (Ty.eraseBounds τ).IsLC :=
  ContainsBvarsUpTo.eraseBounds h

/-- LC of the erase-normal form implies LC of the original (bvars unchanged). -/
theorem Ty.IsLC.of_eraseBounds {τ : Ty} (h : (Ty.eraseBounds τ).IsLC) : τ.IsLC :=
  ContainsBvarsUpTo.of_eraseBounds h

theorem PolyTy.WF.eraseBounds {σ : PolyTy} (h : σ.WF) : (PolyTy.eraseBounds σ).WF := by
  simpa [PolyTy.WF, PolyTy.eraseBounds] using ContainsBvarsUpTo.eraseBounds h

theorem PolyTy.WF.of_eraseBounds {σ : PolyTy} (h : (PolyTy.eraseBounds σ).WF) : σ.WF := by
  simpa [PolyTy.WF, PolyTy.eraseBounds] using ContainsBvarsUpTo.of_eraseBounds h

/-- Total number of bound type variables across a group of schemes. -/
def PolyTy.totalParams (Ms : List PolyTy) : Nat := (Ms.map PolyTy.paramCount).sum

/-- Open a group of schemes at consecutive slices of `Xs` (slice sizes = each
    scheme's `paramCount`). The cofinite `letRec` premise types the recursive group
    monomorphically at one such opening, quantified over all sufficiently-fresh `Xs`. -/
def PolyTy.openGroup : List PolyTy → List Nat → List Ty
  | [],      _  => []
  | M :: Ms, Xs => M.openVars (Xs.take M.paramCount) :: PolyTy.openGroup Ms (Xs.drop M.paramCount)

/-! ### `letRec` shared-monotype generalisation helpers.

The `letRec` rule types the recursive group at *shared monotypes* `τs`, then
generalises each `τⱼ` over the group's gen-var pool `G`. `renameG` is the shared
opening (rename `G ↦ Xs` everywhere — the SAME `Xs` for every binding, so mutual
recursion's type-sharing stays linked); `genGroup G τⱼ` is the body-scheme
`∀ (G ∩ ftv τⱼ). τⱼ`. -/

/-- Rename the group's gen-vars `G` to fresh names `Xs` throughout a monotype: the
    *shared* opening used by the cofinite `letRec` premise. -/
def Ty.renameG (G Xs : List Nat) (τ : Ty) : Ty :=
  Ty.substFvars (G.zip (Xs.map (Ty.fvar ·))) τ

/-- The gen-vars of the pool `G` that actually occur in `τ` (in `G`'s order). -/
def Ty.genFilter (G : List Nat) (τ : Ty) : List Nat := G.filter (· ∈ τ.freeVars)

/-- The body-scheme for one binding: generalise `τ` over `G ∩ ftv(τ)`. -/
def PolyTy.genGroup (G : List Nat) (τ : Ty) : PolyTy :=
  ⟨(Ty.genFilter G τ).length, Ty.closeOver (Ty.genFilter G τ) τ⟩

/-- `genGroup` schemes are well-formed (closing an LC type introduces exactly the
    declared `paramCount`-many bound variables). -/
theorem PolyTy.genGroup_wf {G : List Nat} {τ : Ty} (hτ : τ.IsLC) :
    (PolyTy.genGroup G τ).WF :=
  Ty.closeOver_preserves_bvars hτ


/-! ### Per-binding recursion-group specs (the `letRec` rule's internals).

The fused `letRec` rule (mixed annotated/unannotated groups) carries one
derivation-internal `RecSpec` per binding: an UNANNOTATED member's shared
monotype `τ` (a rule-internal existential, like the historical `letRec`'s
`τs`), or an ANNOTATED member's declared scheme `σ` (pinned to the stored
annotation via `RecSpec.ann`). The two env projections say what the group
looks like from inside the RHSs (`rhsEntry` — monos at their opened shared
monotypes, polys at their FULL schemes) and from the body (`bodyScheme` —
monos generalised over the pool, polys at their schemes). Validated
standalone by `SpikeLetRecMixed` (2026-07-02). -/

/-- Derivation-internal per-binding datum for a recursion group. -/
inductive RecSpec
  | mono (τ : Ty)
  | poly (σ : PolyTy)

/-- What the node stores: `none` for an unannotated member, the scheme for an
    annotated one. The rule's `specs.map RecSpec.ann = anns` premise ties the
    internal specs to the stored annotations. -/
def RecSpec.ann : RecSpec → Option PolyTy
  | .mono _ => none
  | .poly σ => some σ

/-- The env entry a member presents while the group's RHSs are checked, inside
    the shared pool opening `G ↦ Xs`: unannotated members at their opened shared
    monotypes (monomorphic recursion), annotated members at their FULL schemes
    (polymorphic recursion, and polymorphic cross-boundary use). -/
def RecSpec.rhsEntry (G Xs : List Nat) : RecSpec → PolyTy
  | .mono τ => PolyTy.mkTrivial (Ty.renameG G Xs τ)
  | .poly σ => σ

/-- The env entry a member presents to the BODY: unannotated members generalised
    per-binding over the shared pool (`∀ (G ∩ ftv τ). τ`), annotated members at
    their declared schemes. -/
def RecSpec.bodyScheme (G : List Nat) : RecSpec → PolyTy
  | .mono τ => PolyTy.genGroup G τ
  | .poly σ => σ

/-- The free type variables a spec's MONOTYPE contributes (schemes are
    pool-independent and handled pointwise, so they contribute nothing here).
    Used by `typ_subst`'s pool-freshening to dodge the shared monotypes. -/
def RecSpec.monoFreeVars : RecSpec → List Nat
  | .mono τ => τ.freeVars
  | .poly _ => []

/-- Transport of a spec under `[Z ↦ U]` with the pool freshened `G ↦ W` (the
    `typ_subst` `letRec` case): monotypes are renamed onto the fresh pool and
    then substituted; schemes are substituted pointwise (pool-independent). -/
def RecSpec.substFreshened (Z : Nat) (U : Ty) (G W : List Nat) : RecSpec → RecSpec
  | .mono τ => .mono (Ty.substFvar Z U (Ty.renameG G W τ))
  | .poly σ => .poly (PolyTy.substFvar Z U σ)

/-- Pin a spec's monotype at the pool opening `G ↦ Xs` (schemes are untouched).
    The **mono-group trick** for the fused rule's preservation rewrap: re-deriving
    the node with `specs.map (openAt G Xs)` at the EMPTY pool makes the body env
    coincide with the RHS env, so the rule's own cofinite premises supply the
    re-wrapped member's typing directly. -/
def RecSpec.openAt (G Xs : List Nat) : RecSpec → RecSpec
  | .mono τ => .mono (Ty.renameG G Xs τ)
  | .poly σ => .poly σ

theorem RecSpec.ann_eq_none {s : RecSpec} (h : s.ann = none) : ∃ τ, s = .mono τ := by
  cases s with
  | mono τ => exact ⟨τ, rfl⟩
  | poly σ => simp [RecSpec.ann] at h

theorem RecSpec.ann_eq_some {s : RecSpec} {σ : PolyTy} (h : s.ann = some σ) :
    s = .poly σ := by
  cases s with
  | mono τ => simp [RecSpec.ann] at h
  | poly σ' => simpa [RecSpec.ann] using h


/-! ### Freshness packaging. -/

/-- `Xs` is a list of `n` distinct names, all disjoint from `L`. -/
structure FreshNames (L : List Nat) (n : Nat) (Xs : List Nat) : Prop where
  length : Xs.length = n
  nodup  : Xs.Nodup
  avoid  : ∀ x ∈ Xs, x ∉ L


/-! ### Typing-rule premise packaging.

The substantial premises of the typing rules are named here so the rules (and
every proof over them) read as a handful of meaningful propositions instead of
raw quantifier nests. Premises that recurse into the typing relation are
parameterised by it (`TypeOf`), so `TypeOfElabHM` and `TypeOfHM` share them
verbatim — making it syntactically evident that the two relations differ in the
`var` rule ONLY. (The auto-generated recursors see through these definitions and
still provide induction hypotheses for the packaged sub-derivations.) -/

/-- An optional annotation, when present, pins a rule-internal choice: the
    `lambda` rule's parameter type must be the parameter ascription (if any),
    and the `letIn` rule's generalised scheme must be the `let`'s ascription
    (if any). For `none` this is vacuous — the choice is free (inferred).

    **Path R (locked):** pins are **structural** — pure HM `TypeOf*` does not
    identify `BL` with bare `List`. Bounds-blind equality (`AgreesHM` /
    `eraseBounds`) lives only in Infer/unify and in residual bridge theorems
    that project elaborata through `eraseExpr` / `eraseBounds`. -/
def Option.Pins {α : Type _} (ann : Option α) (x : α) : Prop :=
  ∀ a, ann = some a → x = a

/-- **The cofinite let-generalisation premise**: the bound expression types at
    EVERY sufficiently-fresh opening `Xs` of the scheme `M`, with the
    annotation's own scoped type variables opened to the *same* `Xs`
    (`Expr.openBoundTyVars`; for an unannotated `let` the expression is typed
    unchanged). Quantifying over all fresh openings (rather than one existential
    choice) is what makes the rule stable under weakening and substitution; the
    ann-lockstep opening is the spec-level home of scoped type variables. -/
def GeneralisesTo (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (ann : Option PolyTy) (boundExpr : Expr) (M : PolyTy) (L : List Nat) : Prop :=
  ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
    TypeOf ctx (Expr.openBoundTyVars ann Xs boundExpr) (M.openVars Xs)

/-- The constructor-pattern side conditions of a match branch `(.named c n, _)`
    against a scrutinee of type `scrutTy`: the pattern's constructor exists,
    the scrutinee type is its data type (at some type arguments `tyArgs` of the
    declared arity), the pattern binds exactly the constructor's field count,
    and `instContents` are the field types instantiated at `tyArgs` (these are
    what the branch body's env binds, monomorphically). Purely structural — no
    typing recursion — so both branch relations share it. -/
structure BranchCtorSpec (ctors : CtorEnv) (c : CtorName) (n : Nat) (scrutTy : Ty)
    (ctor : Ctor) (tyArgs instContents : List Ty) : Prop where
  lookup     : LookupList.get? ctors c = some ctor
  scrut_eq   : scrutTy = .customTy ctor.tyName tyArgs
  arity      : ctor.paramCount = tyArgs.length
  bind_count : n = ctor.contents.length
  fields     : List.Forall₂ (InstantiatesBy tyArgs) ctor.contents instContents

/-- The context a recursion group's RHSs are checked in, at the shared pool
    opening `G ↦ Xs`: every member of the group is visible — annotated members
    at their FULL declared schemes (enabling polymorphic recursion and
    polymorphic cross-boundary use), unannotated members at their opened shared
    monotypes (`RecSpec.rhsEntry`). -/
def RecSpecs.rhsCtx (ctx : Ctx) (specs : List RecSpec) (G Xs : List Nat) : Ctx :=
  { ctx with env := specs.map (RecSpec.rhsEntry G Xs) ++ ctx.env }

/-- The context a recursion group's BODY is typed in: annotated members at their
    declared schemes, unannotated members generalised per-binding over the shared
    pool `G` (`RecSpec.bodyScheme`). -/
def RecSpecs.bodyCtx (ctx : Ctx) (specs : List RecSpec) (G : List Nat) : Ctx :=
  { ctx with env := specs.map (RecSpec.bodyScheme G) ++ ctx.env }

/-- Well-formed derivation data for a recursion group: the (rule-internal)
    `specs` match the STORED annotations `anns` one-to-one, there is one spec per
    binding, the gen-var pool is duplicate-free, unannotated members' shared
    monotypes are locally closed, and annotated members' declared schemes are
    well-formed. -/
structure RecSpecs.WF (anns : List (Option PolyTy)) (bindings : List Expr)
    (specs : List RecSpec) (G : List Nat) : Prop where
  anns_eq : specs.map RecSpec.ann = anns
  length  : bindings.length = specs.length
  nodup   : G.Nodup
  mono_lc : ∀ τ, RecSpec.mono τ ∈ specs → τ.IsLC
  poly_wf : ∀ σ, RecSpec.poly σ ∈ specs → σ.WF

/-- **Cofinite premise for the UNANNOTATED members** (the Damas–Milner
    monomorphic-recursion half, Pottier's `LetRec`): for every sufficiently-fresh
    shared pool opening `G ↦ Xs` — the SAME `Xs` for the whole group, which is
    what keeps mutual monotype-sharing linked — each unannotated member's RHS
    types AS STORED at its opened shared monotype `τ[G↦Xs]`, in the group RHS
    context. Cofinite (à la `letIn`, NOT existential) ⇒ sound under weakening. -/
def RecSpecs.MonoTyped (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List Expr) (specs : List RecSpec) (G L : List Nat) : Prop :=
  ∀ Xs, FreshNames L G.length Xs →
    ∀ p ∈ bindings.zip specs, ∀ τ, p.2 = .mono τ →
      TypeOf (RecSpecs.rhsCtx ctx specs G Xs) p.1 (Ty.renameG G Xs τ)

/-- **Cofinite premise for the ANNOTATED members** (the polymorphic-recursion
    half, Pottier's `LetRecPoly`): inside every fresh pool opening `G ↦ Xs`, each
    annotated member's RHS is checked **scheme-relatively** — opened at its OWN
    fresh skolems `Ys` (length `σ.paramCount`) against its scheme's opening. The
    `Ys` quantifier is NESTED INSIDE the `Xs` one and excludes it (`L ++ Xs`), so
    the shared monotypes are fixed before any `Ys` is chosen: an unannotated
    member's monotype can never capture an annotated sibling's skolem
    (machine-checked: `SpikeLetRecMixed.skolemLeak_untypeable`). -/
def RecSpecs.PolyTyped (TypeOf : Ctx → Expr → Ty → Prop) (ctx : Ctx)
    (bindings : List Expr) (specs : List RecSpec) (G L : List Nat) : Prop :=
  ∀ Xs, FreshNames L G.length Xs →
    ∀ p ∈ bindings.zip specs, ∀ σ, p.2 = .poly σ →
      ∀ Ys, FreshNames (L ++ Xs) σ.paramCount Ys →
        TypeOf (RecSpecs.rhsCtx ctx specs G Xs) (p.1.openTyVars Ys) (σ.openVars Ys)


/-! ### The *declarative* HM typing relation `TypeOfHM` (the completeness spec).

Classic Damas–Milner typing, **decoration-blind**: the algorithm-independent
specification of "this (source) program is HM-typeable", against which the
elaborator's completeness / principality is stated. It ranges over the same `Expr`
as `TypeOfElabHM` but **ignores** the `tyArgs` stored in `var` nodes — a use
instantiates its scheme by *some* witness types (existentially), exactly as in
textbook HM, with no `length = paramCount` requirement.

`TypeOfHM` and `TypeOfElabHM` differ in **exactly one rule** — `var`. Every other
constructor is identical: `ctor`/`match` store no tyArgs (already decoration-blind),
and the `let`/`letRec(Ann)` openings act on annotation scoped-type-variables (present
in source terms) and harmlessly on the ignored var-tyArgs. Consequently
`TypeOfElabHM e τ → TypeOfHM e τ` (the elaborated relation is the stricter one). The
dynamics / progress / preservation / type safety are stated about `TypeOfElabHM`;
`TypeOfHM` borrows its operational meaning through elaboration. -/

mutual

/-- Decoration-blind declarative Hindley–Milner typing (the source-level spec). -/
inductive TypeOfHM : Ctx → Expr → Ty → Prop
  | primLitUnit :
    TypeOfHM ctx (.primLit .unit) (.prim .unit)

  | primLitInt :
    TypeOfHM ctx (.primLit (.int n)) (.prim .int)

  | primLitNat :
    TypeOfHM ctx (.primLit (.nat n)) (.prim .nat)

  | primLitChar :
    TypeOfHM ctx (.primLit (.char c)) (.prim .char)

  /-- `intAdd : int → int → int` (identical to the `TypeOfElabHM` rule — a primop
      carries no `tyArgs`, so the two relations agree; `faithful` is trivial). -/
  | primBinOpIntAdd :
    TypeOfHM ctx (.primBinOp .intAdd)
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))

  /-- `intSub : int → int → int`. -/
  | primBinOpIntSub :
    TypeOfHM ctx (.primBinOp .intSub)
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))

  /-- `intLt : int → int → Bool` (identical to the `TypeOfElabHM` rule). -/
  | primBinOpIntLt :
    TypeOfHM ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfHM ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfHM ctx (.primBinOp .intLt)
      (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))

  /-- `charLt : char → char → Bool` (identical to the `TypeOfElabHM` rule). -/
  | primBinOpCharLt :
    TypeOfHM ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfHM ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfHM ctx (.primBinOp .charLt)
      (.arrow (.prim .char) (.arrow (.prim .char) (.customTy ⟨"Bool"⟩ [])))

  | lambda :
    paramTy.IsLC →
    ann.Pins paramTy →
    bodyCtx = { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
    TypeOfHM ctx f (.arrow argTy retTy) →
    TypeOfHM ctx input argTy →
    TypeOfHM ctx (.app f input) retTy

  /-- Cofinite let-generalisation (identical to `TypeOfElabHM.letIn`; see
      `GeneralisesTo`). -/
  | letIn {M : PolyTy} {L : List Nat} :
    PolyTy.WF M →
    ann.Pins M →
    GeneralisesTo TypeOfHM ctx ann boundExpr M L →
    bodyCtx = { ctx with env := M :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.letIn ann boundExpr body) bodyTy

  /-- **The one rule that differs from `TypeOfElabHM`.** Decoration-blind: the
      stored `tyArgs` are ignored (the use is well-typed for *any* decoration), and
      the scheme is instantiated by *some* witness `instArgs` (existential), with no
      `length = paramCount` requirement — the classic HM instantiation. -/
  | var :
    ctx.env[dbl]? = some polyTy →
    (∀ tyArg ∈ instArgs, tyArg.IsLC) →
    polyTy.InstantiatesTo instArgs ty →
    TypeOfHM ctx (.var dbl) ty

  | ctor :
    LookupList.get? ctx.ctors name = some ctor →
    (∀ tyArg ∈ tyArgs, tyArg.IsLC) →
    ctor.toTy.InstantiatesTo tyArgs ty →
    TypeOfHM ctx (.ctor name) ty

  | match_ :
    TypeOfHM ctx scrutinee scrutTy →
    branches ≠ [] →
    (∀ branch ∈ branches, TypeOfMatchBranch ctx branch scrutTy resultTy) →
    TypeOfHM ctx (.match_ scrutinee branches) resultTy

  /-- Mixed recursive group (the SAME packaged premises as `TypeOfElabHM.letRec`
      — shared via the relation-parametric `RecSpecs.MonoTyped`/`PolyTyped` —
      recursing into declarative `TypeOfHM`). -/
  | letRec {specs : List RecSpec} {G L : List Nat} :
    RecSpecs.WF anns bindings specs G →
    RecSpecs.MonoTyped TypeOfHM ctx bindings specs G L →
    RecSpecs.PolyTyped TypeOfHM ctx bindings specs G L →
    bodyCtx = RecSpecs.bodyCtx ctx specs G →
    TypeOfHM bodyCtx body ρ →
    TypeOfHM ctx (.letRec anns bindings body) ρ


/-- Match-branch typing for the declarative `TypeOfHM` (mirrors
    `TypeOfElabMatchBranch`, sharing `BranchCtorSpec`; the scrutinee's `tyArgs`
    are an existential witness). -/
inductive TypeOfMatchBranch :
  (ctx : Ctx) → (MatchPattern × Expr) → (scrutTy : Ty) → (resultTy : Ty) → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {c : CtorName} {n : Nat} {tyArgs instContents : List Ty} :
    BranchCtorSpec ctx.ctors c n scrutTy ctor tyArgs instContents →
    bodyCtx = { ctx with env := instContents.map PolyTy.mkTrivial ++ ctx.env } →
    TypeOfHM bodyCtx bodyExpr resultTy →
    TypeOfMatchBranch ctx (.named c n, bodyExpr) scrutTy resultTy
  | wildcard {ctx : Ctx} :
    TypeOfHM ctx bodyExpr resultTy →
    TypeOfMatchBranch ctx (.wildcard, bodyExpr) scrutTy resultTy

end


/-! ### Key commute lemmas. -/

/-- An element is not in `TyList.freeVars tys` iff it's not in any element's
    freeVars. Standard distribution over dedup'd concatenation. -/
theorem TyList.not_mem_freeVars_iff {Z : Nat} {tys : List Ty} :
    Z ∉ TyList.freeVars tys ↔ ∀ t ∈ tys, Z ∉ t.freeVars := by
  induction tys with
  | nil => simp [TyList.freeVars]
  | cons hd tl ih =>
    simp only [TyList.freeVars, List.mem_dedup, List.mem_append, not_or,
               List.mem_cons, forall_eq_or_imp]
    rw [ih]

/-- If every element of `tys` is unchanged by `Ty.substFvar Z U`, then so is
    `TyList.substFvar Z U tys`. Plain list induction; used in `customTy`
    cases of the LHS lemmas. -/
private theorem TyList.substFvar_eq_self_of_all
    {Z : Nat} {U : Ty} {tys : List Ty}
    (h_all : ∀ t ∈ tys, Ty.substFvar Z U t = t) :
    TyList.substFvar Z U tys = tys := by
  induction tys with
  | nil => rfl
  | cons hd tl ih =>
    simp only [TyList.substFvar, List.cons.injEq]
    refine ⟨h_all hd List.mem_cons_self, ih ?_⟩
    intro t ht
    exact h_all t (List.mem_cons_of_mem _ ht)

theorem Ty.substFvar_fresh {Z : Nat} {U ty : Ty}
    (h : Z ∉ ty.freeVars) :
    Ty.substFvar Z U ty = ty := by
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.substFvar, Ty.arrow.injEq]
    exact ⟨ih_a h.1, ih_b h.2⟩
  | bvar _ => rfl
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton] at h
    simp only [Ty.substFvar, if_neg (Ne.symm h)]
  | customTy _ tys ih =>
    simp only [Ty.freeVars] at h
    have h' : ∀ t ∈ tys, Z ∉ t.freeVars :=
      TyList.not_mem_freeVars_iff.mp h
    simp only [Ty.substFvar, Ty.customTy.injEq, true_and]
    exact TyList.substFvar_eq_self_of_all (fun t ht => ih t ht (h' t ht))
  | bl lo hi e ih =>
    simp only [Ty.freeVars] at h
    simp only [Ty.substFvar, Ty.bl.injEq, true_and]
    exact ih h

/-- A block of type-fvar substitutions whose keys all avoid a scheme's body free
    vars leaves the scheme fixed. -/
theorem PolyTy.substFvars_eq_self_of_fresh {pairs : List (Nat × Ty)} :
    ∀ {σ : PolyTy}, (∀ p ∈ pairs, p.1 ∉ σ.body.freeVars) → PolyTy.substFvars pairs σ = σ := by
  induction pairs with
  | nil => intro σ _; rfl
  | cons hd tl ih =>
    intro σ h
    obtain ⟨Z, U⟩ := hd
    have hZ : Z ∉ σ.body.freeVars := h (Z, U) List.mem_cons_self
    have hstep : PolyTy.substFvar Z U σ = σ := by
      unfold PolyTy.substFvar
      rw [Ty.substFvar_fresh hZ]
    simp only [PolyTy.substFvars, hstep]
    exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- Instantiation is a no-op on locally-closed types: nothing to instantiate. -/
private theorem TyList.instantiate_eq_self_of_all_lc
    {σ : Nat → Ty} {tys : List Ty}
    (h_all : ∀ t ∈ tys, Ty.IsLC t)
    (ih : ∀ t ∈ tys, Ty.IsLC t → Ty.instantiate σ t = t) :
    TyList.instantiate σ tys = tys := by
  induction tys with
  | nil => rfl
  | cons hd tl ih_tl =>
    simp only [TyList.instantiate, List.cons.injEq]
    refine ⟨ih hd List.mem_cons_self (h_all hd List.mem_cons_self), ?_⟩
    exact ih_tl
      (fun t ht => h_all t (List.mem_cons_of_mem _ ht))
      (fun t ht => ih t (List.mem_cons_of_mem _ ht))

theorem Ty.instantiate_eq_self_of_lc {σ : Nat → Ty} {ty : Ty}
    (h : Ty.IsLC ty) :
    Ty.instantiate σ ty = ty := by
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    cases h with
    | arrow h_a h_b =>
      simp only [Ty.instantiate, Ty.arrow.injEq]
      exact ⟨ih_a h_a, ih_b h_b⟩
  | bvar _ =>
    cases h with
    | bvar h_lt => exact absurd h_lt (by omega)
  | fvar _ => rfl
  | customTy nm tys ih =>
    cases h with
    | customTy h_all =>
      simp only [Ty.instantiate, Ty.customTy.injEq, true_and]
      exact TyList.instantiate_eq_self_of_all_lc h_all ih
  | bl lo hi e ih =>
    cases h with
    | bl he =>
      simp only [Ty.instantiate, Ty.bl.injEq, true_and]
      exact ih he

/-- `substFvar` swaps with `instantiate` element-wise on a list, given the
    pointwise swap on each element. -/
private theorem TyList.substFvar_instantiate_swap
    {Z : Nat} {U : Ty} {σ : Nat → Ty} {tys : List Ty}
    (ih : ∀ t ∈ tys,
            Ty.substFvar Z U (Ty.instantiate σ t)
              = Ty.instantiate σ (Ty.substFvar Z U t)) :
    TyList.substFvar Z U (TyList.instantiate σ tys)
      = TyList.instantiate σ (TyList.substFvar Z U tys) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih_tl =>
    simp only [TyList.substFvar, TyList.instantiate, List.cons.injEq]
    refine ⟨ih hd List.mem_cons_self, ?_⟩
    exact ih_tl (fun t ht => ih t (List.mem_cons_of_mem _ ht))

theorem Ty.substFvar_openVars
    {Z : Nat} {U ty : Ty} {Xs : List Nat}
    (h_lc : Ty.IsLC U)
    (h_Z_not_in_Xs : Z ∉ Xs) :
    Ty.substFvar Z U (Ty.openVars Xs ty)
      = Ty.openVars Xs (Ty.substFvar Z U ty) := by
  -- `openVars` is just `instantiate` with the specific substitution
  -- `i ↦ Xs[i]? .elim (.bvar i) .fvar`. Unfold and induct on `ty`.
  unfold Ty.openVars
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.arrow.injEq]
    exact ⟨ih_a, ih_b⟩
  | bvar i =>
    simp only [Ty.instantiate, Ty.substFvar]
    -- Goal: substFvar Z U (Xs[i]?.elim (.bvar i) .fvar) = Xs[i]?.elim (.bvar i) .fvar
    cases h_xs : Xs[i]? with
    | none => simp [Ty.substFvar]
    | some x =>
      have h_mem : x ∈ Xs := List.mem_of_getElem? h_xs
      have h_ne : x ≠ Z := fun heq => h_Z_not_in_Xs (heq ▸ h_mem)
      simp [Ty.substFvar, h_ne]
  | fvar n =>
    simp only [Ty.instantiate, Ty.substFvar]
    -- LHS: if n=Z then U else .fvar n
    -- RHS: instantiate σ (if n=Z then U else .fvar n)
    by_cases h_n : n = Z
    · simp only [if_pos h_n]
      -- Need U = instantiate σ U
      exact (Ty.instantiate_eq_self_of_lc h_lc).symm
    · simp only [if_neg h_n, Ty.instantiate]
  | customTy nm tys ih =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.customTy.injEq, true_and]
    exact TyList.substFvar_instantiate_swap (fun t ht => ih t ht)
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.bl.injEq, true_and]
    exact ih

/-- `substFvar` commutes with offset opening (`Ty.openVarsFrom`), mirroring
    `Ty.substFvar_openVars`: the only new wrinkle is the `i < d` guard. -/
theorem Ty.substFvar_openVarsFrom
    {Z d : Nat} {U ty : Ty} {Xs : List Nat}
    (h_lc : Ty.IsLC U) (h_Z_not_in_Xs : Z ∉ Xs) :
    Ty.substFvar Z U (Ty.openVarsFrom d Xs ty)
      = Ty.openVarsFrom d Xs (Ty.substFvar Z U ty) := by
  unfold Ty.openVarsFrom
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b ih_a ih_b =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.arrow.injEq]; exact ⟨ih_a, ih_b⟩
  | bvar i =>
    simp only [Ty.instantiate, Ty.substFvar]
    by_cases h_d : i < d
    · simp only [if_pos h_d, Ty.substFvar]
    · simp only [if_neg h_d]
      cases h_xs : Xs[i - d]? with
      | none => simp [Ty.substFvar]
      | some x =>
        have h_ne : x ≠ Z := fun heq => h_Z_not_in_Xs (heq ▸ List.mem_of_getElem? h_xs)
        simp [Ty.substFvar, h_ne]
  | fvar n =>
    simp only [Ty.instantiate, Ty.substFvar]
    by_cases h_n : n = Z
    · simp only [if_pos h_n]; exact (Ty.instantiate_eq_self_of_lc h_lc).symm
    · simp only [if_neg h_n, Ty.instantiate]
  | customTy nm tys ih =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.customTy.injEq, true_and]
    exact TyList.substFvar_instantiate_swap (fun t ht => ih t ht)
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.bl.injEq, true_and]
    exact ih

/-- `substFvar` commutes with annotation-body opening (the ann-list analogue of
    `Ty.substFvar_openVarsFrom`): needed for the `letRec` case of
    `Expr.substTyFvar_openTyVarsAux`. -/
theorem RecGroup.substFvar_openAnns {Z d : Nat} {U : Ty} {Xs : List Nat}
    {anns : List (Option PolyTy)} (hU : U.IsLC) (hZ : Z ∉ Xs) :
    (RecGroup.openAnns d Xs anns).map (Option.map (PolyTy.substFvar Z U))
      = RecGroup.openAnns d Xs (anns.map (Option.map (PolyTy.substFvar Z U))) := by
  simp only [RecGroup.openAnns, List.map_map]
  refine List.map_congr_left (fun a _ => ?_)
  cases a with
  | none => rfl
  | some σ =>
    simp only [Function.comp_apply, Option.map_some, Option.some.injEq, PolyTy.substFvar,
      PolyTy.mk.injEq, true_and]
    exact Ty.substFvar_openVarsFrom hU hZ

/-- `substTyFvar` commutes with `openTyVarsAux` (offset opening of a term's scoped
    type variables), given the substituted-in type is locally closed and `Z` is
    not an opening name. The term-level analogue of `Ty.substFvar_openVarsFrom`. -/
theorem Expr.substTyFvar_openTyVarsAux
    {Z : Nat} {U : Ty} {Xs : List Nat}
    (h_lc : Ty.IsLC U) (h_Z : Z ∉ Xs) :
    ∀ (e : Expr) (d : Nat),
      (e.openTyVarsAux d Xs).substTyFvar Z U
        = (e.substTyFvar Z U).openTyVarsAux d Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d; rfl
  | primBinOp op => intro d; rfl
  | app f inp ih_f ih_i =>
    intro d; simp only [Expr.openTyVarsAux, Expr.substTyFvar]; rw [ih_f d, ih_i d]
  | lambda ann body ih =>
    intro d
    cases ann with
    | none => simp only [Expr.openTyVarsAux, Expr.substTyFvar, Option.map_none]; rw [ih d]
    | some t =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvar, Option.map_some]
      rw [Ty.substFvar_openVarsFrom h_lc h_Z, ih d]
  | letIn ann be body ih_be ih_body =>
    intro d
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvar, Option.map_none]
      rw [ih_be d, ih_body d]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvar, Option.map_some, PolyTy.substFvar]
      rw [Ty.substFvar_openVarsFrom h_lc h_Z, ih_be (d + σ.paramCount), ih_body d]
  | var n => intro d; rfl
  | ctor nm => intro d; rfl
  | match_ scrut branches ih_scrut ih_branches =>
    intro d
    simp only [Expr.openTyVarsAux, Expr.substTyFvar, Expr.match_.injEq]
    refine ⟨ih_scrut d, ?_⟩
    revert ih_branches
    induction branches with
    | nil => intro _; rfl
    | cons hd tl ih_tl =>
      intro ih_branches
      obtain ⟨pat, body⟩ := hd
      simp only [BranchList.openTyVarsAux, BranchList.substTyFvar]
      rw [ih_branches pat body List.mem_cons_self d,
          ih_tl (fun pat' body' hm => ih_branches pat' body' (List.mem_cons_of_mem _ hm))]
  | letRec anns bindings body ih_bindings ih_body =>
    intro d
    simp only [Expr.openTyVarsAux, Expr.substTyFvar]
    rw [Expr.letRec.injEq]
    refine ⟨RecGroup.substFvar_openAnns h_lc h_Z, ?_, ih_body d⟩
    revert ih_bindings
    induction bindings generalizing anns with
    | nil => intro _; cases anns <;> rfl
    | cons hd tl ih =>
      intro ih_bindings
      cases anns with
      | nil =>
        simp only [RecGroup.openTyVarsAux, RecGroup.substTyFvar, List.map_nil, List.cons.injEq]
        exact ⟨ih_bindings hd List.mem_cons_self d,
          ih [] (fun e he => ih_bindings e (List.mem_cons_of_mem _ he))⟩
      | cons a as =>
        cases a with
        | none =>
          simp only [RecGroup.openTyVarsAux, RecGroup.substTyFvar, List.map_cons,
            Option.map_none, RecAnn.params, Nat.add_zero, List.cons.injEq]
          exact ⟨ih_bindings hd List.mem_cons_self d,
            ih as (fun e he => ih_bindings e (List.mem_cons_of_mem _ he))⟩
        | some σ =>
          simp only [RecGroup.openTyVarsAux, RecGroup.substTyFvar, List.map_cons,
            Option.map_some, RecAnn.params, PolyTy.substFvar, List.cons.injEq]
          exact ⟨ih_bindings hd List.mem_cons_self (d + σ.paramCount),
            ih as (fun e he => ih_bindings e (List.mem_cons_of_mem _ he))⟩

/-- `substTyFvar` commutes with the top-level `Expr.openTyVars`. -/
theorem Expr.substTyFvar_openTyVars
    {Z : Nat} {U : Ty} {Xs : List Nat} {e : Expr}
    (h_lc : Ty.IsLC U) (h_Z : Z ∉ Xs) :
    (e.openTyVars Xs).substTyFvar Z U = (e.substTyFvar Z U).openTyVars Xs := by
  unfold Expr.openTyVars
  exact Expr.substTyFvar_openTyVarsAux h_lc h_Z e 0

/-- `substTyFvar` commutes with `openBoundTyVars` (the `let`-rule opener),
    threading the substitution through the annotation. -/
theorem Expr.substTyFvar_openBoundTyVars
    {Z : Nat} {U : Ty} {Xs : List Nat} {ann : Option PolyTy} {e : Expr}
    (h_lc : Ty.IsLC U) (h_Z : Z ∉ Xs) :
    (Expr.openBoundTyVars ann Xs e).substTyFvar Z U
      = Expr.openBoundTyVars (ann.map (PolyTy.substFvar Z U)) Xs (e.substTyFvar Z U) := by
  cases ann with
  | none => rfl
  | some σ =>
    simp only [Expr.openBoundTyVars, Option.map_some]
    exact Expr.substTyFvar_openTyVars h_lc h_Z

/-- `shiftFrom` (a term-variable renumbering) commutes with `openTyVarsAux`
    (opening scoped type variables in annotations): they touch disjoint parts of
    a term, so the order is irrelevant. Needed for `weaken_env`'s `letIn`
    cofinite case (the opened bound expression must be weakened). -/
theorem Expr.shiftFrom_openTyVarsAux {Xs : List Nat} (n : Nat) :
    ∀ (e : Expr) (d k : Nat),
      (e.openTyVarsAux d Xs).shiftFrom k n = (e.shiftFrom k n).openTyVarsAux d Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d k; rfl
  | primBinOp op => intro d k; rfl
  | app f inp ih_f ih_i =>
    intro d k; simp only [Expr.openTyVarsAux, Expr.shiftFrom]; rw [ih_f d k, ih_i d k]
  | lambda ann body ih =>
    intro d k; simp only [Expr.openTyVarsAux, Expr.shiftFrom]; rw [ih d (k + 1)]
  | letIn ann be body ih_be ih_body =>
    intro d k
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.shiftFrom]; rw [ih_be d k, ih_body d (k + 1)]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.shiftFrom]
      rw [ih_be (d + σ.paramCount) k, ih_body d (k + 1)]
  | var m => intro d k; simp only [Expr.openTyVarsAux, Expr.shiftFrom]; split <;> rfl
  | ctor nm => intro d k; rfl
  | match_ scrut branches ih_scrut ih_branches =>
    intro d k
    simp only [Expr.openTyVarsAux, Expr.shiftFrom, Expr.match_.injEq]
    refine ⟨ih_scrut d k, ?_⟩
    revert ih_branches
    induction branches with
    | nil => intro _; rfl
    | cons hd tl ih_tl =>
      intro ih_branches
      obtain ⟨pat, body⟩ := hd
      simp only [BranchList.openTyVarsAux, BranchList.shiftFrom]
      rw [ih_branches pat body List.mem_cons_self d (k + pat.bindCount),
          ih_tl (fun pat' body' hm => ih_branches pat' body' (List.mem_cons_of_mem _ hm))]
  | letRec anns bindings body ih_bindings ih_body =>
    intro d k
    simp only [Expr.openTyVarsAux, Expr.shiftFrom, RecGroup.openTyVarsAux_length]
    rw [Expr.letRec.injEq]
    refine ⟨rfl, ?_, ih_body d (k + bindings.length)⟩
    generalize k + bindings.length = m
    revert ih_bindings
    induction bindings generalizing anns with
    | nil => intro _; cases anns <;> rfl
    | cons hd tl ih =>
      intro ih_bindings
      cases anns with
      | nil =>
        simp only [RecGroup.openTyVarsAux, RecGroup.shiftFrom, List.cons.injEq]
        exact ⟨ih_bindings hd List.mem_cons_self d m,
          ih [] (fun e he => ih_bindings e (List.mem_cons_of_mem _ he))⟩
      | cons a as =>
        simp only [RecGroup.openTyVarsAux, RecGroup.shiftFrom, List.cons.injEq]
        exact ⟨ih_bindings hd List.mem_cons_self (d + RecAnn.params a) m,
          ih as (fun e he => ih_bindings e (List.mem_cons_of_mem _ he))⟩

/-- `shiftFrom` commutes with the top-level `Expr.openTyVars`. -/
theorem Expr.shiftFrom_openTyVars {Xs : List Nat} {e : Expr} (k n : Nat) :
    (e.openTyVars Xs).shiftFrom k n = (e.shiftFrom k n).openTyVars Xs := by
  unfold Expr.openTyVars
  exact Expr.shiftFrom_openTyVarsAux n e 0 k

/-- `shiftFrom` commutes with `openBoundTyVars` (the `let`-rule opener). The
    annotation is untouched by `shiftFrom`. -/
theorem Expr.shiftFrom_openBoundTyVars {ann : Option PolyTy} {Xs : List Nat} {e : Expr}
    (k n : Nat) :
    (Expr.openBoundTyVars ann Xs e).shiftFrom k n
      = Expr.openBoundTyVars ann Xs (e.shiftFrom k n) := by
  cases ann with
  | none => rfl
  | some σ =>
    simp only [Expr.openBoundTyVars]
    exact Expr.shiftFrom_openTyVars k n

/-- Free vars of a list of types (used in `openWith_eq_substFvars_openVars`'s
    freshness condition). -/
def Ty.freeVarsList : List Ty → List Nat
  | []       => []
  | hd :: tl => (hd.freeVars ++ Ty.freeVarsList tl).dedup

/-! #### `substFvars` distribution + key lemmas (toward `typ_substs_intro`). -/

theorem TyList.substFvar_eq_map {Z : Nat} {U : Ty} {tys : List Ty} :
    TyList.substFvar Z U tys = tys.map (Ty.substFvar Z U) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp only [TyList.substFvar, List.map_cons, ih]

theorem TyList.instantiate_eq_map {σ : Nat → Ty} {tys : List Ty} :
    TyList.instantiate σ tys = tys.map (Ty.instantiate σ) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp only [TyList.instantiate, List.map_cons, ih]

theorem Ty.substFvars_prim {pairs : List (Nat × Ty)} {p : PrimTy} :
    Ty.substFvars pairs (.prim p) = .prim p := by
  induction pairs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simpa only [Ty.substFvars, Ty.substFvar] using ih

theorem Ty.substFvars_bvar {pairs : List (Nat × Ty)} {i : Nat} :
    Ty.substFvars pairs (.bvar i) = .bvar i := by
  induction pairs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simpa only [Ty.substFvars, Ty.substFvar] using ih

theorem Ty.substFvars_arrow {pairs : List (Nat × Ty)} {a b : Ty} :
    Ty.substFvars pairs (.arrow a b)
      = .arrow (Ty.substFvars pairs a) (Ty.substFvars pairs b) := by
  induction pairs generalizing a b with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simpa only [Ty.substFvars, Ty.substFvar] using ih

theorem Ty.substFvars_customTy {pairs : List (Nat × Ty)} {nm : TyName} {tys : List Ty} :
    Ty.substFvars pairs (.customTy nm tys)
      = .customTy nm (tys.map (Ty.substFvars pairs)) := by
  induction pairs generalizing tys with
  | nil => simp only [Ty.substFvars, List.map_id_fun', id_eq]
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Ty.substFvars, Ty.substFvar, TyList.substFvar_eq_map]
    rw [ih, List.map_map]
    rfl

theorem Ty.substFvars_bl {pairs : List (Nat × Ty)} {lo hi : FHM.Bounds.CountSlot} {e : Ty} :
    Ty.substFvars pairs (.bl lo hi e) = .bl lo hi (Ty.substFvars pairs e) := by
  induction pairs generalizing e with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simpa only [Ty.substFvars, Ty.substFvar] using ih

/-- Free vars of a single type are contained in the free vars of any list
    containing it (`Ty.freeVarsList` flavour, used for the `Vs` freshness). -/
private theorem Ty.freeVars_subset_freeVarsList {V : Ty} {Vs : List Ty}
    (h : V ∈ Vs) : ∀ x ∈ V.freeVars, x ∈ Ty.freeVarsList Vs := by
  induction Vs with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    intro x hx
    simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append]
    cases h with
    | head _ => exact .inl hx
    | tail _ h' => exact .inr (ih h' x hx)

/-- Same, but for the private `TyList.freeVars` used inside `(customTy _ _).freeVars`. -/
theorem TyList.mem_freeVars_of_mem {t : Ty} {tys : List Ty} {x : Nat}
    (ht : t ∈ tys) (hx : x ∈ t.freeVars) : x ∈ TyList.freeVars tys := by
  induction tys with
  | nil => exact absurd ht List.not_mem_nil
  | cons hd tl ih =>
    simp only [TyList.freeVars, List.mem_dedup, List.mem_append]
    cases ht with
    | head _ => exact .inl hx
    | tail _ h' => exact .inr (ih h')

/-- Substituting a list of `(key, value)` pairs none of whose keys occur in
    `ty` leaves `ty` unchanged. -/
theorem Ty.substFvars_eq_self_of_no_key {pairs : List (Nat × Ty)} {ty : Ty}
    (h : ∀ p ∈ pairs, p.1 ∉ ty.freeVars) :
    Ty.substFvars pairs ty = ty := by
  induction pairs generalizing ty with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    have hZ : Z ∉ ty.freeVars := h (Z, U) List.mem_cons_self
    simp only [Ty.substFvars]
    rw [Ty.substFvar_fresh hZ]
    exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-- The key lemma for the `bvar` case of `typ_substs_intro`: substituting the
    zipped `(Xs, Vs)` pairs into `fvar x` (where `x = Xs[i]`, `v = Vs[i]`)
    yields `v`. The first `i` substitutions don't fire (distinct keys, `Xs`
    nodup); the `i`-th fires; later ones don't touch `v` (`Xs` fresh for `Vs`). -/
theorem Ty.substFvars_zip_fvar_eq {Xs : List Nat} {Vs : List Ty}
    {i : Nat} {x : Nat} {v : Ty}
    (h_len : Vs.length = Xs.length)
    (h_nodup : Xs.Nodup)
    (h_fresh : ∀ X ∈ Xs, X ∉ Ty.freeVarsList Vs)
    (hx : Xs[i]? = some x)
    (hv : Vs[i]? = some v) :
    Ty.substFvars (Xs.zip Vs) (.fvar x) = v := by
  induction Xs generalizing Vs i x v with
  | nil => simp at hx
  | cons X0 Xs' ih =>
    cases Vs with
    | nil => simp at h_len
    | cons V0 Vs' =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hv
        -- hx : X0 = x, hv : V0 = v
        simp only [List.zip_cons_cons, Ty.substFvars]
        rw [← hx, show Ty.substFvar X0 V0 (.fvar X0) = V0 by simp [Ty.substFvar], ← hv]
        -- substFvars (Xs'.zip Vs') V0 = V0: no key (∈ Xs') touches V0's fvars
        apply Ty.substFvars_eq_self_of_no_key
        intro p hp hcontra
        have hp1 : p.1 ∈ Xs' := (List.of_mem_zip hp).1
        refine h_fresh p.1 (List.mem_cons_of_mem _ hp1) ?_
        exact Ty.freeVars_subset_freeVarsList List.mem_cons_self p.1 hcontra
      | succ k =>
        simp only [List.getElem?_cons_succ] at hx hv
        have h_X0_notin : X0 ∉ Xs' := (List.nodup_cons.mp h_nodup).1
        have h_x_mem : x ∈ Xs' := List.mem_of_getElem? hx
        have h_ne : x ≠ X0 := fun h => h_X0_notin (h ▸ h_x_mem)
        have h_len' : Vs'.length = Xs'.length := by
          simp only [List.length_cons] at h_len; omega
        have h_fresh' : ∀ X ∈ Xs', X ∉ Ty.freeVarsList Vs' := by
          intro X hX hc
          refine h_fresh X (List.mem_cons_of_mem _ hX) ?_
          simp only [Ty.freeVarsList, List.mem_dedup, List.mem_append]
          exact .inr hc
        simp only [List.zip_cons_cons, Ty.substFvars]
        rw [show Ty.substFvar X0 V0 (.fvar x) = .fvar x by simp [Ty.substFvar, h_ne]]
        exact ih h_len' (List.nodup_cons.mp h_nodup).2 h_fresh' hx hv

/-- The "rename-open" intro lemma — Chargueraud's `typ_substs_intro`.
    Opening `ty` with `Vs` factors through opening with fresh `Xs` followed
    by substituting each `Xi` by the corresponding `Vi`.

    Crucial freshness: `Xs` must be disjoint not only from `ty.freeVars` but
    also from each `Vi.freeVars` — otherwise iterated substitution can
    "double-substitute" (substituting `X₀` into `V₁` if `X₀ ∈ V₁.freeVars`).
    My initial sketch had this incomplete; restored per Chargueraud's actual
    statement. -/
theorem Ty.openWith_eq_substFvars_openVars
    {ty : Ty} {Vs : List Ty} {Xs : List Nat}
    (h_lc_Vs : Ty.AreLC Xs.length Vs)
    (h_Xs_nodup : Xs.Nodup)
    (h_Xs_fresh_ty : ∀ X ∈ Xs, X ∉ ty.freeVars)
    (h_Xs_fresh_Vs : ∀ X ∈ Xs, X ∉ Ty.freeVarsList Vs) :
    Ty.openWith Vs ty
      = Ty.substFvars (Xs.zip Vs) (Ty.openVars Xs ty) := by
  obtain ⟨h_len, _⟩ := h_lc_Vs
  unfold Ty.openWith Ty.openVars
  induction ty using Ty.rec_strong with
  | prim _ =>
    simp only [Ty.instantiate]
    exact (Ty.substFvars_prim).symm
  | arrow a b ih_a ih_b =>
    simp only [Ty.instantiate]
    rw [Ty.substFvars_arrow]
    have ha : ∀ X ∈ Xs, X ∉ a.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
    have hb : ∀ X ∈ Xs, X ∉ b.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
    rw [ih_a ha, ih_b hb]
  | bvar i =>
    simp only [Ty.instantiate]
    by_cases h_i : i < Xs.length
    · -- in range: openVars → fvar Xs[i], openWith → Vs[i]
      obtain ⟨x, hx⟩ : ∃ x, Xs[i]? = some x := ⟨_, List.getElem?_eq_getElem h_i⟩
      obtain ⟨v, hv⟩ : ∃ v, Vs[i]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [hx, hv]
      simp only [Option.getD, Option.elim]
      exact (Ty.substFvars_zip_fvar_eq h_len h_Xs_nodup h_Xs_fresh_Vs hx hv).symm
    · -- out of range: both sides are bvar i
      have hXi : Xs[i]? = none := List.getElem?_eq_none (by omega)
      have hVi : Vs[i]? = none := List.getElem?_eq_none (by omega)
      rw [hXi, hVi]
      simp only [Option.getD, Option.elim]
      exact (Ty.substFvars_bvar).symm
  | fvar n =>
    simp only [Ty.instantiate]
    -- n ∉ Xs (from freshness), so no substitution fires
    have h_n_notin : n ∉ Xs := by
      intro hn
      exact h_Xs_fresh_ty n hn (by simp [Ty.freeVars])
    refine (Ty.substFvars_eq_self_of_no_key ?_).symm
    intro p hp hc
    -- p.1 ∈ Xs and p.1 ∈ (fvar n).freeVars = [n] ⇒ p.1 = n ⇒ n ∈ Xs, contradiction
    have hp1 : p.1 ∈ Xs := (List.of_mem_zip hp).1
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact h_n_notin (hc ▸ hp1)
  | customTy nm tys ih =>
    simp only [Ty.instantiate]
    rw [TyList.instantiate_eq_map, TyList.instantiate_eq_map, Ty.substFvars_customTy,
        List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    have ht_fresh : ∀ X ∈ Xs, X ∉ t.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (TyList.mem_freeVars_of_mem ht hc)
    simpa using ih t ht ht_fresh
  | bl lo hi e ih =>
    simp only [Ty.instantiate]
    rw [Ty.substFvars_bl]
    have he : ∀ X ∈ Xs, X ∉ e.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (by simp only [Ty.freeVars]; exact hc)
    rw [ih he]

/-! ### `openVars` / `closeOver` round-trip lemmas (copied from `InferW`)

These pure `Ty`-level lemmas about `Ty.openVars`, `Ty.openWith`, `Ty.closeOver`,
`Ty.substFvars`, and `Ty.freeVars` were originally developed in `InferW` but
depend only on Core definitions, so they live here. -/

theorem Ty.openVars_arrow {Xs : List Nat} {a b : Ty} :
    Ty.openVars Xs (.arrow a b) = .arrow (Ty.openVars Xs a) (Ty.openVars Xs b) := rfl

theorem Ty.openVars_customTy {Xs : List Nat} {nm : TyName} {tys : List Ty} :
    Ty.openVars Xs (.customTy nm tys) = .customTy nm (tys.map (Ty.openVars Xs)) := by
  unfold Ty.openVars
  simp only [Ty.instantiate, TyList.instantiate_eq_map]

theorem Ty.openVars_bl {Xs : List Nat} {lo hi : FHM.Bounds.CountSlot} {e : Ty} :
    Ty.openVars Xs (.bl lo hi e) = .bl lo hi (Ty.openVars Xs e) := rfl

/-- Opening with fresh *names* `Xs` is opening with those names as `fvar` types. -/
theorem Ty.openVars_eq_openWith {Xs : List Nat} {ty : Ty} :
    Ty.openVars Xs ty = Ty.openWith (Xs.map (Ty.fvar ·)) ty := by
  unfold Ty.openVars Ty.openWith
  congr 1
  funext i
  rcases h : Xs[i]? with _ | x
  · simp [h]
  · simp [h, List.getElem?_map]

/-- `idxOf?` pinpoints the element: if it returns index `i`, then `l[i]? = a`. -/
private theorem List.getElem?_of_idxOf? {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} {a : α} {i : Nat} (h : l.idxOf? a = some i) : l[i]? = some a := by
  induction l generalizing i with
  | nil => simp [List.idxOf?_nil] at h
  | cons x xs ih =>
    rw [List.idxOf?_cons] at h
    split at h
    · rename_i hxa
      simp only [Option.some.injEq] at h
      subst h
      simp [eq_of_beq hxa]
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      simpa using ih hj

private theorem TyList.closeOver_eq_map (gs : List Nat) (tys : List Ty) :
    TyList.closeOver gs tys = tys.map (Ty.closeOver gs) := by
  induction tys with
  | nil => rfl
  | cons hd tl ih => simp [TyList.closeOver, ih]

/-- Closing over `gs` then opening with the *same* `gs` is the identity on an LC
    type (`gs` nodup ⇒ each closed var reopens to itself). -/
theorem Ty.openVars_closeOver_self {gs : List Nat} :
    ∀ {τ : Ty}, τ.IsLC → Ty.openVars gs (Ty.closeOver gs τ) = τ := by
  intro τ hτ
  induction τ using Ty.rec_strong with
  | prim p => rfl
  | bvar i => cases hτ with | bvar h => omega
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | none => simp [Ty.openVars, Ty.instantiate]
    | some i =>
      have hgi : gs[i]? = some n := List.getElem?_of_idxOf? h_idx
      simp [Ty.openVars, Ty.instantiate, hgi]
  | arrow a b iha ihb =>
    cases hτ with | arrow ha hb => simp only [Ty.closeOver, Ty.openVars_arrow, iha ha, ihb hb]
  | customTy nm tys ih =>
    cases hτ with
    | customTy hall =>
      simp only [Ty.closeOver, TyList.closeOver_eq_map, Ty.openVars_customTy, List.map_map]
      apply congrArg (Ty.customTy nm)
      conv_rhs => rw [← List.map_id tys]
      apply List.map_congr_left
      intro t ht
      exact ih t ht (hall t ht)
  | bl lo hi e ih =>
    cases hτ with
    | bl he =>
      simp only [Ty.closeOver, Ty.openVars_bl, ih he]

/-- The free vars of a list of `fvar`s are exactly the names. -/
theorem Ty.mem_freeVarsList_map_fvar {Xs : List Nat} {g : Nat} :
    g ∈ Ty.freeVarsList (Xs.map (Ty.fvar ·)) ↔ g ∈ Xs := by
  induction Xs with
  | nil => simp [Ty.freeVarsList]
  | cons x xs ih =>
    simp [Ty.freeVarsList, Ty.freeVars, ih]

/-- A closed-over var no longer occurs free. -/
theorem Ty.not_mem_closeOver_freeVars {gs : List Nat} {g : Nat} (hg : g ∈ gs) :
    ∀ {τ : Ty}, g ∉ (Ty.closeOver gs τ).freeVars := by
  intro τ
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.freeVars]
  | bvar i => simp [Ty.closeOver, Ty.freeVars]
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | none =>
      have hn : n ∉ gs := List.idxOf?_eq_none_iff.mp h_idx
      simp only [Ty.freeVars, List.mem_singleton]
      intro hgn; exact hn (hgn ▸ hg)
    | some i => simp [Ty.freeVars]
  | arrow a b iha ihb => simp [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.closeOver, Ty.freeVars, TyList.closeOver_eq_map]
    rw [TyList.not_mem_freeVars_iff]
    intro t' ht'
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ih t ht
  | bl lo hi e ih =>
    simp only [Ty.closeOver, Ty.freeVars]
    exact ih

/-- The full round-trip: closing over `gs` then opening with fresh `Xs` renames
    each `gs[i]` to `Xs[i]`. -/
theorem Ty.openVars_closeOver_rename {gs Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) (h_gs_nodup : gs.Nodup) (h_len : Xs.length = gs.length)
    (h_disj : ∀ g ∈ gs, g ∉ Xs) :
    Ty.openVars Xs (Ty.closeOver gs τ)
      = Ty.substFvars (gs.zip (Xs.map (Ty.fvar ·))) τ := by
  rw [Ty.openVars_eq_openWith,
    Ty.openWith_eq_substFvars_openVars (Xs := gs) (Vs := Xs.map (Ty.fvar ·))
      ⟨by simp [h_len], fun V hV => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp hV; exact .fvar⟩
      h_gs_nodup
      (fun g hg => Ty.not_mem_closeOver_freeVars hg)
      (fun g hg hc => h_disj g hg (Ty.mem_freeVarsList_map_fvar.mp hc)),
    Ty.openVars_closeOver_self hτ]

/-- For a nodup list, `idxOf?` of the element at index `i` is `some i`. -/
private theorem List.idxOf?_getElem_self {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) :
    l.idxOf? l[i] = some i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    cases i with
    | zero => simp [List.idxOf?_cons]
    | succ j =>
      have hj : j < xs.length := by simpa using hi
      have hmem : xs[j] ∈ xs := List.getElem_mem hj
      have hxne : (x == xs[j]) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h; exact hnd.1 (h ▸ hmem)
      rw [List.getElem_cons_succ, List.idxOf?_cons, hxne]
      simp [ih hnd.2 hj]

/-- Open-then-close round-trip: closing the just-opened fresh names recovers the
    scheme body. (Converse of `Ty.openVars_closeOver_self`.) -/
theorem Ty.closeOver_openVars_self {Xs : List Nat} {ty : Ty}
    (hnodup : Xs.Nodup) (hbv : ContainsBvarsUpTo Xs.length ty)
    (hfresh : ∀ x ∈ Xs, x ∉ ty.freeVars) :
    Ty.closeOver Xs (Ty.openVars Xs ty) = ty := by
  induction ty using Ty.rec_strong with
  | prim p => rfl
  | bvar i =>
    cases hbv with
    | bvar hlt =>
      simp only [Ty.openVars, Ty.instantiate, List.getElem?_eq_getElem hlt, Option.elim_some]
      rw [Ty.closeOver.eq_6, List.idxOf?_getElem_self hnodup hlt]
  | fvar n =>
    have hn : n ∉ Xs := fun h => hfresh n h (by simp [Ty.freeVars])
    simp only [Ty.openVars, Ty.instantiate]
    rw [Ty.closeOver.eq_6, List.idxOf?_eq_none_iff.mpr hn]
  | arrow a b iha ihb =>
    cases hbv with
    | arrow hba hbb =>
      have hfa : ∀ x ∈ Xs, x ∉ a.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inl hc)))
      have hfb : ∀ x ∈ Xs, x ∉ b.freeVars := fun x hx hc =>
        hfresh x hx (List.mem_dedup.mpr (List.mem_append.mpr (Or.inr hc)))
      simp only [Ty.openVars_arrow, Ty.closeOver, iha hba hfa, ihb hbb hfb]
  | customTy nm tys ih =>
    cases hbv with
    | customTy hball =>
      simp only [Ty.openVars_customTy, Ty.closeOver, TyList.closeOver_eq_map, List.map_map]
      apply congrArg (Ty.customTy nm)
      conv_rhs => rw [← List.map_id tys]
      apply List.map_congr_left
      intro t ht
      exact ih t ht (hball t ht)
        (fun x hx hc => hfresh x hx (TyList.mem_freeVars_of_mem ht hc))
  | bl lo hi e ih =>
    cases hbv with
    | bl he =>
      have hf : ∀ x ∈ Xs, x ∉ e.freeVars := fun x hx hc =>
        hfresh x hx (by simp only [Ty.freeVars]; exact hc)
      simp only [Ty.openVars_bl, Ty.closeOver, ih he hf]

/-! ### `letRec` generalisation helpers: `Ty.renameG`, `Ty.genFilter`,
    `PolyTy.genGroup` (pure `Ty`/`PolyTy`-level lemmas). -/

/-- Membership in `TyList.freeVars` is membership in some element's free vars. -/
theorem TyList.mem_freeVars_iff {g : Nat} {tys : List Ty} :
    g ∈ TyList.freeVars tys ↔ ∃ t ∈ tys, g ∈ t.freeVars := by
  induction tys with
  | nil => simp [TyList.freeVars]
  | cons hd tl ih =>
    constructor
    · intro h
      simp only [TyList.freeVars, List.mem_dedup, List.mem_append] at h
      rcases h with h | h
      · exact ⟨hd, List.mem_cons_self, h⟩
      · obtain ⟨t, ht, hg⟩ := ih.mp h
        exact ⟨t, List.mem_cons_of_mem _ ht, hg⟩
    · rintro ⟨t, ht, hg⟩
      simp only [TyList.freeVars, List.mem_dedup, List.mem_append]
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact .inl hg
      · exact .inr (ih.mpr ⟨t, ht', hg⟩)

/-- **Lemma 1.** `closeOver` never *introduces* a free variable: every free var
    of `closeOver gs τ` was already free in `τ`. -/
theorem Ty.freeVars_closeOver_subset {gs : List Nat} {τ : Ty} {g : Nat} :
    g ∈ (Ty.closeOver gs τ).freeVars → g ∈ τ.freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.freeVars]
  | bvar i => simp [Ty.closeOver, Ty.freeVars]
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | some i => simp [Ty.freeVars]
    | none => simp [Ty.freeVars]
  | arrow a b iha ihb =>
    intro h
    simp only [Ty.closeOver, Ty.freeVars, List.mem_dedup, List.mem_append] at h ⊢
    exact h.imp iha ihb
  | customTy nm tys ih =>
    intro h
    simp only [Ty.closeOver, Ty.freeVars, TyList.closeOver_eq_map] at h ⊢
    rw [TyList.mem_freeVars_iff] at h ⊢
    obtain ⟨t', ht', hg⟩ := h
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    exact ⟨t, ht, ih t ht hg⟩
  | bl lo hi e ih =>
    intro h
    simp only [Ty.closeOver, Ty.freeVars] at h ⊢
    exact ih h

/-- **Lemma 2.** Closing over the *renamed* gen-vars `gs'` after renaming
    `gs ↦ gs'` recovers closing over the original `gs`: `closeOver` is invariant
    under freshening of the closed-over variables. -/
theorem Ty.closeOver_rename {gs gs' : List Nat} {τ : Ty}
    (hτ : τ.IsLC) (hlen : gs'.length = gs.length) (hgs : gs.Nodup) (hgs' : gs'.Nodup)
    (hdisj : ∀ g ∈ gs, g ∉ gs') (hfresh : ∀ g' ∈ gs', g' ∉ τ.freeVars) :
    Ty.closeOver gs' (Ty.substFvars (gs.zip (gs'.map (Ty.fvar ·))) τ)
      = Ty.closeOver gs τ := by
  rw [← Ty.openVars_closeOver_rename hτ hgs hlen hdisj]
  exact Ty.closeOver_openVars_self hgs'
    (by rw [hlen]; exact Ty.closeOver_preserves_bvars hτ)
    (fun g' hg' hc => hfresh g' hg' (Ty.freeVars_closeOver_subset hc))

/-- Closing over variables none of which occur free in `τ` is the identity. -/
theorem Ty.closeOver_eq_self_of_fresh {gs : List Nat} {τ : Ty}
    (h : ∀ g ∈ gs, g ∉ τ.freeVars) : Ty.closeOver gs τ = τ := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver]
  | bvar i => simp [Ty.closeOver]
  | fvar n =>
    have hn : n ∉ gs := fun hmem => h n hmem (by simp [Ty.freeVars])
    rw [Ty.closeOver.eq_6, List.idxOf?_eq_none_iff.mpr hn]
  | arrow a b iha ihb =>
    have ha : ∀ g ∈ gs, g ∉ a.freeVars := fun g hg hc =>
      h g hg (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
    have hb : ∀ g ∈ gs, g ∉ b.freeVars := fun g hg hc =>
      h g hg (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
    simp only [Ty.closeOver, iha ha, ihb hb]
  | customTy nm tys ih =>
    simp only [Ty.closeOver, TyList.closeOver_eq_map]
    apply congrArg (Ty.customTy nm)
    conv_rhs => rw [← List.map_id tys]
    apply List.map_congr_left
    intro t ht
    exact ih t ht (fun g hg hc => h g hg (TyList.mem_freeVars_of_mem ht hc))
  | bl lo hi e ih =>
    have he : ∀ g ∈ gs, g ∉ e.freeVars := fun g hg hc =>
      h g hg (by simp only [Ty.freeVars]; exact hc)
    simp only [Ty.closeOver, ih he]

/-- `substFvar` commutes with `closeOver` when the substituted variable `Z` and
    all free vars of the replacement `U` avoid the closed-over pool `gs`. -/
theorem Ty.substFvar_closeOver_comm {Z : Nat} {U : Ty} {gs : List Nat} {τ : Ty}
    (hZ : Z ∉ gs) (hU : ∀ g ∈ gs, g ∉ U.freeVars) :
    Ty.substFvar Z U (Ty.closeOver gs τ) = Ty.closeOver gs (Ty.substFvar Z U τ) := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.substFvar]
  | bvar i => simp [Ty.closeOver, Ty.substFvar]
  | fvar n =>
    rw [Ty.closeOver.eq_6]
    cases h_idx : gs.idxOf? n with
    | some i =>
      have hn : n ∈ gs := List.mem_of_getElem? (List.getElem?_of_idxOf? h_idx)
      have hnz : ¬ n = Z := fun h => hZ (h ▸ hn)
      simp only [Ty.substFvar, if_neg hnz, Ty.closeOver.eq_6, h_idx]
    | none =>
      have hn : n ∉ gs := List.idxOf?_eq_none_iff.mp h_idx
      by_cases hnz : n = Z
      · simp only [Ty.substFvar, if_pos hnz]
        exact (Ty.closeOver_eq_self_of_fresh hU).symm
      · simp only [Ty.substFvar, if_neg hnz, Ty.closeOver.eq_6, List.idxOf?_eq_none_iff.mpr hn]
  | arrow a b iha ihb =>
    simp only [Ty.closeOver, Ty.substFvar, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.closeOver, Ty.substFvar, TyList.closeOver_eq_map, TyList.substFvar_eq_map,
               List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    simpa using ih t ht
  | bl lo hi e ih =>
    simp only [Ty.closeOver, Ty.substFvar, ih]

/-- For `g ≠ Z` and `g ∉ U.freeVars`, substituting `Z ↦ U` neither adds nor
    removes `g` from the free-var set. -/
theorem Ty.mem_freeVars_substFvar_of {Z g : Nat} {U τ : Ty}
    (hgZ : g ≠ Z) (hgU : g ∉ U.freeVars) :
    g ∈ (Ty.substFvar Z U τ).freeVars ↔ g ∈ τ.freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.substFvar, Ty.freeVars]
  | bvar i => simp [Ty.substFvar, Ty.freeVars]
  | fvar m =>
    by_cases hm : m = Z
    · subst hm
      simp only [Ty.substFvar, Ty.freeVars, List.mem_singleton]
      exact ⟨fun h => absurd h hgU, fun h => absurd h hgZ⟩
    · simp [Ty.substFvar, Ty.freeVars, hm]
  | arrow a b iha ihb =>
    simp only [Ty.substFvar, Ty.freeVars, List.mem_dedup, List.mem_append]
    rw [iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.substFvar, Ty.freeVars, TyList.substFvar_eq_map, TyList.mem_freeVars_iff,
               List.mem_map]
    constructor
    · rintro ⟨t', ⟨t, ht, rfl⟩, hg⟩
      exact ⟨t, ht, (ih t ht).mp hg⟩
    · rintro ⟨t, ht, hg⟩
      exact ⟨Ty.substFvar Z U t, ⟨t, ht, rfl⟩, (ih t ht).mpr hg⟩
  | bl lo hi e ih =>
    simp only [Ty.substFvar, Ty.freeVars]
    exact ih

/-- `genFilter` is unaffected by substituting a variable `Z` that avoids the pool
    `G` with a `U` whose free vars also avoid `G`. -/
theorem Ty.genFilter_substFvar {Z : Nat} {U : Ty} {G : List Nat} {τ : Ty}
    (hZ : Z ∉ G) (hU : ∀ u ∈ U.freeVars, u ∉ G) :
    Ty.genFilter G τ = Ty.genFilter G (Ty.substFvar Z U τ) := by
  unfold Ty.genFilter
  apply List.filter_congr
  intro g hg
  have hgZ : g ≠ Z := fun h => hZ (h ▸ hg)
  have hgU : g ∉ U.freeVars := fun h => hU g h hg
  simp only [decide_eq_decide]
  exact (Ty.mem_freeVars_substFvar_of hgZ hgU).symm

/-- Elements of `genFilter G τ` come from `G`. -/
theorem Ty.mem_of_mem_genFilter {G : List Nat} {τ : Ty} {g : Nat}
    (h : g ∈ Ty.genFilter G τ) : g ∈ G := by
  unfold Ty.genFilter at h
  exact List.mem_of_mem_filter h

/-- **Lemma 3.** `genGroup` commutes with a free-var substitution `Z ↦ U` that
    avoids the gen-var pool `G` (so it neither touches the gen-vars nor reuses
    them). -/
theorem PolyTy.genGroup_substFvar {Z : Nat} {U : Ty} {G : List Nat} {τ : Ty}
    (hZ : Z ∉ G) (hU : ∀ u ∈ U.freeVars, u ∉ G) :
    PolyTy.substFvar Z U (PolyTy.genGroup G τ) = PolyTy.genGroup G (Ty.substFvar Z U τ) := by
  have hgf : Ty.genFilter G τ = Ty.genFilter G (Ty.substFvar Z U τ) :=
    Ty.genFilter_substFvar hZ hU
  have hZgf : Z ∉ Ty.genFilter G τ := fun h => hZ (Ty.mem_of_mem_genFilter h)
  have hUgf : ∀ g ∈ Ty.genFilter G τ, g ∉ U.freeVars :=
    fun g hg hc => hU g hc (Ty.mem_of_mem_genFilter hg)
  simp only [PolyTy.genGroup, PolyTy.substFvar]
  rw [← hgf, Ty.substFvar_closeOver_comm hZgf hUgf]


/-! #### Helpers for `genGroup` invariance under freshening the pool (Lemma 4). -/

/-- The free vars of `substFvars s τ` are exactly the free vars contributed by
    substituting `s` into each free var of `τ`. -/
theorem Ty.mem_freeVars_substFvars_image {s : List (Nat × Ty)} {τ : Ty} {v : Nat} :
    v ∈ (Ty.substFvars s τ).freeVars
      ↔ ∃ m ∈ τ.freeVars, v ∈ (Ty.substFvars s (Ty.fvar m)).freeVars := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.substFvars_prim, Ty.freeVars]
  | bvar i => simp [Ty.substFvars_bvar, Ty.freeVars]
  | fvar n =>
    simp only [Ty.freeVars, List.mem_singleton]
    constructor
    · intro h; exact ⟨n, rfl, h⟩
    · rintro ⟨m, rfl, h⟩; exact h
  | arrow a b iha ihb =>
    rw [Ty.substFvars_arrow]
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, iha, ihb]
    constructor
    · rintro (⟨m, hm, hv⟩ | ⟨m, hm, hv⟩)
      · exact ⟨m, .inl hm, hv⟩
      · exact ⟨m, .inr hm, hv⟩
    · rintro ⟨m, (hm | hm), hv⟩
      · exact .inl ⟨m, hm, hv⟩
      · exact .inr ⟨m, hm, hv⟩
  | customTy nm tys ih =>
    rw [Ty.substFvars_customTy]
    simp only [Ty.freeVars, TyList.mem_freeVars_iff, List.mem_map]
    constructor
    · rintro ⟨t', ⟨t, ht, rfl⟩, hv⟩
      obtain ⟨m, hm, hvm⟩ := (ih t ht).mp hv
      exact ⟨m, ⟨t, ht, hm⟩, hvm⟩
    · rintro ⟨m, ⟨t, ht, hm⟩, hvm⟩
      exact ⟨Ty.substFvars s t, ⟨t, ht, rfl⟩, (ih t ht).mpr ⟨m, hm, hvm⟩⟩
  | bl lo hi e ih =>
    rw [Ty.substFvars_bl]
    simp only [Ty.freeVars]
    exact ih

/-- Substituting the renaming `G ↦ W` into `fvar G[i]` yields `fvar W[i]`. -/
theorem Ty.substFvars_zip_fvar_renameG {G W : List Nat} {i a b : Nat}
    (hlen : W.length = G.length) (hG : G.Nodup) (hdisj : ∀ g ∈ G, g ∉ W)
    (hi : G[i]? = some a) (hi' : W[i]? = some b) :
    Ty.substFvars (G.zip (W.map (Ty.fvar ·))) (Ty.fvar a) = Ty.fvar b := by
  refine Ty.substFvars_zip_fvar_eq ?_ hG ?_ hi ?_
  · rw [List.length_map]; exact hlen
  · intro X hX hc
    exact hdisj X hX (Ty.mem_freeVarsList_map_fvar.mp hc)
  · simp [List.getElem?_map, hi']

/-- In a `Nodup` list, `getElem?` is injective on indices that hit `some a`. -/
theorem List.getElem?_inj_of_nodup {α : Type*} {l : List α} {i j : Nat} {a : α}
    (h : l.Nodup) (hi : l[i]? = some a) (hj : l[j]? = some a) : i = j := by
  obtain ⟨hil, hia⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hja⟩ := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj_iff h (hi := hil) (hj := hjl)).mp (hia.trans hja.symm)

/-- **Occurrence after renaming.** For the renaming `G ↦ W` (aligned index `i`),
    `W[i]` is free in `renameG G W τ` exactly when `G[i]` is free in `τ`. -/
theorem Ty.mem_freeVars_renameG_iff {G W : List Nat} {τ : Ty} {i a b : Nat}
    (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hdisj : ∀ g ∈ G, g ∉ W) (hfresh : ∀ w ∈ W, w ∉ τ.freeVars)
    (hi : G[i]? = some a) (hi' : W[i]? = some b) :
    b ∈ (Ty.renameG G W τ).freeVars ↔ a ∈ τ.freeVars := by
  unfold Ty.renameG
  rw [Ty.mem_freeVars_substFvars_image]
  constructor
  · rintro ⟨m, hm, hb⟩
    by_cases hmG : m ∈ G
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmG
      obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.mp hj
      have hjW : j < W.length := by omega
      have hwj : W[j]? = some W[j] := List.getElem?_eq_getElem hjW
      have hsub : Ty.substFvars (G.zip (W.map (Ty.fvar ·))) (Ty.fvar m) = Ty.fvar W[j] :=
        Ty.substFvars_zip_fvar_renameG hlen hG hdisj hj hwj
      rw [hsub] at hb
      simp only [Ty.freeVars, List.mem_singleton] at hb
      have hwjb : W[j]? = some b := by rw [hwj, hb]
      have hij : i = j := List.getElem?_inj_of_nodup hW hi' hwjb
      have hGj : G[j]? = some a := hij ▸ hi
      have ham : a = m := Option.some.inj (hGj.symm.trans hj)
      rw [ham]; exact hm
    · have hsub : Ty.substFvars (G.zip (W.map (Ty.fvar ·))) (Ty.fvar m) = Ty.fvar m := by
        apply Ty.substFvars_eq_self_of_no_key
        intro pr hpr hc
        simp only [Ty.freeVars, List.mem_singleton] at hc
        exact hmG (hc ▸ (List.of_mem_zip hpr).1)
      rw [hsub] at hb
      simp only [Ty.freeVars, List.mem_singleton] at hb
      have hbW : b ∈ W := List.mem_of_getElem? hi'
      subst hb
      exact absurd hm (hfresh b hbW)
  · intro ha
    refine ⟨a, ha, ?_⟩
    rw [Ty.substFvars_zip_fvar_renameG hlen hG hdisj hi hi']
    simp [Ty.freeVars]

/-- **Drop junk substitutions.** When the values' free vars avoid the keys (so no
    substitution reintroduces a key) and the keys are `Nodup`, applying `ps`
    equals applying only the pairs whose key occurs in `τ`. -/
theorem Ty.substFvars_filter_freeVars {ps : List (Nat × Ty)} {τ : Ty}
    (hkey : (ps.map Prod.fst).Nodup)
    (hval : ∀ p ∈ ps, ∀ k ∈ ps.map Prod.fst, k ∉ p.2.freeVars) :
    Ty.substFvars ps τ
      = Ty.substFvars (ps.filter (fun p => decide (p.1 ∈ τ.freeVars))) τ := by
  induction ps generalizing τ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hkey
    obtain ⟨hZ_notin, hkey_tl⟩ := hkey
    have hval_tl : ∀ p ∈ tl, ∀ k ∈ tl.map Prod.fst, k ∉ p.2.freeVars := fun p hp k hk =>
      hval p (List.mem_cons_of_mem _ hp) k (by simp only [List.map_cons, List.mem_cons]; exact .inr hk)
    have hval_head : ∀ k ∈ tl.map Prod.fst, k ∉ U.freeVars := fun k hk =>
      hval (Z, U) List.mem_cons_self k (by simp only [List.map_cons, List.mem_cons]; exact .inr hk)
    rw [List.filter_cons]
    split
    · rename_i hcond
      have hZτ : Z ∈ τ.freeVars := by simpa using hcond
      simp only [Ty.substFvars]
      rw [ih (τ := Ty.substFvar Z U τ) hkey_tl hval_tl]
      have hfeq : tl.filter (fun p => decide (p.1 ∈ (Ty.substFvar Z U τ).freeVars))
          = tl.filter (fun p => decide (p.1 ∈ τ.freeVars)) := by
        apply List.filter_congr
        intro p hp
        have hp1 : p.1 ∈ tl.map Prod.fst := List.mem_map.mpr ⟨p, hp, rfl⟩
        have hp1Z : p.1 ≠ Z := fun h => hZ_notin (h ▸ hp1)
        have hp1U : p.1 ∉ U.freeVars := hval_head p.1 hp1
        simp only [decide_eq_decide]
        exact Ty.mem_freeVars_substFvar_of hp1Z hp1U
      rw [hfeq]
    · rename_i hcond
      have hZτ : Z ∉ τ.freeVars := by simpa using hcond
      simp only [Ty.substFvars]
      rw [Ty.substFvar_fresh hZτ]
      exact ih (τ := τ) hkey_tl hval_tl

/-- The kept `G.zip W` pairs project (under aligned occurrence) to `genFilter G τ`
    and `genFilter W σ` respectively. -/
theorem Ty.genFilter_zip_proj {G W : List Nat} {τ σ : Ty}
    (hlen : W.length = G.length)
    (hOCC : ∀ p ∈ G.zip W, (p.2 ∈ σ.freeVars ↔ p.1 ∈ τ.freeVars)) :
    Ty.genFilter G τ = ((G.zip W).filter (fun p => decide (p.1 ∈ τ.freeVars))).map Prod.fst
    ∧ Ty.genFilter W σ = ((G.zip W).filter (fun p => decide (p.1 ∈ τ.freeVars))).map Prod.snd := by
  unfold Ty.genFilter
  induction G generalizing W with
  | nil =>
    cases W with
    | nil => exact ⟨rfl, rfl⟩
    | cons w wtl => simp at hlen
  | cons g gtl ih =>
    cases W with
    | nil => simp at hlen
    | cons w wtl =>
      have hlen' : wtl.length = gtl.length := by simpa using hlen
      have hiff : w ∈ σ.freeVars ↔ g ∈ τ.freeVars :=
        hOCC (g, w) (by rw [List.zip_cons_cons]; exact List.mem_cons_self)
      have hOCC_tl : ∀ p ∈ gtl.zip wtl, (p.2 ∈ σ.freeVars ↔ p.1 ∈ τ.freeVars) :=
        fun p hp => hOCC p (by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hp)
      obtain ⟨ih1, ih2⟩ := ih hlen' hOCC_tl
      rw [List.zip_cons_cons]
      by_cases hg : g ∈ τ.freeVars
      · have hw : w ∈ σ.freeVars := hiff.mpr hg
        simp [hg, hw, ih1, ih2]
      · have hw : w ∉ σ.freeVars := fun h => hg (hiff.mp h)
        simp [hg, hw, ih1, ih2]

/-- Filtering the renaming substitution (by occurrence in `τ`) is the same whether
    we filter the `(key, fvar)` list directly or filter `G.zip W` then attach `fvar`. -/
theorem List.filter_zip_map_fvar {G W : List Nat} {τ : Ty} :
    ((G.zip W).filter (fun p => decide (p.1 ∈ τ.freeVars))).map (fun p => (p.1, Ty.fvar p.2))
    = (G.zip (W.map (Ty.fvar ·))).filter (fun p => decide (p.1 ∈ τ.freeVars)) := by
  induction G generalizing W with
  | nil => rfl
  | cons g gtl ih =>
    cases W with
    | nil => rfl
    | cons w wtl =>
      rw [List.map_cons, List.zip_cons_cons, List.zip_cons_cons]
      by_cases hg : g ∈ τ.freeVars <;> simp [hg, ih]

/-- **Lemma 4.** `genGroup` is invariant under freshening the gen-var pool
    `G ↦ W` (renaming the monotype with the same fresh block). -/
theorem PolyTy.genGroup_renameG {G W : List Nat} {τ : Ty}
    (hτ : τ.IsLC) (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hdisj : ∀ g ∈ G, g ∉ W) (hfresh : ∀ w ∈ W, w ∉ τ.freeVars) :
    PolyTy.genGroup G τ = PolyTy.genGroup W (Ty.renameG G W τ) := by
  have hGW : G.length ≤ W.length := le_of_eq hlen.symm
  -- Per-pair occurrence equivalence (aligned index).
  have hOCC : ∀ p ∈ G.zip W,
      (p.2 ∈ (Ty.renameG G W τ).freeVars ↔ p.1 ∈ τ.freeVars) := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
    rw [List.getElem?_zip_eq_some] at hi
    obtain ⟨hiG, hiW⟩ := hi
    exact Ty.mem_freeVars_renameG_iff hlen hG hW hdisj hfresh hiG hiW
  obtain ⟨hAL1, hAL2⟩ := Ty.genFilter_zip_proj hlen hOCC
  have hlen' : (Ty.genFilter W (Ty.renameG G W τ)).length = (Ty.genFilter G τ).length := by
    rw [hAL1, hAL2, List.length_map, List.length_map]
  have hgsND : (Ty.genFilter G τ).Nodup := by unfold Ty.genFilter; exact hG.filter _
  have hgs'ND : (Ty.genFilter W (Ty.renameG G W τ)).Nodup := by
    unfold Ty.genFilter; exact hW.filter _
  have hdisj' : ∀ g ∈ Ty.genFilter G τ, g ∉ Ty.genFilter W (Ty.renameG G W τ) :=
    fun g hg hc => hdisj g (Ty.mem_of_mem_genFilter hg) (Ty.mem_of_mem_genFilter hc)
  have hfresh' : ∀ g' ∈ Ty.genFilter W (Ty.renameG G W τ), g' ∉ τ.freeVars :=
    fun g' hg' => hfresh g' (Ty.mem_of_mem_genFilter hg')
  -- The renaming substitution restricted to vars occurring in `τ`.
  have hkey : ((G.zip (W.map (Ty.fvar ·))).map Prod.fst).Nodup := by
    rw [List.map_fst_zip (by rw [List.length_map]; exact hGW)]; exact hG
  have hval : ∀ p ∈ G.zip (W.map (Ty.fvar ·)),
      ∀ k ∈ (G.zip (W.map (Ty.fvar ·))).map Prod.fst, k ∉ p.2.freeVars := by
    intro p hp k hk
    rw [List.map_fst_zip (by rw [List.length_map]; exact hGW)] at hk
    obtain ⟨w, hw, hpw⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← hpw]
    simp only [Ty.freeVars, List.mem_singleton]
    intro hkw; exact hdisj w (hkw ▸ hk) hw
  have hsubeq : (Ty.genFilter G τ).zip ((Ty.genFilter W (Ty.renameG G W τ)).map (Ty.fvar ·))
      = (G.zip (W.map (Ty.fvar ·))).filter (fun p => decide (p.1 ∈ τ.freeVars)) := by
    rw [hAL1, hAL2, List.map_map, List.zip_map']
    exact List.filter_zip_map_fvar
  have hAL3 : Ty.renameG G W τ
      = Ty.substFvars
          ((Ty.genFilter G τ).zip ((Ty.genFilter W (Ty.renameG G W τ)).map (Ty.fvar ·))) τ := by
    rw [hsubeq]
    unfold Ty.renameG
    exact Ty.substFvars_filter_freeVars hkey hval
  have hbody : Ty.closeOver (Ty.genFilter W (Ty.renameG G W τ)) (Ty.renameG G W τ)
      = Ty.closeOver (Ty.genFilter G τ) τ := by
    nth_rewrite 2 [hAL3]
    exact Ty.closeOver_rename hτ hlen' hgsND hgs'ND hdisj' hfresh'
  unfold PolyTy.genGroup
  rw [hlen', hbody]


/-- **Rename the opening (type level, depth-general).** Opening `t`'s scoped
    `bvar`s (offset `d`) at a fresh block `Ys`, then renaming `Ys ↦ Xs` (as
    `fvar`s), equals opening directly at `Xs`. The freshness side conditions
    (`Ys` nodup, disjoint from `t`'s pre-existing free vars and from `Xs`) ensure
    the rename only touches names introduced by the opening. This is the
    depth-general fact the term-level renamer below recurses with through nested
    schemes; `Ty.openWith_eq_substFvars_openVars` is essentially its `d = 0`
    converse. -/
theorem Ty.substFvars_zip_openVarsFrom {d : Nat} {t : Ty} {Ys Xs : List Nat}
    (h_len : Ys.length = Xs.length) (h_Ys_nodup : Ys.Nodup)
    (h_Ys_t : ∀ y ∈ Ys, y ∉ t.freeVars) (h_Ys_Xs : ∀ y ∈ Ys, y ∉ Xs) :
    Ty.substFvars (Ys.zip (Xs.map (Ty.fvar ·))) (Ty.openVarsFrom d Ys t)
      = Ty.openVarsFrom d Xs t := by
  have h_lenV : (Xs.map (Ty.fvar ·)).length = Ys.length := by
    rw [List.length_map, ← h_len]
  have h_freshV : ∀ Y ∈ Ys, Y ∉ Ty.freeVarsList (Xs.map (Ty.fvar ·)) := by
    intro Y hY hc
    refine h_Ys_Xs Y hY ?_
    clear hY h_len h_Ys_nodup h_Ys_t h_Ys_Xs h_lenV
    induction Xs with
    | nil => simp only [List.map_nil, Ty.freeVarsList] at hc; exact absurd hc List.not_mem_nil
    | cons x xs ih =>
      simp only [List.map_cons, Ty.freeVarsList, List.mem_dedup, List.mem_append] at hc
      cases hc with
      | inl h => simp only [Ty.freeVars, List.mem_singleton] at h; exact h ▸ List.mem_cons_self
      | inr h => exact List.mem_cons_of_mem _ (ih h)
  unfold Ty.openVarsFrom
  induction t using Ty.rec_strong with
  | prim p => simp only [Ty.instantiate, Ty.substFvars_prim]
  | bvar i =>
    simp only [Ty.instantiate]
    by_cases h_d : i < d
    · simp only [if_pos h_d, Ty.substFvars_bvar]
    · simp only [if_neg h_d]
      cases h_ys : Ys[i - d]? with
      | none =>
        have h_xs : Xs[i - d]? = none := by
          rw [List.getElem?_eq_none_iff] at h_ys ⊢; omega
        simp only [h_xs, Option.elim, Ty.substFvars_bvar]
      | some y =>
        have hlt : i - d < Ys.length := by
          obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.mp h_ys; exact h
        have h_xs : Xs[i - d]? = some Xs[i - d] := List.getElem?_eq_getElem (by omega)
        have hvx : (Xs.map (Ty.fvar ·))[i - d]? = some (Ty.fvar Xs[i - d]) := by
          rw [List.getElem?_map, h_xs]; rfl
        simp only [h_xs, Option.elim]
        exact Ty.substFvars_zip_fvar_eq h_lenV h_Ys_nodup h_freshV h_ys hvx
  | fvar n =>
    simp only [Ty.instantiate]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact h_Ys_t p.1 (List.of_mem_zip hp).1 (hc ▸ by simp [Ty.freeVars])
  | arrow a b iha ihb =>
    simp only [Ty.instantiate, Ty.substFvars_arrow]
    rw [iha (fun y hy hc => h_Ys_t y hy (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)),
        ihb (fun y hy hc => h_Ys_t y hy (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc))]
  | customTy nm tys ih =>
    simp only [Ty.instantiate, TyList.instantiate_eq_map, Ty.substFvars_customTy, List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    have ht_fresh : ∀ y ∈ Ys, y ∉ t.freeVars := fun y hy hc =>
      h_Ys_t y hy (by simp only [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hc)
    simpa using ih t ht ht_fresh
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Ty.substFvars_bl]
    have he : ∀ y ∈ Ys, y ∉ e.freeVars := fun y hy hc =>
      h_Ys_t y hy (by simp only [Ty.freeVars]; exact hc)
    rw [ih he]

/-- **Concrete-instantiation version** of `Ty.substFvars_zip_openVarsFrom`: opening
    at fresh `Ys` then substituting `Ys ↦ Vs` (arbitrary types) equals type-beta
    `openTyFrom d Vs`. This is the `Ty`-level engine for the term bridge
    `Expr.substTyFvars_zip_openTyVarsAux_concrete`. -/
theorem Ty.substFvars_zip_openVarsFrom_concrete {d : Nat} {t : Ty} {Ys : List Nat} {Vs : List Ty}
    (h_len : Vs.length = Ys.length) (h_Ys_nodup : Ys.Nodup)
    (h_Ys_t : ∀ y ∈ Ys, y ∉ t.freeVars) (h_Ys_Vs : ∀ y ∈ Ys, y ∉ Ty.freeVarsList Vs)
    (h_Vs_lc : ∀ V ∈ Vs, V.IsLC) :
    Ty.substFvars (Ys.zip Vs) (Ty.openVarsFrom d Ys t) = Ty.openTyFrom d Vs t := by
  unfold Ty.openVarsFrom Ty.openTyFrom
  induction t using Ty.rec_strong with
  | prim p => simp only [Ty.instantiate, Ty.substFvars_prim]
  | bvar i =>
    simp only [Ty.instantiate]
    by_cases h_d : i < d
    · simp only [if_pos h_d, Ty.substFvars_bvar]
    · simp only [if_neg h_d]
      cases h_ys : Ys[i - d]? with
      | none =>
        have h_vs : Vs[i - d]? = none := by
          rw [List.getElem?_eq_none_iff] at h_ys ⊢; omega
        simp only [Option.elim, h_vs, Option.map_none, Option.getD_none, Ty.substFvars_bvar]
      | some y =>
        have hlt : i - d < Ys.length := (List.getElem?_eq_some_iff.mp h_ys).1
        have h_vs : Vs[i - d]? = some Vs[i - d] := List.getElem?_eq_getElem (by omega)
        have h_lc : Ty.shiftBvarsBy d Vs[i - d] = Vs[i - d] := by
          unfold Ty.shiftBvarsBy
          exact Ty.instantiate_eq_self_of_lc (h_Vs_lc _ (List.getElem_mem _))
        simp only [Option.elim, h_vs, Option.map_some, Option.getD_some, h_lc]
        exact Ty.substFvars_zip_fvar_eq h_len h_Ys_nodup h_Ys_Vs h_ys h_vs
  | fvar n =>
    simp only [Ty.instantiate]
    apply Ty.substFvars_eq_self_of_no_key
    intro p hp hc
    simp only [Ty.freeVars, List.mem_singleton] at hc
    exact h_Ys_t p.1 (List.of_mem_zip hp).1 (hc ▸ by simp [Ty.freeVars])
  | arrow a b iha ihb =>
    simp only [Ty.instantiate, Ty.substFvars_arrow]
    rw [iha (fun y hy hc => h_Ys_t y hy (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)),
        ihb (fun y hy hc => h_Ys_t y hy (by
          simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc))]
  | customTy nm tys ih =>
    simp only [Ty.instantiate, TyList.instantiate_eq_map, Ty.substFvars_customTy, List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    have ht_fresh : ∀ y ∈ Ys, y ∉ t.freeVars := fun y hy hc =>
      h_Ys_t y hy (by simp only [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht hc)
    simpa using ih t ht ht_fresh
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Ty.substFvars_bl]
    have he : ∀ y ∈ Ys, y ∉ e.freeVars := fun y hy hc =>
      h_Ys_t y hy (by simp only [Ty.freeVars]; exact hc)
    rw [ih he]

/-! ### `substFvar` interaction with the typing-side predicates.

Helpers needed by `typ_subst_preservation`. -/

/-- `eraseBounds` commutes with a single fvar substitution (erase the replacement too).
    Used by residual dual-stack projections (Path R bridge), not by structural Pins. -/
theorem Ty.eraseBounds_substFvar (Z : Nat) (U : Ty) (τ : Ty) :
    Ty.eraseBounds (Ty.substFvar Z U τ) =
      Ty.substFvar Z (Ty.eraseBounds U) (Ty.eraseBounds τ) := by
  induction τ using Ty.rec_strong with
  | prim _ => rfl
  | arrow a b iha ihb =>
    simp only [Ty.substFvar, Ty.eraseBounds_arrow, iha, ihb]
  | bvar i => rfl
  | fvar n =>
    by_cases hn : n = Z
    · simp only [Ty.substFvar, if_pos hn, Ty.eraseBounds_fvar]
    · simp only [Ty.substFvar, if_neg hn, Ty.eraseBounds_fvar]
  | customTy nm tys ih =>
    simp only [Ty.substFvar, Ty.eraseBounds_customTy, TyList.substFvar_eq_map,
      TyList.eraseBounds_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left fun t ht => ih t ht
  | bl lo hi e ih =>
    simp only [Ty.substFvar, Ty.eraseBounds_bl, bareListTy, TyList.substFvar_eq_map,
      List.map_cons, List.map_nil, ih]

/-- Scheme form of `eraseBounds_substFvar` (paramCount unchanged by both ops). -/
theorem PolyTy.eraseBounds_substFvar (Z : Nat) (U : Ty) (σ : PolyTy) :
    PolyTy.eraseBounds (PolyTy.substFvar Z U σ) =
      PolyTy.substFvar Z (Ty.eraseBounds U) (PolyTy.eraseBounds σ) := by
  cases σ with
  | mk n b =>
    simp only [PolyTy.eraseBounds, PolyTy.substFvar, Ty.eraseBounds_substFvar]

/-- `substFvar` by an LC type preserves local-closedness. (The `bvar` case is
    vacuous: an LC type has no bvars.) -/
theorem Ty.IsLC.substFvar {Z : Nat} {U ty : Ty}
    (h_U : Ty.IsLC U) (h : Ty.IsLC ty) :
    Ty.IsLC (Ty.substFvar Z U ty) := by
  induction ty using Ty.rec_strong with
  | prim _ => exact .prim
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i => cases h with | bvar hlt => exact absurd hlt (by omega)
  | fvar m =>
    simp only [Ty.substFvar]
    by_cases hm : m = Z
    · simp only [if_pos hm]; exact h_U
    · simp only [if_neg hm]; exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.substFvar]
      apply ContainsBvarsUpTo.customTy
      rw [TyList.substFvar_eq_map]
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)
  | bl lo hi e ih =>
    cases h with
    | bl he =>
      simp only [Ty.substFvar]
      exact .bl (ih he)

/-- Instantiation is the identity on locally-closed types (reverse of
    `InstantiatesBy.eq_of_closed`): if `ty` has no bvars, it instantiates to
    itself under any `tyArgs`. -/
theorem InstantiatesBy.refl_of_closed {tyArgs : List Ty} {ty : Ty}
    (h : ContainsBvarsUpTo 0 ty) : InstantiatesBy tyArgs ty ty := by
  induction ty using Ty.rec_strong with
  | prim _ => exact .prim
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i => cases h with | bvar hlt => exact absurd hlt (by omega)
  | fvar n => exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      apply InstantiatesBy.customTy
      have aux : ∀ ts : List Ty, (∀ t ∈ ts, ContainsBvarsUpTo 0 t) →
          (∀ t ∈ ts, InstantiatesBy tyArgs t t) →
          List.Forall₂ (InstantiatesBy tyArgs) ts ts := by
        intro ts
        induction ts with
        | nil => intro _ _; exact .nil
        | cons hd tl ihts =>
          intro hall' hinst'
          exact .cons (hinst' hd List.mem_cons_self)
            (ihts (fun t ht => hall' t (List.mem_cons_of_mem _ ht))
                  (fun t ht => hinst' t (List.mem_cons_of_mem _ ht)))
      exact aux tys hall (fun t ht => ih t ht (hall t ht))
  | bl lo hi e ih =>
    cases h with
    | bl he => exact .bl (ih he)

/-- `substFvar` commutes with `InstantiatesBy` (when the replacement `U` is
    LC): substituting fvars then instantiating bvars equals instantiating
    bvars (with the substituted `tyArgs`) then substituting fvars. -/
theorem InstantiatesBy.substFvar {Z : Nat} {U : Ty}
    (h_U_lc : Ty.IsLC U) {ty1 ty2 : Ty} {tyArgs : List Ty}
    (h : InstantiatesBy tyArgs ty1 ty2) :
    InstantiatesBy (tyArgs.map (Ty.substFvar Z U))
      (Ty.substFvar Z U ty1) (Ty.substFvar Z U ty2) := by
  induction ty1 using Ty.rec_strong generalizing ty2 with
  | prim _ => cases h; exact .prim
  | arrow a b iha ihb =>
    cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    cases h with
    | bvar hsome =>
      simp only [Ty.substFvar]
      apply InstantiatesBy.bvar
      rw [List.getElem?_map, hsome]; rfl
  | fvar n =>
    cases h with
    | fvar =>
      by_cases hn : n = Z
      · simp only [Ty.substFvar, if_pos hn]
        exact InstantiatesBy.refl_of_closed h_U_lc
      · simp only [Ty.substFvar, if_neg hn]; exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hforall =>
      simp only [Ty.substFvar]
      rw [TyList.substFvar_eq_map, TyList.substFvar_eq_map]
      apply InstantiatesBy.customTy
      induction hforall with
      | nil => exact .nil
      | cons hhd htl ihtl =>
        rename_i hd_ty hd_it tl_tys tl_it
        refine .cons (ih hd_ty List.mem_cons_self hhd) ?_
        exact ihtl (fun t ht => ih t (List.mem_cons_of_mem _ ht))
  | bl lo hi e ih =>
    cases h with
    | bl he =>
      simp only [Ty.substFvar]
      exact .bl (ih he)

/-- `Env.substFvar` by a fresh `Z` is the identity. -/
theorem Env.substFvar_fresh {Z : Nat} {U : Ty} {env : Env}
    (h : Z ∉ env.freeVars) : env.substFvar Z U = env := by
  induction env with
  | nil => rfl
  | cons hd tl ih =>
    simp only [Env.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Env.substFvar, List.map_cons]
    have hd_eq : PolyTy.substFvar Z U hd = hd := by
      obtain ⟨pc, body⟩ := hd
      simp only [PolyTy.substFvar]
      rw [Ty.substFvar_fresh h.1]
    rw [hd_eq]
    have htl : Env.substFvar Z U tl = tl := ih h.2
    simp only [Env.substFvar] at htl
    rw [htl]

theorem Env.substFvar_append {Z : Nat} {U : Ty} {a b : Env} :
    Env.substFvar Z U (a ++ b) = Env.substFvar Z U a ++ Env.substFvar Z U b := by
  simp only [Env.substFvar, List.map_append]

/-- `ContainsBvarsUpTo` is monotone in the bound. -/
theorem ContainsBvarsUpTo.mono {m n : Nat} {ty : Ty} (hle : m ≤ n)
    (h : ContainsBvarsUpTo m ty) : ContainsBvarsUpTo n ty := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | fvar => exact .fvar
  | customTy _ ih => exact .customTy (fun t ht => ih t ht)
  | bl _ ih => exact .bl ih
  | bvar hlt => exact .bvar (by omega)

/-- `substFvar` by an LC type preserves any bvar bound (the replacement adds no
    bvars; the original's bvars are untouched). Generalises `Ty.IsLC.substFvar`
    (which is the `n = 0` case). -/
theorem ContainsBvarsUpTo.substFvar {n Z : Nat} {U ty : Ty}
    (h_U : Ty.IsLC U) (h : ContainsBvarsUpTo n ty) :
    ContainsBvarsUpTo n (Ty.substFvar Z U ty) := by
  induction ty using Ty.rec_strong with
  | prim _ => exact .prim
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    cases h with
    | bvar hlt => simp only [Ty.substFvar]; exact .bvar hlt
  | fvar m =>
    simp only [Ty.substFvar]
    by_cases hm : m = Z
    · simp only [if_pos hm]; exact h_U.mono (Nat.zero_le n)
    · simp only [if_neg hm]; exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.substFvar]
      apply ContainsBvarsUpTo.customTy
      rw [TyList.substFvar_eq_map]
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)
  | bl lo hi e ih =>
    cases h with
    | bl he =>
      simp only [Ty.substFvar]
      exact .bl (ih he)

/-- Well-formedness of a scheme is preserved by `substFvar` (with LC
    replacement). -/
theorem PolyTy.WF.substFvar {Z : Nat} {U : Ty} {M : PolyTy}
    (h_U_lc : Ty.IsLC U) (h : M.WF) : (M.substFvar Z U).WF :=
  ContainsBvarsUpTo.substFvar h_U_lc h


/-- A type with no free vars contains no particular free var. -/
theorem NoFreeVars.not_mem_freeVars {ty : Ty} (h : NoFreeVars ty) (Z : Nat) :
    Z ∉ ty.freeVars := by
  induction h with
  | prim => simp [Ty.freeVars]
  | arrow _ _ iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]; exact ⟨iha, ihb⟩
  | bvar => simp [Ty.freeVars]
  | customTy _ ih =>
    simp only [Ty.freeVars]
    exact TyList.not_mem_freeVars_iff.mpr (fun t ht => ih t ht)
  | bl _ ih =>
    simp only [Ty.freeVars]
    exact ih

/-- Substituting a type-fvar is a no-op on a *closed* scheme (one whose body has
    no free type vars). Used to keep annotated-`let` schemes stable under
    `typ_subst_preservation`. -/
theorem PolyTy.substFvar_eq_self_of_closed {Z : Nat} {U : Ty} {σ : PolyTy}
    (h : NoFreeVars σ.body) : PolyTy.substFvar Z U σ = σ := by
  obtain ⟨pc, b⟩ := σ
  simp only [PolyTy.substFvar, Ty.substFvar_fresh (h.not_mem_freeVars Z)]

/-- Every entry of a `bvarRangeFrom` list is a (free-var-free) bound variable. -/
private theorem NoFreeVars.bvarRangeFrom (s n : Nat) :
    ∀ t ∈ Ty.bvarRangeFrom s n, NoFreeVars t := by
  induction n generalizing s with
  | zero => intro t ht; simp [Ty.bvarRangeFrom] at ht
  | succ k ih =>
    intro t ht
    simp only [Ty.bvarRangeFrom, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact .bvar
    · exact ih (s + 1) t ht

/-- Right-nested arrows over free-var-free pieces are free-var-free. -/
private theorem NoFreeVars.wrapArrows {result : Ty} {args : List Ty}
    (hres : NoFreeVars result) (hargs : ∀ a ∈ args, NoFreeVars a) :
    NoFreeVars (Ty.wrapArrows result args) := by
  induction args with
  | nil => exact hres
  | cons hd tl ih =>
    simp only [Ty.wrapArrows]
    exact .arrow (hargs hd List.mem_cons_self)
      (ih (fun a ha => hargs a (List.mem_cons_of_mem _ ha)))

/-- `substFvar` applied element-wise through a `Forall₂ InstantiatesBy`. -/
theorem InstantiatesBy.forall2_substFvar {Z : Nat} {U : Ty}
    (h_U_lc : Ty.IsLC U) {srcs insts tyArgs : List Ty}
    (h : List.Forall₂ (InstantiatesBy tyArgs) srcs insts) :
    List.Forall₂ (InstantiatesBy (tyArgs.map (Ty.substFvar Z U)))
      (srcs.map (Ty.substFvar Z U)) (insts.map (Ty.substFvar Z U)) := by
  induction h with
  | nil => exact .nil
  | cons hhd _ ih => exact .cons (InstantiatesBy.substFvar h_U_lc hhd) ih

/-- `substFvar` distributes over a list of trivial (monomorphic) bindings,
    landing inside both the `map` and the trivialisation. -/
theorem Env.substFvar_map_mkTrivial {Z : Nat} {U : Ty} {ics : List Ty} :
    Env.substFvar Z U (ics.map PolyTy.mkTrivial)
      = (ics.map (Ty.substFvar Z U)).map PolyTy.mkTrivial := by
  simp only [Env.substFvar, List.map_map]
  apply List.map_congr_left
  intro c _
  rfl

/-- A constructor's polytype body has no free type variables (its only type
    variables are the bound ones from the constructor's own `paramCount`). -/
theorem Ctor.toTy_body_noFreeVars (ctor : Ctor) : NoFreeVars ctor.toTy.body := by
  show NoFreeVars (Ty.wrapArrows (Ty.customTy ctor.tyName (Ty.bvarRange ctor.paramCount))
    ctor.contents)
  apply NoFreeVars.wrapArrows
  · exact NoFreeVars.customTy (fun t ht => NoFreeVars.bvarRangeFrom 0 ctor.paramCount t ht)
  · exact ctor.closed

private theorem ContainsBvarsUpTo.wrapArrows {n : Nat} {result : Ty} {args : List Ty}
    (hres : ContainsBvarsUpTo n result) (hargs : ∀ a ∈ args, ContainsBvarsUpTo n a) :
    ContainsBvarsUpTo n (Ty.wrapArrows result args) := by
  induction args with
  | nil => exact hres
  | cons hd tl ih =>
    exact .arrow (hargs hd (List.mem_cons_self ..))
      (ih (fun a ha => hargs a (List.mem_cons_of_mem _ ha)))

private theorem ContainsBvarsUpTo.bvarRangeFrom (s n : Nat) :
    ∀ t ∈ Ty.bvarRangeFrom s n, ContainsBvarsUpTo (s + n) t := by
  induction n generalizing s with
  | zero => intro t ht; simp [Ty.bvarRangeFrom] at ht
  | succ k ih =>
    intro t ht
    simp only [Ty.bvarRangeFrom, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact .bvar (by omega)
    · exact (ih (s + 1) t ht).mono (by omega)

/-- A constructor's type scheme is well-formed: its body's bvars all lie within
    `paramCount` (from `Ctor.bound` on the contents and the result `customTy`). -/
theorem Ctor.toTy_wf (ctor : Ctor) : ctor.toTy.WF := by
  show ContainsBvarsUpTo ctor.paramCount
    (Ty.wrapArrows (Ty.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)) ctor.contents)
  apply ContainsBvarsUpTo.wrapArrows
  · exact .customTy (fun t ht => by
      simpa using ContainsBvarsUpTo.bvarRangeFrom 0 ctor.paramCount t ht)
  · exact ctor.bound


/-- Membership in a `BranchList.substTyFvar`ed branch list reflects back to the
    original: each member is `(pat, body.substTyFvar Z U)` for an original
    `(pat, body) ∈ branches`. -/
theorem BranchList.mem_substTyFvar {Z : Nat} {U : Ty}
    {branches : List (MatchPattern × Expr)} {branch' : MatchPattern × Expr}
    (h : branch' ∈ BranchList.substTyFvar Z U branches) :
    ∃ pat body, (pat, body) ∈ branches ∧ branch' = (pat, body.substTyFvar Z U) := by
  induction branches with
  | nil => simp only [BranchList.substTyFvar] at h; exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [BranchList.substTyFvar, List.mem_cons] at h
    cases h with
    | inl heq => exact ⟨pat, body, List.mem_cons_self, heq⟩
    | inr h' =>
      obtain ⟨p, b, hmem, heq⟩ := ih h'
      exact ⟨p, b, List.mem_cons_of_mem _ hmem, heq⟩

/-- Membership in a `BranchList.shiftFrom`ed branch list reflects back to the
    original: each member is `(pat, body.shiftFrom (threshold + pat.bindCount) n)`
    for an original `(pat, body) ∈ branches`. -/
theorem BranchList.mem_shiftFrom {threshold n : Nat}
    {branches : List (MatchPattern × Expr)} {branch' : MatchPattern × Expr}
    (h : branch' ∈ BranchList.shiftFrom threshold n branches) :
    ∃ pat body, (pat, body) ∈ branches ∧
      branch' = (pat, body.shiftFrom (threshold + pat.bindCount) n) := by
  induction branches with
  | nil => simp only [BranchList.shiftFrom] at h; exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [BranchList.shiftFrom, List.mem_cons] at h
    cases h with
    | inl heq => exact ⟨pat, body, List.mem_cons_self, heq⟩
    | inr h' =>
      obtain ⟨p, b, hmem, heq⟩ := ih h'
      exact ⟨p, b, List.mem_cons_of_mem _ hmem, heq⟩

/-- Membership in a `BranchList.substN`ed branch list reflects to the original:
    each member is `(pat, body.substN (k + pat.bindCount) vs)` for an original
    `(pat, body) ∈ branches`. -/
theorem BranchList.mem_substN {k : Nat} {vs : List Expr}
    {branches : List (MatchPattern × Expr)} {branch' : MatchPattern × Expr}
    (h : branch' ∈ BranchList.substN k vs branches) :
    ∃ pat body, (pat, body) ∈ branches ∧
      branch' = (pat, body.substN (k + pat.bindCount) vs) := by
  induction branches with
  | nil => simp only [BranchList.substN] at h; exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [BranchList.substN, List.mem_cons] at h
    cases h with
    | inl heq => exact ⟨pat, body, List.mem_cons_self, heq⟩
    | inr h' =>
      obtain ⟨p, b, hmem, heq⟩ := ih h'
      exact ⟨p, b, List.mem_cons_of_mem _ hmem, heq⟩

/-! ### `PolyTy.openGroup` helper lemmas (used by the `letRec` metatheory). -/

/-- The opened group has the same length as the scheme list (each scheme yields
    exactly one opened type). -/
theorem PolyTy.openGroup_length (Ms : List PolyTy) (Xs : List Nat) :
    (PolyTy.openGroup Ms Xs).length = Ms.length := by
  induction Ms generalizing Xs with
  | nil => rfl
  | cons M Ms ih => simp only [PolyTy.openGroup, List.length_cons, ih]

/-- `substFvar` preserves a scheme's parameter count (it only rewrites the
    body), hence the group total. -/
theorem PolyTy.totalParams_map_substFvar (Z : Nat) (U : Ty) (Ms : List PolyTy) :
    PolyTy.totalParams (Ms.map (PolyTy.substFvar Z U)) = PolyTy.totalParams Ms := by
  unfold PolyTy.totalParams
  rw [List.map_map]
  congr 1

/-- Opening a single `substFvar`ed scheme commutes with `substFvar` (for an LC
    replacement and fresh opening names). Packages the `letIn` case's `hopen`
    step as a reusable lemma. -/
theorem PolyTy.substFvar_openVars {Z : Nat} {U : Ty} {M : PolyTy} {Xs : List Nat}
    (h_U_lc : Ty.IsLC U) (hZ : Z ∉ Xs) :
    (M.substFvar Z U).openVars Xs = Ty.substFvar Z U (M.openVars Xs) := by
  unfold PolyTy.openVars PolyTy.substFvar
  exact (Ty.substFvar_openVars h_U_lc hZ).symm

/-- Opening a whole `substFvar`ed group commutes with `substFvar`. The cofinite
    `letRec` premise's `typ_subst` case needs this to rewrite the substituted
    group's openings. -/
theorem PolyTy.openGroup_map_substFvar {Z : Nat} {U : Ty} (h_U_lc : Ty.IsLC U) :
    ∀ (Ms : List PolyTy) {Xs : List Nat}, Z ∉ Xs →
      PolyTy.openGroup (Ms.map (PolyTy.substFvar Z U)) Xs
        = (PolyTy.openGroup Ms Xs).map (Ty.substFvar Z U) := by
  intro Ms
  induction Ms with
  | nil => intro Xs _; rfl
  | cons M Ms ih =>
    intro Xs hZ
    show (PolyTy.substFvar Z U M).openVars (Xs.take M.paramCount)
          :: PolyTy.openGroup (Ms.map (PolyTy.substFvar Z U)) (Xs.drop M.paramCount)
        = Ty.substFvar Z U (M.openVars (Xs.take M.paramCount))
          :: (PolyTy.openGroup Ms (Xs.drop M.paramCount)).map (Ty.substFvar Z U)
    refine congrArg₂ List.cons ?_ (ih (fun hc => hZ (List.drop_subset _ _ hc)))
    exact PolyTy.substFvar_openVars h_U_lc (fun hc => hZ (List.take_subset _ _ hc))

/-- A member of `(l.map f).zip (r.map g)` reflects to a member of `l.zip r`:
    both the bindings and their opened types are transformed in the `letRec`
    `typ_subst`/`subst` cases. -/
private theorem List.mem_zip_map {α β γ δ : Type _} {f : α → γ} {g : β → δ} :
    ∀ {l : List α} {r : List β} {p : γ × δ},
      p ∈ (l.map f).zip (r.map g) → ∃ a b, (a, b) ∈ l.zip r ∧ p = (f a, g b) := by
  intro l
  induction l with
  | nil => intro r p h; simp at h
  | cons hd tl ih =>
    intro r p h
    cases r with
    | nil => simp at h
    | cons rhd rtl =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
      cases h with
      | inl heq => exact ⟨hd, rhd, List.mem_cons_self, heq⟩
      | inr h' =>
        obtain ⟨a, b, hmem, heq⟩ := ih h'
        exact ⟨a, b, List.mem_cons_of_mem _ hmem, heq⟩

/-- Every element of a list is `≤` its `max`-fold. -/
theorem List.le_foldr_max {a : Nat} {l : List Nat}
    (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    simp only [List.foldr_cons]
    cases h with
    | head => exact le_max_left _ _
    | tail _ h' => exact le_trans (ih h') (le_max_right _ _)

/-- For any finite `avoid` list and any `n`, there exist `n` distinct names
    avoiding `avoid`. (Take `n` consecutive numbers above `max avoid`.) -/
theorem exists_fresh_names (avoid : List Nat) (n : Nat) :
    ∃ Xs : List Nat, Xs.length = n ∧ Xs.Nodup ∧ ∀ x ∈ Xs, x ∉ avoid := by
  refine ⟨(List.range n).map (· + (avoid.foldr max 0 + 1)), ?_, ?_, ?_⟩
  · simp
  · apply List.Nodup.map (fun a b hab => by omega) List.nodup_range
  · intro x hx hmem
    simp only [List.mem_map, List.mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    have hle := List.le_foldr_max hmem
    omega

/-! ### `renameG` composition helpers (for the `letRec` `typ_subst` case). -/

/-- Forward direction: a member of `l.zip r` maps to a member of `l.zip (r.map g)`
    (the right components are transformed). -/
private theorem List.mem_zip_map_right {α β γ : Type _} {g : β → γ}
    {l : List α} {r : List β} {a : α} {b : β}
    (h : (a, b) ∈ l.zip r) : (a, g b) ∈ l.zip (r.map g) := by
  induction l generalizing r with
  | nil => simp at h
  | cons hd tl ih =>
    cases r with
    | nil => simp at h
    | cons rhd rtl =>
      simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h ⊢
      cases h with
      | inl heq =>
        rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact Or.inl rfl
      | inr h' => exact Or.inr (ih h')

/-- The shared opening `renameG G Xs τ` is exactly "close over `G`, then open at
    `Xs`", whenever the side conditions for the round-trip hold. This is the
    `(openVars_closeOver_rename).symm` after unfolding `renameG`. -/
private theorem Ty.renameG_eq_openVars_closeOver {G Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) (hG : G.Nodup) (hlen : Xs.length = G.length) (hdisj : ∀ g ∈ G, g ∉ Xs) :
    Ty.renameG G Xs τ = Ty.openVars Xs (Ty.closeOver G τ) := by
  unfold Ty.renameG
  exact (Ty.openVars_closeOver_rename hτ hG hlen hdisj).symm

/-- Iterated `substFvar` by LC replacements preserves local-closedness. -/
private theorem Ty.IsLC.substFvars {s : List (Nat × Ty)} {τ : Ty}
    (hs : ∀ p ∈ s, p.2.IsLC) (hτ : τ.IsLC) : (Ty.substFvars s τ).IsLC := by
  induction s generalizing τ with
  | nil => exact hτ
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Ty.substFvars]
    exact ih (fun p hp => hs p (List.mem_cons_of_mem _ hp))
      (Ty.IsLC.substFvar (hs (Z, U) List.mem_cons_self) hτ)

/-- `renameG` (a renaming to fresh `fvar`s) preserves local-closedness. -/
private theorem Ty.renameG_isLC {G Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) : (Ty.renameG G Xs τ).IsLC := by
  unfold Ty.renameG
  refine Ty.IsLC.substFvars ?_ hτ
  intro p hp
  obtain ⟨x, _, hx⟩ := List.mem_map.mp (List.of_mem_zip hp).2
  rw [← hx]; exact .fvar

/-- **renameG composition.** Renaming `G ↦ W` (to a fresh, `τ`-avoiding pool `W`)
    then `W ↦ Xs` equals renaming `G ↦ Xs` directly. The freshness side
    conditions (`W` avoids `G`, `τ`, and `Xs`; `G` avoids `Xs`) ensure no
    capture. -/
theorem Ty.renameG_renameG {G W Xs : List Nat} {τ : Ty}
    (hτ : τ.IsLC) (hG : G.Nodup) (hW : W.Nodup)
    (hWlen : W.length = G.length) (hXlen : Xs.length = G.length)
    (hGW : ∀ g ∈ G, g ∉ W) (hWτ : ∀ w ∈ W, w ∉ τ.freeVars)
    (hWXs : ∀ w ∈ W, w ∉ Xs) (hGXs : ∀ g ∈ G, g ∉ Xs) :
    Ty.renameG W Xs (Ty.renameG G W τ) = Ty.renameG G Xs τ := by
  have heq1 : Ty.renameG G W τ = Ty.openVars W (Ty.closeOver G τ) :=
    Ty.renameG_eq_openVars_closeOver hτ hG hWlen hGW
  have hY : (Ty.openVars W (Ty.closeOver G τ)).IsLC := by
    rw [← heq1]; exact Ty.renameG_isLC hτ
  rw [heq1, Ty.renameG_eq_openVars_closeOver hY hW (hXlen.trans hWlen.symm) hWXs,
      Ty.closeOver_openVars_self hW
        (by rw [hWlen]; exact Ty.closeOver_preserves_bvars hτ)
        (fun w hw hc => hWτ w hw (Ty.freeVars_closeOver_subset hc))]
  exact (Ty.renameG_eq_openVars_closeOver hτ hG hXlen hGXs).symm

/-- **renameG commutes with substFvar.** When the fresh pool `W` avoids `Z` and
    the free vars of `U`, and `Xs` avoids `Z`, renaming commutes with the
    substitution `Z ↦ U`. -/
theorem Ty.renameG_substFvar_comm {Z : Nat} {U : Ty} {W Xs : List Nat} {τ : Ty}
    (hUlc : U.IsLC) (hZW : Z ∉ W) (hUW : ∀ u ∈ U.freeVars, u ∉ W) (hZXs : Z ∉ Xs)
    (hτ : τ.IsLC) (hW : W.Nodup) (hWlen : Xs.length = W.length) (hWXs : ∀ w ∈ W, w ∉ Xs) :
    Ty.renameG W Xs (Ty.substFvar Z U τ) = Ty.substFvar Z U (Ty.renameG W Xs τ) := by
  rw [Ty.renameG_eq_openVars_closeOver (Ty.IsLC.substFvar hUlc hτ) hW hWlen hWXs,
      Ty.renameG_eq_openVars_closeOver hτ hW hWlen hWXs,
      ← Ty.substFvar_closeOver_comm hZW (fun g hg hc => hUW g hc hg),
      Ty.substFvar_openVars hUlc hZXs]

mutual
theorem SmallStep.IsValue.shiftFrom {e : Expr} (k n : Nat)
    (h : SmallStep.IsValue e) : SmallStep.IsValue (e.shiftFrom k n) := by
  cases h with
  | primLit p => exact .primLit p
  | lambda ann body => exact .lambda _ _
  | ctor name => exact .ctor name
  | ctorApp hf hv => exact .ctorApp (hf.shiftFrom k n) (hv.shiftFrom k n)
  | primBinOp op => exact .primBinOp op
  | primBinOpPartial hv => exact .primBinOpPartial (hv.shiftFrom k n)
theorem SmallStep.IsCtorChain.shiftFrom {e : Expr} (k n : Nat)
    (h : SmallStep.IsCtorChain e) : SmallStep.IsCtorChain (e.shiftFrom k n) := by
  cases h with
  | ctor name => exact .ctor name
  | app hf hv => exact .app (hf.shiftFrom k n) (hv.shiftFrom k n)
end

/-- The free type variables occurring in a term's *annotations* (lambda param
    annotations and `let` scheme annotations), collected recursively. A
    type-fvar substitution whose keys all avoid this set leaves the term fixed
    (`Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars`). -/
def Expr.tyFreeVars : Expr → List Nat
  | .primLit _          => []
  | .primBinOp _        => []
  | .lambda ann body    => (ann.elim [] Ty.freeVars) ++ body.tyFreeVars
  | .app f arg          => f.tyFreeVars ++ arg.tyFreeVars
  | .letIn ann rhs body => (ann.elim [] (fun σ => σ.body.freeVars)) ++ rhs.tyFreeVars ++ body.tyFreeVars
  | .var _             => []
  | .ctor _             => []
  | .match_ scrut branches => scrut.tyFreeVars ++ BranchList.tyFreeVars branches
  | .letRec anns bindings body =>
      -- kept annotations contribute the free type vars in their bodies (scoped vars).
      AnnList.tyFreeVars anns ++ RecGroup.tyFreeVars bindings ++ body.tyFreeVars
where
  BranchList.tyFreeVars : List (MatchPattern × Expr) → List Nat
  | []                  => []
  | (_, body) :: rest   => body.tyFreeVars ++ Expr.tyFreeVars.BranchList.tyFreeVars rest
  RecGroup.tyFreeVars : List Expr → List Nat
  | []        => []
  | e :: rest => e.tyFreeVars ++ Expr.tyFreeVars.RecGroup.tyFreeVars rest
  AnnList.tyFreeVars : List (Option PolyTy) → List Nat
  | []        => []
  | a :: rest => (a.elim [] (fun σ => σ.body.freeVars)) ++ Expr.tyFreeVars.AnnList.tyFreeVars rest

/-- Substituting a fresh type variable (one not occurring in the term's
    annotations) is a no-op. -/
theorem Expr.substTyFvar_eq_self_of_not_mem_tyFreeVars {Z : Nat} {U : Ty} {e : Expr}
    (h : Z ∉ e.tyFreeVars) : e.substTyFvar Z U = e := by
  induction e using Expr.rec_strong with
  | primLit p => rfl
  | primBinOp op => rfl
  | app f arg ihf iha =>
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at h
    simp only [Expr.substTyFvar, ihf h.1, iha h.2]
  | var n => rfl
  | ctor nm => rfl
  | lambda ann body ih =>
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at h
    simp only [Expr.substTyFvar, ih h.2]
    congr 1
    cases ann with
    | none => rfl
    | some T => simp only [Option.map_some, Option.some.injEq]; exact Ty.substFvar_fresh h.1
  | letIn ann rhs body ihr ihb =>
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at h
    obtain ⟨⟨hann, hrhs⟩, hbody⟩ := h
    simp only [Expr.substTyFvar, ihr hrhs, ihb hbody]
    congr 1
    cases ann with
    | none => rfl
    | some σ =>
      simp only [Option.map_some, Option.some.injEq]
      show PolyTy.substFvar Z U σ = σ
      unfold PolyTy.substFvar
      rw [Ty.substFvar_fresh hann]
  | match_ scrut branches ihscrut ihbranches =>
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at h
    obtain ⟨hscrut, hbranches⟩ := h
    simp only [Expr.substTyFvar, ihscrut hscrut]
    congr 1
    clear ihscrut hscrut
    induction branches with
    | nil => rfl
    | cons hd tl ihtl =>
      obtain ⟨pat, body⟩ := hd
      simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append, not_or] at hbranches
      simp only [BranchList.substTyFvar, List.cons.injEq, Prod.mk.injEq, true_and]
      refine ⟨ihbranches pat body List.mem_cons_self hbranches.1, ?_⟩
      exact ihtl (fun p e hp => ihbranches p e (List.mem_cons_of_mem _ hp)) hbranches.2
  | letRec anns bindings body ih_bindings ih_body =>
    simp only [Expr.tyFreeVars, List.mem_append, not_or] at h
    obtain ⟨⟨hanns, hbindings⟩, hbody⟩ := h
    simp only [Expr.substTyFvar, Expr.letRec.injEq]
    refine ⟨?_, ?_, ih_body hbody⟩
    · clear ih_bindings ih_body hbindings hbody
      induction anns with
      | nil => rfl
      | cons hd tl ihtl =>
        simp only [Expr.tyFreeVars.AnnList.tyFreeVars, List.mem_append, not_or] at hanns
        simp only [List.map_cons, List.cons.injEq]
        refine ⟨?_, ihtl hanns.2⟩
        cases hd with
        | none => rfl
        | some σ =>
          simp only [Option.map_some, Option.some.injEq]
          show PolyTy.substFvar Z U σ = σ
          unfold PolyTy.substFvar
          rw [Ty.substFvar_fresh (by simpa [Option.elim] using hanns.1)]
    · clear ih_body hbody hanns
      induction bindings with
      | nil => rfl
      | cons hd tl ihtl =>
        simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append, not_or] at hbindings
        simp only [RecGroup.substTyFvar, List.cons.injEq]
        refine ⟨ih_bindings hd List.mem_cons_self hbindings.1, ?_⟩
        exact ihtl (fun e he hp => ih_bindings e (List.mem_cons_of_mem _ he) hp) hbindings.2

/-- Iterated version: a list of type-fvar substitutions whose keys all avoid the
    term's annotation free variables leaves the term fixed. -/
theorem Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars {pairs : List (Nat × Ty)} :
    ∀ {e : Expr}, (∀ p ∈ pairs, p.1 ∉ e.tyFreeVars) → e.substTyFvars pairs = e := by
  induction pairs with
  | nil => intro e _; rfl
  | cons hd tl ih =>
    intro e h
    obtain ⟨Z, U⟩ := hd
    have hZ : Z ∉ e.tyFreeVars := h (Z, U) List.mem_cons_self
    simp only [Expr.substTyFvars]
    rw [Expr.substTyFvar_eq_self_of_not_mem_tyFreeVars hZ]
    exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-! ### `substTyFvars` structural distribution (toward the term-level rename lemma).

`Expr.substTyFvars` (a left-to-right fold of `Expr.substTyFvar`) pushes through
every term constructor; the annotation cases map the corresponding `Ty`/`PolyTy`
substitution over the stored annotation. These mirror the `Ty.substFvars_*`
distribution lemmas. -/

private theorem BranchList.substTyFvar_eq_map {Z : Nat} {U : Ty}
    {brs : List (MatchPattern × Expr)} :
    BranchList.substTyFvar Z U brs = brs.map (fun pb => (pb.1, pb.2.substTyFvar Z U)) := by
  induction brs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨p, b⟩ := hd; simp only [BranchList.substTyFvar, List.map_cons, ih]

theorem BranchList.openTyVarsAux_eq_map {d : Nat} {Xs : List Nat}
    {brs : List (MatchPattern × Expr)} :
    BranchList.openTyVarsAux d Xs brs = brs.map (fun pb => (pb.1, pb.2.openTyVarsAux d Xs)) := by
  induction brs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨p, b⟩ := hd; simp only [BranchList.openTyVarsAux, List.map_cons, ih]

theorem Expr.substTyFvars_app {σ : List (Nat × Ty)} {f arg : Expr} :
    Expr.substTyFvars σ (.app f arg) = .app (f.substTyFvars σ) (arg.substTyFvars σ) := by
  induction σ generalizing f arg with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simp only [Expr.substTyFvars, Expr.substTyFvar, ih]

theorem Expr.substTyFvars_var {σ : List (Nat × Ty)} {n : Nat} :
    Expr.substTyFvars σ (.var n) = .var n := by
  induction σ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simpa [Expr.substTyFvars, Expr.substTyFvar] using ih

theorem Expr.substTyFvars_lambda {σ : List (Nat × Ty)} {ann : Option Ty} {body : Expr} :
    Expr.substTyFvars σ (.lambda ann body)
      = .lambda (ann.map (Ty.substFvars σ)) (body.substTyFvars σ) := by
  induction σ generalizing ann body with
  | nil => cases ann <;> rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Expr.substTyFvar]
    rw [ih]
    cases ann with
    | none => rfl
    | some t => simp only [Option.map_some, Ty.substFvars]

theorem Expr.substTyFvars_letIn {σ : List (Nat × Ty)} {ann : Option PolyTy} {rhs body : Expr} :
    Expr.substTyFvars σ (.letIn ann rhs body)
      = .letIn (ann.map (fun M => ⟨M.paramCount, Ty.substFvars σ M.body⟩))
          (rhs.substTyFvars σ) (body.substTyFvars σ) := by
  induction σ generalizing ann rhs body with
  | nil => cases ann <;> rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Expr.substTyFvar]
    rw [ih]
    cases ann with
    | none => rfl
    | some M => simp only [Option.map_some, PolyTy.substFvar, Ty.substFvars]

theorem Expr.substTyFvars_match {σ : List (Nat × Ty)} {scrut : Expr}
    {branches : List (MatchPattern × Expr)} :
    Expr.substTyFvars σ (.match_ scrut branches)
      = .match_ (scrut.substTyFvars σ) (branches.map (fun pb => (pb.1, pb.2.substTyFvars σ))) := by
  induction σ generalizing scrut branches with
  | nil =>
    simp only [Expr.substTyFvars]
    congr 1
    conv_lhs => rw [← List.map_id branches]
    apply List.map_congr_left
    rintro ⟨p, b⟩ _; rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Expr.substTyFvar, BranchList.substTyFvar_eq_map, ih,
      List.map_map, Function.comp_def]

/-- `PolyTy.substFvars` acts only on the body (paramCount preserved). -/
theorem PolyTy.substFvars_eq (S : List (Nat × Ty)) (σ : PolyTy) :
    PolyTy.substFvars S σ = ⟨σ.paramCount, Ty.substFvars S σ.body⟩ := by
  induction S generalizing σ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [PolyTy.substFvars, ih, PolyTy.substFvar, Ty.substFvars]

/-- Iterated `Option.map ∘ PolyTy.substFvar` (left-to-right), the ann-level
    analogue of `PolyTy.substFvars` (mirrors the `letRec` case of
    `Expr.substTyFvar`). -/
def RecAnn.substFvars : List (Nat × Ty) → Option PolyTy → Option PolyTy
  | []             , a => a
  | (Z, U) :: rest , a => RecAnn.substFvars rest (a.map (PolyTy.substFvar Z U))

@[simp] theorem RecAnn.substFvars_none (pairs : List (Nat × Ty)) :
    RecAnn.substFvars pairs none = none := by
  induction pairs with
  | nil => rfl
  | cons hd tl ih => obtain ⟨Z, U⟩ := hd; simp only [RecAnn.substFvars, Option.map_none, ih]

@[simp] theorem RecAnn.substFvars_some (pairs : List (Nat × Ty)) (σ : PolyTy) :
    RecAnn.substFvars pairs (some σ) = some (PolyTy.substFvars pairs σ) := by
  induction pairs generalizing σ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [RecAnn.substFvars, Option.map_some, ih, PolyTy.substFvars]

/-- Ann-list analogue of `Ty.substFvars_zip_openVarsFrom`: renaming the fresh
    skolems `Ys ↦ Xs` through opened annotation bodies is the same as opening at
    `Xs`. -/
theorem RecGroup.substFvars_zip_openAnns {d : Nat} {Ys Xs : List Nat}
    {anns : List (Option PolyTy)}
    (h_len : Ys.length = Xs.length) (h_Ys_nodup : Ys.Nodup)
    (h_Ys : ∀ y ∈ Ys, ∀ σ, some σ ∈ anns → y ∉ σ.body.freeVars)
    (h_Ys_Xs : ∀ y ∈ Ys, y ∉ Xs) :
    (RecGroup.openAnns d Ys anns).map (RecAnn.substFvars (Ys.zip (Xs.map (Ty.fvar ·))))
      = RecGroup.openAnns d Xs anns := by
  simp only [RecGroup.openAnns, List.map_map]
  refine List.map_congr_left (fun a ha => ?_)
  cases a with
  | none => simp [Function.comp_apply]
  | some σ =>
    simp only [Function.comp_apply, Option.map_some, RecAnn.substFvars_some,
      Option.some.injEq, PolyTy.substFvars_eq]
    rw [Ty.substFvars_zip_openVarsFrom h_len h_Ys_nodup
      (fun y hy => h_Ys y hy σ ha) h_Ys_Xs]

/-- The `instTy` (concrete `Vs`) analogue of `RecGroup.substFvars_zip_openAnns`. -/
theorem RecGroup.substFvars_zip_instAnns {d : Nat} {Ys : List Nat} {Vs : List Ty}
    {anns : List (Option PolyTy)}
    (h_len : Vs.length = Ys.length) (h_Ys_nodup : Ys.Nodup)
    (h_Ys : ∀ y ∈ Ys, ∀ σ, some σ ∈ anns → y ∉ σ.body.freeVars)
    (h_Ys_Vs : ∀ y ∈ Ys, y ∉ Ty.freeVarsList Vs) (h_Vs_lc : ∀ V ∈ Vs, V.IsLC) :
    (RecGroup.openAnns d Ys anns).map (RecAnn.substFvars (Ys.zip Vs))
      = RecGroup.instAnns d Vs anns := by
  simp only [RecGroup.openAnns, RecGroup.instAnns, List.map_map]
  refine List.map_congr_left (fun a ha => ?_)
  cases a with
  | none => simp [Function.comp_apply]
  | some σ =>
    simp only [Function.comp_apply, Option.map_some, RecAnn.substFvars_some,
      Option.some.injEq, PolyTy.substFvars_eq]
    rw [Ty.substFvars_zip_openVarsFrom_concrete h_len h_Ys_nodup
      (fun y hy => h_Ys y hy σ ha) h_Ys_Vs h_Vs_lc]

theorem Expr.substTyFvars_letRec {pairs : List (Nat × Ty)} {anns : List (Option PolyTy)}
    {bindings : List Expr} {body : Expr} :
    Expr.substTyFvars pairs (.letRec anns bindings body)
      = .letRec (anns.map (RecAnn.substFvars pairs)) (bindings.map (·.substTyFvars pairs))
          (body.substTyFvars pairs) := by
  induction pairs generalizing anns bindings body with
  | nil =>
    simp only [Expr.substTyFvars]
    rw [Expr.letRec.injEq]
    refine ⟨?_, ?_, rfl⟩
    · conv_lhs => rw [← List.map_id anns]
      apply List.map_congr_left; intro a _; rfl
    · conv_lhs => rw [← List.map_id bindings]
      apply List.map_congr_left; intro b _; rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Expr.substTyFvar, RecAnn.substFvars,
      RecGroup.substTyFvar_eq_map, ih, List.map_map, Function.comp_def]

/-- A branch body's annotation free vars are among the branch list's. -/
private theorem Expr.mem_branchList_tyFreeVars {p : MatchPattern} {b : Expr} {y : Nat}
    {brs : List (MatchPattern × Expr)} (hmem : (p, b) ∈ brs) (hy : y ∈ b.tyFreeVars) :
    y ∈ Expr.tyFreeVars.BranchList.tyFreeVars brs := by
  induction brs with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p', b'⟩ := hd
    simp only [Expr.tyFreeVars.BranchList.tyFreeVars, List.mem_append]
    rcases List.mem_cons.mp hmem with h | h
    · rw [Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; exact .inl hy
    · exact .inr (ih h)

/-- A `letRec` binding's annotation free vars are among the group's. -/
private theorem Expr.mem_recGroup_tyFreeVars {e : Expr} {y : Nat}
    {bs : List Expr} (hmem : e ∈ bs) (hy : y ∈ e.tyFreeVars) :
    y ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bs := by
  induction bs with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    simp only [Expr.tyFreeVars.RecGroup.tyFreeVars, List.mem_append]
    rcases List.mem_cons.mp hmem with h | h
    · subst h; exact .inl hy
    · exact .inr (ih h)

/-- A `letRec` annotation's body free vars are among the ann list's. -/
private theorem Expr.mem_annList_tyFreeVars {σ : PolyTy} {y : Nat}
    {anns : List (Option PolyTy)} (hmem : some σ ∈ anns) (hy : y ∈ σ.body.freeVars) :
    y ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns := by
  induction anns with
  | nil => exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    simp only [Expr.tyFreeVars.AnnList.tyFreeVars, List.mem_append]
    rcases List.mem_cons.mp hmem with h | h
    · subst h; exact .inl hy
    · exact .inr (ih h)

/-- **Rename the opening (term level, depth-general).** Opening a term `e`'s
    scoped type variables (offset `d`) at a fresh block `Ys`, then renaming
    `Ys ↦ Xs` (as `fvar`s through the annotations), equals opening directly at
    `Xs`. The annotation cases use `Ty.substFvars_zip_openVarsFrom`. Freshness
    side conditions (`Ys` nodup, disjoint from `e`'s pre-existing annotation free
    vars and from `Xs`) ensure the rename only touches names introduced by the
    opening. -/
theorem Expr.substTyFvars_zip_openTyVarsAux {Ys Xs : List Nat}
    (h_len : Ys.length = Xs.length) (h_Ys_nodup : Ys.Nodup) (h_Ys_Xs : ∀ y ∈ Ys, y ∉ Xs) :
    ∀ (e : Expr) (d : Nat), (∀ y ∈ Ys, y ∉ e.tyFreeVars) →
      (e.openTyVarsAux d Ys).substTyFvars (Ys.zip (Xs.map (Ty.fvar ·)))
        = e.openTyVarsAux d Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p =>
    intro d _; simp only [Expr.openTyVarsAux]
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | primBinOp op =>
    intro d _; simp only [Expr.openTyVarsAux]
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | var n => intro d _; simp [Expr.openTyVarsAux, Expr.substTyFvars_var]
  | ctor nm =>
    intro d _; simp only [Expr.openTyVarsAux]
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | app f arg ihf iharg =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.substTyFvars_app]
    rw [ihf d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto)),
        iharg d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto))]
  | lambda ann body ih =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.substTyFvars_lambda]
    rw [ih d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto))]
    cases ann with
    | none => rfl
    | some t =>
      simp only [Option.map_some]
      rw [Ty.substFvars_zip_openVarsFrom h_len h_Ys_nodup
        (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))
        h_Ys_Xs]
  | letIn ann rhs body ihrhs ihbody =>
    intro d hfresh
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvars_letIn, Option.map_none]
      rw [ihrhs d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto)),
          ihbody d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.substTyFvars_letIn]
      rw [ihrhs (d + σ.paramCount) (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto)),
          ihbody d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))]
      simp only [Option.map_some]
      rw [Ty.substFvars_zip_openVarsFrom h_len h_Ys_nodup
        (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))
        h_Ys_Xs]
  | match_ scrut branches ihscrut ihbranches =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, BranchList.openTyVarsAux_eq_map, Expr.substTyFvars_match]
    rw [ihscrut d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto))]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨p, b⟩ hpb
    simp only [Function.comp_def]
    rw [ihbranches p b hpb d (fun y hy hc => hfresh y hy (by
      simp only [Expr.tyFreeVars, List.mem_append]
      exact .inr (Expr.mem_branchList_tyFreeVars hpb hc)))]
  | letRec anns bindings body ih_bindings ih_body =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.substTyFvars_letRec, Expr.letRec.injEq]
    refine ⟨?_, ?_, ih_body d (fun y hy hc => hfresh y hy (by
      simp only [Expr.tyFreeVars, List.mem_append]; tauto))⟩
    · -- the annotation bodies are opened over `Ys`; renaming `Ys ↦ Xs` = opening over `Xs`
      exact RecGroup.substFvars_zip_openAnns h_len h_Ys_nodup
        (fun y hy σ hσ hc => hfresh y hy (by
          simp only [Expr.tyFreeVars, List.mem_append]
          exact .inl (.inl (Expr.mem_annList_tyFreeVars hσ hc)))) h_Ys_Xs
    · rw [RecGroup.openTyVarsAux_eq_zip, RecGroup.openTyVarsAux_eq_zip, List.map_map]
      apply List.map_congr_left
      intro p hp
      simp only [Function.comp_def]
      exact ih_bindings p.1 (List.of_mem_zip hp).1 p.2 (fun y hy hc => hfresh y hy (by
        simp only [Expr.tyFreeVars, List.mem_append]
        exact .inl (.inr (Expr.mem_recGroup_tyFreeVars (List.of_mem_zip hp).1 hc))))

/-- Top-level form of `Expr.substTyFvars_zip_openTyVarsAux`
    (`Expr.openTyVars = Expr.openTyVarsAux 0`). The key bridge for soundness of
    scoped type variables: the algorithm checks the bound expression opened at one
    skolem block `Ys`; this lets the declarative cofinite premise be recovered by
    renaming `Ys` to any fresh `Xs`. -/
theorem Expr.substTyFvars_zip_openTyVars {Ys Xs : List Nat} {e : Expr}
    (h_len : Ys.length = Xs.length) (h_Ys_nodup : Ys.Nodup)
    (h_Ys_e : ∀ y ∈ Ys, y ∉ e.tyFreeVars) (h_Ys_Xs : ∀ y ∈ Ys, y ∉ Xs) :
    (e.openTyVars Ys).substTyFvars (Ys.zip (Xs.map (Ty.fvar ·))) = e.openTyVars Xs := by
  unfold Expr.openTyVars
  exact Expr.substTyFvars_zip_openTyVarsAux h_len h_Ys_nodup h_Ys_Xs e 0 h_Ys_e

/-- **Concrete-instantiation bridge** (the term-level engine for the new
    `HasScheme.fromHasSchemeVars`): opening `e`'s scoped variables at fresh `Ys`,
    then substituting `Ys ↦ Vs` (arbitrary types), equals type-beta `e.instTyAux d
    Vs`. The annotation/`var` cases use `Ty.substFvars_zip_openVarsFrom_concrete`. -/
theorem Expr.substTyFvars_zip_openTyVarsAux_concrete {Ys : List Nat} {Vs : List Ty}
    (h_len : Vs.length = Ys.length) (h_Ys_nodup : Ys.Nodup)
    (h_Ys_Vs : ∀ y ∈ Ys, y ∉ Ty.freeVarsList Vs) (h_Vs_lc : ∀ V ∈ Vs, V.IsLC) :
    ∀ (e : Expr) (d : Nat), (∀ y ∈ Ys, y ∉ e.tyFreeVars) →
      (e.openTyVarsAux d Ys).substTyFvars (Ys.zip Vs) = e.instTyAux d Vs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p =>
    intro d _; simp only [Expr.openTyVarsAux, Expr.instTyAux]
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | primBinOp op =>
    intro d _; simp only [Expr.openTyVarsAux, Expr.instTyAux]
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | var n => intro d _; simp [Expr.openTyVarsAux, Expr.instTyAux, Expr.substTyFvars_var]
  | ctor nm =>
    intro d _; simp only [Expr.openTyVarsAux, Expr.instTyAux]
    exact Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars (by simp [Expr.tyFreeVars])
  | app f arg ihf iharg =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.instTyAux, Expr.substTyFvars_app]
    rw [ihf d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto)),
        iharg d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto))]
  | lambda ann body ih =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.instTyAux, Expr.substTyFvars_lambda]
    rw [ih d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto))]
    cases ann with
    | none => rfl
    | some t =>
      simp only [Option.map_some]
      rw [Ty.substFvars_zip_openVarsFrom_concrete h_len h_Ys_nodup
        (fun y hy hc => hfresh y hy (by
          simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))
        h_Ys_Vs h_Vs_lc]
  | letIn ann rhs body ihrhs ihbody =>
    intro d hfresh
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.instTyAux, Expr.substTyFvars_letIn, Option.map_none]
      rw [ihrhs d (fun y hy hc => hfresh y hy (by
            simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto)),
          ihbody d (fun y hy hc => hfresh y hy (by
            simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.instTyAux, Expr.substTyFvars_letIn]
      rw [ihrhs (d + σ.paramCount) (fun y hy hc => hfresh y hy (by
            simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto)),
          ihbody d (fun y hy hc => hfresh y hy (by
            simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))]
      simp only [Option.map_some]
      rw [Ty.substFvars_zip_openVarsFrom_concrete h_len h_Ys_nodup
        (fun y hy hc => hfresh y hy (by
          simp only [Expr.tyFreeVars, Option.elim, List.mem_append]; tauto))
        h_Ys_Vs h_Vs_lc]
  | match_ scrut branches ihscrut ihbranches =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.instTyAux, BranchList.openTyVarsAux_eq_map,
      BranchList.instTyAux_eq_map, Expr.substTyFvars_match]
    rw [ihscrut d (fun y hy hc => hfresh y hy (by simp only [Expr.tyFreeVars, List.mem_append]; tauto))]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨p, b⟩ hpb
    simp only [Function.comp_def]
    rw [ihbranches p b hpb d (fun y hy hc => hfresh y hy (by
      simp only [Expr.tyFreeVars, List.mem_append]
      exact .inr (Expr.mem_branchList_tyFreeVars hpb hc)))]
  | letRec anns bindings body ih_bindings ih_body =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.instTyAux, Expr.substTyFvars_letRec, Expr.letRec.injEq]
    refine ⟨?_, ?_, ih_body d (fun y hy hc => hfresh y hy (by
      simp only [Expr.tyFreeVars, List.mem_append]; tauto))⟩
    · exact RecGroup.substFvars_zip_instAnns h_len h_Ys_nodup
        (fun y hy σ hσ hc => hfresh y hy (by
          simp only [Expr.tyFreeVars, List.mem_append]
          exact .inl (.inl (Expr.mem_annList_tyFreeVars hσ hc)))) h_Ys_Vs h_Vs_lc
    · rw [RecGroup.openTyVarsAux_eq_zip, RecGroup.instTyAux_eq_zip, List.map_map]
      apply List.map_congr_left
      intro p hp
      simp only [Function.comp_def]
      exact ih_bindings p.1 (List.of_mem_zip hp).1 p.2 (fun y hy hc => hfresh y hy (by
        simp only [Expr.tyFreeVars, List.mem_append]
        exact .inl (.inr (Expr.mem_recGroup_tyFreeVars (List.of_mem_zip hp).1 hc))))

theorem Expr.substTyFvars_zip_openTyVars_concrete {Ys : List Nat} {Vs : List Ty} {e : Expr}
    (h_len : Vs.length = Ys.length) (h_Ys_nodup : Ys.Nodup)
    (h_Ys_e : ∀ y ∈ Ys, y ∉ e.tyFreeVars) (h_Ys_Vs : ∀ y ∈ Ys, y ∉ Ty.freeVarsList Vs)
    (h_Vs_lc : ∀ V ∈ Vs, V.IsLC) :
    (e.openTyVars Ys).substTyFvars (Ys.zip Vs) = e.instTy Vs := by
  unfold Expr.openTyVars Expr.instTy
  exact Expr.substTyFvars_zip_openTyVarsAux_concrete h_len h_Ys_nodup h_Ys_Vs h_Vs_lc e 0 h_Ys_e

/-! ### Annotation-free structural size (a well-founded measure for derivation
    recursion). The D2 algorithm infers the bound expression *opened* at skolems
    (`rhs.openTyVars Ys`), which is not a structural subterm of the `let`, so the
    default term measure no longer decreases for the `Infer`-recursive metatheory.
    `Expr.size` ignores type annotations, so `openTyVars` preserves it
    (`Expr.size_openTyVars`), giving a measure that *does* decrease. -/
mutual
def Expr.size : Expr → Nat
  | .primLit _          => 1
  | .primBinOp _        => 1
  | .lambda _ body      => 1 + body.size
  | .app f arg          => 1 + f.size + arg.size
  | .letIn _ rhs body   => 1 + rhs.size + body.size
  | .var _ => 1
  | .ctor _             => 1
  | .match_ scrut branches => 1 + scrut.size + Expr.sizeBranches branches
  | .letRec _ bindings body  => 1 + Expr.sizeRecGroup bindings + body.size
def Expr.sizeBranches : List (MatchPattern × Expr) → Nat
  | []                  => 0
  | (_, b) :: rest      => 1 + b.size + Expr.sizeBranches rest
def Expr.sizeRecGroup : List Expr → Nat
  | []        => 0
  | e :: rest => 1 + e.size + Expr.sizeRecGroup rest
end

/-- `Expr.size` is invariant under opening scoped type variables (it ignores the
    annotations that `openTyVars` rewrites). The match-case branch reasoning lives
    here in `Core` where `BranchList.openTyVarsAux` is in scope. -/
theorem Expr.size_openTyVarsAux {Xs : List Nat} :
    ∀ (e : Expr) (d : Nat), (e.openTyVarsAux d Xs).size = e.size := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d; rfl
  | primBinOp op => intro d; rfl
  | app f inp ihf ihi => intro d; simp only [Expr.openTyVarsAux, Expr.size, ihf, ihi]
  | lambda ann body ih => intro d; simp only [Expr.openTyVarsAux, Expr.size, ih]
  | letIn ann be body ihbe ihbody =>
    intro d
    cases ann with
    | none => simp only [Expr.openTyVarsAux, Expr.size, ihbe, ihbody]
    | some σ => simp only [Expr.openTyVarsAux, Expr.size, ihbe, ihbody]
  | var n => intro d; rfl
  | ctor nm => intro d; rfl
  | match_ scrut branches ihs ihbs =>
    intro d
    simp only [Expr.openTyVarsAux, Expr.size]
    rw [ihs d]
    congr 1
    revert ihbs
    induction branches with
    | nil => intro _; rfl
    | cons hd tl ihtl =>
      intro ihbs
      obtain ⟨pat, body⟩ := hd
      simp only [BranchList.openTyVarsAux, Expr.sizeBranches]
      rw [ihbs pat body List.mem_cons_self d,
          ihtl (fun p e hm => ihbs p e (List.mem_cons_of_mem _ hm))]
  | letRec anns bindings body ih_bindings ih_body =>
    intro d
    simp only [Expr.openTyVarsAux, Expr.size]
    rw [ih_body d]
    have hrec : Expr.sizeRecGroup (RecGroup.openTyVarsAux d Xs anns bindings)
        = Expr.sizeRecGroup bindings := by
      revert ih_bindings
      induction bindings generalizing anns with
      | nil => intro _; cases anns <;> rfl
      | cons hd tl ihtl =>
        intro ih_bindings
        cases anns with
        | nil =>
          simp only [RecGroup.openTyVarsAux, Expr.sizeRecGroup]
          rw [ih_bindings hd List.mem_cons_self d,
              ihtl [] (fun e he => ih_bindings e (List.mem_cons_of_mem _ he))]
        | cons a as =>
          simp only [RecGroup.openTyVarsAux, Expr.sizeRecGroup]
          rw [ih_bindings hd List.mem_cons_self (d + RecAnn.params a),
              ihtl as (fun e he => ih_bindings e (List.mem_cons_of_mem _ he))]
    rw [hrec]

theorem Expr.size_openTyVars {Xs : List Nat} {e : Expr} :
    (e.openTyVars Xs).size = e.size := Expr.size_openTyVarsAux e 0

/-! ### Free-variable containment under opening

Opening a term's scoped type variables (`Expr.openTyVars Xs`) can only introduce
the fresh opening names `Xs` into the term's annotation free vars — every other
free var was already there. The `letInAnn` soundness case uses this to bound the
*opened* bound expression's annotation fvars by `K ∪ Ys` (the ambient skolem set
extended with the freshly-allocated skolems). Type-level first, then lifted
through terms (the match-branch reasoning lives here in `Core`, where the private
`BranchList.openTyVarsAux` is in scope, exactly as for `Expr.size_openTyVars`). -/

@[simp] theorem Ty.openVarsFrom_arrow {d : Nat} {Xs : List Nat} {a b : Ty} :
    Ty.openVarsFrom d Xs (.arrow a b)
      = .arrow (Ty.openVarsFrom d Xs a) (Ty.openVarsFrom d Xs b) := rfl
@[simp] theorem Ty.openVarsFrom_customTy {d : Nat} {Xs : List Nat} {nm : TyName} {tys : List Ty} :
    Ty.openVarsFrom d Xs (.customTy nm tys)
      = .customTy nm (tys.map (Ty.openVarsFrom d Xs)) := by
  unfold Ty.openVarsFrom
  simp only [Ty.instantiate, TyList.instantiate_eq_map]

@[simp] theorem Ty.openVarsFrom_bl {d : Nat} {Xs : List Nat} {lo hi : FHM.Bounds.CountSlot} {e : Ty} :
    Ty.openVarsFrom d Xs (.bl lo hi e) = .bl lo hi (Ty.openVarsFrom d Xs e) := rfl

/-- The free vars of an offset opening are among the original free vars or the
    opening names (depth-general form; `Ty.freeVars_openVars_subset` is `d = 0`). -/
theorem Ty.freeVars_openVarsFrom_subset {d : Nat} {Xs : List Nat} {t : Ty} :
    ∀ z ∈ (Ty.openVarsFrom d Xs t).freeVars, z ∈ t.freeVars ∨ z ∈ Xs := by
  induction t using Ty.rec_strong with
  | prim p => intro z hz; simp [Ty.openVarsFrom, Ty.instantiate, Ty.freeVars] at hz
  | fvar n => intro z hz; left; simpa only [Ty.openVarsFrom, Ty.instantiate, Ty.freeVars] using hz
  | bvar i =>
    intro z hz
    simp only [Ty.openVarsFrom, Ty.instantiate] at hz
    by_cases hi : i < d
    · rw [if_pos hi] at hz; simp [Ty.freeVars] at hz
    · rw [if_neg hi] at hz
      cases hh : Xs[i - d]? with
      | none => rw [hh] at hz; simp [Ty.freeVars] at hz
      | some x =>
        rw [hh] at hz
        simp only [Option.elim_some, Ty.freeVars, List.mem_singleton] at hz
        subst hz; exact .inr (List.mem_of_getElem? hh)
  | arrow a b iha ihb =>
    intro z hz
    rw [Ty.openVarsFrom_arrow] at hz
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append] at hz ⊢
    rcases hz with hz | hz
    · rcases iha z hz with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases ihb z hz with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | customTy nm tys ih =>
    intro z hz
    rw [Ty.openVarsFrom_customTy, Ty.freeVars] at hz
    have hex : ∃ t' ∈ tys.map (Ty.openVarsFrom d Xs), z ∈ t'.freeVars := by
      by_contra hcon
      push_neg at hcon
      exact (TyList.not_mem_freeVars_iff.mpr hcon) hz
    obtain ⟨t', ht', hzt'⟩ := hex
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht'
    rcases ih t0 ht0 z hzt' with h | h
    · exact .inl (by rw [Ty.freeVars]; exact TyList.mem_freeVars_of_mem ht0 h)
    · exact .inr h
  | bl lo hi e ih =>
    intro z hz
    simp only [Ty.openVarsFrom_bl, Ty.freeVars] at hz ⊢
    exact ih z hz

/-- A free var of an opened annotation list was either original or a skolem in
    `Xs` (the ann-list analogue of `Ty.freeVars_openVarsFrom_subset`). -/
theorem RecGroup.mem_freeVars_openAnns {d : Nat} {Xs : List Nat} :
    ∀ {anns : List (Option PolyTy)} {z : Nat},
      z ∈ Expr.tyFreeVars.AnnList.tyFreeVars (RecGroup.openAnns d Xs anns) →
      z ∈ Expr.tyFreeVars.AnnList.tyFreeVars anns ∨ z ∈ Xs := by
  intro anns
  induction anns with
  | nil => intro z hz; simp [RecGroup.openAnns, Expr.tyFreeVars.AnnList.tyFreeVars] at hz
  | cons a as ih =>
    intro z hz
    rw [RecGroup.openAnns, List.map_cons, ← RecGroup.openAnns,
      Expr.tyFreeVars.AnnList.tyFreeVars, List.mem_append] at hz
    simp only [Expr.tyFreeVars.AnnList.tyFreeVars, List.mem_append]
    rcases hz with hz | hz
    · cases a with
      | none => simp [Option.elim] at hz
      | some σ =>
        simp only [Option.map_some, Option.elim_some] at hz
        rcases Ty.freeVars_openVarsFrom_subset z hz with h | h
        · exact .inl (.inl h)
        · exact .inr h
    · rcases ih hz with h | h
      · exact .inl (.inr h)
      · exact .inr h

/-- Term-level free-variable containment under offset opening: every annotation
    free var of `e.openTyVarsAux d Xs` was already an annotation free var of `e`,
    or is one of the opening names `Xs`. -/
theorem Expr.tyFreeVars_openTyVarsAux {Xs : List Nat} :
    ∀ (e : Expr) (d : Nat) (z : Nat),
      z ∈ (e.openTyVarsAux d Xs).tyFreeVars → z ∈ e.tyFreeVars ∨ z ∈ Xs := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d z hz; simp [Expr.openTyVarsAux, Expr.tyFreeVars] at hz
  | primBinOp op => intro d z hz; simp [Expr.openTyVarsAux, Expr.tyFreeVars] at hz
  | var n => intro d z hz; simp [Expr.openTyVarsAux, Expr.tyFreeVars] at hz
  | ctor nm => intro d z hz; simp [Expr.openTyVarsAux, Expr.tyFreeVars] at hz
  | app f arg ihf iha =>
    intro d z hz
    simp only [Expr.openTyVarsAux, Expr.tyFreeVars, List.mem_append] at hz ⊢
    rcases hz with hz | hz
    · rcases ihf d z hz with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases iha d z hz with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | lambda ann body ih =>
    intro d z hz
    cases ann with
    | none =>
      -- `lambda none` opens/erases-annotations to `body` definitionally.
      exact ih d z hz
    | some T =>
      simp only [Expr.openTyVarsAux, Expr.tyFreeVars, Option.map_some, Option.elim_some,
        List.mem_append] at hz ⊢
      rcases hz with hz | hz
      · rcases Ty.freeVars_openVarsFrom_subset z hz with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases ih d z hz with h | h
        · exact .inl (.inr h)
        · exact .inr h
  | letIn ann rhs body ihr ihb =>
    intro d z hz
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.tyFreeVars, Option.elim_none, List.nil_append,
        List.mem_append] at hz ⊢
      rcases hz with hz | hz
      · rcases ihr d z hz with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · rcases ihb d z hz with h | h
        · exact .inl (.inr h)
        · exact .inr h
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.tyFreeVars, Option.elim_some, List.mem_append] at hz ⊢
      rcases hz with (hz | hz) | hz
      · rcases Ty.freeVars_openVarsFrom_subset z hz with h | h
        · exact .inl (.inl (.inl h))
        · exact .inr h
      · rcases ihr (d + σ.paramCount) z hz with h | h
        · exact .inl (.inl (.inr h))
        · exact .inr h
      · rcases ihb d z hz with h | h
        · exact .inl (.inr h)
        · exact .inr h
  | match_ scrut branches ihs ihbs =>
    intro d z hz
    simp only [Expr.openTyVarsAux, Expr.tyFreeVars, List.mem_append] at hz ⊢
    rcases hz with hz | hz
    · rcases ihs d z hz with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · have hbr : z ∈ Expr.tyFreeVars.BranchList.tyFreeVars branches ∨ z ∈ Xs := by
        revert hz
        revert ihbs
        induction branches with
        | nil =>
          intro _ hz
          simp [BranchList.openTyVarsAux, Expr.tyFreeVars.BranchList.tyFreeVars] at hz
        | cons hd tl ihtl =>
          intro ihbs hz
          obtain ⟨pat, body⟩ := hd
          simp only [BranchList.openTyVarsAux, Expr.tyFreeVars.BranchList.tyFreeVars,
            List.mem_append] at hz ⊢
          rcases hz with hz | hz
          · rcases ihbs pat body List.mem_cons_self d z hz with h | h
            · exact .inl (.inl h)
            · exact .inr h
          · rcases ihtl (fun p e hm => ihbs p e (List.mem_cons_of_mem _ hm)) hz with h | h
            · exact .inl (.inr h)
            · exact .inr h
      rcases hbr with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | letRec anns bindings body ih_bindings ih_body =>
    intro d z hz
    simp only [Expr.openTyVarsAux, Expr.tyFreeVars, List.mem_append] at hz ⊢
    rcases hz with (hz | hz) | hz
    · -- annotations are opened; the var was original or is a skolem in `Xs`
      rcases RecGroup.mem_freeVars_openAnns hz with h | h
      · exact .inl (.inl (.inl h))
      · exact .inr h
    · have hrec : z ∈ Expr.tyFreeVars.RecGroup.tyFreeVars bindings ∨ z ∈ Xs := by
        revert hz
        revert ih_bindings
        induction bindings generalizing anns with
        | nil =>
          intro _ hz
          cases anns <;>
            simp [RecGroup.openTyVarsAux, Expr.tyFreeVars.RecGroup.tyFreeVars] at hz
        | cons hd tl ihtl =>
          intro ih_bindings hz
          cases anns with
          | nil =>
            simp only [RecGroup.openTyVarsAux, Expr.tyFreeVars.RecGroup.tyFreeVars,
              List.mem_append] at hz ⊢
            rcases hz with hz | hz
            · rcases ih_bindings hd List.mem_cons_self d z hz with h | h
              · exact .inl (.inl h)
              · exact .inr h
            · rcases ihtl [] (fun e he => ih_bindings e (List.mem_cons_of_mem _ he)) hz with h | h
              · exact .inl (.inr h)
              · exact .inr h
          | cons a as =>
            simp only [RecGroup.openTyVarsAux, Expr.tyFreeVars.RecGroup.tyFreeVars,
              List.mem_append] at hz ⊢
            rcases hz with hz | hz
            · rcases ih_bindings hd List.mem_cons_self (d + RecAnn.params a) z hz with h | h
              · exact .inl (.inl h)
              · exact .inr h
            · rcases ihtl as (fun e he => ih_bindings e (List.mem_cons_of_mem _ he)) hz with h | h
              · exact .inl (.inr h)
              · exact .inr h
      rcases hrec with h | h
      · exact .inl (.inl (.inr h))
      · exact .inr h
    · rcases ih_body d z hz with h | h
      · exact .inl (.inr h)
      · exact .inr h

/-- Top-level free-variable containment under opening (`d = 0`). The bridge the
    `letInAnn` soundness case needs: the opened bound expression's annotation
    fvars are among `rhs`'s original ones or the skolems `Xs`. -/
theorem Expr.tyFreeVars_openTyVars {Xs : List Nat} {e : Expr} {z : Nat}
    (hz : z ∈ (e.openTyVars Xs).tyFreeVars) : z ∈ e.tyFreeVars ∨ z ∈ Xs :=
  Expr.tyFreeVars_openTyVarsAux e 0 z hz

/-- Instantiation with the "identity on bvars" substitution is a no-op. -/
private theorem Ty.instantiate_bvar_id {ty : Ty} :
    Ty.instantiate (fun i => .bvar i) ty = ty := by
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | arrow _ _ ih_a ih_b =>
    simp only [Ty.instantiate, Ty.arrow.injEq]; exact ⟨ih_a, ih_b⟩
  | bvar _ => rfl
  | fvar _ => rfl
  | customTy _ tys ih =>
    simp only [Ty.instantiate, Ty.customTy.injEq, true_and]
    induction tys with
    | nil => rfl
    | cons hd tl ih_tl =>
      simp only [TyList.instantiate, List.cons.injEq]
      refine ⟨ih hd List.mem_cons_self, ?_⟩
      exact ih_tl (fun t ht => ih t (List.mem_cons_of_mem _ ht))
  | bl lo hi e ih =>
    simp only [Ty.instantiate, Ty.bl.injEq, true_and]; exact ih

/-- Opening with the empty list of types is identity: nothing to instantiate. -/
theorem Ty.openWith_nil {ty : Ty} : Ty.openWith [] ty = ty := by
  unfold Ty.openWith
  have heq : (fun i => ([] : List Ty)[i]?.getD (.bvar i)) = (fun i => Ty.bvar i) := by
    funext i; simp
  rw [heq]
  exact Ty.instantiate_bvar_id

/- Values are preserved under multi-substitution (`substN` only rewrites free
   term vars / descends under binders; value shape is untouched). Mutual with
   `IsCtorChain.substN`. -/
mutual
theorem SmallStep.IsValue.substN {e : Expr} (k : Nat) (vs : List Expr)
    (h : SmallStep.IsValue e) : SmallStep.IsValue (e.substN k vs) := by
  cases h with
  | primLit p => exact .primLit p
  | lambda ann body => exact .lambda _ _
  | ctor name => exact .ctor name
  | ctorApp hf hv => exact .ctorApp (hf.substN k vs) (hv.substN k vs)
  | primBinOp op => exact .primBinOp op
  | primBinOpPartial hv => exact .primBinOpPartial (hv.substN k vs)
theorem SmallStep.IsCtorChain.substN {e : Expr} (k : Nat) (vs : List Expr)
    (h : SmallStep.IsCtorChain e) : SmallStep.IsCtorChain (e.substN k vs) := by
  cases h with
  | ctor name => exact .ctor name
  | app hf hv => exact .app (hf.substN k vs) (hv.substN k vs)
end

/-- If `ty`'s bvars are all `< n` and `ty` instantiates to `τ` under `tyArgs`,
    then `τ` is the result of opening `ty` with the length-`n` prefix of
    `tyArgs` (padding unused slots, which `ty` can't reference, with `unit`).
    This bridges the var rule's `InstantiatesBy` to the scheme's `openWith`. -/
theorem InstantiatesBy.eq_openWith_range {tyArgs : List Ty} {n : Nat} {ty τ : Ty}
    (h : InstantiatesBy tyArgs ty τ) (h_bv : ContainsBvarsUpTo n ty) :
    τ = Ty.openWith ((List.range n).map (fun i => (tyArgs[i]?).getD (.prim .unit))) ty := by
  induction ty using Ty.rec_strong generalizing τ with
  | prim p => cases h; rfl
  | arrow a b iha ihb =>
    cases h_bv with
    | arrow hba hbb =>
      cases h with
      | arrow ha hb =>
        simp only [Ty.openWith, Ty.instantiate] at *
        rw [iha ha hba, ihb hb hbb]
  | bvar i =>
    cases h_bv with
    | bvar h_lt =>
      cases h with
      | bvar hsome =>
        simp only [Ty.openWith, Ty.instantiate, List.getElem?_map, List.getElem?_range,
          h_lt, Option.map_some, Option.getD_some, hsome]
  | fvar m => cases h; rfl
  | customTy nm tys ih =>
    cases h_bv with
    | customTy hball =>
      cases h with
      | customTy hforall =>
        simp only [Ty.openWith, Ty.instantiate]
        congr 1
        rw [TyList.instantiate_eq_map]
        induction hforall with
        | nil => rfl
        | cons hhd htl ihtl =>
          rename_i hd_ty hd_inst tl_tys tl_inst
          have h_hd := ih hd_ty List.mem_cons_self hhd (hball hd_ty List.mem_cons_self)
          have h_tl := ihtl
            (fun t ht => ih t (List.mem_cons_of_mem _ ht))
            (fun t ht => hball t (List.mem_cons_of_mem _ ht))
          simp only [List.map_cons]
          simp only [Ty.openWith] at h_hd
          rw [← h_hd, h_tl]
  | bl lo hi e ih =>
    cases h_bv with
    | bl he_bv =>
      cases h with
      | bl he =>
        simp only [Ty.openWith, Ty.instantiate, Ty.bl.injEq, true_and]
        exact ih he he_bv

/-! ### Type-beta / scoped-opening commutation infrastructure.

The `letIn` case of `subst_lemma` (and `subst_lemma_many`) must commute the
term-level multi-substitution `substN` (whose substituted branch type-betas via
`instTy`) past the type-level opener `openTyVarsAux`. With the *shifted*
`openTyFrom` (which makes opening-to-types behave like opening-to-fvars), these
commute, provided the substituted values' type annotations are scoped within the
type arguments supplied at their use sites — which holds for well-typed values
(`HasScheme`). This block develops that commutation. -/

/-- Shifting a type by `ℓ` commutes with offset opening: opening at threshold
    `d+ℓ` after a `ℓ`-shift equals shifting after opening at threshold `d`. The
    `bvar` arithmetic lines up exactly (this is the identity that the de Bruijn
    shift in `openTyFrom` was added to satisfy). -/
theorem Ty.openVarsFrom_shiftBvarsBy (ℓ d : Nat) (Ys : List Nat) (t : Ty) :
    Ty.openVarsFrom (d + ℓ) Ys (Ty.shiftBvarsBy ℓ t)
      = Ty.shiftBvarsBy ℓ (Ty.openVarsFrom d Ys t) := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | fvar n => rfl
  | bvar i =>
    simp only [Ty.shiftBvarsBy, Ty.openVarsFrom, Ty.instantiate]
    by_cases hi : i < d
    · rw [if_pos hi, if_pos (by omega : i + ℓ < d + ℓ)]
      simp only [Ty.instantiate]
    · rw [if_neg hi, if_neg (by omega : ¬ i + ℓ < d + ℓ)]
      have : i + ℓ - (d + ℓ) = i - d := by omega
      rw [this]
      cases Ys[i - d]? with
      | none => simp only [Option.elim, Ty.instantiate]
      | some y => simp only [Option.elim, Ty.instantiate]
  | arrow a b iha ihb =>
    simp only [Ty.shiftBvarsBy, Ty.openVarsFrom, Ty.instantiate] at *
    rw [Ty.arrow.injEq]; exact ⟨iha, ihb⟩
  | customTy nm tys ih =>
    simp only [Ty.shiftBvarsBy, Ty.openVarsFrom, Ty.instantiate, TyList.instantiate_eq_map,
      List.map_map, Ty.customTy.injEq, true_and]
    apply List.map_congr_left
    intro t ht
    simpa only [Ty.shiftBvarsBy, Ty.openVarsFrom, Function.comp_def] using ih t ht
  | bl lo hi e ih =>
    simp only [Ty.shiftBvarsBy, Ty.openVarsFrom, Ty.instantiate, Ty.bl.injEq, true_and]
    exact ih

/-- Offset opening is the identity on types whose bvars are all `< d`. -/
theorem Ty.openVarsFrom_eq_self_of_bvars {d : Nat} {Xs : List Nat} {t : Ty}
    (h : ContainsBvarsUpTo d t) : Ty.openVarsFrom d Xs t = t := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | fvar n => rfl
  | bvar i => cases h with | bvar hlt => simp only [Ty.openVarsFrom, Ty.instantiate, if_pos hlt]
  | arrow a b iha ihb =>
    cases h with
    | arrow ha hb => simp only [Ty.openVarsFrom_arrow, iha ha, ihb hb]
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.openVarsFrom_customTy, Ty.customTy.injEq, true_and]
      conv_rhs => rw [← List.map_id tys]
      exact List.map_congr_left (fun t ht => by rw [id_eq]; exact ih t ht (hall t ht))
  | bl lo hi e ih =>
    cases h with
    | bl he => simp only [Ty.openVarsFrom_bl, ih he]

/-- Type-beta is a no-op on a type whose `bvar`s are all `< d` (nothing in range to
    instantiate). The companion of `openVarsFrom_eq_self_of_bvars` for `openTyFrom`. -/
theorem Ty.openTyFrom_eq_self_of_bvars {d : Nat} {Ts : List Ty} {t : Ty}
    (h : ContainsBvarsUpTo d t) : Ty.openTyFrom d Ts t = t := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | fvar n => rfl
  | bvar i => cases h with | bvar hlt => simp only [Ty.openTyFrom, Ty.instantiate, if_pos hlt]
  | arrow a b iha ihb =>
    cases h with
    | arrow ha hb => simp only [Ty.openTyFrom_arrow, iha ha, ihb hb]
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.openTyFrom_customTy, Ty.customTy.injEq, true_and]
      conv_rhs => rw [← List.map_id tys]
      exact List.map_congr_left (fun t ht => by rw [id_eq]; exact ih t ht (hall t ht))
  | bl lo hi e ih =>
    cases h with
    | bl he => simp only [Ty.openTyFrom_bl, ih he]

/-- **Type-beta / opening commute (Ty level).** Opening (offset `d+ℓ`) the result
    of a depth-`ℓ` type-beta equals type-betaing with the opened arguments,
    provided `t`'s bvars are within `ℓ + Ts.length` (so every bvar is either bound
    inside `t` or supplied by `Ts`; nothing dangles to be wrongly opened). The
    `shiftBvarsBy` inside `openTyFrom` is exactly what makes the `Ts`-substituted
    case line up (`openVarsFrom_shiftBvarsBy`). -/
theorem Ty.openVarsFrom_openTyFrom (ℓ d : Nat) (Ys : List Nat) (Ts : List Ty) {t : Ty}
    (h : ContainsBvarsUpTo (ℓ + Ts.length) t) :
    Ty.openVarsFrom (d + ℓ) Ys (Ty.openTyFrom ℓ Ts t)
      = Ty.openTyFrom ℓ (Ts.map (Ty.openVarsFrom d Ys)) t := by
  induction t using Ty.rec_strong with
  | prim p => rfl
  | fvar n => rfl
  | bvar i =>
    cases h with
    | bvar hlt =>
      simp only [Ty.openTyFrom, Ty.instantiate]
      by_cases hiℓ : i < ℓ
      · rw [if_pos hiℓ, if_pos hiℓ]
        simp only [Ty.openVarsFrom, Ty.instantiate, if_pos (by omega : i < d + ℓ)]
      · rw [if_neg hiℓ, if_neg hiℓ, List.getElem?_map]
        have hcov : i - ℓ < Ts.length := by omega
        rw [List.getElem?_eq_getElem hcov]
        simp only [Option.map_some, Option.getD_some]
        exact Ty.openVarsFrom_shiftBvarsBy ℓ d Ys Ts[i - ℓ]
  | arrow a b iha ihb =>
    cases h with
    | arrow ha hb =>
      simp only [Ty.openTyFrom_arrow, Ty.openVarsFrom_arrow, Ty.arrow.injEq]
      exact ⟨iha ha, ihb hb⟩
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.openTyFrom_customTy, Ty.openVarsFrom_customTy, List.map_map,
        Ty.customTy.injEq, true_and]
      apply List.map_congr_left
      intro t ht
      simpa only [Function.comp_def] using ih t ht (hall t ht)
  | bl lo hi e ih =>
    cases h with
    | bl he =>
      simp only [Ty.openTyFrom_bl, Ty.openVarsFrom_bl, ih he]

/-- Opening is a no-op on group annotation bodies already bounded by
    `d + σ.paramCount` (self-contained schemes are the `d`-independent case). -/
theorem RecGroup.openAnns_eq_self_of_bvars {d : Nat} {Xs : List Nat}
    {anns : List (Option PolyTy)}
    (h : ∀ σ, some σ ∈ anns → ContainsBvarsUpTo (d + σ.paramCount) σ.body) :
    RecGroup.openAnns d Xs anns = anns := by
  simp only [RecGroup.openAnns]
  conv_rhs => rw [← List.map_id anns]
  refine List.map_congr_left (fun a ha => ?_)
  cases a with
  | none => rfl
  | some σ =>
    simp only [Option.map_some, id_eq, Option.some.injEq]
    rw [Ty.openVarsFrom_eq_self_of_bvars (h σ ha)]

/-- Type-beta is a no-op on group annotation bodies already bounded by
    `d + σ.paramCount`. -/
theorem RecGroup.instAnns_eq_self_of_bvars {d : Nat} {Ts : List Ty}
    {anns : List (Option PolyTy)}
    (h : ∀ σ, some σ ∈ anns → ContainsBvarsUpTo (d + σ.paramCount) σ.body) :
    RecGroup.instAnns d Ts anns = anns := by
  simp only [RecGroup.instAnns]
  conv_rhs => rw [← List.map_id anns]
  refine List.map_congr_left (fun a ha => ?_)
  cases a with
  | none => rfl
  | some σ =>
    simp only [Option.map_some, id_eq, Option.some.injEq]
    rw [Ty.openTyFrom_eq_self_of_bvars (h σ ha)]

/-- `openAnns`/`instAnns` commute (the ann-list analogue of
    `Ty.openVarsFrom_openTyFrom`), given the annotation bodies are `bvar`-bounded. -/
theorem RecGroup.openAnns_instAnns_comm {d d' : Nat} {Ys : List Nat} {Ts : List Ty}
    {anns : List (Option PolyTy)}
    (hsc : ∀ σ, some σ ∈ anns → ContainsBvarsUpTo (d' + Ts.length + σ.paramCount) σ.body) :
    RecGroup.openAnns (d + d') Ys (RecGroup.instAnns d' Ts anns)
      = RecGroup.instAnns d' (Ts.map (Ty.openVarsFrom d Ys)) anns := by
  simp only [RecGroup.openAnns, RecGroup.instAnns, List.map_map]
  refine List.map_congr_left (fun a ha => ?_)
  cases a with
  | none => rfl
  | some σ =>
    simp only [Function.comp_apply, Option.map_some, Option.some.injEq, PolyTy.mk.injEq, true_and]
    have hb : ContainsBvarsUpTo (d' + σ.paramCount + Ts.length) σ.body :=
      (hsc σ ha).mono (by omega)
    rw [show d + d' + σ.paramCount = d + (d' + σ.paramCount) from by omega]
    exact Ty.openVarsFrom_openTyFrom (d' + σ.paramCount) d Ys Ts hb

/-! **Type-bvar boundedness for terms.** `e.TyBvarBounded n` says every type
    annotation in `e` has bvars `< n` (raised by enclosing scheme binders, exactly
    `openTyVarsAux`'s `d`-bookkeeping). A well-typed `HasScheme ctx v M` value is
    `TyBvarBounded M.paramCount` (its scoped type bvars all reference `M`); this is
    what powers the `subst_lemma` `letIn` commutation. -/
mutual
def Expr.TyBvarBounded (n : Nat) : Expr → Prop
  | .primLit _          => True
  | .primBinOp _        => True
  | .lambda ann body    => (∀ t, ann = some t → ContainsBvarsUpTo n t) ∧ body.TyBvarBounded n
  | .app f arg          => f.TyBvarBounded n ∧ arg.TyBvarBounded n
  | .letIn (some σ) rhs body =>
      ContainsBvarsUpTo (n + σ.paramCount) σ.body ∧
        rhs.TyBvarBounded (n + σ.paramCount) ∧ body.TyBvarBounded n
  | .letIn none rhs body => rhs.TyBvarBounded n ∧ body.TyBvarBounded n
  | .var _             => True
  | .ctor _             => True
  | .match_ scrut branches =>
      scrut.TyBvarBounded n ∧ Expr.TyBvarBounded.BranchList n branches
  | .letRec anns bindings body =>
      -- Depth-aware (mirrors `letIn (some σ)`): each present scheme body may
      -- reference the ambient `n` enclosing type binders in addition to its own
      -- `σ.paramCount`.
      (∀ σ, some σ ∈ anns → ContainsBvarsUpTo (n + σ.paramCount) σ.body) ∧
        Expr.TyBvarBounded.RecGroup n anns bindings ∧ body.TyBvarBounded n
def Expr.TyBvarBounded.BranchList (n : Nat) : List (MatchPattern × Expr) → Prop
  | []                  => True
  | (_, body) :: rest   => body.TyBvarBounded n ∧ Expr.TyBvarBounded.BranchList n rest
/-- Scheme-shielded per-binding boundedness for `letRec` groups: binding `j` is
    bounded at `n + RecAnn.params aⱼ` (its own scheme's variables are in scope
    when annotated), the anns consumed in lockstep. Mirrors
    `RecGroup.openTyVarsAux`/`RecGroup.shieldDepths`. -/
def Expr.TyBvarBounded.RecGroup (n : Nat) : List (Option PolyTy) → List Expr → Prop
  | _,       []        => True
  | [],      e :: rest => e.TyBvarBounded n ∧ Expr.TyBvarBounded.RecGroup n [] rest
  | a :: as, e :: rest =>
      e.TyBvarBounded (n + RecAnn.params a) ∧ Expr.TyBvarBounded.RecGroup n as rest
end

theorem Expr.TyBvarBounded.BranchList_iff {n : Nat} {brs : List (MatchPattern × Expr)} :
    Expr.TyBvarBounded.BranchList n brs ↔ ∀ p b, (p, b) ∈ brs → b.TyBvarBounded n := by
  induction brs with
  | nil => simp [Expr.TyBvarBounded.BranchList]
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [Expr.TyBvarBounded.BranchList, ih, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ⟨hb, hrest⟩ p' b' (heq | hmem)
      · obtain ⟨rfl, rfl⟩ := heq; exact hb
      · exact hrest p' b' hmem
    · intro h
      exact ⟨h p b (Or.inl ⟨rfl, rfl⟩), fun p' b' hmem => h p' b' (Or.inr hmem)⟩

/-- The shielded `RecGroup` predicate is exactly "every binding, paired with its
    shield-depth, is `TyBvarBounded`" — characterised by `RecGroup.shieldDepths`. -/
theorem Expr.TyBvarBounded.RecGroup_iff {n : Nat} {anns : List (Option PolyTy)} {bs : List Expr} :
    Expr.TyBvarBounded.RecGroup n anns bs ↔
      ∀ p ∈ bs.zip (RecGroup.shieldDepths n anns bs), p.1.TyBvarBounded p.2 := by
  induction bs generalizing anns with
  | nil => cases anns <;> simp [Expr.TyBvarBounded.RecGroup, RecGroup.shieldDepths]
  | cons hd tl ih =>
    cases anns with
    | nil =>
      simp only [Expr.TyBvarBounded.RecGroup, RecGroup.shieldDepths, List.zip_cons_cons,
        List.mem_cons, ih, forall_eq_or_imp]
    | cons a as =>
      simp only [Expr.TyBvarBounded.RecGroup, RecGroup.shieldDepths, List.zip_cons_cons,
        List.mem_cons, ih, forall_eq_or_imp]

/-- Build the shielded `RecGroup` predicate from the per-`(binding,ann)`-pair
    bound `e.TyBvarBounded (n + RecAnn.params a)` (lengths matching). -/
theorem Expr.TyBvarBounded.RecGroup_of_zip {n : Nat} {anns : List (Option PolyTy)}
    {bs : List Expr}
    (hlen : bs.length = anns.length)
    (h : ∀ p ∈ bs.zip anns, p.1.TyBvarBounded (n + RecAnn.params p.2)) :
    Expr.TyBvarBounded.RecGroup n anns bs := by
  induction bs generalizing anns with
  | nil => cases anns <;> trivial
  | cons hd tl ih =>
    cases anns with
    | nil => simp at hlen
    | cons a as =>
      refine ⟨h (hd, a) List.mem_cons_self,
        ih (by simpa using hlen) (fun p hp => h p (List.mem_cons_of_mem _ hp))⟩

theorem Expr.TyBvarBounded.mono : ∀ {n m : Nat} {e : Expr},
    e.TyBvarBounded n → n ≤ m → e.TyBvarBounded m := by
  intro n m e
  induction e using Expr.rec_strong generalizing n m with
  | primLit p => intro _ _; trivial
  | primBinOp op => intro _ _; trivial
  | ctor nm => intro _ _; trivial
  | var i => intro _ _; trivial
  | lambda ann body ih =>
    intro h hnm
    exact ⟨fun t hat => ((h.1) t hat).mono hnm, ih h.2 hnm⟩
  | app f arg ihf iharg => intro h hnm; exact ⟨ihf h.1 hnm, iharg h.2 hnm⟩
  | letIn ann rhs body ihr ihb =>
    intro h hnm
    cases ann with
    | none => exact ⟨ihr h.1 hnm, ihb h.2 hnm⟩
    | some σ =>
      exact ⟨h.1.mono (by omega), ihr h.2.1 (by omega), ihb h.2.2 hnm⟩
  | match_ scrut branches ihs ihbs =>
    intro h hnm
    simp only [Expr.TyBvarBounded, Expr.TyBvarBounded.BranchList_iff] at h ⊢
    exact ⟨ihs h.1 hnm, fun p b hmem => ihbs p b hmem (h.2 p b hmem) hnm⟩
  | letRec anns bindings body ihbs ihb =>
    intro h hnm
    simp only [Expr.TyBvarBounded] at h ⊢
    obtain ⟨hsc, hbs, hb⟩ := h
    refine ⟨fun σ hσ => (hsc σ hσ).mono (by omega), ?_, ihb hb hnm⟩
    clear hsc hb ihb
    revert ihbs hbs
    induction bindings generalizing anns with
    | nil => intro _ _; cases anns <;> trivial
    | cons hd tl ih =>
      intro ihbs hbs
      cases anns with
      | nil =>
        simp only [Expr.TyBvarBounded.RecGroup] at hbs ⊢
        exact ⟨ihbs hd List.mem_cons_self hbs.1 hnm,
          ih [] (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2⟩
      | cons a as =>
        simp only [Expr.TyBvarBounded.RecGroup] at hbs ⊢
        exact ⟨ihbs hd List.mem_cons_self hbs.1
            (by omega : n + RecAnn.params a ≤ m + RecAnn.params a),
          ih as (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2⟩

/-- **Reflection (Ty level):** if opening at threshold `m` makes a type bounded by
    `m`, the type was bounded by `m + Xs.length` (the opened bvars were `< m+len`). -/
theorem Ty.containsBvars_of_openVarsFrom (m : Nat) (Xs : List Nat) {t : Ty}
    (h : ContainsBvarsUpTo m (Ty.openVarsFrom m Xs t)) : ContainsBvarsUpTo (m + Xs.length) t := by
  induction t using Ty.rec_strong with
  | prim p => exact .prim
  | fvar n => exact .fvar
  | bvar i =>
    simp only [Ty.openVarsFrom, Ty.instantiate] at h
    by_cases hi : i < m
    · exact .bvar (by omega)
    · rw [if_neg hi] at h
      cases hxs : Xs[i - m]? with
      | none =>
        rw [hxs] at h; simp only [Option.elim] at h
        cases h with | bvar hlt => exact absurd hlt hi
      | some x =>
        have : i - m < Xs.length := (List.getElem?_eq_some_iff.mp hxs).1
        exact .bvar (by omega)
  | arrow a b iha ihb =>
    rw [Ty.openVarsFrom_arrow] at h
    cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | customTy nm tys ih =>
    rw [Ty.openVarsFrom_customTy] at h
    cases h with
    | customTy hall =>
      refine .customTy (fun t ht => ih t ht ?_)
      exact hall _ (List.mem_map_of_mem ht)
  | bl lo hi e ih =>
    rw [Ty.openVarsFrom_bl] at h
    cases h with
    | bl he => exact .bl (ih he)

/-- **Reflection (term level):** if `e` opened at depth `d` is `TyBvarBounded d`,
    then `e` is `TyBvarBounded (d + Xs.length)`. Used to recover a value's scoped
    bound from the `letIn` cofinite premise (which types the opened value). -/
theorem Expr.tyBvarBounded_of_openTyVarsAux (Xs : List Nat) :
    ∀ (e : Expr) (d : Nat), (e.openTyVarsAux d Xs).TyBvarBounded d →
      e.TyBvarBounded (d + Xs.length) := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d _; trivial
  | primBinOp op => intro d _; trivial
  | ctor nm => intro d _; trivial
  | var n => intro d _; trivial
  | app f arg ihf iharg =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h
    exact ⟨ihf d h.1, iharg d h.2⟩
  | lambda ann body ih =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h
    refine ⟨fun t hat => ?_, ih d h.2⟩
    subst hat
    simp only [Option.map_some, Option.some.injEq, forall_eq'] at h
    exact Ty.containsBvars_of_openVarsFrom d Xs h.1
  | letIn ann rhs body ihr ihb =>
    intro d h
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h ⊢
      exact ⟨ihr d h.1, ihb d h.2⟩
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h ⊢
      refine ⟨?_, ?_, ihb d h.2.2⟩
      · have := Ty.containsBvars_of_openVarsFrom (d + σ.paramCount) Xs h.1
        exact this.mono (by omega)
      · have := ihr (d + σ.paramCount) h.2.1
        exact this.mono (by omega)
  | match_ scrut branches ihs ihbs =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded, BranchList.openTyVarsAux_eq_map,
      Expr.TyBvarBounded.BranchList_iff] at h ⊢
    exact ⟨ihs d h.1, fun p b hmem =>
      ihbs p b hmem d (h.2 p (b.openTyVarsAux d Xs) (List.mem_map_of_mem hmem))⟩
  | letRec anns bindings body ihbs ihb =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h ⊢
    obtain ⟨hsc, hbs, hb⟩ := h
    refine ⟨fun σ hσ => ?_, ?_, ihb d hb⟩
    · have hmem : some ({σ with body := Ty.openVarsFrom (d + σ.paramCount) Xs σ.body})
          ∈ RecGroup.openAnns d Xs anns := by
        simp only [RecGroup.openAnns]
        have := List.mem_map_of_mem
          (f := Option.map (fun σ => { σ with body := Ty.openVarsFrom (d + σ.paramCount) Xs σ.body}))
          hσ
        simpa using this
      exact (Ty.containsBvars_of_openVarsFrom (d + σ.paramCount) Xs (hsc _ hmem)).mono (by omega)
    clear hsc hb ihb
    revert ihbs hbs
    induction bindings generalizing anns with
    | nil => intro _ _; cases anns <;> trivial
    | cons hd tl ih =>
      intro ihbs hbs
      cases anns with
      | nil =>
        simp only [RecGroup.openTyVarsAux, RecGroup.openAnns, List.map_nil,
          Expr.TyBvarBounded.RecGroup] at hbs ⊢
        exact ⟨ihbs hd List.mem_cons_self d hbs.1,
          ih [] (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2⟩
      | cons a as =>
        cases a with
        | none =>
          simp only [RecGroup.openTyVarsAux, RecGroup.openAnns, List.map_cons, Option.map_none,
            Expr.TyBvarBounded.RecGroup, RecAnn.params, Nat.add_zero] at hbs ⊢
          refine ⟨ihbs hd List.mem_cons_self d hbs.1, ?_⟩
          have := ih as (fun e he => ihbs e (List.mem_cons_of_mem _ he))
          rw [RecGroup.openAnns] at this
          exact this hbs.2
        | some σ =>
          simp only [RecGroup.openTyVarsAux, RecGroup.openAnns, List.map_cons, Option.map_some,
            Expr.TyBvarBounded.RecGroup, RecAnn.params] at hbs ⊢
          refine ⟨?_, ?_⟩
          · have hh := ihbs hd List.mem_cons_self (d + σ.paramCount) hbs.1
            rwa [show d + σ.paramCount + Xs.length = d + Xs.length + σ.paramCount
              from by omega] at hh
          · have := ih as (fun e he => ihbs e (List.mem_cons_of_mem _ he))
            rw [RecGroup.openAnns] at this
            exact this hbs.2

/-- **Type-beta / scoped-opening commute (term level).** Opening the result of a
    depth-`d'` type-beta equals type-betaing with the opened type arguments,
    provided `e`'s annotations are bounded by `d' + Ts.length` (so the supplied
    `Ts` cover every scoped bvar — no dangling bvar gets wrongly opened). The
    `shiftBvarsBy` in `openTyFrom` (via `Ty.openVarsFrom_openTyFrom`) makes the
    substituted positions line up. -/
theorem Expr.openTyVarsAux_instTyAux (Ys : List Nat) (Ts : List Ty) :
    ∀ (e : Expr) (d d' : Nat), e.TyBvarBounded (d' + Ts.length) →
      (e.instTyAux d' Ts).openTyVarsAux (d + d') Ys
        = e.instTyAux d' (Ts.map (Ty.openVarsFrom d Ys)) := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d d' _; rfl
  | primBinOp op => intro d d' _; rfl
  | ctor nm => intro d d' _; rfl
  | var n => intro d d' _; rfl
  | app f arg ihf iharg =>
    intro d d' h
    simp only [Expr.instTyAux, Expr.openTyVarsAux, Expr.app.injEq]
    exact ⟨ihf d d' h.1, iharg d d' h.2⟩
  | lambda ann body ih =>
    intro d d' h
    simp only [Expr.instTyAux, Expr.openTyVarsAux, Expr.lambda.injEq]
    refine ⟨?_, ih d d' h.2⟩
    cases ann with
    | none => rfl
    | some t =>
      simp only [Option.map_some, Option.some.injEq]
      exact Ty.openVarsFrom_openTyFrom d' d Ys Ts (h.1 t rfl)
  | letIn ann rhs body ihr ihb =>
    intro d d' h
    cases ann with
    | none =>
      simp only [Expr.instTyAux, Expr.openTyVarsAux, Expr.letIn.injEq, true_and]
      exact ⟨ihr d d' h.1, ihb d d' h.2⟩
    | some σ =>
      obtain ⟨hσ, hr, hb⟩ := h
      have hassoc : d + d' + σ.paramCount = d + (d' + σ.paramCount) := by omega
      simp only [Expr.instTyAux, Expr.openTyVarsAux, hassoc]
      rw [ihr d (d' + σ.paramCount) (by rwa [Nat.add_right_comm]),
          ihb d d' hb,
          Ty.openVarsFrom_openTyFrom (d' + σ.paramCount) d Ys Ts (by rwa [Nat.add_right_comm])]
  | match_ scrut branches ihs ihbs =>
    intro d d' h
    simp only [Expr.instTyAux, Expr.openTyVarsAux, BranchList.instTyAux_eq_map,
      BranchList.openTyVarsAux_eq_map, Expr.match_.injEq, List.map_map]
    obtain ⟨hs, hbs⟩ := h
    rw [Expr.TyBvarBounded.BranchList_iff] at hbs
    refine ⟨ihs d d' hs, ?_⟩
    apply List.map_congr_left
    rintro ⟨p, b⟩ hpb
    simp only [Function.comp_def]
    exact congrArg (Prod.mk p) (ihbs p b hpb d d' (hbs p b hpb))
  | letRec anns bindings body ihbs ihb =>
    intro d d' h
    simp only [Expr.TyBvarBounded] at h
    obtain ⟨hsc, hbs, hb⟩ := h
    simp only [Expr.instTyAux, Expr.openTyVarsAux, Expr.letRec.injEq]
    refine ⟨RecGroup.openAnns_instAnns_comm hsc, ?_, ihb d d' hb⟩
    clear hsc hb ihb
    revert ihbs hbs
    induction bindings generalizing anns with
    | nil => intro _ _; cases anns <;> rfl
    | cons hd tl ih =>
      intro ihbs hbs
      cases anns with
      | nil =>
        simp only [RecGroup.instTyAux, RecGroup.openTyVarsAux, RecGroup.instAnns,
          List.map_nil, Expr.TyBvarBounded.RecGroup, List.cons.injEq] at hbs ⊢
        exact ⟨ihbs hd List.mem_cons_self d d' hbs.1,
          ih [] (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2⟩
      | cons a as =>
        cases a with
        | none =>
          simp only [RecGroup.instTyAux, RecGroup.openTyVarsAux, RecGroup.instAnns,
            List.map_cons, Option.map_none, RecAnn.params, Nat.add_zero,
            Expr.TyBvarBounded.RecGroup, List.cons.injEq] at hbs ⊢
          refine ⟨ihbs hd List.mem_cons_self d d' hbs.1, ?_⟩
          have := ih as (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2
          rwa [RecGroup.instAnns] at this
        | some σ =>
          simp only [RecGroup.instTyAux, RecGroup.openTyVarsAux, RecGroup.instAnns,
            List.map_cons, Option.map_some, RecAnn.params,
            Expr.TyBvarBounded.RecGroup, List.cons.injEq] at hbs ⊢
          refine ⟨?_, ?_⟩
          · have hbnd : hd.TyBvarBounded (d' + σ.paramCount + Ts.length) := by
              have hb1 := hbs.1
              rwa [show d' + Ts.length + σ.paramCount = d' + σ.paramCount + Ts.length
                from by omega] at hb1
            have hh := ihbs hd List.mem_cons_self d (d' + σ.paramCount) hbnd
            rwa [show d + (d' + σ.paramCount) = d + d' + σ.paramCount from by omega] at hh
          · have := ih as (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2
            rwa [RecGroup.instAnns] at this

/-! ### The clean substitution lemma (no side condition!). -/

/-- If `ty`'s bvars are `< n` and `tyArgs` has length `n`, then an `InstantiatesBy`
    instance is exactly `openWith tyArgs`. (Specialises `eq_openWith_range`: the
    range-padding collapses to `tyArgs` when the lengths agree.) -/
theorem InstantiatesBy.eq_openWith {tyArgs : List Ty} {ty τ : Ty} {n : Nat}
    (h : InstantiatesBy tyArgs ty τ) (hbv : ContainsBvarsUpTo n ty) (hlen : tyArgs.length = n) :
    τ = Ty.openWith tyArgs ty := by
  have h1 := InstantiatesBy.eq_openWith_range h hbv
  have h2 : (List.range n).map (fun i => (tyArgs[i]?).getD (Ty.prim PrimTy.unit)) = tyArgs := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, hlen]
    · intro i hi1 _
      rw [List.length_map, List.length_range] at hi1
      rw [List.getElem_map, List.getElem_range,
        List.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [h2] at h1; exact h1

theorem Expr.size_pos (e : Expr) : 0 < e.size := by
  cases e <;> simp [Expr.size]

private theorem Expr.size_le_of_mem_branches {p : MatchPattern} {b : Expr}
    {brs : List (MatchPattern × Expr)} (h : (p, b) ∈ brs) :
    b.size ≤ Expr.sizeBranches brs := by
  induction brs with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p', b'⟩ := hd
    simp only [Expr.sizeBranches]
    rcases List.mem_cons.mp h with heq | hmem
    · rw [Prod.mk.injEq] at heq; obtain ⟨_, rfl⟩ := heq; omega
    · have := ih hmem; omega

private theorem Expr.size_le_of_mem_recGroup {e : Expr} {bs : List Expr} (h : e ∈ bs) :
    e.size ≤ Expr.sizeRecGroup bs := by
  induction bs with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    simp only [Expr.sizeRecGroup]
    rcases List.mem_cons.mp h with heq | hmem
    · subst heq; omega
    · have := ih hmem; omega

/-! ## Preservation

Subject reduction: a well-typed term that takes a step stays well-typed at the
same type. The reduction cases reuse the substitution lemmas; the `matchReduce`
case is the substantial one — it lines up the scrutinee's constructor-chain
typing (`ctor_chain_inversion`) with the matched branch's typing
(`TypeOfElabMatchBranch`), proving that the two type-argument lists agree on the
relevant bvar indices so the field instantiations coincide. -/

/-- `bvarRangeFrom` reads back its definition pointwise. -/
theorem Ty.bvarRangeFrom_getElem? : ∀ (n s k : Nat), k < n →
    (Ty.bvarRangeFrom s n)[k]? = some (.bvar (s + k)) := by
  intro n
  induction n with
  | zero => intro s k hk; omega
  | succ m ih =>
    intro s k hk
    cases k with
    | zero => simp [Ty.bvarRangeFrom]
    | succ j =>
      simp only [Ty.bvarRangeFrom, List.getElem?_cons_succ]
      have heq : s + 1 + j = s + (j + 1) := by omega
      rw [ih (s + 1) j (by omega), heq]

/-- The `k`-th element of `bvarRange n` is `.bvar k` (for `k < n`). -/
theorem Ty.bvarRange_getElem? {n k : Nat} (hk : k < n) :
    (Ty.bvarRange n)[k]? = some (Ty.bvar k) := by
  unfold Ty.bvarRange
  simpa using Ty.bvarRangeFrom_getElem? n 0 k hk

open SmallStep in
/-- A value is applied to a unique constructor name and argument list. -/
theorem SmallStep.CtorAppliedTo.det {e : Expr} {n1 n2 : CtorName} {a1 a2 : List Expr}
    (h1 : CtorAppliedTo e n1 a1) (h2 : CtorAppliedTo e n2 a2) : n1 = n2 ∧ a1 = a2 := by
  induction h1 generalizing n2 a2 with
  | base name => cases h2 with | base => exact ⟨rfl, rfl⟩
  | step h1' ih =>
    cases h2 with
    | step h2' => obtain ⟨hn, ha⟩ := ih h2'; subst hn; subst ha; exact ⟨rfl, rfl⟩

open SmallStep in
/-- The matched branch is a member of the branch list. -/
theorem SmallStep.FirstMatchingBranch.mem {name arity} {branches} {pat body}
    (h : FirstMatchingBranch name arity branches pat body) : (pat, body) ∈ branches := by
  induction h with
  | here _ => exact List.mem_cons_self
  | there _ _ ih => exact List.mem_cons_of_mem _ ih

open SmallStep in
/-- The matched branch's pattern fires for the matched constructor (it either
    names that constructor at the right arity, or is a wildcard). -/
theorem SmallStep.FirstMatchingBranch.ctor_eq {name arity branches pat body}
    (h : FirstMatchingBranch name arity branches pat body) :
    pat.matchesCtor name arity = true := by
  induction h with
  | here hc => exact hc
  | there _ _ ih => exact ih

/-- Element-wise determinism for two `Forall₂ (InstantiatesBy …)` over a common
    source list, given a per-element determinism hypothesis. -/
private theorem InstantiatesBy.forall2_det {tyArgs1 tyArgs2 : List Ty} :
    ∀ {tys its1 its2 : List Ty},
      (∀ t ∈ tys, ∀ {a b : Ty},
        InstantiatesBy tyArgs1 t a → InstantiatesBy tyArgs2 t b → a = b) →
      List.Forall₂ (InstantiatesBy tyArgs1) tys its1 →
      List.Forall₂ (InstantiatesBy tyArgs2) tys its2 →
      its1 = its2 := by
  intro tys
  induction tys with
  | nil =>
    intro its1 its2 _ hf1 hf2
    cases hf1; cases hf2; rfl
  | cons hd tl ih =>
    intro its1 its2 hdet hf1 hf2
    cases hf1 with
    | cons h1hd h1tl =>
      cases hf2 with
      | cons h2hd h2tl =>
        have hhd : _ = _ := hdet hd List.mem_cons_self h1hd h2hd
        have htl := ih (fun t ht => hdet t (List.mem_cons_of_mem _ ht)) h1tl h2tl
        rw [hhd, htl]

/-- Two instantiations of a `ContainsBvarsUpTo n` type coincide whenever the two
    argument lists agree on every index below `n`. -/
theorem InstantiatesBy.det_agree {n : Nat} {tyArgs1 tyArgs2 : List Ty}
    (hag : ∀ k, k < n → tyArgs1[k]? = tyArgs2[k]?) :
    ∀ {ty t1 t2 : Ty}, ContainsBvarsUpTo n ty →
      InstantiatesBy tyArgs1 ty t1 → InstantiatesBy tyArgs2 ty t2 → t1 = t2 := by
  intro ty
  induction ty using Ty.rec_strong with
  | prim _ => intro t1 t2 _ h1 h2; cases h1; cases h2; rfl
  | arrow a b iha ihb =>
    intro t1 t2 hbv h1 h2
    cases hbv with
    | arrow hba hbb =>
      cases h1 with
      | arrow h1a h1b =>
        cases h2 with
        | arrow h2a h2b => rw [iha hba h1a h2a, ihb hbb h1b h2b]
  | bvar i =>
    intro t1 t2 hbv h1 h2
    cases hbv with
    | bvar hlt =>
      cases h1 with
      | bvar hs1 =>
        cases h2 with
        | bvar hs2 => have h := hag i hlt; rw [hs1, hs2] at h; simpa using h
  | fvar _ => intro t1 t2 _ h1 h2; cases h1; cases h2; rfl
  | customTy nm tys ih =>
    intro t1 t2 hbv h1 h2
    cases hbv with
    | customTy hall =>
      cases h1 with
      | customTy hf1 =>
        cases h2 with
        | customTy hf2 =>
          congr 1
          exact InstantiatesBy.forall2_det
            (fun t ht {_ _} ha hb => ih t ht (hall t ht) ha hb) hf1 hf2
  | bl lo hi e ih =>
    intro t1 t2 hbv h1 h2
    cases hbv with
    | bl he_bv =>
      cases h1 with
      | bl he1 =>
        cases h2 with
        | bl he2 =>
          congr 1
          exact ih he_bv he1 he2

/-- Opening scoped type variables is a no-op on a term whose annotation `bvar`s are
    all `< d` (used to bridge an unannotated `let`'s cofinite premise — which types
    the *unopened* bound expression — to `HasSchemeVars`). -/
theorem Expr.openTyVarsAux_eq_self_of_tyBvarBounded (Xs : List Nat) :
    ∀ (e : Expr) (d : Nat), e.TyBvarBounded d → e.openTyVarsAux d Xs = e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d _; rfl
  | primBinOp op => intro d _; rfl
  | ctor nm => intro d _; rfl
  | var i => intro d _; rfl
  | lambda ann body ih =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h ⊢
    obtain ⟨hann, hbody⟩ := h
    rw [ih d hbody, Expr.lambda.injEq]
    refine ⟨?_, rfl⟩
    cases ann with
    | none => rfl
    | some t =>
      simp only [Option.map_some, Option.some.injEq]
      exact Ty.openVarsFrom_eq_self_of_bvars (hann t rfl)
  | app f arg ihf iharg =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h ⊢
    obtain ⟨hf, ha⟩ := h
    rw [ihf d hf, iharg d ha]
  | letIn ann rhs body ihr ihb =>
    intro d h
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h ⊢
      obtain ⟨hr, hb⟩ := h
      rw [ihr d hr, ihb d hb]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h ⊢
      obtain ⟨hσ, hr, hb⟩ := h
      rw [ihr (d + σ.paramCount) hr, ihb d hb, Ty.openVarsFrom_eq_self_of_bvars hσ]
  | match_ scrut branches ihs ihbs =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded, BranchList.openTyVarsAux_eq_map] at h ⊢
    obtain ⟨hs, hbs⟩ := h
    rw [Expr.TyBvarBounded.BranchList_iff] at hbs
    rw [ihs d hs, Expr.match_.injEq]
    refine ⟨rfl, ?_⟩
    conv_rhs => rw [← List.map_id branches]
    apply List.map_congr_left
    rintro ⟨p, b⟩ hpb
    simp only [id_eq]
    rw [ihbs p b hpb d (hbs p b hpb)]
  | letRec anns bindings body ihbs ihb =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h ⊢
    obtain ⟨hsc, hbs, hb⟩ := h
    rw [ihb d hb, Expr.letRec.injEq]
    refine ⟨RecGroup.openAnns_eq_self_of_bvars hsc, ?_, rfl⟩
    clear hsc hb ihb
    revert ihbs hbs
    induction bindings generalizing anns with
    | nil => intro _ _; cases anns <;> rfl
    | cons hd tl ih =>
      intro ihbs hbs
      cases anns with
      | nil =>
        simp only [RecGroup.openTyVarsAux, Expr.TyBvarBounded.RecGroup,
          List.cons.injEq] at hbs ⊢
        exact ⟨ihbs hd List.mem_cons_self d hbs.1,
          ih [] (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2⟩
      | cons a as =>
        simp only [RecGroup.openTyVarsAux, Expr.TyBvarBounded.RecGroup,
          List.cons.injEq] at hbs ⊢
        exact ⟨ihbs hd List.mem_cons_self (d + RecAnn.params a) hbs.1,
          ih as (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2⟩

/-- Build a `Forall₂` from a length match plus a per-zipped-pair witness. -/
theorem List.forall₂_of_mem_zip {α β : Type _} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, l₁.length = l₂.length →
      (∀ p ∈ l₁.zip l₂, R p.1 p.2) → List.Forall₂ R l₁ l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ hlen _; cases l₂ with | nil => exact .nil | cons => simp at hlen
  | cons a as ih =>
    intro l₂ hlen hzip
    cases l₂ with
    | nil => simp at hlen
    | cons b bs =>
      refine List.Forall₂.cons (hzip (a, b) ?_) (ih (by simpa using hlen) ?_)
      · simp [List.zip_cons_cons]
      · intro p hp
        exact hzip p (by simp only [List.zip_cons_cons, List.mem_cons]; exact .inr hp)

/-- A member of `l.zip (l.map g)` has its second component determined by the
    first via `g`. -/
private theorem List.mem_zip_self_map {α β : Type _} {g : α → β} {l : List α} {p : α × β}
    (h : p ∈ l.zip (l.map g)) : p.2 = g p.1 := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    cases h with
    | inl heq => subst heq; rfl
    | inr h' => exact ih h'

/-- If `r` has the same length as `l` and `r` is pointwise `f` of `l` (over the
    zip), then `r = l.map f`. -/
private theorem List.map_eq_of_zip {α β : Type _} {f : α → β} :
    ∀ {l : List α} {r : List β}, l.length = r.length →
      (∀ p ∈ l.zip r, p.2 = f p.1) → r = l.map f := by
  intro l
  induction l with
  | nil => intro r hlen _; cases r with | nil => rfl | cons => simp at hlen
  | cons a as ih =>
    intro r hlen hz
    cases r with
    | nil => simp at hlen
    | cons b bs =>
      have hhd : b = f a := hz (a, b) (by simp [List.zip_cons_cons])
      have htl : bs = as.map f :=
        ih (by simpa using hlen)
          (fun p hp => hz p (by simp only [List.zip_cons_cons, List.mem_cons]; exact .inr hp))
      rw [List.map_cons, hhd, htl]

/-- `genGroup` at the empty pool is the trivial scheme: there is nothing to
    generalise. -/
private theorem PolyTy.genGroup_nil {t : Ty} : PolyTy.genGroup [] t = PolyTy.mkTrivial t := by
  have hgf : Ty.genFilter [] t = [] := rfl
  have hcl : Ty.closeOver [] t = t := Ty.closeOver_eq_self_of_fresh (by simp)
  simp only [PolyTy.genGroup, hgf, List.length_nil, hcl, PolyTy.mkTrivial]

/-- Renaming the empty pool is the identity. -/
private theorem Ty.renameG_nil {τ : Ty} : Ty.renameG [] [] τ = τ := rfl

/-- **renameG factors through `genFilter`.** Renaming all of `G` to a fresh,
    `τ`-avoiding pool `W` equals renaming only the relevant slice
    `genFilter G τ ↦ genFilter W (renameG G W τ)` (the gen-vars actually
    occurring in `τ`). The dropped part of `G` does not occur in `τ`. -/
theorem Ty.renameG_eq_genFilter {G W : List Nat} {τ : Ty}
    (hlen : W.length = G.length) (hG : G.Nodup) (hW : W.Nodup)
    (hdisj : ∀ g ∈ G, g ∉ W) (hfresh : ∀ w ∈ W, w ∉ τ.freeVars) :
    Ty.renameG G W τ = Ty.renameG (Ty.genFilter G τ) (Ty.genFilter W (Ty.renameG G W τ)) τ := by
  have hGW : G.length ≤ W.length := le_of_eq hlen.symm
  have hOCC : ∀ p ∈ G.zip W, (p.2 ∈ (Ty.renameG G W τ).freeVars ↔ p.1 ∈ τ.freeVars) := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
    rw [List.getElem?_zip_eq_some] at hi
    obtain ⟨hiG, hiW⟩ := hi
    exact Ty.mem_freeVars_renameG_iff hlen hG hW hdisj hfresh hiG hiW
  obtain ⟨hAL1, hAL2⟩ := Ty.genFilter_zip_proj hlen hOCC
  have hkey : ((G.zip (W.map (Ty.fvar ·))).map Prod.fst).Nodup := by
    rw [List.map_fst_zip (by rw [List.length_map]; exact hGW)]; exact hG
  have hval : ∀ p ∈ G.zip (W.map (Ty.fvar ·)),
      ∀ k ∈ (G.zip (W.map (Ty.fvar ·))).map Prod.fst, k ∉ p.2.freeVars := by
    intro p hp k hk
    rw [List.map_fst_zip (by rw [List.length_map]; exact hGW)] at hk
    obtain ⟨w, hw, hpw⟩ := List.mem_map.mp (List.of_mem_zip hp).2
    rw [← hpw]
    simp only [Ty.freeVars, List.mem_singleton]
    intro hkw; exact hdisj w (hkw ▸ hk) hw
  have hsubeq : (Ty.genFilter G τ).zip ((Ty.genFilter W (Ty.renameG G W τ)).map (Ty.fvar ·))
      = (G.zip (W.map (Ty.fvar ·))).filter (fun p => decide (p.1 ∈ τ.freeVars)) := by
    rw [hAL1, hAL2, List.map_map, List.zip_map']
    exact List.filter_zip_map_fvar
  show Ty.substFvars (G.zip (W.map (Ty.fvar ·))) τ
      = Ty.substFvars ((Ty.genFilter G τ).zip ((Ty.genFilter W (Ty.renameG G W τ)).map (Ty.fvar ·))) τ
  rw [hsubeq]
  exact Ty.substFvars_filter_freeVars hkey hval

/-! ## Multi-step type safety (closure machinery)

The single-step `progress`/`preservation` are lifted to the reflexive-transitive
closure of `Step`: a closed, well-typed program never gets stuck across *any*
number of steps and keeps its type throughout. The ingredient is the closure
lemma `Step.preserves_exhaustive` (so `progress` can be re-applied to every
reachable term), resting on the fact that reduction's substitutions
(`substN`/`shiftFrom`) preserve `AllMatchesExhaustive`. -/

/-- The shifted image of a branch is a member of the shifted branch list. -/
theorem BranchList.mem_shiftFrom_of_mem {threshold n : Nat}
    {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : (pat, body) ∈ branches) :
    (pat, body.shiftFrom (threshold + pat.bindCount) n)
      ∈ BranchList.shiftFrom threshold n branches := by
  induction branches with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [BranchList.shiftFrom, List.mem_cons] at h ⊢
    cases h with
    | inl heq => simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact Or.inl rfl
    | inr h' => exact Or.inr (ih h')

/-- The substituted image of a branch is a member of the substituted branch list. -/
theorem BranchList.mem_substN_of_mem {k : Nat} {vs : List Expr}
    {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : (pat, body) ∈ branches) :
    (pat, body.substN (k + pat.bindCount) vs) ∈ BranchList.substN k vs branches := by
  induction branches with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [BranchList.substN, List.mem_cons] at h ⊢
    cases h with
    | inl heq => simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact Or.inl rfl
    | inr h' => exact Or.inr (ih h')

namespace SmallStep

/-- `shiftFrom` preserves branch-body exhaustiveness (companion to
    `AllMatchesExhaustive.shiftFrom`). -/
theorem AllBranchBodiesExhaustive.shiftFrom {ctors : CtorEnv} {threshold n : Nat}
    {branches : List (MatchPattern × Expr)}
    (ih : ∀ pat e, (pat, e) ∈ branches →
      AllMatchesExhaustive ctors e → ∀ (threshold n : Nat),
        AllMatchesExhaustive ctors (e.shiftFrom threshold n))
    (h : AllBranchBodiesExhaustive ctors branches) :
    AllBranchBodiesExhaustive ctors (BranchList.shiftFrom threshold n branches) := by
  induction branches with
  | nil => exact .nil
  | cons hd tl ih_tl =>
    obtain ⟨pat, body⟩ := hd
    cases h with
    | cons hbody hrest =>
      simp only [BranchList.shiftFrom]
      exact .cons (ih pat body List.mem_cons_self hbody (threshold + pat.bindCount) n)
        (ih_tl (fun p e hm hae => ih p e (List.mem_cons_of_mem _ hm) hae) hrest)

/-- `shiftFrom` (a term-variable renumbering) preserves match-exhaustiveness: it
    never touches a match's patterns or the ctor env, only `.var` indices. -/
theorem AllMatchesExhaustive.shiftFrom {ctors : CtorEnv} :
    ∀ {e : Expr}, AllMatchesExhaustive ctors e → ∀ (threshold n : Nat),
      AllMatchesExhaustive ctors (e.shiftFrom threshold n) := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _ threshold n; exact .primLit
  | primBinOp op => intro _ _ _; exact .primBinOp
  | var m => intro _ threshold n; simp only [Expr.shiftFrom]; split <;> exact .var
  | ctor nm => intro _ threshold n; exact .ctor
  | lambda ann body ih =>
    intro h threshold n; cases h with
    | lambda hb => simp only [Expr.shiftFrom]; exact .lambda (ih hb (threshold + 1) n)
  | app f arg ihf iharg =>
    intro h threshold n; cases h with
    | app hf ha => simp only [Expr.shiftFrom]; exact .app (ihf hf threshold n) (iharg ha threshold n)
  | letIn ann rhs body ihr ihb =>
    intro h threshold n; cases h with
    | letIn hr hb =>
      simp only [Expr.shiftFrom]; exact .letIn (ihr hr threshold n) (ihb hb (threshold + 1) n)
  | match_ scrut branches ihs ihbr =>
    intro h threshold n; cases h with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      simp only [Expr.shiftFrom]
      exact AllMatchesExhaustive.match_ (ihs h_scrut threshold n)
        (AllBranchBodiesExhaustive.shiftFrom ihbr h_bodies)
        (fun c n body hmem => by
          obtain ⟨p, b, hm, heq⟩ := BranchList.mem_shiftFrom hmem
          rw [Prod.mk.injEq] at heq
          obtain ⟨hp, -⟩ := heq
          subst hp
          exact h_cover1 c n b hm)
        (fun ctorName ctor hlook htyName => by
          obtain ⟨pat, body, hmem, hcov⟩ := h_cover2 ctorName ctor hlook htyName
          exact ⟨pat, body.shiftFrom (threshold + pat.bindCount) n,
            BranchList.mem_shiftFrom_of_mem hmem, hcov⟩)
  | letRec anns bindings body ih_bindings ih_body =>
    intro h threshold n; cases h with
    | letRec hbindings hbody =>
      simp only [Expr.shiftFrom]
      refine .letRec ?_ (ih_body hbody (threshold + bindings.length) n)
      intro e he
      rw [RecGroup.shiftFrom_eq_map] at he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      exact ih_bindings e' he' (hbindings e' he') (threshold + bindings.length) n

/-- `instTy` preserves branch-body exhaustiveness (companion to
    `AllMatchesExhaustive.instTyAux`). -/
private theorem AllBranchBodiesExhaustive.instTyAux_aux {ctors : CtorEnv}
    {d : Nat} {Ts : List Ty} :
    ∀ (brs : List (MatchPattern × Expr)),
      (∀ p b, (p, b) ∈ brs → AllMatchesExhaustive ctors b →
        AllMatchesExhaustive ctors (b.instTyAux d Ts)) →
      AllBranchBodiesExhaustive ctors brs →
      AllBranchBodiesExhaustive ctors (BranchList.instTyAux d Ts brs) := by
  intro brs
  induction brs with
  | nil => intro _ _; exact .nil
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    intro hopen hbb
    cases hbb with
    | cons hbody hrest =>
      simp only [BranchList.instTyAux]
      exact .cons (hopen p b List.mem_cons_self hbody)
        (ih (fun p' b' hm => hopen p' b' (List.mem_cons_of_mem _ hm)) hrest)

/-- `instTy` (type-beta) preserves match-exhaustiveness: it only rewrites type
    annotations, never a match's patterns or the ctor env. `d` is generalized
    because an annotated `letIn`'s bound expression is type-beta'd at a deeper depth. -/
theorem AllMatchesExhaustive.instTyAux {ctors : CtorEnv} (Ts : List Ty) :
    ∀ (e : Expr) (d : Nat), AllMatchesExhaustive ctors e →
      AllMatchesExhaustive ctors (e.instTyAux d Ts) := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _ _; exact .primLit
  | primBinOp op => intro _ _; exact .primBinOp
  | var i =>  intro _ _; exact .var
  | ctor nm => intro _ _; exact .ctor
  | lambda ann body ih => intro d h; cases h with | lambda hb => exact .lambda (ih d hb)
  | app f arg ihf iharg =>
    intro d h; cases h with | app hf ha => exact .app (ihf d hf) (iharg d ha)
  | letIn ann rhs body ihr ihb =>
    intro d h
    cases h with
    | letIn hr hb =>
      cases ann with
      | none => exact .letIn (ihr d hr) (ihb d hb)
      | some σ => exact .letIn (ihr (d + σ.paramCount) hr) (ihb d hb)
  | match_ scrut branches ihs ihbs =>
    intro d h
    cases h with
    | match_ hscrut hbranches hpinned hcover =>
      expose_names
      simp only [Expr.instTyAux]
      refine .match_ (tyName := tyName) (ihs d hscrut)
        (AllBranchBodiesExhaustive.instTyAux_aux branches
          (fun p b hm hb => ihbs p b hm d hb) hbranches) ?_ ?_
      · intro c n body' hmem
        rw [BranchList.instTyAux_eq_map, List.mem_map] at hmem
        obtain ⟨⟨p, b⟩, hmem0, heq⟩ := hmem
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact hpinned c n b hmem0
      · intro ctorName ctor hlook htyn
        obtain ⟨pat, body, hmem, hcov⟩ := hcover ctorName ctor hlook htyn
        refine ⟨pat, body.instTyAux d Ts, ?_, hcov⟩
        rw [BranchList.instTyAux_eq_map]
        exact List.mem_map_of_mem hmem
  | letRec anns bindings body ihbs ihb =>
    intro d h
    cases h with
    | letRec hbs hb =>
      simp only [Expr.instTyAux]
      refine .letRec ?_ (ihb d hb)
      intro e hmem
      rw [RecGroup.instTyAux_eq_zip, List.mem_map] at hmem
      obtain ⟨p, hp, rfl⟩ := hmem
      exact ihbs p.1 (List.of_mem_zip hp).1 p.2 (hbs p.1 (List.of_mem_zip hp).1)

/-- `instTy` preserves match-exhaustiveness (depth-0 corollary). -/
theorem AllMatchesExhaustive.instTy {ctors : CtorEnv} {e : Expr} (Ts : List Ty)
    (h : AllMatchesExhaustive ctors e) : AllMatchesExhaustive ctors (e.instTy Ts) :=
  AllMatchesExhaustive.instTyAux Ts e 0 h

/-- `substN` preserves branch-body exhaustiveness (companion to
    `AllMatchesExhaustive.substN`). -/
theorem AllBranchBodiesExhaustive.substN {ctors : CtorEnv} {k : Nat} {vs : List Expr}
    {branches : List (MatchPattern × Expr)}
    (ih : ∀ pat e, (pat, e) ∈ branches →
      AllMatchesExhaustive ctors e → ∀ (k' : Nat),
        AllMatchesExhaustive ctors (e.substN k' vs))
    (h : AllBranchBodiesExhaustive ctors branches) :
    AllBranchBodiesExhaustive ctors (BranchList.substN k vs branches) := by
  induction branches with
  | nil => exact .nil
  | cons hd tl ih_tl =>
    obtain ⟨pat, body⟩ := hd
    cases h with
    | cons hbody hrest =>
      simp only [BranchList.substN]
      exact .cons (ih pat body List.mem_cons_self hbody (k + pat.bindCount))
        (ih_tl (fun p e hm hae => ih p e (List.mem_cons_of_mem _ hm) hae) hrest)

/-- `substN` preserves match-exhaustiveness, provided every substituted value is
    exhaustive: substitution leaves a match's patterns and the ctor env untouched,
    so coverage is unchanged; the only inserted sub-terms are the (exhaustive)
    values, shifted by `shiftFrom` (which also preserves exhaustiveness). -/
theorem AllMatchesExhaustive.substN {ctors : CtorEnv} {vs : List Expr}
    (hvs : ∀ v ∈ vs, AllMatchesExhaustive ctors v) :
    ∀ {e : Expr}, AllMatchesExhaustive ctors e → ∀ (k : Nat),
      AllMatchesExhaustive ctors (e.substN k vs) := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _ k; exact .primLit
  | primBinOp op => intro _ _; exact .primBinOp
  | var m =>
    intro _ k
    simp only [Expr.substN]
    split
    · exact .var
    · split
      · next h => exact AllMatchesExhaustive.shiftFrom (hvs _ (List.getElem_mem h)) 0 k
      · exact .var
  | ctor nm => intro _ k; exact .ctor
  | lambda ann body ih =>
    intro h k; cases h with
    | lambda hb => simp only [Expr.substN]; exact .lambda (ih hb (k + 1))
  | app f arg ihf iharg =>
    intro h k; cases h with
    | app hf ha => simp only [Expr.substN]; exact .app (ihf hf k) (iharg ha k)
  | letIn ann rhs body ihr ihb =>
    intro h k; cases h with
    | letIn hr hb => simp only [Expr.substN]; exact .letIn (ihr hr k) (ihb hb (k + 1))
  | match_ scrut branches ihs ihbr =>
    intro h k; cases h with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      simp only [Expr.substN]
      exact AllMatchesExhaustive.match_ (ihs h_scrut k)
        (AllBranchBodiesExhaustive.substN ihbr h_bodies)
        (fun c n body hmem => by
          obtain ⟨p, b, hm, heq⟩ := BranchList.mem_substN hmem
          rw [Prod.mk.injEq] at heq
          obtain ⟨hp, -⟩ := heq
          subst hp
          exact h_cover1 c n b hm)
        (fun ctorName ctor hlook htyName => by
          obtain ⟨pat, body, hmem, hcov⟩ := h_cover2 ctorName ctor hlook htyName
          exact ⟨pat, body.substN (k + pat.bindCount) vs,
            BranchList.mem_substN_of_mem hmem, hcov⟩)
  | letRec anns bindings body ih_bindings ih_body =>
    intro h k; cases h with
    | letRec hbindings hbody =>
      simp only [Expr.substN]
      refine .letRec ?_ (ih_body hbody (k + bindings.length))
      intro e he
      rw [RecGroup.substN_eq_map] at he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      exact ih_bindings e' he' (hbindings e' he') (k + bindings.length)

/-- The substituted image of a branch is a member of the `substTyFvar`ed list. -/
theorem BranchList.mem_substTyFvar_of_mem {Z : Nat} {U : Ty}
    {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : (pat, body) ∈ branches) :
    (pat, body.substTyFvar Z U) ∈ BranchList.substTyFvar Z U branches := by
  induction branches with
  | nil => exact absurd h List.not_mem_nil
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [BranchList.substTyFvar, List.mem_cons] at h ⊢
    cases h with
    | inl heq =>
      simp only [Prod.mk.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; exact Or.inl rfl
    | inr h' => exact Or.inr (ih h')

/-- Companion: `substTyFvar` preserves branch-body exhaustiveness. -/
private theorem AllBranchBodiesExhaustive.substTyFvar {ctors : CtorEnv} {Z : Nat} {U : Ty}
    {branches : List (MatchPattern × Expr)}
    (ih : ∀ pat e, (pat, e) ∈ branches → AllMatchesExhaustive ctors e →
      AllMatchesExhaustive ctors (e.substTyFvar Z U))
    (h : AllBranchBodiesExhaustive ctors branches) :
    AllBranchBodiesExhaustive ctors (BranchList.substTyFvar Z U branches) := by
  induction branches with
  | nil => exact .nil
  | cons hd tl ih_tl =>
    obtain ⟨pat, body⟩ := hd
    cases h with
    | cons hbody hrest =>
      simp only [BranchList.substTyFvar]
      exact .cons (ih pat body List.mem_cons_self hbody)
        (ih_tl (fun p e hm hae => ih p e (List.mem_cons_of_mem _ hm) hae) hrest)

/-- Single-step `substTyFvar` preserves match-exhaustiveness: it only rewrites
    type annotations / var tyArgs, never match patterns or the ctor env. -/
theorem AllMatchesExhaustive.substTyFvar {ctors : CtorEnv} (Z : Nat) (U : Ty) :
    ∀ {e : Expr}, AllMatchesExhaustive ctors e →
      AllMatchesExhaustive ctors (e.substTyFvar Z U) := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro _; exact .primLit
  | primBinOp op => intro _; exact .primBinOp
  | var i =>  intro _; exact .var
  | ctor nm => intro _; exact .ctor
  | lambda ann body ih =>
    intro h; cases h with | lambda hb => exact .lambda (ih hb)
  | app f arg ihf iharg =>
    intro h; cases h with | app hf ha => exact .app (ihf hf) (iharg ha)
  | letIn ann rhs body ihr ihb =>
    intro h; cases h with | letIn hr hb => exact .letIn (ihr hr) (ihb hb)
  | match_ scrut branches ihs ihbs =>
    intro h
    cases h with
    | match_ hscrut hbranches hpinned hcover =>
      expose_names
      simp only [Expr.substTyFvar]
      refine .match_ (tyName := tyName) (ihs hscrut)
        (AllBranchBodiesExhaustive.substTyFvar
          (fun p b hm hb => ihbs p b hm hb) hbranches) ?_ ?_
      · intro c n body' hmem
        obtain ⟨p, b, hmem0, heq⟩ := BranchList.mem_substTyFvar hmem
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        exact hpinned c n b hmem0
      · intro ctorName ctor hlook htyn
        obtain ⟨pat, body, hmem, hcov⟩ := hcover ctorName ctor hlook htyn
        exact ⟨pat, body.substTyFvar Z U, BranchList.mem_substTyFvar_of_mem hmem, hcov⟩
  | letRec anns bindings body ihbs ihb =>
    intro h
    cases h with
    | letRec hbs hb =>
      simp only [Expr.substTyFvar, RecGroup.substTyFvar_eq_map]
      refine .letRec ?_ (ihb hb)
      intro e hmem
      rw [List.mem_map] at hmem
      obtain ⟨e0, he0, rfl⟩ := hmem
      exact ihbs e0 he0 (hbs e0 he0)

/-- Iterated `substTyFvars` preserves match-exhaustiveness. -/
theorem AllMatchesExhaustive.substTyFvars {ctors : CtorEnv} (S : List (Nat × Ty)) :
    ∀ {e : Expr}, AllMatchesExhaustive ctors e →
      AllMatchesExhaustive ctors (e.substTyFvars S) := by
  induction S with
  | nil => intro e h; simpa [Expr.substTyFvars] using h
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    intro e h
    simp only [Expr.substTyFvars]
    exact ih (AllMatchesExhaustive.substTyFvar Z U h)

/-- Every argument of a constructor-chain value is exhaustive if the chain is. -/
theorem CtorAppliedTo.args_exhaustive {ctors : CtorEnv} {e : Expr} {name : CtorName}
    {args : List Expr} (h : CtorAppliedTo e name args)
    (he : AllMatchesExhaustive ctors e) : ∀ a ∈ args, AllMatchesExhaustive ctors a := by
  induction h with
  | base name => intro a ha; exact absurd ha List.not_mem_nil
  | step _ ih =>
    cases he with
    | app hf harg =>
      intro a ha
      rw [List.mem_append] at ha
      cases ha with
      | inl h_in => exact ih hf a h_in
      | inr h_in => rw [List.mem_singleton] at h_in; subst h_in; exact harg

/-- A branch body drawn from an exhaustively-checked branch list is itself
    exhaustive. -/
theorem AllBranchBodiesExhaustive.mem {ctors : CtorEnv} :
    ∀ {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr},
      AllBranchBodiesExhaustive ctors branches → (pat, body) ∈ branches →
      AllMatchesExhaustive ctors body := by
  intro branches
  induction branches with
  | nil => intro pat body _ hmem; exact absurd hmem List.not_mem_nil
  | cons hd tl ih =>
    intro pat body h hmem
    obtain ⟨pat', body'⟩ := hd
    cases h with
    | cons hbody hrest =>
      cases hmem with
      | head => exact hbody
      | tail _ hmem' => exact ih hrest hmem'

/-- **Reduction preserves match-exhaustiveness.** Reduction never invents new
    match patterns: congruence steps keep the same matches, and the substituting
    steps insert exhaustive values into exhaustive bodies (`AllMatchesExhaustive`
    is closed under `substN`). The `matchReduce` case selects a branch body, which
    is exhaustive because the whole branch list was. -/
theorem Step.preserves_exhaustive {ctors : CtorEnv} {e e' : Expr}
    (h_exh : AllMatchesExhaustive ctors e) (h_step : Step e e') :
    AllMatchesExhaustive ctors e' := by
  induction h_step with
  | beta hval =>
    cases h_exh with
    | app h_lam h_v =>
      cases h_lam with
      | lambda h_body =>
        exact AllMatchesExhaustive.substN
          (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact h_v) h_body 0
  | letReduce =>
    cases h_exh with
    | letIn h_v h_body =>
      exact AllMatchesExhaustive.substN
        (fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact h_v) h_body 0
  | deltaIntAdd => exact .primLit
  | deltaIntSub => exact .primLit
  | deltaIntLt => exact .ctor
  | deltaCharLt => exact .ctor
  | matchReduce hval hctor hfirst =>
    cases h_exh with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      exact AllMatchesExhaustive.substN
        (fun a ha => CtorAppliedTo.args_exhaustive hctor h_scrut a (List.mem_of_mem_take ha))
        (h_bodies.mem hfirst.mem) 0
  | matchWildReduce hval hnc =>
    rename_i scrut body rest
    cases h_exh with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      exact h_bodies.mem (List.mem_cons_self ..)
  | appFn _ ih => cases h_exh with | app hf ha => exact .app (ih hf) ha
  | appArg hv _ ih => cases h_exh with | app hf ha => exact .app hf (ih ha)
  | matchScrut _ ih =>
    cases h_exh with
    | match_ h_scrut h_bodies h_cover1 h_cover2 =>
      exact .match_ (ih h_scrut) h_bodies h_cover1 h_cover2
  | letRecUnfold =>
    rename_i anns bindings body
    cases h_exh with
    | letRec hbindings hbody =>
      refine AllMatchesExhaustive.substN ?_ hbody 0
      intro v hv
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hv
      exact .letRec hbindings (hbindings e' he')

end SmallStep

/-! ## Term-level closedness: `Expr.varsBelow`

Core has `Ty.isClosed` for types but no term-level free-variable
machinery. The verified pattern-compilation campaign needs this:
captured scrutinee sub-values are closed, so `substN`/`shiftFrom`
leave them untouched as they are pushed through emitted nested matches.
`Expr.varsBelow n e` = every free term-var of `e` is `< n`;
`e.varsBelow 0` = closed. Type-level variables are irrelevant throughout. -/

mutual

/-- Every free term-var of `e` is `< n`. Binders raise the bound: `lambda`/
    `letIn` bodies by 1, a match branch body by its pattern's `bindCount`, a
    `letRec` group's bindings and body by the group size (mirroring
    `Expr.shiftFrom`/`Expr.substN`'s threshold bookkeeping). -/
def Expr.varsBelow (n : Nat) : Expr → Bool
  | .var i => decide (i < n)
  | .primLit _ => true
  | .primBinOp _ => true
  | .ctor _ => true
  | .lambda _ body => Expr.varsBelow (n + 1) body
  | .app f arg => Expr.varsBelow n f && Expr.varsBelow n arg
  | .letIn _ rhs body => Expr.varsBelow n rhs && Expr.varsBelow (n + 1) body
  | .match_ scrut branches =>
      Expr.varsBelow n scrut && BranchListClosed.varsBelow n branches
  | .letRec _ bindings body =>
      RecGroupClosed.varsBelow (n + bindings.length) bindings
        && Expr.varsBelow (n + bindings.length) body

def BranchListClosed.varsBelow (n : Nat) : List (MatchPattern × Expr) → Bool
  | [] => true
  | (pat, body) :: rest =>
      Expr.varsBelow (n + pat.bindCount) body
        && BranchListClosed.varsBelow n rest

def RecGroupClosed.varsBelow (n : Nat) : List Expr → Bool
  | [] => true
  | e :: rest => Expr.varsBelow n e && RecGroupClosed.varsBelow n rest

end

/-! ## Monotonicity

Raising the bound preserves `varsBelow`: if every free var is `< m` and `m ≤ n`,
then every free var is `< n`. Proved by structural induction on the expression
(via `Expr.rec_strong`), with the branch-list / rec-group companions handling the
embedded lists. -/

/-- Monotonicity of `Expr.varsBelow` in the bound. -/
theorem Expr.varsBelow_mono (e : Expr) :
    ∀ {m n : Nat}, m ≤ n → Expr.varsBelow m e = true → Expr.varsBelow n e = true := by
  induction e using Expr.rec_strong with
  | primLit p => intro m n _ _; rfl
  | primBinOp op => intro m n _ _; rfl
  | ctor nm => intro m n _ _; rfl
  | var i => 
    intro m n hmn h
    simp only [Expr.varsBelow, decide_eq_true_eq] at h ⊢
    omega
  | lambda ann body ih =>
    intro m n hmn h
    simp only [Expr.varsBelow] at h ⊢
    exact ih (by omega) h
  | app f arg ihf iharg =>
    intro m n hmn h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨ihf hmn h.1, iharg hmn h.2⟩
  | letIn ann rhs body ihrhs ihbody =>
    intro m n hmn h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨ihrhs hmn h.1, ihbody (by omega : m + 1 ≤ n + 1) h.2⟩
  | match_ scrut branches ihscrut ihbrs =>
    intro m n hmn h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨ihscrut hmn h1, ?_⟩
    have key : ∀ (brs : List (MatchPattern × Expr)),
        (∀ pat e, (pat, e) ∈ brs →
          ∀ a b, a ≤ b → Expr.varsBelow a e = true → Expr.varsBelow b e = true) →
        BranchListClosed.varsBelow m brs = true → BranchListClosed.varsBelow n brs = true := by
      intro brs
      induction brs with
      | nil => intro _ _; rfl
      | cons hd tl ih =>
        obtain ⟨pat, body⟩ := hd
        intro hmono hh
        simp only [BranchListClosed.varsBelow, Bool.and_eq_true] at hh ⊢
        refine ⟨hmono pat body List.mem_cons_self _ _ (by omega) hh.1, ?_⟩
        exact ih (fun p e hmem => hmono p e (List.mem_cons_of_mem _ hmem)) hh.2
    exact key branches ihbrs h2
  | letRec anns bindings body ihbindings ihbody =>
    intro m n hmn h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ihbody (by omega : m + bindings.length ≤ n + bindings.length) h2⟩
    have key : ∀ (bs : List Expr),
        (∀ e ∈ bs, ∀ a b, a ≤ b → Expr.varsBelow a e = true → Expr.varsBelow b e = true) →
        RecGroupClosed.varsBelow (m + bindings.length) bs = true →
        RecGroupClosed.varsBelow (n + bindings.length) bs = true := by
      intro bs
      induction bs with
      | nil => intro _ _; rfl
      | cons hd tl ih =>
        intro hmono hh
        simp only [RecGroupClosed.varsBelow, Bool.and_eq_true] at hh ⊢
        refine ⟨hmono hd List.mem_cons_self _ _ (by omega) hh.1, ?_⟩
        exact ih (fun e hmem => hmono e (List.mem_cons_of_mem _ hmem)) hh.2
    exact key bindings ihbindings h1

/-- Branch-list companion of `Expr.varsBelow_mono`. -/
theorem BranchListClosed.varsBelow_mono {m n : Nat} (hmn : m ≤ n) :
    ∀ (branches : List (MatchPattern × Expr)),
      BranchListClosed.varsBelow m branches = true → BranchListClosed.varsBelow n branches = true := by
  intro branches
  induction branches with
  | nil => intro _; rfl
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    intro h
    simp only [BranchListClosed.varsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.varsBelow_mono body (by omega : m + pat.bindCount ≤ n + pat.bindCount) h.1, ih h.2⟩

/-- Rec-group companion of `Expr.varsBelow_mono`. -/
theorem RecGroupClosed.varsBelow_mono {m n : Nat} (hmn : m ≤ n) :
    ∀ (bindings : List Expr),
      RecGroupClosed.varsBelow m bindings = true → RecGroupClosed.varsBelow n bindings = true := by
  intro bindings
  induction bindings with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro h
    simp only [RecGroupClosed.varsBelow, Bool.and_eq_true] at h ⊢
    exact ⟨Expr.varsBelow_mono hd hmn h.1, ih h.2⟩

/-! ## `shiftFrom` is the identity on terms with all vars below the shift threshold

`Expr.shiftFrom`'s branch-list / rec-group companions are `private` in Core, so we
cannot name them. We instead work through the `match_`/`letRec` nodes themselves:
tiny structural projections (`matchBranchesOf`, `letRecBindingsOf`, `letRecBodyOf`)
let us state the branch/binding equalities that Core's private helpers produce, and
these reduce definitionally against `Expr.shiftFrom`/`Expr.substN`. -/

/-- Project the branch list of a `match_` (else `[]`). -/
def Expr.matchBranchesOf : Expr → List (MatchPattern × Expr)
  | .match_ _ brs => brs
  | _ => []

/-- Project the binding list of a `letRec` (else `[]`). -/
def Expr.letRecBindingsOf : Expr → List Expr
  | .letRec _ bs _ => bs
  | _ => []

/-- Rewrite the whole map to the list when it is pointwise the identity. -/
private theorem List.map_self_of_mem {α : Type _} {f : α → α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = a) → l.map f = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
    intro h
    simp only [List.map_cons]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Each branch body of a closed branch list is closed under its raised bound. -/
theorem BranchListClosed.varsBelow_of_mem {n : Nat} :
    ∀ {brs : List (MatchPattern × Expr)}, BranchListClosed.varsBelow n brs = true →
      ∀ pat body, (pat, body) ∈ brs → Expr.varsBelow (n + pat.bindCount) body = true := by
  intro brs
  induction brs with
  | nil => intro _ pat body hmem; exact absurd hmem (List.not_mem_nil)
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    intro h pat body hmem
    simp only [BranchListClosed.varsBelow, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ heq
      exact h.1
    · exact ih h.2 pat body hmem'

/-- Each binding of a closed rec-group is closed under the shared bound. -/
theorem RecGroupClosed.varsBelow_of_mem {n : Nat} :
    ∀ {bs : List Expr}, RecGroupClosed.varsBelow n bs = true →
      ∀ e ∈ bs, Expr.varsBelow n e = true := by
  intro bs
  induction bs with
  | nil => intro _ e hmem; exact absurd hmem (List.not_mem_nil)
  | cons hd tl ih =>
    intro h e hmem
    simp only [RecGroupClosed.varsBelow, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · exact h.1
    · exact ih h.2 e hmem'

/-- One `Expr.shiftFrom` step over a `match_` branch list, exposed through
    projections (Core's `BranchList.shiftFrom` reduces to exactly this). -/
private theorem Expr.shiftFrom_match_cons (scrut : Expr) (pat : MatchPattern)
    (body : Expr) (rest : List (MatchPattern × Expr)) (t n : Nat) :
    ((Expr.match_ scrut ((pat, body) :: rest)).shiftFrom t n).matchBranchesOf
      = (pat, body.shiftFrom (t + pat.bindCount) n)
        :: ((Expr.match_ scrut rest).shiftFrom t n).matchBranchesOf := rfl

/-- The shifted branch list of a `match_` equals the pointwise shift of the
    branches (the public face of Core's private `BranchList.shiftFrom`). -/
private theorem Expr.shiftFrom_matchBranches (n : Nat) (scrut : Expr) :
    ∀ (brs : List (MatchPattern × Expr)) (t : Nat),
      ((Expr.match_ scrut brs).shiftFrom t n).matchBranchesOf
        = brs.map (fun pb => (pb.1, pb.2.shiftFrom (t + pb.1.bindCount) n)) := by
  intro brs
  induction brs with
  | nil => intro t; rfl
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    intro t
    rw [Expr.shiftFrom_match_cons, ih t]
    simp only [List.map_cons]

/-- One `Expr.shiftFrom` step over a `letRec` binding list, head split off with
    the tail kept at the *same* threshold. -/
private theorem Expr.shiftFrom_letRec_headtail (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (t n : Nat) :
    ((Expr.letRec anns (e :: rest) body).shiftFrom t n).letRecBindingsOf
      = e.shiftFrom (t + (e :: rest).length) n
        :: ((Expr.letRec anns (e :: rest) body).shiftFrom t n).letRecBindingsOf.tail := rfl

/-- Peeling the head binding shifts the recursion base by one; the tail of the
    shifted `(e :: rest)` binding list is the shifted `rest` list (at the base
    incremented past `e`'s binder). -/
private theorem Expr.shiftFrom_letRec_bridge (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (base n : Nat) :
    ((Expr.letRec anns (e :: rest) body).shiftFrom base n).letRecBindingsOf.tail
      = ((Expr.letRec anns rest body).shiftFrom (base + 1) n).letRecBindingsOf := by
  simp only [Expr.shiftFrom, Expr.letRecBindingsOf, List.length_cons]
  rw [show base + (rest.length + 1) = base + 1 + rest.length from by omega]
  rfl

/-- The shifted binding list of a `letRec` equals the pointwise shift of the
    bindings (the public face of Core's private `RecGroup.shiftFrom`). -/
private theorem Expr.shiftFrom_letRecBindings (n : Nat) :
    ∀ (bs : List Expr) (base : Nat) (anns : List (Option PolyTy)) (body : Expr),
      ((Expr.letRec anns bs body).shiftFrom base n).letRecBindingsOf
        = bs.map (·.shiftFrom (base + bs.length) n) := by
  intro bs
  induction bs with
  | nil => intro base anns body; rfl
  | cons e rest ih =>
    intro base anns body
    rw [Expr.shiftFrom_letRec_headtail, Expr.shiftFrom_letRec_bridge, ih (base + 1) anns body]
    simp only [List.map_cons, List.length_cons]
    congr 1
    apply List.map_congr_left
    intro x _
    congr 1
    omega

/-- Definitional unfolding of `Expr.shiftFrom` on a `match_`, with the branch list
    named through `matchBranchesOf`. -/
private theorem Expr.shiftFrom_match_eq (scrut : Expr) (brs : List (MatchPattern × Expr))
    (t n : Nat) :
    (Expr.match_ scrut brs).shiftFrom t n
      = Expr.match_ (scrut.shiftFrom t n) ((Expr.match_ scrut brs).shiftFrom t n).matchBranchesOf :=
  rfl

/-- Definitional unfolding of `Expr.shiftFrom` on a `letRec`, with the binding list
    named through `letRecBindingsOf`. -/
private theorem Expr.shiftFrom_letRec_eq (anns : List (Option PolyTy)) (bs : List Expr)
    (body : Expr) (t n : Nat) :
    (Expr.letRec anns bs body).shiftFrom t n
      = Expr.letRec anns ((Expr.letRec anns bs body).shiftFrom t n).letRecBindingsOf
          (body.shiftFrom (t + bs.length) n) :=
  rfl

/-- `shiftFrom` is the identity on an expression all of whose free term-vars are
    below the shift threshold `t`. -/
theorem Expr.shiftFrom_of_varsBelow (n : Nat) :
    ∀ (e : Expr) (t : Nat), Expr.varsBelow t e = true → e.shiftFrom t n = e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro t _; rfl
  | primBinOp op => intro t _; rfl
  | ctor nm => intro t _; rfl
  | var i => 
    intro t h
    simp only [Expr.varsBelow, decide_eq_true_eq] at h
    simp only [Expr.shiftFrom, if_pos h]
  | lambda ann body ih =>
    intro t h
    simp only [Expr.varsBelow] at h
    simp only [Expr.shiftFrom, ih (t + 1) h]
  | app f arg ihf iharg =>
    intro t h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    simp only [Expr.shiftFrom, ihf t h.1, iharg t h.2]
  | letIn ann rhs body ihrhs ihbody =>
    intro t h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    simp only [Expr.shiftFrom, ihrhs t h.1, ihbody (t + 1) h.2]
  | match_ scrut branches ihscrut ihbrs =>
    intro t h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    obtain ⟨hs, hbrs⟩ := h
    rw [Expr.shiftFrom_match_eq, Expr.shiftFrom_matchBranches, ihscrut t hs]
    congr 1
    apply List.map_self_of_mem
    intro pb hmem
    obtain ⟨pat, body⟩ := pb
    have := ihbrs pat body hmem (t + pat.bindCount)
      (BranchListClosed.varsBelow_of_mem hbrs pat body hmem)
    simp only [this]
  | letRec anns bindings body ihbindings ihbody =>
    intro t h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    obtain ⟨hbd, hbody⟩ := h
    rw [Expr.shiftFrom_letRec_eq, Expr.shiftFrom_letRecBindings,
      ihbody (t + bindings.length) hbody]
    congr 1
    apply List.map_self_of_mem
    intro e hmem
    exact ihbindings e hmem (t + bindings.length)
      (RecGroupClosed.varsBelow_of_mem hbd e hmem)

/-- `shiftFrom` is the identity on closed terms, at any threshold. -/
theorem Expr.shiftFrom_of_closed {e : Expr} (h : Expr.varsBelow 0 e = true) (t n : Nat) :
    e.shiftFrom t n = e :=
  Expr.shiftFrom_of_varsBelow n e t (Expr.varsBelow_mono e (Nat.zero_le t) h)

/-! ## `substN` is the identity on terms with all vars below the substitution depth

Same structure as the `shiftFrom` layer: Core's `BranchList.substN`/`RecGroup.substN`
are `private`, so we route through the `match_`/`letRec` node projections. -/

/-- One `Expr.substN` step over a `match_` branch list, exposed through projections. -/
private theorem Expr.substN_match_cons (scrut : Expr) (pat : MatchPattern)
    (body : Expr) (rest : List (MatchPattern × Expr)) (k : Nat) (vs : List Expr) :
    ((Expr.match_ scrut ((pat, body) :: rest)).substN k vs).matchBranchesOf
      = (pat, body.substN (k + pat.bindCount) vs)
        :: ((Expr.match_ scrut rest).substN k vs).matchBranchesOf := rfl

/-- The substituted branch list of a `match_` equals the pointwise substitution of
    the branches (the public face of Core's private `BranchList.substN`). -/
private theorem Expr.substN_matchBranches (vs : List Expr) (scrut : Expr) :
    ∀ (brs : List (MatchPattern × Expr)) (k : Nat),
      ((Expr.match_ scrut brs).substN k vs).matchBranchesOf
        = brs.map (fun pb => (pb.1, pb.2.substN (k + pb.1.bindCount) vs)) := by
  intro brs
  induction brs with
  | nil => intro k; rfl
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    intro k
    rw [Expr.substN_match_cons, ih k]
    simp only [List.map_cons]

/-- One `Expr.substN` step over a `letRec` binding list, head split off with the
    tail kept at the same depth. -/
private theorem Expr.substN_letRec_headtail (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (k : Nat) (vs : List Expr) :
    ((Expr.letRec anns (e :: rest) body).substN k vs).letRecBindingsOf
      = e.substN (k + (e :: rest).length) vs
        :: ((Expr.letRec anns (e :: rest) body).substN k vs).letRecBindingsOf.tail := rfl

/-- Peeling the head binding bumps the recursion base by one. -/
private theorem Expr.substN_letRec_bridge (anns : List (Option PolyTy)) (e : Expr)
    (rest : List Expr) (body : Expr) (base : Nat) (vs : List Expr) :
    ((Expr.letRec anns (e :: rest) body).substN base vs).letRecBindingsOf.tail
      = ((Expr.letRec anns rest body).substN (base + 1) vs).letRecBindingsOf := by
  simp only [Expr.substN, Expr.letRecBindingsOf, List.length_cons]
  rw [show base + (rest.length + 1) = base + 1 + rest.length from by omega]
  rfl

/-- The substituted binding list of a `letRec` equals the pointwise substitution of
    the bindings (the public face of Core's private `RecGroup.substN`). -/
private theorem Expr.substN_letRecBindings (vs : List Expr) :
    ∀ (bs : List Expr) (base : Nat) (anns : List (Option PolyTy)) (body : Expr),
      ((Expr.letRec anns bs body).substN base vs).letRecBindingsOf
        = bs.map (·.substN (base + bs.length) vs) := by
  intro bs
  induction bs with
  | nil => intro base anns body; rfl
  | cons e rest ih =>
    intro base anns body
    rw [Expr.substN_letRec_headtail, Expr.substN_letRec_bridge, ih (base + 1) anns body]
    simp only [List.map_cons, List.length_cons]
    congr 1
    apply List.map_congr_left
    intro x _
    congr 1
    omega

/-- Definitional unfolding of `Expr.substN` on a `match_`. -/
private theorem Expr.substN_match_eq (scrut : Expr) (brs : List (MatchPattern × Expr))
    (k : Nat) (vs : List Expr) :
    (Expr.match_ scrut brs).substN k vs
      = Expr.match_ (scrut.substN k vs) ((Expr.match_ scrut brs).substN k vs).matchBranchesOf :=
  rfl

/-- Definitional unfolding of `Expr.substN` on a `letRec`. -/
private theorem Expr.substN_letRec_eq (anns : List (Option PolyTy)) (bs : List Expr)
    (body : Expr) (k : Nat) (vs : List Expr) :
    (Expr.letRec anns bs body).substN k vs
      = Expr.letRec anns ((Expr.letRec anns bs body).substN k vs).letRecBindingsOf
          (body.substN (k + bs.length) vs) :=
  rfl

/-- `substN` is the identity on an expression all of whose free term-vars are below
    the substitution depth `k`: there is nothing in range to replace. -/
theorem Expr.substN_of_varsBelow (vs : List Expr) :
    ∀ (e : Expr) (k : Nat), Expr.varsBelow k e = true → e.substN k vs = e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro k _; rfl
  | primBinOp op => intro k _; rfl
  | ctor nm => intro k _; rfl
  | var i => 
    intro k h
    simp only [Expr.varsBelow, decide_eq_true_eq] at h
    simp only [Expr.substN, if_pos h]
  | lambda ann body ih =>
    intro k h
    simp only [Expr.varsBelow] at h
    simp only [Expr.substN, ih (k + 1) h]
  | app f arg ihf iharg =>
    intro k h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    simp only [Expr.substN, ihf k h.1, iharg k h.2]
  | letIn ann rhs body ihrhs ihbody =>
    intro k h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    simp only [Expr.substN, ihrhs k h.1, ihbody (k + 1) h.2]
  | match_ scrut branches ihscrut ihbrs =>
    intro k h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    obtain ⟨hs, hbrs⟩ := h
    rw [Expr.substN_match_eq, Expr.substN_matchBranches, ihscrut k hs]
    congr 1
    apply List.map_self_of_mem
    intro pb hmem
    obtain ⟨pat, body⟩ := pb
    have := ihbrs pat body hmem (k + pat.bindCount)
      (BranchListClosed.varsBelow_of_mem hbrs pat body hmem)
    simp only [this]
  | letRec anns bindings body ihbindings ihbody =>
    intro k h
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    obtain ⟨hbd, hbody⟩ := h
    rw [Expr.substN_letRec_eq, Expr.substN_letRecBindings,
      ihbody (k + bindings.length) hbody]
    congr 1
    apply List.map_self_of_mem
    intro e hmem
    exact ihbindings e hmem (k + bindings.length)
      (RecGroupClosed.varsBelow_of_mem hbd e hmem)

/-- `substN` is the identity on closed terms, at any depth. -/
theorem Expr.substN_of_closed {e : Expr} (h : Expr.varsBelow 0 e = true) (k : Nat)
    (vs : List Expr) : e.substN k vs = e :=
  Expr.substN_of_varsBelow vs e k (Expr.varsBelow_mono e (Nat.zero_le k) h)

/-! ## `varsBelow` ignores type-variable opening

`Expr.openTyVarsAux` (hence `openTyVars`/`openBoundTyVars`) only rewrites type
annotations and `var` `tyArgs`; it never touches a term-var's de Bruijn index or
the binder skeleton, so it leaves `varsBelow` unchanged. This is what lets the
typing lemma reflect the cofinite premises (which type the *opened* bound
expressions) back to the stored terms. -/

/-- `openTyVarsAux` preserves `varsBelow` at every term-bound `n` and type-depth `d`. -/
theorem Expr.varsBelow_openTyVarsAux (Xs : List Nat) :
    ∀ (e : Expr) (n d : Nat),
      Expr.varsBelow n (e.openTyVarsAux d Xs) = Expr.varsBelow n e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro n d; rfl
  | primBinOp op => intro n d; rfl
  | ctor nm => intro n d; rfl
  | var i =>  intro n d; rfl
  | lambda ann body ih =>
    intro n d
    simp only [Expr.openTyVarsAux, Expr.varsBelow, ih]
  | app f arg ihf iharg =>
    intro n d
    simp only [Expr.openTyVarsAux, Expr.varsBelow, ihf, iharg]
  | letIn ann rhs body ihrhs ihbody =>
    intro n d
    cases ann with
    | none => simp only [Expr.openTyVarsAux, Expr.varsBelow, ihrhs, ihbody]
    | some σ => simp only [Expr.openTyVarsAux, Expr.varsBelow, ihrhs, ihbody]
  | match_ scrut branches ihscrut ihbrs =>
    intro n d
    simp only [Expr.openTyVarsAux, Expr.varsBelow, ihscrut]
    congr 1
    have key : ∀ (brs : List (MatchPattern × Expr)),
        (∀ pat body, (pat, body) ∈ brs →
          ∀ n' d', Expr.varsBelow n' (body.openTyVarsAux d' Xs) = Expr.varsBelow n' body) →
        BranchListClosed.varsBelow n (BranchList.openTyVarsAux d Xs brs)
          = BranchListClosed.varsBelow n brs := by
      intro brs
      induction brs with
      | nil => intro _; rfl
      | cons hd tl ih =>
        obtain ⟨pat, body⟩ := hd
        intro hb
        simp only [BranchList.openTyVarsAux, BranchListClosed.varsBelow,
          hb pat body List.mem_cons_self (n + pat.bindCount) d]
        rw [ih (fun p b hm => hb p b (List.mem_cons_of_mem _ hm))]
    exact key branches ihbrs
  | letRec anns bindings body ihbindings ihbody =>
    intro n d
    simp only [Expr.openTyVarsAux, Expr.varsBelow, ihbody]
    have hlen : (RecGroup.openTyVarsAux d Xs anns bindings).length = bindings.length := by
      clear ihbindings ihbody
      induction bindings generalizing anns with
      | nil => rfl
      | cons e rest ih =>
        cases anns with
        | nil => simp only [RecGroup.openTyVarsAux, List.length_cons, ih]
        | cons a as => simp only [RecGroup.openTyVarsAux, List.length_cons, ih]
    rw [hlen]
    congr 1
    have key : ∀ (bs : List Expr) (as : List (Option PolyTy)),
        (∀ e ∈ bs, ∀ n' d', Expr.varsBelow n' (e.openTyVarsAux d' Xs) = Expr.varsBelow n' e) →
        RecGroupClosed.varsBelow (n + bindings.length) (RecGroup.openTyVarsAux d Xs as bs)
          = RecGroupClosed.varsBelow (n + bindings.length) bs := by
      intro bs
      induction bs with
      | nil => intro as _; rfl
      | cons e rest ih =>
        intro as hb
        cases as with
        | nil =>
          simp only [RecGroup.openTyVarsAux, RecGroupClosed.varsBelow,
            hb e List.mem_cons_self (n + bindings.length) d]
          rw [ih [] (fun x hx => hb x (List.mem_cons_of_mem _ hx))]
        | cons a as' =>
          simp only [RecGroup.openTyVarsAux, RecGroupClosed.varsBelow,
            hb e List.mem_cons_self (n + bindings.length) (d + RecAnn.params a)]
          rw [ih as' (fun x hx => hb x (List.mem_cons_of_mem _ hx))]
    exact key bindings anns ihbindings

/-- `varsBelow` is invariant under scoped type-variable opening. -/
theorem Expr.varsBelow_openTyVars (Xs : List Nat) (e : Expr) (n : Nat) :
    Expr.varsBelow n (e.openTyVars Xs) = Expr.varsBelow n e :=
  Expr.varsBelow_openTyVarsAux Xs e n 0

/-- `varsBelow` is invariant under `let`-bound type-variable opening. -/
theorem Expr.varsBelow_openBoundTyVars (ann : Option PolyTy) (Xs : List Nat) (e : Expr) (n : Nat) :
    Expr.varsBelow n (Expr.openBoundTyVars ann Xs e) = Expr.varsBelow n e := by
  cases ann with
  | none => rfl
  | some σ => exact Expr.varsBelow_openTyVars Xs e n

/-! ## Well-typed terms have every free var below the context length

The declarative typing relation `TypeOfElabHM` maintains the invariant that a
well-typed expression is `varsBelow ctx.env.length`: the `var` rule forces an
in-range context lookup, and every binder rule extends the env by exactly the
amount `varsBelow`'s bookkeeping expects (`lambda`/`letIn` +1, a match branch by
its `bindCount`, a `letRec` group by its length). Type-level machinery (scheme
instantiation, scoped-var openings in the cofinite premises) is irrelevant — only
the term-var context lookups matter, and the openings are absorbed by
`Expr.varsBelow_openTyVars`. -/

/-- Assemble a closed branch list from per-branch closedness. -/
theorem RecGroupClosed.varsBelow_of_forall {n : Nat} :
    ∀ {bs : List Expr}, (∀ e ∈ bs, Expr.varsBelow n e = true) →
      RecGroupClosed.varsBelow n bs = true := by
  intro bs
  induction bs with
  | nil => intro _; rfl
  | cons e rest ih =>
    intro h
    simp only [RecGroupClosed.varsBelow, Bool.and_eq_true]
    exact ⟨h e List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

