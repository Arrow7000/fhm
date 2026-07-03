import Mathlib


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


inductive Ty
  | prim : PrimTy → Ty
  | arrow : (from_ to_ : Ty) → Ty
  /-- Bound var – only makes sense within the context of a polytype -/
  | bvar : Nat → Ty
  /-- Free var – unbound var. In spec-land this signifies an unconstrained variable. In algorithm-land this is a unification variable. -/
  | fvar : Nat → Ty
  /-- A custom type with its type params -/
  | customTy : TyName → List Ty → Ty
  deriving Repr



structure PolyTy where
  paramCount : Nat
  /-- May reference params by `.bvar`s in range of `paramCount`  -/
  body : Ty

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
    literal operands. Arithmetic ops (`intAdd`/`intSub`) return `int`
    unconditionally; the comparison op `intLt` returns `Bool` and so is only
    well-typed relative to an env providing `Bool` (see `TypeOfElabHM.primBinOpIntLt`). -/
inductive PrimBinOp
  | intAdd
  | intSub
  | intLt
  deriving DecidableEq, Repr



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
  /-- A variable use, carrying the explicit type arguments at which its scheme is
      instantiated (type-passing). `tyArgs = []` for a monomorphic use. These are
      runtime-relevant: they drive type-beta when a polymorphic binding is unfolded.
      We initialise this to `[]`. Only gets replaced with real `tyArgs` during elaboration. -/
  | var (deBruijnIndex : Nat) (tyArgs : List Ty)
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

/-- Closing doesn't add any more bvars than it is expected to -/
theorem Ty.closeOver_preserves_bvars : ContainsBvarsUpTo 0 ty → ContainsBvarsUpTo vars.length (ty.closeOver vars) := by
  intro prem
  induction ty using Ty.closeOver.induct vars (motive_2 := fun tys ↦ (∀ t ∈ tys, ContainsBvarsUpTo 0 t) → ∀ t ∈ tys, ContainsBvarsUpTo vars.length (t.closeOver vars)) with
  | case1 =>
    simp [closeOver]
    constructor
  | case2 a b aih bih =>
    cases prem
    tauto
  | case3 =>
    simp [closeOver]
    constructor
    cases prem
    omega
  | case4 nm tys ih =>
    cases prem
    constructor
    intro ty tyin
    have : ∀ l, TyList.closeOver vars l = l.map (Ty.closeOver vars) := by
      intro l; induction l with
      | nil => simp [TyList.closeOver]
      | cons hd tl ihl => simp [TyList.closeOver, ihl]
    rw [this] at tyin
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp tyin
    exact ih (by assumption) t ht
  | case5 n i hsome =>
    rw [Ty.closeOver.eq_5]
    simp [hsome]
    refine .bvar ?_
    exact List.idxOf?_lt_length hsome
  | case6 n hnone =>
    rw [Ty.closeOver.eq_5]
    simp [hnone]
    exact .fvar
  | case7 =>
    rename_i h
    simp at h
  | case8 arg rest ih_arg ih_rest =>
    rename_i hall t ht
    simp [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ih_arg (hall _ (by simp))
    · exact ih_rest (fun t ht => hall t (List.mem_cons_of_mem _ ht)) t ht


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
    (customTy : ∀ nm tys, (∀ t ∈ tys, motive t) → motive (.customTy nm tys)) :
    (ty : Ty) → motive ty
  | .prim p          => prim p
  | .arrow a b       =>
      arrow a b
        (Ty.rec_strong prim arrow bvar fvar customTy a)
        (Ty.rec_strong prim arrow bvar fvar customTy b)
  | .bvar n          => bvar n
  | .fvar n          => fvar n
  | .customTy nm tys =>
      customTy nm tys
        (fun t _ht => Ty.rec_strong prim arrow bvar fvar customTy t)
termination_by ty => sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem _ht; omega)

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
    (var        : ∀ n tyArgs, motive (.var n tyArgs))
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
  | .var n tyArgs       => var n tyArgs
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
Shift all `.var i` with `i ≥ threshold` up by `n`. Traverses into binders with
`threshold` incremented by the number of new bindings introduced.

Used by `substN`: when a value is inserted at substitution depth `k`, it has
to pass under `k` new binders, which shifts its free vars up by `k`.
-/
def Expr.shiftFrom (threshold : Nat) (n : Nat) : Expr → Expr
  | .var i tyArgs      => if i < threshold then .var i tyArgs else .var (i + n) tyArgs
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
private def RecGroup.shiftFrom (threshold : Nat) (n : Nat) : List Expr → List Expr
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
  | .var i tyArgs       => .var i (tyArgs.map (Ty.openTyFrom d Ts))
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
  | var n tyArgs =>
    intro d; simp only [Expr.instTyAux, Expr.var.injEq, true_and]
    conv_rhs => rw [← List.map_id tyArgs]
    exact List.map_congr_left (fun t _ => Ty.openTyFrom_nil d t)
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

Replaces `.var (k + j)` with `(vs[j]).shiftFrom 0 k` for `j ∈ [0, vs.length)`,
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
  | .var i tyArgs =>
      if i < k then .var i tyArgs
      else if h : i - k < vs.length then ((vs[i - k]).instTy tyArgs).shiftFrom 0 k
      else .var (i - vs.length) tyArgs
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

private def RecGroup.substN (k : Nat) (vs : List Expr) : List Expr → List Expr
  | []        => []
  | e :: rest => e.substN k vs :: RecGroup.substN k vs rest

end

/-- Single-var substitution. Beta-reduces `(λ. body) v` to `body.subst1 0 v`.

In other words, replaces all references to `.var k` with value `v`. This could be either during function application or replacing a let binding with its referent value. It also shifts all `.var`s up or down where appropriate so things stay well-indexed. -/
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
      | var a b => simp [isValue, isCtorChain] at hv
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
  | var _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
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
  | var a b => simp [isCtorChain] at h
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
  | var _ _ => simp [isValue] at hv
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
    | var _ _ => simp [isValue, isCtorChain] at hv
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
      | var _ _ => simp [isCtorChain] at hv'
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
  | primLit _ | primBinOp _ | lambda _ _ _ | ctor _ | var _ _ => simp [step] at h
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

theorem step_deterministic {e e₁ e₂ : Expr}
    (h₁ : Step e e₁) (h₂ : Step e e₂) : e₁ = e₂ := by
  have := step_complete h₁
  have := step_complete h₂
  simp_all




end SmallStep




/-! ## Well-scopedness

`WellScopedUnder n e` means every `.var i` in `e` satisfies `i < n`. Under de
Bruijn indices with the cons-on-binder convention, the typing relation maintains
the invariant that any well-typed expression is well-scoped under
`ctx.env.length`.

Lambda/let/match introduce 1, 1, or `pat.contents` new levels respectively,
raising the scope bound inside their body. -/

mutual

inductive Expr.WellScopedUnder : Nat → Expr → Prop
  | primLit {n p}            : Expr.WellScopedUnder n (.primLit p)
  | ctor    {n c}            : Expr.WellScopedUnder n (.ctor c)
  | var     {n i tyArgs}     : i < n → Expr.WellScopedUnder n (.var i tyArgs)
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
  | var : AllMatchesExhaustive ctors (.var n tyArgs)
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
  | .var i tyArgs       => .var i (tyArgs.map (Ty.substFvar Z U))
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
  | .var i tyArgs       => .var i (tyArgs.map (Ty.openVarsFrom d Xs))
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
private theorem RecGroup.shiftFrom_eq_map (threshold n : Nat) (bs : List Expr) :
    RecGroup.shiftFrom threshold n bs = bs.map (·.shiftFrom threshold n) := by
  induction bs with
  | nil => rfl
  | cons hd tl ih => simp only [RecGroup.shiftFrom, List.map_cons, ih]

private theorem RecGroup.substN_eq_map (k : Nat) (vs : List Expr) (bs : List Expr) :
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
  | var n tyArgs =>
    intro d
    simp only [Expr.instTyAux, Expr.openTyVarsAux, Expr.var.injEq, true_and]
    exact List.map_congr_left (fun t _ => Ty.openTyFrom_fvar_eq_openVarsFrom d Xs t)
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
private theorem List.mem_zip_map_left {α β γ : Type _} {f : α → γ} :
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
    (if any). For `none` this is vacuous — the choice is free (inferred). -/
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


/-! ### The declarative typing relation `TypeOfElabHM`.

Syntax-directed Hindley–Milner typing. All rules are standard except the
let-generalising rule (`letIn`), which uses a **cofinite**
"for-all-fresh" premise to express generalisation (see the module doc above):

```
  PolyTy.WF M →
  (∀ Xs, FreshNames L M.paramCount Xs → TypeOfElabHM ctx boundExpr (M.openVars Xs)) →
  bodyCtx = { ctx with env := M :: ctx.env } →
  TypeOfElabHM bodyCtx body bodyTy →
  TypeOfElabHM ctx (.letIn ann boundExpr body) bodyTy
```

The cofinite premise's IH is *universally quantified in `Xs`*, so when
`subst_lemma`/`weaken_env` descend through a `letIn` and the env grows, they
re-instantiate it at names fresh for the bigger env — no side conditions.

`var`/`ctor`/`match_` instantiate schemes via `InstantiatesBy` (equivalent to
`openWith` on a well-formed scheme). -/

mutual

/-- Cofinite (locally-nameless-style) declarative typing relation. -/
inductive TypeOfElabHM : Ctx → Expr → Ty → Prop
  | primLitUnit :
    TypeOfElabHM ctx (.primLit .unit) (.prim .unit)

  | primLitInt :
    TypeOfElabHM ctx (.primLit (.int n)) (.prim .int)

  | primLitNat :
    TypeOfElabHM ctx (.primLit (.nat n)) (.prim .nat)

  | primLitChar :
    TypeOfElabHM ctx (.primLit (.char c)) (.prim .char)

  /-- `intAdd : int → int → int`. A fixed, env-independent monotype (no premises)
      — the operational counterpart is the `SmallStep.Step.deltaIntAdd` δ-rule. -/
  | primBinOpIntAdd :
    TypeOfElabHM ctx (.primBinOp .intAdd)
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))

  /-- `intSub : int → int → int`. -/
  | primBinOpIntSub :
    TypeOfElabHM ctx (.primBinOp .intSub)
      (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int)))

  /-- `intLt : int → int → Bool`. Env-dependent: the δ-result is `.ctor "True"`
      or `.ctor "False"`, so this is well-typed only when the ambient env types
      those ctors at `Bool` — carried as the two premises (reusing the `ctor`
      typing judgment). Then preservation types the δ-result directly from a
      premise: typechecks ⟹ Bool present ⟹ result well-typed. -/
  | primBinOpIntLt :
    TypeOfElabHM ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfElabHM ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) →
    TypeOfElabHM ctx (.primBinOp .intLt)
      (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))

  | lambda :
    -- `paramTy` is locally closed (no dangling type `bvar`s). When the lambda
    -- sits inside a `let`-bound expression, its annotation may mention the
    -- enclosing scheme's type variables; those are `bvar`s in the stored term but
    -- get replaced by fresh `fvar`s (via `Expr.openTyVars`) before this rule
    -- fires, so `paramTy` is `bvar`-free here while still possibly carrying free
    -- type variables — the scoped ones (need NOT be closed; consistency under
    -- type substitution is kept by `typ_subst_preservation` pushing `[Z↦U]`
    -- through the term's annotations).
    paramTy.IsLC →
    ann.Pins paramTy →
    bodyCtx = { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } →
    TypeOfElabHM bodyCtx body bodyTy →
    TypeOfElabHM ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
    TypeOfElabHM ctx f (.arrow argTy retTy) →
    TypeOfElabHM ctx input argTy →
    TypeOfElabHM ctx (.app f input) retTy

  /-- Cofinite let-generalisation. See module doc above and `GeneralisesTo`.
      `M` is the generalised scheme; when an annotation is present it pins `M`
      (`Option.Pins`), and the cofinite premise then enforces "the annotation is
      not more general than `boundExpr` actually is" for free.

      NOTE: no value restriction — our language is pure (no effects/refs), so
      generalising an arbitrary let-bound expression is sound (plain
      Damas–Milner). Chargueraud needs `value boundExpr` only because mini-ML
      has mutable refs. -/
  | letIn {M : PolyTy} {L : List Nat} :
    PolyTy.WF M →
    ann.Pins M →
    GeneralisesTo TypeOfElabHM ctx ann boundExpr M L →
    bodyCtx = { ctx with env := M :: ctx.env } →
    TypeOfElabHM bodyCtx body bodyTy →
    TypeOfElabHM ctx (.letIn ann boundExpr body) bodyTy

  /-- Type-passing variable use: the STORED `tyArgs` instantiate the scheme, and
      must supply exactly one locally-closed type argument per scheme parameter
      (`Ty.AreLC`). The arity pin is what makes LITERAL subject reduction hold:
      when a polymorphic binding is unfolded, the value's annotations are
      type-beta'd with `tyArgs` (`instTy`), and only a full instantiation
      guarantees no scheme `bvar` is left dangling. -/
  | var :
    ctx.env[dbl]? = some polyTy →
    Ty.AreLC polyTy.paramCount tyArgs →
    polyTy.InstantiatesTo tyArgs ty →
    TypeOfElabHM ctx (.var dbl tyArgs) ty

  | ctor :
    LookupList.get? ctx.ctors name = some ctor →
    (∀ tyArg ∈ tyArgs, tyArg.IsLC) →
    ctor.toTy.InstantiatesTo tyArgs ty →
    TypeOfElabHM ctx (.ctor name) ty

  | match_ :
    TypeOfElabHM ctx scrutinee scrutTy →
    branches ≠ [] →
    (∀ branch ∈ branches, TypeOfElabMatchBranch ctx branch scrutTy resultTy) →
    TypeOfElabHM ctx (.match_ scrutinee branches) resultTy

  /-- (Mutually) recursive binding group with per-binding optional annotations —
      the FUSION of Damas–Milner monomorphic recursion (Pottier's `LetRec`; see
      `letrec-design.md`) for the unannotated members and annotated *polymorphic*
      recursion (Pottier's `LetRecPoly`) for the annotated ones. Spiked standalone
      as `SpikeLetRecMixed.MixedRule` (2026-07-02); the all-`none` / all-`some`
      degenerate rules are the historical `letRec` / `letRecAnn`.

      The rule invents per-member derivation data `specs` (shared monotypes for
      unannotated members, the pinned schemes for annotated ones) over a gen-var
      pool `G`, tied to the stored `anns` by `RecSpecs.WF`. Every RHS is checked
      in the group context `RecSpecs.rhsCtx` (see `RecSpecs.MonoTyped` /
      `RecSpecs.PolyTyped` for the two cofinite regimes and why their quantifier
      nesting is load-bearing); the body sees `RecSpecs.bodyCtx` (unannotated
      members generalised over the pool). Together with the per-binding
      depth-shielding in `instTyAux`/`openTyVarsAux`, annotated members'
      own-variable polymorphic recursion satisfies subject reduction. -/
  | letRec {specs : List RecSpec} {G L : List Nat} :
    RecSpecs.WF anns bindings specs G →
    RecSpecs.MonoTyped TypeOfElabHM ctx bindings specs G L →
    RecSpecs.PolyTyped TypeOfElabHM ctx bindings specs G L →
    bodyCtx = RecSpecs.bodyCtx ctx specs G →
    TypeOfElabHM bodyCtx body ρ →
    TypeOfElabHM ctx (.letRec anns bindings body) ρ


/-- Match-branch typing for `TypeOfElabHM`. A named branch's constructor-pattern
    side conditions are bundled in `BranchCtorSpec`; the body types with the
    instantiated field types bound MONOMORPHICALLY (`mkTrivial` — so no cofinite
    type-var quantifier is needed, and the term-var quantifier vanishes under de
    Bruijn levels). -/
inductive TypeOfElabMatchBranch :
  (ctx : Ctx) → (MatchPattern × Expr) → (scrutTy : Ty) → (resultTy : Ty) → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {c : CtorName} {n : Nat} {tyArgs instContents : List Ty} :
    BranchCtorSpec ctx.ctors c n scrutTy ctor tyArgs instContents →
    bodyCtx = { ctx with env := instContents.map PolyTy.mkTrivial ++ ctx.env } →
    TypeOfElabHM bodyCtx bodyExpr resultTy →
    TypeOfElabMatchBranch ctx (.named c n, bodyExpr) scrutTy resultTy
  /-- A wildcard branch binds nothing and types its body in the unextended
      context; it imposes no constraint on the scrutinee's type (in particular
      the scrutinee need not be a `customTy`). -/
  | wildcard {ctx : Ctx} :
    TypeOfElabHM ctx bodyExpr resultTy →
    TypeOfElabMatchBranch ctx (.wildcard, bodyExpr) scrutTy resultTy

end


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
    TypeOfHM ctx (.var dbl tyArgs) ty

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


/-! ### Cofinite typing-at-scheme predicates. -/

/-- `t` types at *every* opening of `M` by sufficiently-fresh names. The `L`
    is the cofinite exclusion set; existentially quantified at the use site.
    This is exactly the cofinite premise of `TypeOfElabHM.letIn`, packaged. -/
def HasSchemeVars (L : List Nat) (ctx : Ctx) (e : Expr) (M : PolyTy) : Prop :=
  ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
    TypeOfElabHM ctx (e.instTy (Xs.map Ty.fvar)) (M.openVars Xs)

/-- `t.instTy Vs` types at *every* type-level instance of `M` (by LC types of the
    right arity). This is the **type-passing** `HasScheme`: opening the scheme's
    variables means substituting them through `t`'s own annotations (type-beta,
    `instTy`), not dropping them. This is what `subst_lemma`'s substituted-`var`
    case demands — `substN` produces `(v.instTy tyArgs).shiftFrom 0 k`. -/
def HasScheme (ctx : Ctx) (e : Expr) (M : PolyTy) : Prop :=
  ∀ Vs : List Ty, Ty.AreLC M.paramCount Vs →
    TypeOfElabHM ctx (e.instTy Vs) (M.openWith Vs)


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
  | var n tyArgs =>
    intro d
    simp only [Expr.openTyVarsAux, Expr.substTyFvar]
    refine congrArg (Expr.var n) ?_
    induction tyArgs with
    | nil => rfl
    | cons t ts ih => simp only [List.map_cons, Ty.substFvar_openVarsFrom h_lc h_Z, ih]
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
  | var m _ => intro d k; simp only [Expr.openTyVarsAux, Expr.shiftFrom]; split <;> rfl
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
    rw [Ty.closeOver.eq_5]
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
    rw [Ty.closeOver.eq_5]
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
      rw [Ty.closeOver.eq_5, List.idxOf?_getElem_self hnodup hlt]
  | fvar n =>
    have hn : n ∉ Xs := fun h => hfresh n h (by simp [Ty.freeVars])
    simp only [Ty.openVars, Ty.instantiate]
    rw [Ty.closeOver.eq_5, List.idxOf?_eq_none_iff.mpr hn]
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
    rw [Ty.closeOver.eq_5]
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
    rw [Ty.closeOver.eq_5, List.idxOf?_eq_none_iff.mpr hn]
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

/-- `substFvar` commutes with `closeOver` when the substituted variable `Z` and
    all free vars of the replacement `U` avoid the closed-over pool `gs`. -/
theorem Ty.substFvar_closeOver_comm {Z : Nat} {U : Ty} {gs : List Nat} {τ : Ty}
    (hZ : Z ∉ gs) (hU : ∀ g ∈ gs, g ∉ U.freeVars) :
    Ty.substFvar Z U (Ty.closeOver gs τ) = Ty.closeOver gs (Ty.substFvar Z U τ) := by
  induction τ using Ty.rec_strong with
  | prim p => simp [Ty.closeOver, Ty.substFvar]
  | bvar i => simp [Ty.closeOver, Ty.substFvar]
  | fvar n =>
    rw [Ty.closeOver.eq_5]
    cases h_idx : gs.idxOf? n with
    | some i =>
      have hn : n ∈ gs := List.mem_of_getElem? (List.getElem?_of_idxOf? h_idx)
      have hnz : ¬ n = Z := fun h => hZ (h ▸ hn)
      simp only [Ty.substFvar, if_neg hnz, Ty.closeOver.eq_5, h_idx]
    | none =>
      have hn : n ∉ gs := List.idxOf?_eq_none_iff.mp h_idx
      by_cases hnz : n = Z
      · simp only [Ty.substFvar, if_pos hnz]
        exact (Ty.closeOver_eq_self_of_fresh hU).symm
      · simp only [Ty.substFvar, if_neg hnz, Ty.closeOver.eq_5, List.idxOf?_eq_none_iff.mpr hn]
  | arrow a b iha ihb =>
    simp only [Ty.closeOver, Ty.substFvar, iha, ihb]
  | customTy nm tys ih =>
    simp only [Ty.closeOver, Ty.substFvar, TyList.closeOver_eq_map, TyList.substFvar_eq_map,
               List.map_map]
    apply congrArg (Ty.customTy nm)
    apply List.map_congr_left
    intro t ht
    simpa using ih t ht

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


/-! ### `substFvar` interaction with the typing-side predicates.

Helpers needed by `typ_subst_preservation`. -/

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


/-! ### Metatheory infrastructure. -/

/-- The per-branch motive used internally by `TypeOfElabHM.rec_strong`. For a branch
    `(pat, body)` it bundles the inverted `TypeOfElabMatchBranch` structure (the
    constructor lookup, type-name/arity agreements, the field instantiations)
    together with an induction hypothesis on the branch *body* derivation.

    Phrased existentially so the `mk` minor premise of the auto-generated mutual
    recursor `TypeOfElabHM.rec` can produce it from the body IH, and the `match_`
    case of a `rec_strong` proof can destructure it to rebuild each branch. -/
abbrev TypeOfElabHM.BranchMotive
    (motive : (ctx : Ctx) → (e : Expr) → (τ : Ty) → TypeOfElabHM ctx e τ → Prop)
    (ctx : Ctx) (branch : MatchPattern × Expr) (scrutTy : Ty)
    (resultTy : Ty) : Prop :=
  (∃ (ctor : Ctor) (c : CtorName) (n : Nat) (tyArgs : List Ty) (instContents : List Ty),
    branch.1 = .named c n ∧
    BranchCtorSpec ctx.ctors c n scrutTy ctor tyArgs instContents ∧
    ∃ hbody : TypeOfElabHM ⟨instContents.map PolyTy.mkTrivial ++ ctx.env, ctx.ctors⟩ branch.2 resultTy,
      motive ⟨instContents.map PolyTy.mkTrivial ++ ctx.env, ctx.ctors⟩ branch.2 resultTy hbody)
  ∨
  (branch.1 = .wildcard ∧
    ∃ hbody : TypeOfElabHM ctx branch.2 resultTy,
      motive ctx branch.2 resultTy hbody)

/--
Strong induction principle for the mutual `TypeOfElabHM`/`TypeOfElabMatchBranch`
relation, packaged with a *single* motive on `TypeOfElabHM` derivations so the
metatheory can do `induction h using TypeOfElabHM.rec_strong` and never touch the
mutual recursor / `motive_2` directly.

Each constructor's minor premise carries induction hypotheses for its recursive
sub-derivations. The crucial cases:

* `letIn`: the cofinite premise `hcofin` (which types the *opened* bound
  expression `Expr.openBoundTyVars ann Xs boundExpr` — a transform of
  `boundExpr`, not a structural subterm) comes with an IH
  `∀ Xs hf, motive … (hcofin Xs hf)`, plus the body IH. This is what the
  structural `Expr.rec_strong` cannot provide.
* `match_`: each branch carries (via `BranchMotive`) the inverted branch
  structure together with an IH on that branch's body derivation.

Built on the auto-generated `TypeOfElabHM.rec` with an internal
`motive_2 := BranchMotive`. -/
@[elab_as_elim]
theorem TypeOfElabHM.rec_strong
    {motive : (ctx : Ctx) → (e : Expr) → (τ : Ty) → TypeOfElabHM ctx e τ → Prop}
    (primLitUnit : ∀ {ctx : Ctx}, motive ctx (.primLit .unit) (.prim .unit) .primLitUnit)
    (primLitInt : ∀ {ctx : Ctx} {n : ℤ}, motive ctx (.primLit (.int n)) (.prim .int) .primLitInt)
    (primLitNat : ∀ {ctx : Ctx} {n : ℕ}, motive ctx (.primLit (.nat n)) (.prim .nat) .primLitNat)
    (primLitChar : ∀ {ctx : Ctx} {c : Char}, motive ctx (.primLit (.char c)) (.prim .char) .primLitChar)
    (primBinOpIntAdd : ∀ {ctx : Ctx},
      motive ctx (.primBinOp .intAdd)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))) .primBinOpIntAdd)
    (primBinOpIntSub : ∀ {ctx : Ctx},
      motive ctx (.primBinOp .intSub)
        (.arrow (.prim .int) (.arrow (.prim .int) (.prim .int))) .primBinOpIntSub)
    (primBinOpIntLt : ∀ {ctx : Ctx}
      (htrue : TypeOfElabHM ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []))
      (hfalse : TypeOfElabHM ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ [])),
      motive ctx (.ctor ⟨"True"⟩) (.customTy ⟨"Bool"⟩ []) htrue →
      motive ctx (.ctor ⟨"False"⟩) (.customTy ⟨"Bool"⟩ []) hfalse →
      motive ctx (.primBinOp .intLt)
        (.arrow (.prim .int) (.arrow (.prim .int) (.customTy ⟨"Bool"⟩ [])))
        (.primBinOpIntLt htrue hfalse))
    (lambda : ∀ {paramTy : Ty} {ann : Option Ty} {bodyCtx ctx : Ctx} {body : Expr} {bodyTy : Ty}
      (hpc : paramTy.IsLC) (hann : ann.Pins paramTy)
      (heq : bodyCtx = { env := PolyTy.mkTrivial paramTy :: ctx.env, ctors := ctx.ctors })
      (hbody : TypeOfElabHM bodyCtx body bodyTy),
      motive bodyCtx body bodyTy hbody →
      motive ctx (.lambda ann body) (.arrow paramTy bodyTy) (.lambda hpc hann heq hbody))
    (app : ∀ {ctx : Ctx} {f : Expr} {argTy retTy : Ty} {input : Expr}
      (hf : TypeOfElabHM ctx f (.arrow argTy retTy)) (hinput : TypeOfElabHM ctx input argTy),
      motive ctx f (.arrow argTy retTy) hf → motive ctx input argTy hinput →
      motive ctx (.app f input) retTy (.app hf hinput))
    (letIn : ∀ {ann : Option PolyTy} {ctx : Ctx} {boundExpr : Expr} {bodyCtx : Ctx} {body : Expr}
      {bodyTy : Ty} {M : PolyTy} {L : List Nat}
      (hwf : M.WF) (hann : ann.Pins M)
      (hcofin : GeneralisesTo TypeOfElabHM ctx ann boundExpr M L)
      (heq : bodyCtx = { env := M :: ctx.env, ctors := ctx.ctors })
      (hbody : TypeOfElabHM bodyCtx body bodyTy),
      (∀ Xs (hf : FreshNames L M.paramCount Xs),
        motive ctx (Expr.openBoundTyVars ann Xs boundExpr) (M.openVars Xs) (hcofin Xs hf)) →
      motive bodyCtx body bodyTy hbody →
      motive ctx (.letIn ann boundExpr body) bodyTy (.letIn hwf hann hcofin heq hbody))
    (var : ∀ {dbl : Nat} {polyTy : PolyTy} {tyArgs : List Ty} {ty : Ty} {ctx : Ctx}
      (hlook : ctx.env[dbl]? = some polyTy)
      (hlc : Ty.AreLC polyTy.paramCount tyArgs)
      (hinst : polyTy.InstantiatesTo tyArgs ty),
      motive ctx (.var dbl tyArgs) ty (.var hlook hlc hinst))
    (ctor : ∀ {name : CtorName} {ctorr : Ctor} {tyArgs : List Ty} {ty : Ty} {ctx : Ctx}
      (hlook : LookupList.get? ctx.ctors name = some ctorr)
      (htyargs : ∀ tyArg ∈ tyArgs, tyArg.IsLC)
      (hinst : ctorr.toTy.InstantiatesTo tyArgs ty),
      motive ctx (.ctor name) ty (.ctor hlook htyargs hinst))
    (match_ : ∀ {ctx : Ctx} {scrutinee : Expr} {scrutTy : Ty}
      {branches : List (MatchPattern × Expr)} {resultTy : Ty}
      (hscrut : TypeOfElabHM ctx scrutinee scrutTy) (hne : branches ≠ [])
      (hbrs : ∀ branch ∈ branches, TypeOfElabMatchBranch ctx branch scrutTy resultTy),
      motive ctx scrutinee scrutTy hscrut →
      (∀ branch ∈ branches, TypeOfElabHM.BranchMotive motive ctx branch scrutTy resultTy) →
      motive ctx (.match_ scrutinee branches) resultTy (.match_ hscrut hne hbrs))
    (letRec : ∀ {ctx bodyCtx : Ctx} {anns : List (Option PolyTy)} {bindings : List Expr}
      {specs : List RecSpec} {G L : List Nat} {body : Expr} {ρ : Ty}
      (hwf : RecSpecs.WF anns bindings specs G)
      (hmono : RecSpecs.MonoTyped TypeOfElabHM ctx bindings specs G L)
      (hpoly : RecSpecs.PolyTyped TypeOfElabHM ctx bindings specs G L)
      (heq : bodyCtx = RecSpecs.bodyCtx ctx specs G)
      (hbody : TypeOfElabHM bodyCtx body ρ),
      (∀ Xs (hf : FreshNames L G.length Xs)
          p (hp : p ∈ bindings.zip specs) τ (hτ : p.2 = .mono τ),
        motive (RecSpecs.rhsCtx ctx specs G Xs)
          p.1 (Ty.renameG G Xs τ) (hmono Xs hf p hp τ hτ)) →
      (∀ Xs (hf : FreshNames L G.length Xs)
          p (hp : p ∈ bindings.zip specs) σ (hσ : p.2 = .poly σ)
          Ys (hfY : FreshNames (L ++ Xs) σ.paramCount Ys),
        motive (RecSpecs.rhsCtx ctx specs G Xs)
          (p.1.openTyVars Ys) (σ.openVars Ys) (hpoly Xs hf p hp σ hσ Ys hfY)) →
      motive bodyCtx body ρ hbody →
      motive ctx (.letRec anns bindings body) ρ
        (.letRec hwf hmono hpoly heq hbody))
    {ctx : Ctx} {e : Expr} {τ : Ty} (h : TypeOfElabHM ctx e τ) : motive ctx e τ h := by
  induction h using TypeOfElabHM.rec
    (motive_2 := fun ctx br scrutTy resultTy _ =>
      TypeOfElabHM.BranchMotive motive ctx br scrutTy resultTy) with
  | primLitUnit => exact primLitUnit
  | primLitInt => exact primLitInt
  | primLitNat => exact primLitNat
  | primLitChar => exact primLitChar
  | primBinOpIntAdd => exact primBinOpIntAdd
  | primBinOpIntSub => exact primBinOpIntSub
  | primBinOpIntLt htrue hfalse ihtrue ihfalse => exact primBinOpIntLt htrue hfalse ihtrue ihfalse
  | lambda hpc hann heq hbody ihbody => exact lambda hpc hann heq hbody ihbody
  | app hf hinput ihf ihinput => exact app hf hinput ihf ihinput
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
      exact letIn hwf hann hcofin heq hbody ihcofin ihbody
  | var hlook hlc hinst => exact var hlook hlc hinst
  | ctor hlook htyargs hinst => exact ctor hlook htyargs hinst
  | match_ hscrut hne hbrs ihscrut ihbrs => exact match_ hscrut hne hbrs ihscrut ihbrs
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
      exact letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody
  | mk hspec heq hbodyT ih =>
      subst heq
      exact Or.inl ⟨_, _, _, _, _, rfl, hspec, hbodyT, ih⟩
  | wildcard hbodyT ih =>
      exact Or.inr ⟨rfl, hbodyT, ih⟩

/-- **Faithfulness** (`TypeOfElabHM ⊆ TypeOfHM`): every elaborated typing erases to a
    declarative HM typing — the type-passing decorations never type a program that
    plain HM would reject. The two relations differ only in `var`, where the stored
    `tyArgs` (and their dropped `length = paramCount` constraint) simply furnish the
    declarative rule's existential instantiation witness. This is the spec-vs-spec
    adequacy edge complementing elaboration soundness / completeness. -/
theorem TypeOfElabHM.faithful {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfElabHM ctx e τ) : TypeOfHM ctx e τ := by
  induction h using TypeOfElabHM.rec_strong with
  | primLitUnit => exact .primLitUnit
  | primLitInt => exact .primLitInt
  | primLitNat => exact .primLitNat
  | primLitChar => exact .primLitChar
  | primBinOpIntAdd => exact .primBinOpIntAdd
  | primBinOpIntSub => exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse => exact .primBinOpIntLt ihtrue ihfalse
  | lambda hpc hann heq _ ihbody => exact .lambda hpc hann heq ihbody
  | app _ _ ihf ihinput => exact .app ihf ihinput
  | letIn hwf hann _ heq _ ihcofin ihbody => exact .letIn hwf hann ihcofin heq ihbody
  | var hlook hlc hinst => exact .var hlook hlc.2 hinst
  | ctor hlook htyargs hinst => exact .ctor hlook htyargs hinst
  | match_ _ hne _ ihscrut ihbrs =>
      refine .match_ ihscrut hne ?_
      rintro ⟨pat, body⟩ hb
      rcases ihbrs (pat, body) hb with
        ⟨ct, c, n, tyArgs, instContents, hpat, hspec, _, hbodyIH⟩ | ⟨hpat, _, hbodyIH⟩
      · subst hpat
        exact .mk hspec rfl hbodyIH
      · subst hpat
        exact .wildcard hbodyIH
  | letRec hwf _ _ heq _ ihmono ihpoly ihbody =>
      exact .letRec hwf ihmono ihpoly heq ihbody

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

/-- Type-substitution preserves typing (uniform form): substituting a single
    type variable `Z ↦ U` (with `U` locally closed) simultaneously through the
    env, the term's annotations (`Expr.substTyFvar`), and the type preserves the
    derivation. Proven by induction on the derivation (`rec_strong`) so the
    `letIn` cofinite case — whose premise types a *transform* of the bound
    expression, not a structural subterm — goes through.

    Chargueraud's `typing_typ_subst`. -/
theorem TypeOfElabHM.typ_subst_preservation_uniform {Z : Nat} {U : Ty} (h_U_lc : U.IsLC)
    {ctx : Ctx} {e : Expr} {τ : Ty} (h : TypeOfElabHM ctx e τ) :
    TypeOfElabHM ⟨ctx.env.substFvar Z U, ctx.ctors⟩ (e.substTyFvar Z U) (Ty.substFvar Z U τ) := by
  induction h using TypeOfElabHM.rec_strong with
  | primLitUnit => exact .primLitUnit
  | primLitInt => exact .primLitInt
  | primLitNat => exact .primLitNat
  | primLitChar => exact .primLitChar
  | primBinOpIntAdd => exact .primBinOpIntAdd
  | primBinOpIntSub => exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse => exact .primBinOpIntLt ihtrue ihfalse
  | app _ _ ihf ihinput =>
    simp only [Expr.substTyFvar]
    simp only [Ty.substFvar] at ihf
    exact .app ihf ihinput
  | lambda hpc hann heq hbody ihbody =>
    subst heq
    expose_names
    simp only [Ty.substFvar, Expr.substTyFvar]
    refine TypeOfElabHM.lambda (Ty.IsLC.substFvar h_U_lc hpc) ?_ rfl ?_
    · intro T hT
      rcases ann with _ | T₀
      · simp at hT
      · simp only [Option.map_some, Option.some.injEq] at hT
        subst hT
        rw [hann T₀ rfl]
    · simpa only [Env.substFvar, List.map_cons, PolyTy.substFvar, PolyTy.mkTrivial] using ihbody
  | var hlook hlc hinst =>
    simp only [Expr.substTyFvar]
    have hlook' := congrArg (Option.map (PolyTy.substFvar Z U)) hlook
    simp only [Option.map_some] at hlook'
    rw [← List.getElem?_map] at hlook'
    refine TypeOfElabHM.var hlook'
      ⟨by simpa only [List.length_map, PolyTy.substFvar] using hlc.1, ?_⟩
      (InstantiatesBy.substFvar h_U_lc hinst)
    intro tyArg hmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    exact Ty.IsLC.substFvar h_U_lc (hlc.2 t ht)
  | ctor hlook htyargs hinst =>
    simp only [Expr.substTyFvar]
    have hbody := InstantiatesBy.substFvar (Z := Z) (U := U) h_U_lc hinst
    rw [Ty.substFvar_fresh (NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars _) Z)] at hbody
    refine TypeOfElabHM.ctor hlook ?_ hbody
    intro tyArg hmem
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
    exact Ty.IsLC.substFvar h_U_lc (htyargs t ht)
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    subst heq
    expose_names
    simp only [Expr.substTyFvar]
    refine TypeOfElabHM.letIn (M := PolyTy.substFvar Z U M) (L := Z :: L)
      (PolyTy.WF.substFvar h_U_lc hwf) ?_ ?_ rfl ?_
    · intro σ hσ
      rcases ann with _ | σ₀
      · simp at hσ
      · simp only [Option.map_some, Option.some.injEq] at hσ
        subst hσ
        rw [hann σ₀ rfl]
    · intro Xs hfresh
      have hZ_notin : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
      have hXs_freshL : FreshNames L M.paramCount Xs :=
        ⟨by simpa using hfresh.length, hfresh.nodup,
         fun x hx hc => hfresh.avoid x hx (List.mem_cons_of_mem _ hc)⟩
      have hbe := ihcofin Xs hXs_freshL
      rw [Expr.substTyFvar_openBoundTyVars h_U_lc hZ_notin] at hbe
      have hopen : (M.substFvar Z U).openVars Xs = Ty.substFvar Z U (M.openVars Xs) := by
        unfold PolyTy.openVars PolyTy.substFvar
        exact (Ty.substFvar_openVars h_U_lc hZ_notin).symm
      rw [hopen]
      exact hbe
    · simpa only [Env.substFvar, List.map_cons] using ihbody
  | match_ hscrut hne hbrs ihscrut ihbrs =>
    simp only [Expr.substTyFvar]
    refine TypeOfElabHM.match_ ihscrut ?_ ?_
    · intro hcontra
      obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
      rw [hb] at hcontra
      simp [BranchList.substTyFvar] at hcontra
    · intro branch' hmem'
      obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_substTyFvar hmem'
      rcases ihbrs (pat, body) hmem with
        ⟨ct, c, n, tyArgs, instContents, hpat, hspec, _, hbodyIH⟩ |
        ⟨hpat, _, hbodyIH⟩
      · subst hpat
        have hcc : ct.contents.map (Ty.substFvar Z U) = ct.contents := by
          have hpt : ∀ c ∈ ct.contents, Ty.substFvar Z U c = id c := fun c hc =>
            Ty.substFvar_fresh ((ct.closed c hc).not_mem_freeVars Z)
          rw [List.map_congr_left hpt, List.map_id]
        have hinstC' := InstantiatesBy.forall2_substFvar (Z := Z) (U := U) h_U_lc hspec.fields
        rw [hcc] at hinstC'
        rw [Env.substFvar_append, Env.substFvar_map_mkTrivial] at hbodyIH
        refine TypeOfElabMatchBranch.mk
          ⟨hspec.lookup, ?_, by simpa using hspec.arity, hspec.bind_count, hinstC'⟩ rfl hbodyIH
        rw [hspec.scrut_eq]; simp [Ty.substFvar, TyList.substFvar_eq_map]
      · subst hpat
        exact TypeOfElabMatchBranch.wildcard hbodyIH
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    -- The fused case = the historical `letRec` machinery (pool freshening
    -- `G ↦ W`, monotypes transported by `renameG_substFvar_comm`/`renameG_renameG`/
    -- `genGroup_renameG`) + the historical `letRecAnn` machinery (schemes
    -- substituted pointwise, opening/substFvar commutation) running
    -- simultaneously; the env transport splits pointwise by `RecSpec`
    -- constructor. Ported from `SpikeLetRecMixed.MixedRule.typ_subst`.
    subst heq
    expose_names
    simp only [Expr.substTyFvar, RecGroup.substTyFvar_eq_map]
    -- Freshen the gen-var pool `G ↦ W` to dodge `Z`, `U`'s free vars, and the
    -- shared monotypes' free vars.
    obtain ⟨W, hWlen0, hWnodup, hWavoid⟩ :=
      exists_fresh_names (G ++ [Z] ++ U.freeVars ++ specs.flatMap RecSpec.monoFreeVars) G.length
    have hWG : ∀ w ∈ W, w ∉ G := fun w hw hc =>
      hWavoid w hw (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hc)))
    have hGW : ∀ g ∈ G, g ∉ W := fun g hg hc => hWG g hc hg
    have hZW : Z ∉ W := fun hc =>
      hWavoid Z hc (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_singleton.2 rfl))))
    have hUW : ∀ u ∈ U.freeVars, u ∉ W := fun u hu hc =>
      hWavoid u hc (List.mem_append_left _ (List.mem_append_right _ hu))
    have hWfree : ∀ τ, RecSpec.mono τ ∈ specs → ∀ w ∈ W, w ∉ τ.freeVars :=
      fun τ hτ w hw hc =>
        hWavoid w hw (List.mem_append_right _
          (List.mem_flatMap.mpr ⟨.mono τ, hτ, hc⟩))
    refine TypeOfElabHM.letRec
      (specs := specs.map (RecSpec.substFreshened Z U G W))
      (G := W) (L := Z :: (G ++ W ++ L))
      ⟨?_, ?_, hWnodup, ?_, ?_⟩ ?_ ?_ rfl ?_
    · -- the stored annotations transport pointwise
      rw [List.map_map, ← hwf.anns_eq, List.map_map]
      apply List.map_congr_left
      intro s _
      cases s <;> rfl
    · simp only [List.length_map]; exact hwf.length
    · -- transported monotypes are LC
      intro τ' hτ'
      obtain ⟨s, hs, hsubst⟩ := List.mem_map.mp hτ'
      cases s with
      | mono τ =>
        injection hsubst with hττ
        rw [← hττ]
        exact Ty.IsLC.substFvar h_U_lc (Ty.renameG_isLC (hwf.mono_lc τ hs))
      | poly σ => exact RecSpec.noConfusion hsubst
    · -- transported schemes are WF
      intro σ' hσ'
      obtain ⟨s, hs, hsubst⟩ := List.mem_map.mp hσ'
      cases s with
      | mono τ => exact RecSpec.noConfusion hsubst
      | poly σ =>
        injection hsubst with hσσ
        rw [← hσσ]
        exact PolyTy.WF.substFvar h_U_lc (hwf.poly_wf σ hs)
    · -- UNANNOTATED members: the historical `letRec` transport
      intro Xs hfresh p hp τ' hτ'
      have hXlen : Xs.length = G.length := hfresh.length.trans hWlen0
      have hZXs : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
      have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
        hfresh.avoid g hc (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hg)))
      have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
        hfresh.avoid w hc (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ hw)))
      have hXsL : FreshNames L G.length Xs :=
        ⟨hXlen, hfresh.nodup, fun x hx hc =>
          hfresh.avoid x hx (List.mem_cons_of_mem _ (List.mem_append_right _ hc))⟩
      have key : ∀ τ, RecSpec.mono τ ∈ specs →
          Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ))
            = Ty.substFvar Z U (Ty.renameG G Xs τ) := by
        intro τ hτ
        rw [Ty.renameG_substFvar_comm h_U_lc hZW hUW hZXs
              (Ty.renameG_isLC (hwf.mono_lc τ hτ)) hWnodup hfresh.length hWXs,
            Ty.renameG_renameG (hwf.mono_lc τ hτ) hwf.nodup hWnodup hWlen0 hXlen hGW (hWfree τ hτ) hWXs hGXs]
      have henv_rhs : (specs.map (RecSpec.substFreshened Z U G W)).map (RecSpec.rhsEntry W Xs)
          = Env.substFvar Z U (specs.map (RecSpec.rhsEntry G Xs)) := by
        show _ = (specs.map (RecSpec.rhsEntry G Xs)).map (PolyTy.substFvar Z U)
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro s hs
        cases s with
        | mono τ =>
          show PolyTy.mkTrivial (Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ)))
            = PolyTy.substFvar Z U (PolyTy.mkTrivial (Ty.renameG G Xs τ))
          rw [key τ hs]
          rfl
        | poly σ => rfl
      obtain ⟨a, b, hab, rfl⟩ := List.mem_zip_map hp
      cases b with
      | poly σ => exact RecSpec.noConfusion hτ'
      | mono τ =>
        injection hτ' with hττ
        rw [← hττ, key τ (List.of_mem_zip hab).2]
        have hIH := ihmono Xs hXsL (a, .mono τ) hab τ rfl
        simp only [RecSpecs.rhsCtx] at hIH
        rw [Env.substFvar_append, ← henv_rhs] at hIH
        exact hIH
    · -- ANNOTATED members: the historical `letRecAnn` transport, nested inside
      -- the pool opening
      intro Xs hfresh p hp σ' hσ' Ys hYs
      have hXlen : Xs.length = G.length := hfresh.length.trans hWlen0
      have hZXs : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
      have hXsL : FreshNames L G.length Xs :=
        ⟨hXlen, hfresh.nodup, fun x hx hc =>
          hfresh.avoid x hx (List.mem_cons_of_mem _ (List.mem_append_right _ hc))⟩
      have hWXs : ∀ w ∈ W, w ∉ Xs := fun w hw hc =>
        hfresh.avoid w hc (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ hw)))
      have key : ∀ τ, RecSpec.mono τ ∈ specs →
          Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ))
            = Ty.substFvar Z U (Ty.renameG G Xs τ) := by
        intro τ hτ
        have hGXs : ∀ g ∈ G, g ∉ Xs := fun g hg hc =>
          hfresh.avoid g hc (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hg)))
        rw [Ty.renameG_substFvar_comm h_U_lc hZW hUW hZXs
              (Ty.renameG_isLC (hwf.mono_lc τ hτ)) hWnodup hfresh.length hWXs,
            Ty.renameG_renameG (hwf.mono_lc τ hτ) hwf.nodup hWnodup hWlen0 hXlen hGW (hWfree τ hτ) hWXs hGXs]
      have henv_rhs : (specs.map (RecSpec.substFreshened Z U G W)).map (RecSpec.rhsEntry W Xs)
          = Env.substFvar Z U (specs.map (RecSpec.rhsEntry G Xs)) := by
        show _ = (specs.map (RecSpec.rhsEntry G Xs)).map (PolyTy.substFvar Z U)
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro s hs
        cases s with
        | mono τ =>
          show PolyTy.mkTrivial (Ty.renameG W Xs (Ty.substFvar Z U (Ty.renameG G W τ)))
            = PolyTy.substFvar Z U (PolyTy.mkTrivial (Ty.renameG G Xs τ))
          rw [key τ hs]
          rfl
        | poly σ => rfl
      obtain ⟨a, b, hab, rfl⟩ := List.mem_zip_map hp
      cases b with
      | mono τ => exact RecSpec.noConfusion hσ'
      | poly σ =>
        injection hσ' with hσσ
        rw [← hσσ]
        have hpc : σ'.paramCount = σ.paramCount := by rw [← hσσ]; rfl
        have hZYs : Z ∉ Ys := fun hc =>
          hYs.avoid Z hc (List.mem_append_left _ List.mem_cons_self)
        have hYsOld : FreshNames (L ++ Xs) σ.paramCount Ys := by
          refine ⟨hYs.length.trans hpc, hYs.nodup, ?_⟩
          intro y hy hc
          rcases List.mem_append.mp hc with hcL | hcXs
          · exact hYs.avoid y hy (List.mem_append_left _
              (List.mem_cons_of_mem _ (List.mem_append_right _ hcL)))
          · exact hYs.avoid y hy (List.mem_append_right _ hcXs)
        have hIH := ihpoly Xs hXsL (a, .poly σ) hab σ rfl Ys hYsOld
        simp only [RecSpecs.rhsCtx] at hIH
        rw [Expr.substTyFvar_openTyVars h_U_lc hZYs,
            ← PolyTy.substFvar_openVars h_U_lc hZYs,
            Env.substFvar_append, ← henv_rhs] at hIH
        exact hIH
    · -- the body: env transport pointwise by constructor
      have henv_body : (specs.map (RecSpec.substFreshened Z U G W)).map (RecSpec.bodyScheme W)
          = Env.substFvar Z U (specs.map (RecSpec.bodyScheme G)) := by
        show _ = (specs.map (RecSpec.bodyScheme G)).map (PolyTy.substFvar Z U)
        rw [List.map_map, List.map_map]
        apply List.map_congr_left
        intro s hs
        cases s with
        | mono τ =>
          show PolyTy.genGroup W (Ty.substFvar Z U (Ty.renameG G W τ))
            = PolyTy.substFvar Z U (PolyTy.genGroup G τ)
          rw [PolyTy.genGroup_renameG (hwf.mono_lc τ hs) hWlen0 hwf.nodup hWnodup hGW (hWfree τ hs),
            PolyTy.genGroup_substFvar hZW hUW]
        | poly σ => rfl
      simp only [RecSpecs.bodyCtx] at ihbody
      rw [Env.substFvar_append, ← henv_body] at ihbody
      exact ihbody

theorem TypeOfElabHM.typ_subst_preservation
    {ctors : CtorEnv} {env_post env_outer : Env}
    {e : Expr} {τ : Ty} {Z : Nat} {U : Ty}
    (h_Z_fresh_outer : Z ∉ env_outer.freeVars)
    (h_U_lc : U.IsLC)
    (h : TypeOfElabHM ⟨env_post ++ env_outer, ctors⟩ e τ) :
    TypeOfElabHM ⟨env_post.substFvar Z U ++ env_outer, ctors⟩ (e.substTyFvar Z U) (Ty.substFvar Z U τ) := by
  -- A direct corollary of the uniform version: uniform substitution turns the
  -- whole env `env_post ++ env_outer` into `(env_post ++ env_outer).substFvar Z U`,
  -- and `env_outer` is unchanged since `Z` is fresh for it.
  have huniform := TypeOfElabHM.typ_subst_preservation_uniform (Z := Z) (U := U) h_U_lc h
  rwa [show (⟨env_post ++ env_outer, ctors⟩ : Ctx).env.substFvar Z U
        = env_post.substFvar Z U ++ env_outer from by
      show Env.substFvar Z U (env_post ++ env_outer) = _
      rw [Env.substFvar_append, Env.substFvar_fresh h_Z_fresh_outer]] at huniform

/- Values are preserved under `shiftFrom` (it only renumbers free term vars,
   leaving the value shape intact). Mutual with `IsCtorChain.shiftFrom`. -/
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

/-- Weakening: insert `env_extra` in the middle of the environment (shifting the
    expression's term-var indices to match), with **no** env-freshness side
    condition. This goes through precisely because the cofinite `letIn`
    rule lets us grow the exclusion set `L` to dodge `env_extra`'s
    type vars on the fly inside the IH.

    Chargueraud's `typing_weaken`. -/
theorem TypeOfElabHM.weaken_env
    {ctors : CtorEnv} {env_pre env_extra env : Env} {e : Expr} {τ : Ty}
    (h : TypeOfElabHM ⟨env_pre ++ env, ctors⟩ e τ) :
    TypeOfElabHM ⟨env_pre ++ env_extra ++ env, ctors⟩
      (e.shiftFrom env_pre.length env_extra.length) τ := by
  -- Derivation induction (`rec_strong`): the `letIn` cofinite case needs an IH
  -- for the *opened* bound expression, which structural induction can't reach.
  -- Generalize over the env split point `env_pre'` (it grows under binders).
  suffices H : ∀ {ctx' : Ctx} {e' : Expr} {τ' : Ty}, TypeOfElabHM ctx' e' τ' →
      ∀ (env_pre' : Env), ctx'.env = env_pre' ++ env →
        TypeOfElabHM ⟨env_pre' ++ env_extra ++ env, ctx'.ctors⟩
          (e'.shiftFrom env_pre'.length env_extra.length) τ' by
    exact H h env_pre rfl
  intro ctx' e' τ' hd
  induction hd using TypeOfElabHM.rec_strong with
  | primLitUnit => intro env_pre' _; exact .primLitUnit
  | primLitInt => intro env_pre' _; exact .primLitInt
  | primLitNat => intro env_pre' _; exact .primLitNat
  | primLitChar => intro env_pre' _; exact .primLitChar
  | primBinOpIntAdd => intro env_pre' _; exact .primBinOpIntAdd
  | primBinOpIntSub => intro env_pre' _; exact .primBinOpIntSub
  | primBinOpIntLt _ _ ihtrue ihfalse =>
    intro env_pre' hctx
    exact .primBinOpIntLt (ihtrue env_pre' hctx) (ihfalse env_pre' hctx)
  | app hf hinput ihf ihinput =>
    intro env_pre' hctx
    simp only [Expr.shiftFrom]
    exact .app (ihf env_pre' hctx) (ihinput env_pre' hctx)
  | ctor hlook htyargs hinst =>
    intro env_pre' _
    exact .ctor hlook htyargs hinst
  | var hlook hlc hinst =>
    intro env_pre' hctx
    expose_names
    rw [hctx] at hlook
    simp only [Expr.shiftFrom]
    by_cases h_lt : dbl < env_pre'.length
    · rw [if_pos h_lt]
      refine .var ?_ hlc hinst
      show (env_pre' ++ env_extra ++ env)[dbl]? = _
      rw [List.getElem?_append_left
            (by simp only [List.length_append]; omega : dbl < (env_pre' ++ env_extra).length),
          List.getElem?_append_left h_lt]
      rwa [List.getElem?_append_left h_lt] at hlook
    · push_neg at h_lt
      rw [if_neg (Nat.not_lt.mpr h_lt)]
      refine .var ?_ hlc hinst
      show (env_pre' ++ env_extra ++ env)[dbl + env_extra.length]? = _
      rw [List.getElem?_append_right
            (by simp only [List.length_append]; omega :
              (env_pre' ++ env_extra).length ≤ dbl + env_extra.length)]
      rw [show dbl + env_extra.length - (env_pre' ++ env_extra).length = dbl - env_pre'.length
            from by simp only [List.length_append]; omega]
      rwa [List.getElem?_append_right h_lt] at hlook
  | lambda hpc hann heq hbody ihbody =>
    intro env_pre' hctx
    subst heq
    simp only [Expr.shiftFrom]
    refine TypeOfElabHM.lambda hpc hann rfl ?_
    expose_names
    have hb := ihbody (PolyTy.mkTrivial paramTy :: env_pre') (by rw [hctx, List.cons_append])
    simpa only [List.cons_append, List.length_cons] using hb
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    intro env_pre' hctx
    subst heq
    expose_names
    simp only [Expr.shiftFrom]
    refine TypeOfElabHM.letIn (M := M) (L := L) hwf hann ?_ rfl ?_
    · intro Xs hfresh
      have hc := ihcofin Xs hfresh env_pre' hctx
      rwa [Expr.shiftFrom_openBoundTyVars] at hc
    · have hb := ihbody (M :: env_pre') (by rw [hctx, List.cons_append])
      simpa only [List.cons_append, List.length_cons] using hb
  | match_ hscrut hne hbrs ihscrut ihbrs =>
    intro env_pre' hctx
    simp only [Expr.shiftFrom]
    refine TypeOfElabHM.match_ (ihscrut env_pre' hctx) ?_ ?_
    · intro hcontra
      obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil hne
      rw [hb] at hcontra
      simp [BranchList.shiftFrom] at hcontra
    · intro branch' hmem'
      obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_shiftFrom hmem'
      rcases ihbrs (pat, body) hmem with
        ⟨ct, c, n, tyArgs, instContents, hpat, hspec, _, hbodyIH⟩ |
        ⟨hpat, _, hbodyIH⟩
      · subst hpat
        simp only [MatchPattern.bindCount]
        have hib := hbodyIH (instContents.map PolyTy.mkTrivial ++ env_pre')
          (by rw [hctx, List.append_assoc])
        simp only [List.length_append, List.length_map] at hib
        rw [← hspec.fields.length_eq, ← hspec.bind_count,
            show n + env_pre'.length = env_pre'.length + n
              from Nat.add_comm _ _] at hib
        refine TypeOfElabMatchBranch.mk
          ⟨hspec.lookup, hspec.scrut_eq, hspec.arity, hspec.bind_count, hspec.fields⟩ rfl ?_
        rw [show env_pre' ++ env_extra ++ env = env_pre' ++ (env_extra ++ env)
              from List.append_assoc _ _ _]
        rw [List.append_assoc, List.append_assoc] at hib
        exact hib
      · subst hpat
        simp only [MatchPattern.bindCount, Nat.add_zero]
        exact TypeOfElabMatchBranch.wildcard (hbodyIH env_pre' hctx)
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    -- Ported from `SpikeLetRecMixed.MixedRule.weaken_env_front`: both cofinite
    -- openings are quantified (never pinned) and the specs are ctx-free ⇒
    -- delegate each RHS/body to the IH; no `L` growth, no side conditions.
    intro env_pre' hctx
    subst heq
    expose_names
    simp only [Expr.shiftFrom, RecGroup.shiftFrom_eq_map]
    refine TypeOfElabHM.letRec (specs := specs) (G := G) (L := L)
      ⟨hwf.anns_eq, ?_, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩ ?_ ?_ rfl ?_
    · rw [List.length_map]; exact hwf.length
    · intro Xs hfresh p hp τ hτ
      obtain ⟨a, b, _, hq, rfl⟩ := List.mem_zip_map_left hp
      have hc := ihmono Xs hfresh (a, b) hq τ hτ
        (specs.map (RecSpec.rhsEntry G Xs) ++ env_pre')
        (by simp only [RecSpecs.rhsCtx]; rw [hctx, List.append_assoc])
      simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
      rw [← hwf.length, Nat.add_comm bindings.length env_pre'.length] at hc
      simp only [RecSpecs.rhsCtx, List.append_assoc] at hc ⊢
      exact hc
    · intro Xs hfresh p hp σ hσ Ys hYs
      obtain ⟨a, b, _, hq, rfl⟩ := List.mem_zip_map_left hp
      have hc := ihpoly Xs hfresh (a, b) hq σ hσ Ys hYs
        (specs.map (RecSpec.rhsEntry G Xs) ++ env_pre')
        (by simp only [RecSpecs.rhsCtx]; rw [hctx, List.append_assoc])
      rw [Expr.shiftFrom_openTyVars] at hc
      simp only [RecSpecs.rhsCtx, List.length_append, List.length_map] at hc
      rw [← hwf.length, Nat.add_comm bindings.length env_pre'.length] at hc
      simp only [RecSpecs.rhsCtx, List.append_assoc] at hc ⊢
      exact hc
    · have hb := ihbody (specs.map (RecSpec.bodyScheme G) ++ env_pre')
        (by simp only [RecSpecs.bodyCtx]; rw [hctx, List.append_assoc])
      simp only [RecSpecs.bodyCtx, List.length_append, List.length_map] at hb
      rw [← hwf.length, Nat.add_comm bindings.length env_pre'.length] at hb
      simp only [RecSpecs.bodyCtx, List.append_assoc] at hb ⊢
      exact hb

/-- Iterated type substitution preserves typing: substituting each `(Zᵢ, Uᵢ)`
    in turn (with every `Zᵢ` fresh for the env and every `Uᵢ` locally closed)
    preserves the derivation. Chargueraud's `typing_typ_substs`. -/
theorem TypeOfElabHM.typ_substs_preservation {ctx : Ctx} {e : Expr}
    (pairs : List (Nat × Ty))
    (h_fresh : ∀ p ∈ pairs, p.1 ∉ ctx.env.freeVars)
    (h_lc : ∀ p ∈ pairs, Ty.IsLC p.2)
    {τ : Ty} (h : TypeOfElabHM ctx e τ) :
    TypeOfElabHM ctx (e.substTyFvars pairs) (Ty.substFvars pairs τ) := by
  induction pairs generalizing e τ with
  | nil => exact h
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Ty.substFvars]
    have hZ : Z ∉ ctx.env.freeVars := h_fresh (Z, U) List.mem_cons_self
    have hU : Ty.IsLC U := h_lc (Z, U) List.mem_cons_self
    have hstep := TypeOfElabHM.typ_subst_preservation (env_post := []) (env_outer := ctx.env)
      (ctors := ctx.ctors) hZ hU h
    simp only [Env.substFvar, List.map_nil, List.nil_append] at hstep
    exact ih (fun p hp => h_fresh p (List.mem_cons_of_mem _ hp))
             (fun p hp => h_lc p (List.mem_cons_of_mem _ hp)) hstep

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
  | .var _ tyArgs       => tyArgs.flatMap Ty.freeVars
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
  | var n tyArgs =>
    simp only [Expr.substTyFvar, Expr.var.injEq, true_and]
    have h' : ∀ t ∈ tyArgs, Z ∉ t.freeVars := by
      intro t ht hc
      exact h (by simp only [Expr.tyFreeVars, List.mem_flatMap]; exact ⟨t, ht, hc⟩)
    clear h
    induction tyArgs with
    | nil => rfl
    | cons hd tl ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨Ty.substFvar_fresh (h' hd List.mem_cons_self),
             ih (fun t ht => h' t (List.mem_cons_of_mem _ ht))⟩
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

theorem Expr.substTyFvars_var {σ : List (Nat × Ty)} {n : Nat} {tyArgs : List Ty} :
    Expr.substTyFvars σ (.var n tyArgs) = .var n (tyArgs.map (Ty.substFvars σ)) := by
  induction σ generalizing tyArgs with
  | nil =>
    simp only [Expr.substTyFvars]
    congr 1
    conv_lhs => rw [← List.map_id tyArgs]
    apply List.map_congr_left; intro t _; rfl
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Expr.substTyFvars, Expr.substTyFvar, ih, List.map_map, Function.comp_def,
      Ty.substFvars]

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
  | var n tyArgs =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.substTyFvars_var, Expr.var.injEq, true_and, List.map_map]
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_def]
    exact Ty.substFvars_zip_openVarsFrom h_len h_Ys_nodup
      (fun y hy hc => hfresh y hy (by
        simp only [Expr.tyFreeVars, List.mem_flatMap]; exact ⟨t, ht, hc⟩))
      h_Ys_Xs
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
  | var n tyArgs =>
    intro d hfresh
    simp only [Expr.openTyVarsAux, Expr.instTyAux, Expr.substTyFvars_var, Expr.var.injEq,
      true_and, List.map_map]
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_def]
    exact Ty.substFvars_zip_openVarsFrom_concrete h_len h_Ys_nodup
      (fun y hy hc => hfresh y hy (by
        simp only [Expr.tyFreeVars, List.mem_flatMap]; exact ⟨t, ht, hc⟩))
      h_Ys_Vs h_Vs_lc
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
  | .var _ _            => 1
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
  | var n tyArgs =>
    intro d z hz
    simp only [Expr.openTyVarsAux, Expr.tyFreeVars, List.mem_flatMap] at hz ⊢
    obtain ⟨t', ht', hzt'⟩ := hz
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ht'
    rcases Ty.freeVars_openVarsFrom_subset z hzt' with h | h
    · exact .inl ⟨t, ht, h⟩
    · exact .inr h
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

/-- The bridge: a cofinite-vars witness gives a "for-all-instances" witness.
    Chargueraud's `has_scheme_from_vars`. For any `Vs`, pick `Xs` fresh for
    everything relevant, use the cofinite witness at `Xs`, then iteratively
    `typ_subst_preservation`-substitute each `Xᵢ ↦ Vᵢ` (the
    `openWith = substFvars ∘ openVars` identity bridges the two openings). The
    `Xs` are also chosen fresh for `e`'s own annotation free vars, so the
    `substTyFvars` ripple introduced by `typ_substs_preservation` collapses back
    to `e`. -/
theorem HasScheme.fromHasSchemeVars
    {L : List Nat} {ctx : Ctx} {e : Expr} {M : PolyTy}
    (h : HasSchemeVars L ctx e M) :
    HasScheme ctx e M := by
  intro Vs hVs
  obtain ⟨hVlen, hVlc⟩ := hVs
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names
      (L ++ M.body.freeVars ++ Ty.freeVarsList Vs ++ ctx.env.freeVars ++ e.tyFreeVars) M.paramCount
  -- split the combined freshness into its parts
  have hX_L : ∀ x ∈ Xs, x ∉ L := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_Mbody : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_Vs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList Vs := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_env : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_e : ∀ x ∈ Xs, x ∉ e.tyFreeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hVlen' : Vs.length = Xs.length := by rw [hVlen, hXlen]
  -- the cofinite witness, instantiated at our fresh Xs (it types `e.instTy (Xs.map fvar)`)
  have hwit := h Xs ⟨hXlen, hXnodup, hX_L⟩
  -- bridge openWith to substFvars ∘ openVars
  have hrewrite : M.openWith Vs = Ty.substFvars (Xs.zip Vs) (M.openVars Xs) := by
    unfold PolyTy.openWith PolyTy.openVars
    exact Ty.openWith_eq_substFvars_openVars ⟨hVlen', hVlc⟩ hXnodup hX_Mbody hX_Vs
  show TypeOfElabHM ctx (e.instTy Vs) (M.openWith Vs)
  rw [hrewrite]
  have hsub := TypeOfElabHM.typ_substs_preservation (Xs.zip Vs)
    (fun p hp => hX_env p.1 (List.of_mem_zip hp).1)
    (fun p hp => hVlc p.2 (List.of_mem_zip hp).2) hwit
  -- `e.instTy (Xs.map fvar) = e.openTyVars Xs`, then the concrete bridge turns the
  -- `substTyFvars (Xs ↦ Vs)` ripple into `e.instTy Vs`.
  rw [Expr.instTy_fvar_eq_openTyVars] at hsub
  rwa [Expr.substTyFvars_zip_openTyVars_concrete hVlen' hXnodup hX_e hX_Vs hVlc] at hsub

/-- Instantiation with the "identity on bvars" substitution is a no-op. Used
    in `HasScheme.ofTypeOfElabHM` to show that opening an arity-0 scheme with the
    empty arg list returns the underlying type unchanged. -/
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

/-- Opening with the empty list of types is identity: nothing to instantiate. -/
theorem Ty.openWith_nil {ty : Ty} : Ty.openWith [] ty = ty := by
  unfold Ty.openWith
  have heq : (fun i => ([] : List Ty)[i]?.getD (.bvar i)) = (fun i => Ty.bvar i) := by
    funext i; simp
  rw [heq]
  exact Ty.instantiate_bvar_id

/-- Monomorphic `has_scheme`: a regular typing is a `HasScheme` for the
    trivial 0-binder scheme. Chargueraud's `has_scheme_from_typ`. -/
theorem HasScheme.ofTypeOfElabHM
    {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfElabHM ctx e τ) :
    HasScheme ctx e (PolyTy.mkTrivial τ) := by
  intro Vs h_lc
  obtain ⟨h_len, _⟩ := h_lc
  -- PolyTy.mkTrivial τ has paramCount = 0, so Vs = []
  have h_vs_nil : Vs = [] := List.length_eq_zero_iff.mp h_len
  subst h_vs_nil
  show TypeOfElabHM ctx (e.instTy []) (PolyTy.openWith [] (PolyTy.mkTrivial τ))
  rw [Expr.instTy_nil]
  unfold PolyTy.openWith PolyTy.mkTrivial
  rw [Ty.openWith_nil]
  exact h


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
  | .var _ tyArgs       => ∀ t ∈ tyArgs, ContainsBvarsUpTo n t
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
  | var i tyArgs => intro h hnm t ht; exact (h t ht).mono hnm
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
  | var n tyArgs =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h
    intro t ht
    exact Ty.containsBvars_of_openVarsFrom d Xs (h _ (List.mem_map_of_mem ht))
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

/-- Extract a branch body's `TyBvarBounded 0` from its `BranchMotive` (under the
    `tyBvarBounded` motive, which ignores the derivation). -/
private theorem TypeOfElabHM.branchMotive_tyBvarBounded {ctx : Ctx} {p : MatchPattern} {b : Expr}
    {scrutTy resultTy : Ty}
    (h : TypeOfElabHM.BranchMotive (fun _ e _ _ => e.TyBvarBounded 0) ctx (p, b) scrutTy resultTy) :
    b.TyBvarBounded 0 := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hb⟩ | ⟨_, _, hb⟩
  · exact hb
  · exact hb

/-- **Well-typed terms are type-`bvar`-closed** (no free type bvars). The `lambda`
    rule forces annotations LC, the `var`/`ctor` rules force `tyArgs` LC, schemes
    are WF; the `letIn`-with-scheme case reflects the opened cofinite premise. -/
theorem TypeOfElabHM.tyBvarBounded {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfElabHM ctx e τ) : e.TyBvarBounded 0 := by
  induction h using TypeOfElabHM.rec_strong with
  | primLitUnit => trivial
  | primLitInt => trivial
  | primLitNat => trivial
  | primLitChar => trivial
  | primBinOpIntAdd => trivial
  | primBinOpIntSub => trivial
  | primBinOpIntLt _ _ _ _ => trivial
  | app _ _ ihf ihi => exact ⟨ihf, ihi⟩
  | var hlook hlc hinst => exact hlc.2
  | ctor _ _ _ => trivial
  | lambda hpc hann heq hbody ihbody =>
    refine ⟨fun t ht => ?_, ihbody⟩
    rw [← hann t ht]; exact hpc
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    expose_names
    cases hann_ann : ann with
    | none =>
      simp only [Expr.TyBvarBounded]
      refine ⟨?_, ihbody⟩
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
      have := ihcofin Xs ⟨hXlen, hXnodup, hXavoid⟩
      rw [hann_ann] at this
      simpa only [Expr.openBoundTyVars] using this
    | some σ =>
      have hMσ : M = σ := hann σ hann_ann
      subst hMσ
      simp only [Expr.TyBvarBounded]
      refine ⟨by simpa using hwf, ?_, ihbody⟩
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
      have hc := ihcofin Xs ⟨hXlen, hXnodup, hXavoid⟩
      rw [hann_ann] at hc
      simp only [Expr.openBoundTyVars] at hc
      have := Expr.tyBvarBounded_of_openTyVarsAux Xs boundExpr 0 hc
      simpa only [Nat.zero_add, hXlen] using this
  | match_ hscrut hne hbrs ihscrut ihbrs =>
    exact ⟨ihscrut, Expr.TyBvarBounded.BranchList_iff.mpr
      (fun p b hmem => TypeOfElabHM.branchMotive_tyBvarBounded (ihbrs (p, b) hmem))⟩
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    expose_names
    refine ⟨?_, ?_, ihbody⟩
    · -- annotated schemes are WF (via the spec link `hwf.anns_eq`)
      intro σ hσ
      rw [← hwf.anns_eq] at hσ
      obtain ⟨s, hs, hsa⟩ := List.mem_map.mp hσ
      cases RecSpec.ann_eq_some hsa
      simpa using hwf.poly_wf σ hs
    · -- per-binding boundedness at the shield depths
      rw [← hwf.anns_eq]
      refine Expr.TyBvarBounded.RecGroup_of_zip (by simpa using hwf.length) (fun p hp => ?_)
      obtain ⟨e, s, hes, rfl⟩ := List.mem_zip_map_right_ex hp
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
      cases s with
      | mono τ =>
        simp only [RecSpec.ann, RecAnn.params, Nat.add_zero]
        exact ihmono Xs ⟨hXlen, hXnodup, hXavoid⟩ (e, .mono τ) hes τ rfl
      | poly σ =>
        simp only [RecSpec.ann, RecAnn.params]
        obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ := exists_fresh_names (L ++ Xs) σ.paramCount
        have hc := ihpoly Xs ⟨hXlen, hXnodup, hXavoid⟩ (e, .poly σ) hes σ rfl
          Ys ⟨hYlen, hYnodup, hYavoid⟩
        have hb := Expr.tyBvarBounded_of_openTyVarsAux Ys e 0
          (by simpa only [Expr.openTyVars] using hc)
        simpa only [Nat.zero_add, hYlen] using hb

/-- A `HasScheme` value is type-`bvar`-bounded by its scheme's arity: its scoped
    type bvars all reference `M`. (Open at fresh `fvar`s — coinciding with
    `instTy` — type the opened value, which is `TyBvarBounded 0`; reflect back.) -/
theorem HasScheme.tyBvarBounded {ctx : Ctx} {v : Expr} {M : PolyTy}
    (h : HasScheme ctx v M) : v.TyBvarBounded M.paramCount := by
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names [] M.paramCount
  have hVs_lc : Ty.AreLC M.paramCount (Xs.map Ty.fvar) := by
    refine ⟨by rw [List.length_map, hXlen], ?_⟩
    intro V hV; obtain ⟨x, _, rfl⟩ := List.mem_map.mp hV; exact .fvar
  have htyped := h (Xs.map Ty.fvar) hVs_lc
  rw [Expr.instTy_fvar_eq_openTyVars] at htyped
  have hbound := TypeOfElabHM.tyBvarBounded htyped
  have := Expr.tyBvarBounded_of_openTyVarsAux Xs v 0 (by
    simpa only [Expr.openTyVars] using hbound)
  simpa only [Nat.zero_add, hXlen] using this

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
  | var n tyArgs =>
    intro d d' h
    simp only [Expr.instTyAux, Expr.openTyVarsAux, Expr.var.injEq, true_and, List.map_map]
    apply List.map_congr_left
    intro t ht
    simp only [Function.comp_def]
    exact Ty.openVarsFrom_openTyFrom d' d Ys Ts (h t ht)
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

/-! **Substituted variables supply enough type arguments.** `e.SubstArgsGe Ns k`
    says every `var i tyArgs` in `e` that `substN k vs` would replace (i.e.
    `k ≤ i < k + Ns.length`) supplies at least `Ns[i-k]` type arguments. With
    `Ns = (substituted schemes).map paramCount`, this is exactly the var-rule
    invariant `tyArgs.length = scheme.paramCount`, and it gives the coverage the
    `substN`/`openTyVars` commutation needs. -/
mutual
def Expr.SubstArgsGe (Ns : List Nat) (k : Nat) : Expr → Prop
  | .primLit _          => True
  | .primBinOp _        => True
  | .lambda _ body      => body.SubstArgsGe Ns (k + 1)
  | .app f arg          => f.SubstArgsGe Ns k ∧ arg.SubstArgsGe Ns k
  | .letIn _ rhs body   => rhs.SubstArgsGe Ns k ∧ body.SubstArgsGe Ns (k + 1)
  | .var i tyArgs       => ∀ N, Ns[i - k]? = some N → k ≤ i → N ≤ tyArgs.length
  | .ctor _             => True
  | .match_ scrut branches => scrut.SubstArgsGe Ns k ∧ Expr.SubstArgsGe.BranchList Ns k branches
  | .letRec _ bindings body =>
      Expr.SubstArgsGe.RecGroup Ns (k + bindings.length) bindings ∧
        body.SubstArgsGe Ns (k + bindings.length)
def Expr.SubstArgsGe.BranchList (Ns : List Nat) (k : Nat) :
    List (MatchPattern × Expr) → Prop
  | []                  => True
  | (pat, body) :: rest =>
      body.SubstArgsGe Ns (k + pat.bindCount) ∧ Expr.SubstArgsGe.BranchList Ns k rest
def Expr.SubstArgsGe.RecGroup (Ns : List Nat) (k : Nat) : List Expr → Prop
  | []        => True
  | e :: rest => e.SubstArgsGe Ns k ∧ Expr.SubstArgsGe.RecGroup Ns k rest
end

theorem Expr.SubstArgsGe.BranchList_iff {Ns : List Nat} {k : Nat}
    {brs : List (MatchPattern × Expr)} :
    Expr.SubstArgsGe.BranchList Ns k brs ↔
      ∀ p b, (p, b) ∈ brs → b.SubstArgsGe Ns (k + p.bindCount) := by
  induction brs with
  | nil => simp [Expr.SubstArgsGe.BranchList]
  | cons hd tl ih =>
    obtain ⟨p, b⟩ := hd
    simp only [Expr.SubstArgsGe.BranchList, ih, List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro ⟨hb, hrest⟩ p' b' (heq | hmem)
      · obtain ⟨rfl, rfl⟩ := heq; exact hb
      · exact hrest p' b' hmem
    · intro h; exact ⟨h p b (Or.inl ⟨rfl, rfl⟩), fun p' b' hmem => h p' b' (Or.inr hmem)⟩

theorem Expr.SubstArgsGe.RecGroup_iff {Ns : List Nat} {k : Nat} {bs : List Expr} :
    Expr.SubstArgsGe.RecGroup Ns k bs ↔ ∀ e ∈ bs, e.SubstArgsGe Ns k := by
  induction bs with
  | nil => simp [Expr.SubstArgsGe.RecGroup]
  | cons hd tl ih =>
    simp only [Expr.SubstArgsGe.RecGroup, ih, List.mem_cons]
    constructor
    · rintro ⟨hb, hrest⟩ e (rfl | hmem)
      · exact hb
      · exact hrest e hmem
    · intro h; exact ⟨h hd (Or.inl rfl), fun e hmem => h e (Or.inr hmem)⟩

/-- `SubstArgsGe` is invariant under scoped-variable opening (which preserves term
    structure and every `tyArgs` length). -/
theorem Expr.SubstArgsGe_openTyVarsAux (Ns : List Nat) (Ys : List Nat) :
    ∀ (e : Expr) (d k : Nat),
      Expr.SubstArgsGe Ns k (e.openTyVarsAux d Ys) → Expr.SubstArgsGe Ns k e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d k _; trivial
  | primBinOp op => intro d k _; trivial
  | ctor nm => intro d k _; trivial
  | var n tyArgs =>
    intro d k h
    simp only [Expr.openTyVarsAux, Expr.SubstArgsGe, List.length_map] at h
    exact h
  | app f arg ihf iharg =>
    intro d k h
    simp only [Expr.openTyVarsAux, Expr.SubstArgsGe] at h
    exact ⟨ihf d k h.1, iharg d k h.2⟩
  | lambda ann body ih =>
    intro d k h
    simp only [Expr.openTyVarsAux, Expr.SubstArgsGe] at h
    exact ih d (k + 1) h
  | letIn ann rhs body ihr ihb =>
    intro d k h
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.SubstArgsGe] at h
      exact ⟨ihr d k h.1, ihb d (k + 1) h.2⟩
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.SubstArgsGe] at h
      exact ⟨ihr (d + σ.paramCount) k h.1, ihb d (k + 1) h.2⟩
  | match_ scrut branches ihs ihbs =>
    intro d k h
    simp only [Expr.openTyVarsAux, Expr.SubstArgsGe, BranchList.openTyVarsAux_eq_map,
      Expr.SubstArgsGe.BranchList_iff] at h ⊢
    refine ⟨ihs d k h.1, fun p b hmem => ?_⟩
    exact ihbs p b hmem d (k + p.bindCount) (h.2 p (b.openTyVarsAux d Ys) (List.mem_map_of_mem hmem))
  | letRec anns bindings body ihbs ihb =>
    intro d k h
    simp only [Expr.openTyVarsAux, Expr.SubstArgsGe, RecGroup.openTyVarsAux_length] at h ⊢
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ihb d (k + bindings.length) h2⟩
    clear h2 ihb
    generalize k + bindings.length = m at h1 ⊢
    revert ihbs h1
    induction bindings generalizing anns with
    | nil => intro _ _; trivial
    | cons hd tl ih =>
      intro ihbs h1
      cases anns with
      | nil =>
        simp only [RecGroup.openTyVarsAux, Expr.SubstArgsGe.RecGroup] at h1 ⊢
        exact ⟨ihbs hd List.mem_cons_self d m h1.1,
          ih [] (fun e he => ihbs e (List.mem_cons_of_mem _ he)) h1.2⟩
      | cons a as =>
        simp only [RecGroup.openTyVarsAux, Expr.SubstArgsGe.RecGroup] at h1 ⊢
        exact ⟨ihbs hd List.mem_cons_self (d + RecAnn.params a) m h1.1,
          ih as (fun e he => ihbs e (List.mem_cons_of_mem _ he)) h1.2⟩

/-- A well-typed term satisfies `SubstArgsGe` for the schemes bound at any prefix
    split of its context: the `var` rule pins `tyArgs.length = scheme.paramCount`,
    so every substituted-position use supplies exactly (hence `≥`) its scheme's
    arity of type arguments. -/
theorem TypeOfElabHM.substArgsGe {ctors : CtorEnv} {blk env : Env} :
    ∀ {ctx : Ctx} {e : Expr} {τ : Ty}, TypeOfElabHM ctx e τ →
      ∀ env_post : Env, ctx = ⟨env_post ++ blk ++ env, ctors⟩ →
        e.SubstArgsGe (blk.map PolyTy.paramCount) env_post.length := by
  intro ctx e τ h
  induction h using TypeOfElabHM.rec_strong with
  | primLitUnit => intro _ _; trivial
  | primLitInt => intro _ _; trivial
  | primLitNat => intro _ _; trivial
  | primLitChar => intro _ _; trivial
  | primBinOpIntAdd => intro _ _; trivial
  | primBinOpIntSub => intro _ _; trivial
  | primBinOpIntLt _ _ _ _ => intro _ _; trivial
  | ctor _ _ _ => intro _ _; trivial
  | app _ _ ihf ihi => intro env_post hctx; exact ⟨ihf env_post hctx, ihi env_post hctx⟩
  | var hlook hlc hinst =>
    intro env_post hctx
    subst hctx
    simp only [Expr.SubstArgsGe]
    intro N hN hki
    rw [List.getElem?_map] at hN
    obtain ⟨polyTy', hpoly, hpc⟩ := Option.map_eq_some_iff.mp hN
    have hlt := (List.getElem?_eq_some_iff.mp hpoly).1
    rw [show (⟨env_post ++ blk ++ env, ctors⟩ : Ctx).env = env_post ++ blk ++ env from rfl,
      List.append_assoc, List.getElem?_append_right hki, List.getElem?_append_left hlt,
      hpoly, Option.some.injEq] at hlook
    rw [hlc.1, ← hlook]
    exact le_of_eq hpc.symm
  | lambda hpc hann heq hbody ihbody =>
    intro env_post hctx
    subst heq
    subst hctx
    expose_names
    exact ihbody (PolyTy.mkTrivial paramTy :: env_post) rfl
  | letIn hwf hann hcofin heq hbody ihcofin ihbody =>
    intro env_post hctx
    subst heq
    subst hctx
    expose_names
    refine ⟨?_, ihbody (M :: env_post) rfl⟩
    obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
    have hc := ihcofin Xs ⟨hXlen, hXnodup, hXavoid⟩ env_post rfl
    cases ann with
    | none => simpa only [Expr.openBoundTyVars] using hc
    | some σ =>
      rw [Expr.openBoundTyVars] at hc
      exact Expr.SubstArgsGe_openTyVarsAux _ Xs _ 0 _ hc
  | match_ hscrut hne hbrs ihscrut ihbrs =>
    intro env_post hctx
    subst hctx
    refine ⟨ihscrut env_post rfl, ?_⟩
    rw [Expr.SubstArgsGe.BranchList_iff]
    intro p b hmem
    rcases ihbrs (p, b) hmem with
      ⟨ct, c, n, tyArgs, instContents, hpat, hspec, _, hbodyIH⟩ |
      ⟨hpat, _, hbodyIH⟩
    · have hpeq : p = MatchPattern.named c n := hpat
      subst hpeq
      have := hbodyIH (instContents.map PolyTy.mkTrivial ++ env_post)
        (by simp only [List.append_assoc])
      simp only [MatchPattern.bindCount]
      rw [List.length_append, List.length_map, ← hspec.fields.length_eq, ← hspec.bind_count,
        Nat.add_comm] at this
      exact this
    · have hpeq : p = MatchPattern.wildcard := hpat
      subst hpeq
      simp only [MatchPattern.bindCount, Nat.add_zero]
      exact hbodyIH env_post rfl
  | letRec hwf hmono hpoly heq hbody ihmono ihpoly ihbody =>
    intro env_post hctx
    subst heq
    subst hctx
    expose_names
    refine ⟨?_, ?_⟩
    · rw [Expr.SubstArgsGe.RecGroup_iff]
      intro e hmem
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hmem
      obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
      have hlt : i < (bindings.zip specs).length := by
        rw [List.length_zip, ← hwf.length, Nat.min_self]; exact hi
      have henv : (specs.map (RecSpec.rhsEntry G Xs)).length = bindings.length := by
        rw [List.length_map, hwf.length]
      cases hspec : (bindings.zip specs)[i].2 with
      | mono τ =>
        have hc := ihmono Xs ⟨hXlen, hXnodup, hXavoid⟩ _ (List.getElem_mem hlt) τ hspec
          (specs.map (RecSpec.rhsEntry G Xs) ++ env_post)
          (by simp only [RecSpecs.rhsCtx, List.append_assoc])
        rw [List.getElem_zip] at hc
        rw [List.length_append, henv, Nat.add_comm] at hc
        exact hc
      | poly σ =>
        obtain ⟨Ys, hYlen, hYnodup, hYavoid⟩ := exists_fresh_names (L ++ Xs) σ.paramCount
        have hc := ihpoly Xs ⟨hXlen, hXnodup, hXavoid⟩ _ (List.getElem_mem hlt) σ hspec
          Ys ⟨hYlen, hYnodup, hYavoid⟩
          (specs.map (RecSpec.rhsEntry G Xs) ++ env_post)
          (by simp only [RecSpecs.rhsCtx, List.append_assoc])
        rw [List.getElem_zip] at hc
        have hc' := Expr.SubstArgsGe_openTyVarsAux _ Ys _ 0 _ hc
        rw [List.length_append, henv, Nat.add_comm] at hc'
        exact hc'
    · have := ihbody (specs.map (RecSpec.bodyScheme G) ++ env_post)
        (by simp only [RecSpecs.bodyCtx, List.append_assoc])
      rw [List.length_append, List.length_map, ← hwf.length, Nat.add_comm] at this
      exact this

/-- **Term-substitution commutes with scoped-variable opening.** `substN` (with
    type-beta folded into its substituted branch) commutes with `openTyVarsAux`,
    provided every substituted value `vs[j]` is `TyBvarBounded` by its scheme arity
    `Ns[j]` and `e` supplies enough type arguments (`SubstArgsGe`). This is the
    engine of `subst_lemma`'s annotated-`letIn` cofinite reconstruction. -/
theorem Expr.substN_openTyVarsAux_comm {Ys : List Nat} {vs : List Expr} {Ns : List Nat}
    (h_len : vs.length = Ns.length)
    (h_vs : ∀ (j : Nat) (v : Expr) (N : Nat),
      vs[j]? = some v → Ns[j]? = some N → Expr.TyBvarBounded N v) :
    ∀ (e : Expr) (d k : Nat), e.SubstArgsGe Ns k →
      (e.openTyVarsAux d Ys).substN k vs = (e.substN k vs).openTyVarsAux d Ys := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d k _; rfl
  | primBinOp op => intro d k _; rfl
  | ctor nm => intro d k _; rfl
  | var i tyArgs =>
    intro d k h_sa
    simp only [Expr.openTyVarsAux, Expr.substN]
    by_cases hik : i < k
    · simp only [if_pos hik, Expr.openTyVarsAux]
    · simp only [if_neg hik]
      by_cases hiv : i - k < vs.length
      · simp only [dif_pos hiv]
        rw [← Expr.shiftFrom_openTyVarsAux]
        congr 1
        have hNsome : Ns[i - k]? = some Ns[i - k] :=
          List.getElem?_eq_getElem (by rw [← h_len]; exact hiv)
        have hb : vs[i - k].TyBvarBounded Ns[i - k] :=
          h_vs (i - k) vs[i - k] Ns[i - k] (List.getElem?_eq_getElem hiv) hNsome
        have hle : Ns[i - k] ≤ tyArgs.length := by
          simp only [Expr.SubstArgsGe] at h_sa
          exact h_sa (Ns[i - k]) hNsome (by omega)
        have hcomm := Expr.openTyVarsAux_instTyAux Ys tyArgs vs[i - k] d 0
          (by simpa using Expr.TyBvarBounded.mono hb hle)
        simp only [Nat.add_zero] at hcomm
        simpa only [Expr.instTy] using hcomm.symm
      · simp only [dif_neg hiv, Expr.openTyVarsAux]
  | app f arg ihf iharg =>
    intro d k h
    simp only [Expr.openTyVarsAux, Expr.substN]
    rw [ihf d k h.1, iharg d k h.2]
  | lambda ann body ih =>
    intro d k h
    simp only [Expr.openTyVarsAux, Expr.substN]
    congr 1
    exact ih d (k + 1) h
  | letIn ann rhs body ihr ihb =>
    intro d k h
    cases ann with
    | none =>
      simp only [Expr.openTyVarsAux, Expr.substN]
      rw [ihr d k h.1, ihb d (k + 1) h.2]
    | some σ =>
      simp only [Expr.openTyVarsAux, Expr.substN]
      rw [ihr (d + σ.paramCount) k h.1, ihb d (k + 1) h.2]
  | match_ scrut branches ihs ihbs =>
    intro d k h
    simp only [Expr.openTyVarsAux, Expr.substN, Expr.match_.injEq]
    obtain ⟨hs, hbs⟩ := h
    rw [Expr.SubstArgsGe.BranchList_iff] at hbs
    refine ⟨ihs d k hs, ?_⟩
    revert ihbs hbs
    induction branches with
    | nil => intro _ _; rfl
    | cons hd tl ihtl =>
      obtain ⟨p, b⟩ := hd
      intro ihbs hbs
      simp only [BranchList.openTyVarsAux, BranchList.substN, List.cons.injEq, Prod.mk.injEq,
        true_and]
      refine ⟨ihbs p b List.mem_cons_self d (k + p.bindCount) (hbs p b List.mem_cons_self), ?_⟩
      exact ihtl (fun p' b' hm => ihbs p' b' (List.mem_cons_of_mem _ hm))
        (fun p' b' hm => hbs p' b' (List.mem_cons_of_mem _ hm))
  | letRec anns bindings body ihbs ihb =>
    intro d k h
    simp only [Expr.openTyVarsAux, Expr.substN, RecGroup.openTyVarsAux_length,
      Expr.letRec.injEq, true_and]
    obtain ⟨hbs, hb⟩ := h
    rw [Expr.SubstArgsGe.RecGroup_iff] at hbs
    refine ⟨?_, ihb d (k + bindings.length) hb⟩
    clear hb ihb
    generalize k + bindings.length = m at hbs ⊢
    revert ihbs hbs
    induction bindings generalizing anns with
    | nil => intro _ _; cases anns <;> rfl
    | cons hd tl ih =>
      intro ihbs hbs
      cases anns with
      | nil =>
        simp only [RecGroup.openTyVarsAux, RecGroup.substN, List.cons.injEq]
        exact ⟨ihbs hd List.mem_cons_self d m (hbs hd List.mem_cons_self),
          ih [] (fun e he => ihbs e (List.mem_cons_of_mem _ he))
              (fun e he => hbs e (List.mem_cons_of_mem _ he))⟩
      | cons a as =>
        simp only [RecGroup.openTyVarsAux, RecGroup.substN, List.cons.injEq]
        exact ⟨ihbs hd List.mem_cons_self (d + RecAnn.params a) m (hbs hd List.mem_cons_self),
          ih as (fun e he => ihbs e (List.mem_cons_of_mem _ he))
              (fun e he => hbs e (List.mem_cons_of_mem _ he))⟩

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

/-- Multi-binding substitution: substitute a block of values `vs` for a block of
    schemes `Ms`. The substituted-position `var` case type-betas via the new
    `HasScheme` (`v.instTy tyArgs` types at the instance); the annotated-`letIn`
    cofinite reconstruction uses `substN_openTyVarsAux_comm` (term substitution and
    scoped-variable opening commute, since `tyArgs` cover the values' scoped bvars).
    Strong induction on `Expr.size` (which `openTyVars` preserves) lets the `letIn`
    case recurse on the *opened* bound expression. -/
theorem TypeOfElabHM.subst_lemma_many
    {ctors : CtorEnv} {env Ms : Env} {vs : List Expr}
    (h_Ms_wf : ∀ M ∈ Ms, M.WF)
    (h_vs : List.Forall₂ (fun v M => HasScheme ⟨env, ctors⟩ v M) vs Ms) :
    ∀ (n : Nat) (e : Expr), e.size ≤ n → ∀ (env_post : Env) (τ : Ty),
      TypeOfElabHM ⟨env_post ++ Ms ++ env, ctors⟩ e τ →
      TypeOfElabHM ⟨env_post ++ env, ctors⟩ (e.substN env_post.length vs) τ := by
  have h_len : vs.length = Ms.length := h_vs.length_eq
  -- the substituted values' scoped bvars are bounded by their scheme arities
  have h_bound : ∀ (j : Nat) (w : Expr) (N : Nat),
      vs[j]? = some w → (Ms.map PolyTy.paramCount)[j]? = some N → Expr.TyBvarBounded N w := by
    intro j w N hw hN
    rw [List.getElem?_map] at hN
    obtain ⟨Mj, hMj, rfl⟩ := Option.map_eq_some_iff.mp hN
    obtain ⟨hlen', hrel⟩ := List.forall₂_iff_get.mp h_vs
    have hjv : j < vs.length := (List.getElem?_eq_some_iff.mp hw).1
    have hjM : j < Ms.length := (List.getElem?_eq_some_iff.mp hMj).1
    have hrelj := hrel j hjv hjM
    rw [List.getElem?_eq_getElem hjv, Option.some.injEq] at hw
    rw [List.getElem?_eq_getElem hjM, Option.some.injEq] at hMj
    subst hw; subst hMj
    exact HasScheme.tyBvarBounded hrelj
  intro n
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_le.mpr (Expr.size_pos e))
  | succ n ih =>
    intro e he env_post τ h_body
    cases h_body with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitChar  => exact .primLitChar
    | primBinOpIntAdd => exact .primBinOpIntAdd
    | primBinOpIntSub => exact .primBinOpIntSub
    | primBinOpIntLt htrue hfalse =>
      cases htrue with
      | ctor hlookT htyargsT hinstT =>
        cases hfalse with
        | ctor hlookF htyargsF hinstF =>
          exact .primBinOpIntLt (.ctor hlookT htyargsT hinstT) (.ctor hlookF htyargsF hinstF)
    | ctor hlook htyargs hinst => exact .ctor hlook htyargs hinst
    | app hf hi =>
      simp only [Expr.size] at he
      simp only [Expr.substN]
      exact .app (ih _ (by omega) _ _ hf) (ih _ (by omega) _ _ hi)
    | lambda hpc hann heq hbody =>
      subst heq
      simp only [Expr.size] at he
      simp only [Expr.substN]
      refine TypeOfElabHM.lambda hpc hann rfl ?_
      have := ih _ (by omega) (PolyTy.mkTrivial _ :: env_post) _ hbody
      simpa using this
    | @letIn ann _ boundExpr _ body bodyTy M' L hsch hann hcofin heq hbodyinner =>
      subst heq
      simp only [Expr.size] at he
      simp only [Expr.substN]
      refine TypeOfElabHM.letIn (M := M') (L := L) hsch hann (fun Xs hfresh => ?_) rfl ?_
      · have hbe := hcofin Xs hfresh
        expose_names
        cases ann with
        | none =>
          simp only [Expr.openBoundTyVars] at hbe ⊢
          exact ih _ (by omega) env_post _ hbe
        | some σ =>
          simp only [Expr.openBoundTyVars] at hbe ⊢
          have hopen_typed := ih _ (by rw [Expr.size_openTyVars]; omega) env_post _ hbe
          have hsa : (boundExpr.openTyVars Xs).SubstArgsGe (Ms.map PolyTy.paramCount)
              env_post.length := TypeOfElabHM.substArgsGe hbe env_post rfl
          have hsa' : boundExpr.SubstArgsGe (Ms.map PolyTy.paramCount) env_post.length :=
            Expr.SubstArgsGe_openTyVarsAux _ Xs _ 0 _ hsa
          have hcomm := Expr.substN_openTyVarsAux_comm (Ys := Xs)
            (by rw [List.length_map]; exact h_len) h_bound
            boundExpr 0 env_post.length hsa'
          simp only [Expr.openTyVars] at hopen_typed ⊢
          rw [hcomm] at hopen_typed
          exact hopen_typed
      · exact ih _ (by omega) (M' :: env_post) _ hbodyinner
    | @var dbl polyTy tyArgs ty _ h_lookup h_lc h_inst =>
      by_cases h_lt : dbl < env_post.length
      · have h_subst : (Expr.var dbl tyArgs).substN env_post.length vs = .var dbl tyArgs := by
          simp [Expr.substN, h_lt]
        rw [h_subst]
        refine .var ?_ h_lc h_inst
        show (env_post ++ env)[dbl]? = _
        rw [List.getElem?_append_left h_lt]
        rw [List.append_assoc, List.getElem?_append_left h_lt] at h_lookup
        exact h_lookup
      · push_neg at h_lt
        by_cases h_in : dbl - env_post.length < vs.length
        · -- inside the substituted block: type-beta `vs[dbl-k]` at `tyArgs`
          have hMlt : dbl - env_post.length < Ms.length := by omega
          have h_subst : (Expr.var dbl tyArgs).substN env_post.length vs
              = (vs[dbl - env_post.length].instTy tyArgs).shiftFrom 0 env_post.length := by
            simp only [Expr.substN]
            rw [if_neg (by omega), dif_pos h_in]
          rw [h_subst]
          rw [List.append_assoc, List.getElem?_append_right h_lt,
              List.getElem?_append_left hMlt, List.getElem?_eq_getElem hMlt,
              Option.some.injEq] at h_lookup
          subst h_lookup
          have hMwf : Ms[dbl - env_post.length].WF := h_Ms_wf _ (List.getElem_mem hMlt)
          have hhs : HasScheme ⟨env, ctors⟩ vs[dbl - env_post.length]
              Ms[dbl - env_post.length] := (List.forall₂_iff_get.mp h_vs).2 _ h_in hMlt
          have hτ : τ = Ms[dbl - env_post.length].openWith tyArgs := by
            have := InstantiatesBy.eq_openWith h_inst hMwf h_lc.1
            simpa [PolyTy.openWith] using this
          have hv_typed : TypeOfElabHM ⟨env, ctors⟩
              (vs[dbl - env_post.length].instTy tyArgs) τ := by
            rw [hτ]; exact hhs tyArgs h_lc
          exact TypeOfElabHM.weaken_env (env_pre := []) (env_extra := env_post) hv_typed
        · -- above the block: shift down by `vs.length`
          push_neg at h_in
          have h_subst : (Expr.var dbl tyArgs).substN env_post.length vs
              = .var (dbl - vs.length) tyArgs := by
            simp only [Expr.substN]
            rw [if_neg (by omega), dif_neg (by omega)]
          rw [h_subst]
          refine .var ?_ h_lc h_inst
          rw [List.getElem?_append_right (by omega : env_post.length ≤ dbl - vs.length)]
          rw [List.append_assoc, List.getElem?_append_right h_lt,
              List.getElem?_append_right (by omega : Ms.length ≤ dbl - env_post.length)]
            at h_lookup
          rw [show (dbl - vs.length) - env_post.length
                = (dbl - env_post.length) - Ms.length by omega]
          exact h_lookup
    | match_ h_scrut h_ne h_brs =>
      expose_names
      simp only [Expr.size] at he
      simp only [Expr.substN]
      refine TypeOfElabHM.match_ (ih _ (by omega) _ _ h_scrut) ?_ ?_
      · intro hcontra
        obtain ⟨⟨p, b⟩, rest, hb⟩ := List.exists_cons_of_ne_nil h_ne
        rw [hb] at hcontra
        simp [BranchList.substN] at hcontra
      · intro branch' hmem'
        obtain ⟨pat, body, hmem, rfl⟩ := BranchList.mem_substN hmem'
        have hbsize : body.size ≤ n :=
          le_trans (Expr.size_le_of_mem_branches hmem) (by omega)
        cases pat with
        | named c m =>
          simp only [MatchPattern.bindCount]
          cases h_brs (.named c m, body) hmem with
          | mk hspec h_ctx h_bodyT =>
            subst h_ctx
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ Ms ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ Ms ++ env
                  by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
              at h_bodyT
            have ih_b := ih body hbsize (instContents.map PolyTy.mkTrivial ++ env_post) _ h_bodyT
            simp only [List.length_append, List.length_map] at ih_b
            rw [← hspec.fields.length_eq, ← hspec.bind_count] at ih_b
            rw [show m + env_post.length = env_post.length + m from Nat.add_comm _ _] at ih_b
            refine TypeOfElabMatchBranch.mk
              ⟨hspec.lookup, hspec.scrut_eq, hspec.arity, hspec.bind_count, hspec.fields⟩ rfl ?_
            rw [List.append_assoc] at ih_b
            exact ih_b
        | wildcard =>
          simp only [MatchPattern.bindCount, Nat.add_zero]
          cases h_brs (.wildcard, body) hmem with
          | wildcard h_bodyT =>
            exact TypeOfElabMatchBranch.wildcard (ih body hbsize env_post _ h_bodyT)
    | letRec hwf hmonoP hpolyP heq hbodyT =>
      subst heq
      expose_names
      simp only [Expr.size] at he
      simp only [Expr.substN, RecGroup.substN_eq_map]
      refine TypeOfElabHM.letRec (specs := specs) (G := G) (L := L)
        ⟨hwf.anns_eq, ?_, hwf.nodup, hwf.mono_lc, hwf.poly_wf⟩ ?_ ?_ rfl ?_
      · rw [List.length_map]; exact hwf.length
      · -- UNANNOTATED members: typed as stored (the historical `letRec` shape)
        intro Xs hfresh p hp τ' hτ'
        obtain ⟨a, b, hmemBind, hq, rfl⟩ := List.mem_zip_map_left hp
        have hbT := hmonoP Xs hfresh (a, b) hq τ' hτ'
        simp only [RecSpecs.rhsCtx] at hbT
        rw [← List.append_assoc, ← List.append_assoc] at hbT
        have hasize : a.size ≤ n :=
          le_trans (Expr.size_le_of_mem_recGroup hmemBind) (by omega)
        have ihb := ih a hasize _ _ hbT
        rw [List.append_assoc] at ihb
        simp only [List.length_append, List.length_map] at ihb
        rw [← hwf.length, Nat.add_comm bindings.length env_post.length] at ihb
        exact ihb
      · -- ANNOTATED members: opened at own skolems (the historical `letRecAnn`
        -- shape, with the `substN`/`openTyVars` commutation)
        intro Xs hfresh p hp σ hσ Ys hYs
        obtain ⟨a, b, hmemBind, hq, rfl⟩ := List.mem_zip_map_left hp
        have hbT := hpolyP Xs hfresh (a, b) hq σ hσ Ys hYs
        simp only [RecSpecs.rhsCtx] at hbT
        rw [← List.append_assoc, ← List.append_assoc] at hbT
        have hasize : (a.openTyVars Ys).size ≤ n := by
          rw [Expr.size_openTyVars]
          exact le_trans (Expr.size_le_of_mem_recGroup hmemBind) (by omega)
        have hopen := ih (a.openTyVars Ys) hasize _ _ hbT
        have hsa : (a.openTyVars Ys).SubstArgsGe (Ms.map PolyTy.paramCount)
            (specs.map (RecSpec.rhsEntry G Xs) ++ env_post).length :=
          TypeOfElabHM.substArgsGe hbT (specs.map (RecSpec.rhsEntry G Xs) ++ env_post) rfl
        have hsa' : a.SubstArgsGe (Ms.map PolyTy.paramCount)
            (specs.map (RecSpec.rhsEntry G Xs) ++ env_post).length :=
          Expr.SubstArgsGe_openTyVarsAux _ Ys _ 0 _ hsa
        have hcomm := Expr.substN_openTyVarsAux_comm (Ys := Ys)
          (by rw [List.length_map]; exact h_len) h_bound a 0
          (specs.map (RecSpec.rhsEntry G Xs) ++ env_post).length hsa'
        simp only [Expr.openTyVars] at hopen ⊢
        rw [hcomm] at hopen
        rw [List.append_assoc] at hopen
        simp only [List.length_append, List.length_map] at hopen
        rw [← hwf.length, Nat.add_comm bindings.length env_post.length] at hopen
        exact hopen
      · simp only [RecSpecs.bodyCtx] at hbodyT
        rw [← List.append_assoc, ← List.append_assoc] at hbodyT
        have ihb := ih body (by omega) _ _ hbodyT
        rw [List.append_assoc] at ihb
        simp only [List.length_append, List.length_map] at ihb
        rw [← hwf.length, Nat.add_comm bindings.length env_post.length] at ihb
        exact ihb

/-- Single-value substitution (`beta`/`letReduce`): the `Ms = [M]`, `vs = [v]`
    instance of `subst_lemma_many`. -/
theorem TypeOfElabHM.subst_lemma
    {ctors : CtorEnv} {env_post env : Env}
    {e : Expr} {τ : Ty} {M : PolyTy} {v : Expr}
    (h_M_wf : M.WF)
    (h_body : TypeOfElabHM ⟨env_post ++ [M] ++ env, ctors⟩ e τ)
    (h_v : HasScheme ⟨env, ctors⟩ v M) :
    TypeOfElabHM ⟨env_post ++ env, ctors⟩ (e.substN env_post.length [v]) τ :=
  TypeOfElabHM.subst_lemma_many (Ms := [M]) (vs := [v])
    (by intro M' hM'; rw [List.mem_singleton] at hM'; subst hM'; exact h_M_wf)
    (List.Forall₂.cons h_v List.Forall₂.nil) e.size e (Nat.le_refl _) env_post τ h_body



/-! ## Canonical forms

Inversion lemmas: a *value* of a given type has a particular syntactic shape.
Used by progress to conclude the next step exists when a value sits in a given
type position. These only invert the value constructors (`lambda`/`pair`/
`ctor`/ctor-chains), so they're unaffected by the cofinite `let` rules. -/

/-- A well-typed constructor chain has a `wrapArrows … (customTy …)` type:
    a prefix of arrows ending in a `customTy`.

    Inducts syntactically on `e` (rather than on `h_chain`) because `IsCtorChain`
    is mutually defined with `IsValue`, so the `induction` tactic refuses it. -/
private lemma TypeOfElabHM.ctor_chain_has_customTy_form
    {ctx e τ}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : TypeOfElabHM ctx e τ) :
    ∃ name args tys, τ = Ty.wrapArrows (.customTy name args) tys := by
  induction e using Expr.rec_strong generalizing ctx τ with
  | ctor _ =>
    cases h_ty with
    | ctor _ _ h_inst =>
      have ⟨instArgs, instTys, h_eq⟩ :=
        InstantiatesBy.wrapArrows_customTy_form h_inst
      exact ⟨_, instArgs, instTys, h_eq⟩
  | app _ _ ihf _ =>
    cases h_chain with
    | app h_chain' _ =>
      cases h_ty with
      | app h_f_ty _ =>
        obtain ⟨name, args, tys, h_eq⟩ := ihf h_chain' h_f_ty
        cases tys with
        | nil => simp [Ty.wrapArrows] at h_eq
        | cons _ rest =>
          simp only [Ty.wrapArrows] at h_eq
          injection h_eq with _ h_ret
          exact ⟨name, args, rest, h_ret⟩
  | primLit _      => cases h_chain
  | primBinOp _    => cases h_chain
  | lambda _ _ _   => cases h_chain
  | letIn _ _ _ _ _ => cases h_chain
  | var _          => cases h_chain
  | match_ _ _ _ _ => cases h_chain
  | letRec _ _ _ _ _ => cases h_chain

theorem TypeOfElabHM.canonical_arrow {ctx e argTy retTy}
    (h_ty : TypeOfElabHM ctx e (.arrow argTy retTy))
    (h_val : SmallStep.IsValue e) :
    (∃ ann body, e = .lambda ann body) ∨ SmallStep.IsCtorChain e
    ∨ (∃ op, e = .primBinOp op) ∨ (∃ op v, e = .app (.primBinOp op) v) := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda ann body => exact .inl ⟨ann, body, rfl⟩
  | ctor name => exact .inr (.inl (.ctor name))
  | ctorApp h_chain h_v => exact .inr (.inl (.app h_chain h_v))
  -- a bare primop and a one-argument-short application are both arrow-typed values
  | primBinOp op => exact .inr (.inr (.inl ⟨op, rfl⟩))
  | primBinOpPartial hv => exact .inr (.inr (.inr ⟨_, _, rfl⟩))

theorem TypeOfElabHM.canonical_customTy {ctx e tyName tyArgs}
    (h_ty : TypeOfElabHM ctx e (.customTy tyName tyArgs))
    (h_val : SmallStep.IsValue e) :
    SmallStep.IsCtorChain e := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda _ _ => cases h_ty
  | ctor name => exact .ctor name
  | ctorApp h_chain h_v => exact .app h_chain h_v
  -- `primBinOp`/`primBinOpPartial` are arrow-typed, never `customTy` — the typing
  -- rule for `.primBinOp _` forces an arrow, contradicting `customTy`.
  | primBinOp op => cases h_ty
  | primBinOpPartial hv => cases h_ty with | app h_pbo _ => cases h_pbo

/-- Canonical forms at `int`: a value of type `int` is an integer literal. A
    lambda / bare primop / partial primop application is arrow-typed, and a
    constructor chain is `customTy`-headed, so none of them can inhabit `int`. -/
theorem TypeOfElabHM.canonical_int {ctx e}
    (h_ty : TypeOfElabHM ctx e (.prim .int))
    (h_val : SmallStep.IsValue e) :
    ∃ m : Int, e = .primLit (.int m) := by
  cases h_val with
  | primLit p => cases h_ty; exact ⟨_, rfl⟩
  | lambda _ _ => cases h_ty
  | ctor name =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      TypeOfElabHM.ctor_chain_has_customTy_form (.ctor name) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | ctorApp h_chain h_v =>
    obtain ⟨_, _, tys, h_eq⟩ :=
      TypeOfElabHM.ctor_chain_has_customTy_form (.app h_chain h_v) h_ty
    cases tys <;> simp [Ty.wrapArrows] at h_eq
  | primBinOp op => cases h_ty
  | primBinOpPartial hv => cases h_ty with | app h_pbo _ => cases h_pbo


/-! ## Constructor-chain typing inversion

The keystone for both progress (the matched-constructor's type name and arity)
and preservation's `match_` case (the applied arguments are well-typed at the
instantiated field types). Inducting over the chain, each `app` consumes one of
the constructor's `contents` (one arrow of its `wrapArrows` type). We track the
already-`consumed` fields and the `remaining` ones explicitly. -/

private theorem List.Forall₂.snoc {α β : Type _} {R : α → β → Prop}
    {l1 : List α} {l2 : List β} {a : α} {b : β}
    (h : List.Forall₂ R l1 l2) (hab : R a b) :
    List.Forall₂ R (l1 ++ [a]) (l2 ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hhd _ ih => exact .cons hhd ih

/-- A well-typed constructor chain decomposes into a head constructor applied to
    args, where the consumed fields are well-typed at their instantiations and
    the result type is the remaining fields wrapped over the (instantiated)
    `customTy`. -/
theorem TypeOfElabHM.ctor_chain_inversion {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : TypeOfElabHM ctx e τ) :
    ∃ (name : CtorName) (args : List Expr) (ctor : Ctor)
      (tyArgs consumed remaining : List Ty),
      SmallStep.CtorAppliedTo e name args ∧
      LookupList.get? ctx.ctors name = some ctor ∧
      (∀ t ∈ tyArgs, ContainsBvarsUpTo 0 t) ∧
      ctor.contents = consumed ++ remaining ∧
      List.Forall₂ (fun a c => ∃ ct, InstantiatesBy tyArgs c ct ∧ TypeOfElabHM ctx a ct)
        args consumed ∧
      InstantiatesBy tyArgs
        (Ty.wrapArrows (.customTy ctor.tyName (Ty.bvarRange ctor.paramCount)) remaining) τ := by
  induction e using Expr.rec_strong generalizing τ with
  | ctor name =>
    cases h_ty with
    | ctor hlook htyargs hinst =>
      exact ⟨name, [], _, _, [], _, .base name, hlook, htyargs, rfl, .nil,
        by simpa [Ctor.toTy] using hinst⟩
  | app f arg ihf _ =>
    cases h_chain with
    | app hchainf hvarg =>
      cases h_ty with
      | app hf harg =>
        obtain ⟨name, args, ctor, tyArgs, consumed, remaining, hcat, hlook, htyargs,
          hcontents, hforall, hinst_f⟩ := ihf hchainf hf
        cases remaining with
        | nil =>
          simp only [Ty.wrapArrows] at hinst_f
          cases hinst_f
        | cons c rest =>
          simp only [Ty.wrapArrows] at hinst_f
          cases hinst_f with
          | arrow hc hrest =>
            refine ⟨name, args ++ [arg], ctor, tyArgs, consumed ++ [c], rest,
              .step hcat, hlook, htyargs, ?_, hforall.snoc ⟨_, hc, harg⟩, hrest⟩
            rw [hcontents]
            exact (List.append_assoc consumed [c] rest).symm
  | primLit _ => cases h_chain
  | primBinOp _ => cases h_chain
  | lambda _ _ _ => cases h_chain
  | letIn _ _ _ _ _ => cases h_chain
  | var _ => cases h_chain
  | match_ _ _ _ _ => cases h_chain
  | letRec _ _ _ _ _ => cases h_chain


/-! ### Note: reflection layer removed

Under the call-by-name `let` semantics a `letIn` always steps (via `letReduce`),
so `progress`'s `letIn` case is trivial; the earlier operational-semantics ⋈
`openTyVars` reflection layer (reflecting opened⇒raw value-ness/step-existence) is
no longer needed and has been removed. -/

/-! ## Progress

A well-typed, closed term whose matches are all exhaustive is either a value or
can take a step. The interesting case is `match_`: the scrutinee value is a
constructor chain (`canonical_customTy` + `ctor_chain_inversion`), and the
strengthened `AllMatchesExhaustive.match_` guarantees that the head constructor's
type — which is pinned to the branches — has a covering branch.

Type-passing wrinkle: an annotated `let`/`letRecAnn` types its bound expressions
*opened*; we recover the raw bound expression's progress via the reflection
lemmas above. Strong induction on `Expr.size` (preserved by `openTyVars`) lets the
`letIn (some)` case recurse on the opened bound expression. -/

open SmallStep in
theorem TypeOfElabHM.progress {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_ty : TypeOfElabHM ctx e τ) (h_closed : ctx.env = [])
    (h_exh : AllMatchesExhaustive ctx.ctors e) :
    IsValue e ∨ ∃ e', Step e e' := by
  suffices H : ∀ (n : Nat) (e : Expr), e.size ≤ n → ∀ (ctx : Ctx) (τ : Ty),
      TypeOfElabHM ctx e τ → ctx.env = [] → AllMatchesExhaustive ctx.ctors e →
      IsValue e ∨ ∃ e', Step e e' by
    exact H e.size e (Nat.le_refl _) ctx τ h_ty h_closed h_exh
  intro n
  induction n with
  | zero => intro e he; exact absurd he (Nat.not_le.mpr (Expr.size_pos e))
  | succ n ih =>
    intro e hsize ctx τ h_ty h_closed h_exh
    cases h_ty with
    | primLitUnit => exact .inl (.primLit _)
    | primLitInt => exact .inl (.primLit _)
    | primLitNat => exact .inl (.primLit _)
    | primLitChar => exact .inl (.primLit _)
    | primBinOpIntAdd => exact .inl (.primBinOp _)
    | primBinOpIntSub => exact .inl (.primBinOp _)
    | primBinOpIntLt _ _ => exact .inl (.primBinOp _)
    | ctor _ _ _ => exact .inl (.ctor _)
    | lambda _ _ _ _ => exact .inl (.lambda _ _)
    | var h_lookup _ _ => rw [h_closed] at h_lookup; simp at h_lookup
    | @app _ f _ _ arg h_f h_arg =>
      cases h_exh with
      | app h_exh_f h_exh_arg =>
        simp only [Expr.size] at hsize
        rcases ih f (by omega) ctx _ h_f h_closed h_exh_f with hvf | ⟨f', hf⟩
        · rcases ih arg (by omega) ctx _ h_arg h_closed h_exh_arg with hva | ⟨arg', harg⟩
          · rcases TypeOfElabHM.canonical_arrow h_f hvf with
                ⟨ann, body, rfl⟩ | hchain | ⟨op, rfl⟩ | ⟨op, v, rfl⟩
            · exact .inr ⟨_, .beta hva⟩
            · exact .inl (.ctorApp hchain hva)
            · -- `f` is a bare primop; applying one value leaves it one arg short → a value
              exact .inl (.primBinOpPartial hva)
            · -- `f` is a partial primop; this application saturates it → δ-step.
              -- Both operands are values of type `int`, hence literals (canonical_int).
              cases hvf with
              | ctorApp hchain _ => nomatch hchain
              | primBinOpPartial hv =>
                cases h_f with
                | app h_pbo h_v =>
                  cases h_pbo with
                  | primBinOpIntAdd =>
                    obtain ⟨m, rfl⟩ := TypeOfElabHM.canonical_int h_v hv
                    obtain ⟨n, rfl⟩ := TypeOfElabHM.canonical_int h_arg hva
                    exact .inr ⟨_, .deltaIntAdd⟩
                  | primBinOpIntSub =>
                    obtain ⟨m, rfl⟩ := TypeOfElabHM.canonical_int h_v hv
                    obtain ⟨n, rfl⟩ := TypeOfElabHM.canonical_int h_arg hva
                    exact .inr ⟨_, .deltaIntSub⟩
                  | primBinOpIntLt _ _ =>
                    obtain ⟨m, rfl⟩ := TypeOfElabHM.canonical_int h_v hv
                    obtain ⟨n, rfl⟩ := TypeOfElabHM.canonical_int h_arg hva
                    exact .inr ⟨_, .deltaIntLt⟩
          · exact .inr ⟨_, .appArg hvf harg⟩
        · exact .inr ⟨_, .appFn hf⟩
    | letIn _ _ _ _ _ =>
      -- call-by-name: a `let` always steps via `letReduce` (no rhs reduction).
      exact .inr ⟨_, .letReduce⟩
    | @match_ _ scrut scrutTy branches resultTy h_scrut h_ne h_brs =>
      cases h_exh with
      | match_ h_exh_scrut _ h_branch_ty h_match_exh =>
        simp only [Expr.size] at hsize
        rcases ih scrut (by omega) ctx _ h_scrut h_closed h_exh_scrut with hvs | ⟨scrut', hscrut⟩
        · obtain ⟨⟨pat0, body0⟩, rest0, hbeq⟩ := List.exists_cons_of_ne_nil h_ne
          have hb0 : (pat0, body0) ∈ branches := by rw [hbeq]; exact List.mem_cons_self
          by_cases hchain : IsCtorChain scrut
          · obtain ⟨name, args, hcat⟩ := CtorAppliedTo_of_IsCtorChain hchain
            have hcover : ∃ pat body, (pat, body) ∈ branches ∧
                pat.matchesCtor name args.length = true := by
              cases pat0 with
              | wildcard => exact ⟨.wildcard, body0, hb0, rfl⟩
              | named c0 n0 =>
                cases h_brs (.named c0 n0, body0) hb0 with
                | mk hspec0 _ _ =>
                  obtain ⟨name', args', ctor, tyArgs', consumed, remaining,
                    hcat', hlook, _, hcontents, hforall, hinst⟩ :=
                    TypeOfElabHM.ctor_chain_inversion hchain h_scrut
                  obtain ⟨rfl, rfl⟩ : name = name' ∧ args = args' := by
                    have h1 := getCtorArgs_of_CtorAppliedTo hcat
                    have h2 := getCtorArgs_of_CtorAppliedTo hcat'
                    rw [h1, Option.some.injEq, Prod.mk.injEq] at h2; exact h2
                  cases remaining with
                  | cons d rest =>
                    simp only [Ty.wrapArrows] at hinst
                    rw [hspec0.scrut_eq] at hinst; cases hinst
                  | nil =>
                    simp only [Ty.wrapArrows] at hinst
                    rw [List.append_nil] at hcontents
                    have hlen : args.length = ctor.contents.length := by
                      rw [hcontents]; exact hforall.length_eq
                    obtain ⟨ctorB, hlookB, htyB⟩ := h_branch_ty c0 n0 body0 hb0
                    cases hinst with
                    | customTy _ =>
                      obtain ⟨pat, body, hmem, hcov⟩ := h_match_exh name ctor hlook (by
                        injection hspec0.scrut_eq with hn _
                        rw [hn, Option.some.inj (hspec0.lookup.symm.trans hlookB)]; exact htyB)
                      exact ⟨pat, body, hmem, by rw [hlen]; exact hcov⟩
            obtain ⟨pat, body, hmem, hcov⟩ := hcover
            obtain ⟨e', hfmb⟩ := findMatchingBranch_of_exists ⟨pat, body, hmem, hcov⟩
            obtain ⟨pat', body', hfirst, _⟩ := findMatchingBranch_to_FirstMatch hfmb
            exact .inr ⟨_, .matchReduce hvs hcat hfirst⟩
          · have hwild : pat0 = .wildcard := by
              cases pat0 with
              | wildcard => rfl
              | named c0 n0 =>
                cases h_brs (.named c0 n0, body0) hb0 with
                | mk hspecA _ _ =>
                  exact absurd (TypeOfElabHM.canonical_customTy (hspecA.scrut_eq ▸ h_scrut) hvs) hchain
            subst hwild
            rw [hbeq]
            exact .inr ⟨body0, .matchWildReduce hvs hchain⟩
        · exact .inr ⟨_, .matchScrut hscrut⟩
    | letRec _ _ _ _ _ => exact .inr ⟨_, .letRecUnfold⟩


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

/-- Assemble the per-argument `HasScheme` list for the `match` reduction: each
    matched argument is well-typed at the corresponding instantiated field type
    (the two instantiations coincide by `det_agree`), so it has the trivial
    scheme of that type. -/
private theorem InstantiatesBy.build_match_vs
    {ctx : Ctx} {n : Nat} {tyArgs tyArgsS : List Ty}
    (hag : ∀ k, k < n → tyArgs[k]? = tyArgsS[k]?) :
    ∀ {contents instContents : List Ty} {args : List Expr},
      (∀ c ∈ contents, ContainsBvarsUpTo n c) →
      List.Forall₂ (InstantiatesBy tyArgs) contents instContents →
      List.Forall₂ (fun a c => ∃ ct, InstantiatesBy tyArgsS c ct ∧ TypeOfElabHM ctx a ct)
        args contents →
      List.Forall₂ (fun v M => HasScheme ctx v M) args (instContents.map PolyTy.mkTrivial) := by
  intro contents
  induction contents with
  | nil =>
    intro instContents args _ hinst hfor
    cases hinst
    cases hfor
    exact .nil
  | cons hd tl ih =>
    intro instContents args hbound hinst hfor
    cases hinst with
    | cons hihd hitl =>
      cases hfor with
      | cons hfhd hftl =>
        obtain ⟨ct, hctS, htyA⟩ := hfhd
        have hdet := InstantiatesBy.det_agree hag (hbound hd List.mem_cons_self) hihd hctS
        refine List.Forall₂.cons ?_
          (ih (fun c hc => hbound c (List.mem_cons_of_mem _ hc)) hitl hftl)
        rw [hdet]
        exact HasScheme.ofTypeOfElabHM htyA

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
  | var i tyArgs =>
    intro d h
    simp only [Expr.openTyVarsAux, Expr.TyBvarBounded] at h ⊢
    rw [Expr.var.injEq]
    refine ⟨rfl, ?_⟩
    conv_rhs => rw [← List.map_id tyArgs]
    exact List.map_congr_left (fun t ht => Ty.openVarsFrom_eq_self_of_bvars (h t ht))
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

/-- Type-beta is a no-op on a term whose annotation `bvar`s are all `< d`. Used to
    show a re-wrapped (type-`bvar`-closed) `letRec`/`letRecAnn` value is unchanged by
    the `instTy` in the new `HasScheme`. -/
theorem Expr.instTyAux_eq_self_of_tyBvarBounded (Ts : List Ty) :
    ∀ (e : Expr) (d : Nat), e.TyBvarBounded d → e.instTyAux d Ts = e := by
  intro e
  induction e using Expr.rec_strong with
  | primLit p => intro d _; rfl
  | primBinOp op => intro d _; rfl
  | ctor nm => intro d _; rfl
  | var i tyArgs =>
    intro d h
    simp only [Expr.instTyAux, Expr.TyBvarBounded] at h ⊢
    rw [Expr.var.injEq]
    refine ⟨rfl, ?_⟩
    conv_rhs => rw [← List.map_id tyArgs]
    exact List.map_congr_left (fun t ht => Ty.openTyFrom_eq_self_of_bvars (h t ht))
  | lambda ann body ih =>
    intro d h
    simp only [Expr.instTyAux, Expr.TyBvarBounded] at h ⊢
    obtain ⟨hann, hbody⟩ := h
    rw [ih d hbody, Expr.lambda.injEq]
    refine ⟨?_, rfl⟩
    cases ann with
    | none => rfl
    | some t =>
      simp only [Option.map_some, Option.some.injEq]
      exact Ty.openTyFrom_eq_self_of_bvars (hann t rfl)
  | app f arg ihf iharg =>
    intro d h
    simp only [Expr.instTyAux, Expr.TyBvarBounded] at h ⊢
    obtain ⟨hf, ha⟩ := h
    rw [ihf d hf, iharg d ha]
  | letIn ann rhs body ihr ihb =>
    intro d h
    cases ann with
    | none =>
      simp only [Expr.instTyAux, Expr.TyBvarBounded] at h ⊢
      obtain ⟨hr, hb⟩ := h
      rw [ihr d hr, ihb d hb]
    | some σ =>
      simp only [Expr.instTyAux, Expr.TyBvarBounded] at h ⊢
      obtain ⟨hσ, hr, hb⟩ := h
      rw [ihr (d + σ.paramCount) hr, ihb d hb, Ty.openTyFrom_eq_self_of_bvars hσ]
  | match_ scrut branches ihs ihbs =>
    intro d h
    simp only [Expr.instTyAux, Expr.TyBvarBounded, BranchList.instTyAux_eq_map] at h ⊢
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
    simp only [Expr.instTyAux, Expr.TyBvarBounded] at h ⊢
    obtain ⟨hsc, hbs, hb⟩ := h
    rw [ihb d hb, Expr.letRec.injEq]
    refine ⟨RecGroup.instAnns_eq_self_of_bvars hsc, ?_, rfl⟩
    clear hsc hb ihb
    revert ihbs hbs
    induction bindings generalizing anns with
    | nil => intro _ _; cases anns <;> rfl
    | cons hd tl ih =>
      intro ihbs hbs
      cases anns with
      | nil =>
        simp only [RecGroup.instTyAux, Expr.TyBvarBounded.RecGroup,
          List.cons.injEq] at hbs ⊢
        exact ⟨ihbs hd List.mem_cons_self d hbs.1,
          ih [] (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2⟩
      | cons a as =>
        simp only [RecGroup.instTyAux, Expr.TyBvarBounded.RecGroup,
          List.cons.injEq] at hbs ⊢
        exact ⟨ihbs hd List.mem_cons_self (d + RecAnn.params a) hbs.1,
          ih as (fun e he => ihbs e (List.mem_cons_of_mem _ he)) hbs.2⟩

theorem Expr.instTy_eq_self_of_tyBvarBounded {e : Expr} {Ts : List Ty}
    (h : e.TyBvarBounded 0) : e.instTy Ts = e :=
  Expr.instTyAux_eq_self_of_tyBvarBounded Ts e 0 h

/-! ### `letRec` preservation helpers.

Discharging the `letRecUnfold` reduct `body.substN 0 (bindings.map (letRec bindings ·))`
needs: each re-wrapped `letRec bindings eⱼ` has scheme `Mⱼ` (`HasScheme`), then
`subst_lemma_many` substitutes them for the generalised block `Ms` in the body. The
`HasScheme` is built by the **mono-group trick**: re-apply `TypeOfElabHM.letRec` with the
group bound at its *monomorphic opening* `(openGroup Ms Xs).map mkTrivial` (so the
cofinite premise `hcofin` supplies the body directly), then `typ_subst` the opening's
fresh slice to an arbitrary instance — exactly `HasScheme.fromHasSchemeVars`'s argument. -/

/-- Opening a scheme body whose `bvar`s are all `< Xs.length` is locally closed
    (every bound variable gets replaced by a fresh `fvar`). -/
theorem Ty.openVars_lc {ty : Ty} {Xs : List Nat}
    (h : ContainsBvarsUpTo Xs.length ty) : ContainsBvarsUpTo 0 (Ty.openVars Xs ty) := by
  unfold Ty.openVars
  induction ty using Ty.rec_strong with
  | prim _ => exact .prim
  | arrow a b iha ihb => cases h with | arrow ha hb => exact .arrow (iha ha) (ihb hb)
  | bvar i =>
    cases h with
    | bvar hlt =>
      simp only [Ty.instantiate]
      rw [List.getElem?_eq_getElem hlt]
      exact .fvar
  | fvar n => exact .fvar
  | customTy nm tys ih =>
    cases h with
    | customTy hall =>
      simp only [Ty.instantiate]
      apply ContainsBvarsUpTo.customTy
      rw [TyList.instantiate_eq_map]
      intro t ht
      obtain ⟨t0, ht0, rfl⟩ := List.mem_map.mp ht
      exact ih t0 ht0 (hall t0 ht0)

/-- Opening with no names is the identity. -/
theorem Ty.openVars_nil (ty : Ty) : Ty.openVars [] ty = ty := by
  unfold Ty.openVars
  have heq : (fun i => (([] : List Nat)[i]?).elim (Ty.bvar i) Ty.fvar) = (fun i => Ty.bvar i) := by
    funext i; simp
  rw [heq]; exact Ty.instantiate_bvar_id

/-- Every type in a group's opening is locally closed, provided all schemes are
    well-formed and `Xs` is long enough to open every slice fully. -/
theorem PolyTy.openGroup_lc {Ms : List PolyTy} :
    ∀ {Xs : List Nat}, (∀ M ∈ Ms, M.WF) → PolyTy.totalParams Ms ≤ Xs.length →
      ∀ t ∈ PolyTy.openGroup Ms Xs, ContainsBvarsUpTo 0 t := by
  induction Ms with
  | nil => intro Xs _ _ t ht; simp [PolyTy.openGroup] at ht
  | cons M Ms ih =>
    intro Xs hwf hlen t ht
    have htp : PolyTy.totalParams (M :: Ms) = M.paramCount + PolyTy.totalParams Ms := by
      simp [PolyTy.totalParams]
    simp only [PolyTy.openGroup, List.mem_cons] at ht
    cases ht with
    | inl heq =>
      subst heq
      have hlentake : (Xs.take M.paramCount).length = M.paramCount := by
        rw [List.length_take]; omega
      have hbv : ContainsBvarsUpTo (Xs.take M.paramCount).length M.body := by
        rw [hlentake]; exact hwf M List.mem_cons_self
      exact Ty.openVars_lc hbv
    | inr ht' =>
      refine ih (fun M' hM' => hwf M' (List.mem_cons_of_mem _ hM')) ?_ t ht'
      rw [List.length_drop]; omega

/-- The total parameter count of a block of trivial (monomorphic) schemes is 0. -/
theorem PolyTy.totalParams_map_mkTrivial (ts : List Ty) :
    PolyTy.totalParams (ts.map PolyTy.mkTrivial) = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simpa [PolyTy.totalParams, PolyTy.mkTrivial] using ih

/-- Opening a block of trivial schemes at the empty name list recovers the
    underlying monotypes. -/
theorem PolyTy.openGroup_mkTrivial_nil (ts : List Ty) :
    PolyTy.openGroup (ts.map PolyTy.mkTrivial) [] = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, PolyTy.openGroup, List.take_nil, List.drop_nil]
    rw [ih]
    congr 1
    exact Ty.openVars_nil t

/-- A pair from `bindings.zip Ms` corresponds (at the same position) to a pair of
    the binding with its opening `(openGroup Ms Xs)`, whose type is `M.openVars Ys`
    for a length-`paramCount` sublist `Ys` of `Xs`. -/
theorem PolyTy.mem_zip_openGroup {bindings : List Expr} {e : Expr} {M : PolyTy} :
    ∀ {Ms : List PolyTy}, (e, M) ∈ bindings.zip Ms → bindings.length = Ms.length →
      ∀ {Xs : List Nat}, PolyTy.totalParams Ms ≤ Xs.length →
        ∃ Ys, Ys.length = M.paramCount ∧ Ys.Sublist Xs ∧
          (e, M.openVars Ys) ∈ bindings.zip (PolyTy.openGroup Ms Xs) := by
  induction bindings with
  | nil => intro Ms hmem _ Xs _; simp at hmem
  | cons b bs ih =>
    intro Ms hmem hlen Xs hXs
    cases Ms with
    | nil => simp at hmem
    | cons M0 Ms' =>
      have htp : PolyTy.totalParams (M0 :: Ms') = M0.paramCount + PolyTy.totalParams Ms' := by
        simp [PolyTy.totalParams]
      simp only [List.zip_cons_cons, List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
        rw [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        refine ⟨Xs.take M.paramCount, ?_, List.take_sublist _ _, ?_⟩
        · rw [List.length_take]; omega
        · simp only [PolyTy.openGroup, List.zip_cons_cons]
          exact List.mem_cons_self
      | inr hmem' =>
        have hlen' : bs.length = Ms'.length := by simpa using hlen
        obtain ⟨Ys, hYslen, hYsub, hzip⟩ :=
          ih hmem' hlen' (Xs := Xs.drop M0.paramCount) (by rw [List.length_drop]; omega)
        refine ⟨Ys, hYslen, hYsub.trans (List.drop_sublist _ _), ?_⟩
        simp only [PolyTy.openGroup, List.zip_cons_cons]
        exact List.mem_cons_of_mem _ hzip

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

/-- `openAt` transports the stored annotations pointwise-identically. -/
private theorem RecSpec.map_ann_openAt (G Xs : List Nat) (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map RecSpec.ann = specs.map RecSpec.ann := by
  rw [List.map_map]
  apply List.map_congr_left
  intro s _
  cases s <;> rfl

/-- Renaming the empty pool at ANY names is the identity (`[].zip Zs = []`). -/
private theorem Ty.renameG_nil_left {Zs : List Nat} {τ : Ty} : Ty.renameG [] Zs τ = τ := rfl

/-- The transported specs' empty-pool RHS entries are the original specs'
    pool-opened RHS entries. -/
private theorem RecSpec.map_rhsEntry_openAt (G Xs Zs : List Nat) (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map (RecSpec.rhsEntry [] Zs)
      = specs.map (RecSpec.rhsEntry G Xs) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro s _
  cases s with
  | mono τ =>
    show PolyTy.mkTrivial (Ty.renameG [] Zs (Ty.renameG G Xs τ)) = _
    rw [Ty.renameG_nil_left]
    rfl
  | poly σ => rfl

/-- The transported specs' empty-pool BODY schemes are ALSO the original specs'
    pool-opened RHS entries (`genGroup [] = mkTrivial`) — the crux of the
    mono-group trick: body env = RHS env after transport. -/
private theorem RecSpec.map_bodyScheme_openAt (G Xs : List Nat) (specs : List RecSpec) :
    (specs.map (RecSpec.openAt G Xs)).map (RecSpec.bodyScheme [])
      = specs.map (RecSpec.rhsEntry G Xs) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro s _
  cases s with
  | mono τ =>
    show PolyTy.genGroup [] (Ty.renameG G Xs τ) = PolyTy.mkTrivial (Ty.renameG G Xs τ)
    exact PolyTy.genGroup_nil
  | poly σ => rfl

/-- **The fused mono-group trick.** Re-derive `letRec anns bindings e` (any body
    `e` typed in the RHS env at the pool opening `G ↦ Xs`) by re-applying the
    fused rule with the transported specs `specs.map (openAt G Xs)` at the EMPTY
    pool: the transported body env coincides with the original RHS env
    (`map_bodyScheme_openAt`), so the rule's own premises supply everything. -/
theorem TypeOfElabHM.rec_rewrap_typed
    {ctors : CtorEnv} {env : Env} {anns : List (Option PolyTy)} {bindings : List Expr}
    {specs : List RecSpec} {G L : List Nat}
    (hwf : RecSpecs.WF anns bindings specs G)
    (hmono : RecSpecs.MonoTyped TypeOfElabHM ⟨env, ctors⟩ bindings specs G L)
    (hpoly : RecSpecs.PolyTyped TypeOfElabHM ⟨env, ctors⟩ bindings specs G L)
    {Xs : List Nat} (hXs : FreshNames L G.length Xs)
    {e : Expr} {t : Ty}
    (hbody : TypeOfElabHM (RecSpecs.rhsCtx ⟨env, ctors⟩ specs G Xs) e t) :
    TypeOfElabHM ⟨env, ctors⟩ (.letRec anns bindings e) t := by
  refine TypeOfElabHM.letRec
    (specs := specs.map (RecSpec.openAt G Xs)) (G := []) (L := L ++ Xs)
    (bodyCtx := ⟨specs.map (RecSpec.rhsEntry G Xs) ++ env, ctors⟩)
    ⟨by rw [RecSpec.map_ann_openAt]; exact hwf.anns_eq,
     by rw [List.length_map]; exact hwf.length,
     List.nodup_nil, ?_, ?_⟩
    ?_ ?_
    (by simp only [RecSpecs.bodyCtx]; rw [RecSpec.map_bodyScheme_openAt]) hbody
  · -- transported monotypes are LC
    intro τ' hτ'
    obtain ⟨s, hs, hsubst⟩ := List.mem_map.mp hτ'
    cases s with
    | mono τ =>
      injection hsubst with hττ
      rw [← hττ]
      exact Ty.renameG_isLC (hwf.mono_lc τ hs)
    | poly σ => exact RecSpec.noConfusion hsubst
  · -- transported schemes are WF (openAt preserves poly specs)
    intro σ' hσ'
    obtain ⟨s, hs, hsubst⟩ := List.mem_map.mp hσ'
    cases s with
    | mono τ => exact RecSpec.noConfusion hsubst
    | poly σ =>
      injection hsubst with hσσ
      rw [← hσσ]
      exact hwf.poly_wf σ hs
  · -- mono premise at the empty pool: identical opening, RHS env transported
    intro Zs _hZs p hp τ' hτ'
    simp only [RecSpecs.rhsCtx]
    obtain ⟨a, b, hab, rfl⟩ := List.mem_zip_map_right_ex hp
    cases b with
    | poly σ => exact RecSpec.noConfusion hτ'
    | mono τ =>
      injection hτ' with hττ
      rw [← hττ, Ty.renameG_nil_left, RecSpec.map_rhsEntry_openAt]
      exact hmono Xs hXs (a, .mono τ) hab τ rfl
  · -- poly premise at the empty pool: skolems dodge `L ++ Xs` by construction
    intro Zs _hZs p hp σ hσ Ys hYs
    simp only [RecSpecs.rhsCtx]
    obtain ⟨a, b, hab, rfl⟩ := List.mem_zip_map_right_ex hp
    cases b with
    | mono τ => exact RecSpec.noConfusion hσ
    | poly σ' =>
      injection hσ with hσσ
      rw [← hσσ, RecSpec.map_rhsEntry_openAt]
      refine hpoly Xs hXs (a, .poly σ') hab σ' rfl Ys
        ⟨by rw [hYs.length, hσσ], hYs.nodup,
         fun y hy hc => hYs.avoid y hy (List.mem_append_left _ hc)⟩

/-- Each re-wrapped UNANNOTATED member `letRec anns bindings e` has its
    generalised scheme `genGroup G τ`. `rec_rewrap_typed` gives it at a fresh
    pool opening `G ↦ Ws`; then `typ_substs` (à la `HasScheme.fromHasSchemeVars`)
    lifts the fresh opening slice to an arbitrary instance. -/
theorem TypeOfElabHM.rewrap_hasScheme_mono
    {ctors : CtorEnv} {env : Env} {anns : List (Option PolyTy)} {bindings : List Expr}
    {specs : List RecSpec} {G L : List Nat}
    (hwf : RecSpecs.WF anns bindings specs G)
    (hmono : RecSpecs.MonoTyped TypeOfElabHM ⟨env, ctors⟩ bindings specs G L)
    (hpoly : RecSpecs.PolyTyped TypeOfElabHM ⟨env, ctors⟩ bindings specs G L)
    {e : Expr} {τ : Ty} (hmem : (e, RecSpec.mono τ) ∈ bindings.zip specs) :
    HasScheme ⟨env, ctors⟩ (.letRec anns bindings e) (PolyTy.genGroup G τ) := by
  intro Vs hVs
  obtain ⟨hVlen, hVlc⟩ := hVs
  have hτlc : τ.IsLC := hwf.mono_lc τ (List.of_mem_zip hmem).2
  obtain ⟨Ws, hWlen, hWnodup, hWavoid⟩ :=
    exists_fresh_names
      (L ++ G ++ env.freeVars ++ (PolyTy.genGroup G τ).body.freeVars
        ++ Ty.freeVarsList Vs ++ (Expr.letRec anns bindings e).tyFreeVars ++ τ.freeVars) G.length
  have hWfresh : FreshNames L G.length Ws :=
    ⟨hWlen, hWnodup, fun w hw hc => hWavoid w hw (by simp only [List.mem_append]; tauto)⟩
  have hWG : ∀ w ∈ Ws, w ∉ G := fun w hw hc =>
    hWavoid w hw (by simp only [List.mem_append]; tauto)
  have hdisj : ∀ g ∈ G, g ∉ Ws := fun g hg hc => hWG g hc hg
  have hWτ : ∀ w ∈ Ws, w ∉ τ.freeVars := fun w hw hc =>
    hWavoid w hw (by simp only [List.mem_append]; tauto)
  have h1 : TypeOfElabHM ⟨env, ctors⟩ (.letRec anns bindings e) (Ty.renameG G Ws τ) :=
    TypeOfElabHM.rec_rewrap_typed hwf hmono hpoly hWfresh
      (hmono Ws hWfresh (e, .mono τ) hmem τ rfl)
  have ha : Ty.renameG G Ws τ
      = Ty.renameG (Ty.genFilter G τ) (Ty.genFilter Ws (Ty.renameG G Ws τ)) τ :=
    Ty.renameG_eq_genFilter hWlen hwf.nodup hWnodup hdisj hWτ
  have hgg : PolyTy.genGroup G τ = PolyTy.genGroup Ws (Ty.renameG G Ws τ) :=
    PolyTy.genGroup_renameG hτlc hWlen hwf.nodup hWnodup hdisj hWτ
  have hYlen : (Ty.genFilter Ws (Ty.renameG G Ws τ)).length = (Ty.genFilter G τ).length := by
    have h := congrArg PolyTy.paramCount hgg
    simp only [PolyTy.genGroup] at h
    exact h.symm
  have hGFnodup : (Ty.genFilter G τ).Nodup := by unfold Ty.genFilter; exact hwf.nodup.filter _
  have hGF_disj : ∀ g ∈ Ty.genFilter G τ, g ∉ Ty.genFilter Ws (Ty.renameG G Ws τ) :=
    fun g hg hc => hWG g (Ty.mem_of_mem_genFilter hc) (Ty.mem_of_mem_genFilter hg)
  have hb : (PolyTy.genGroup G τ).openVars (Ty.genFilter Ws (Ty.renameG G Ws τ))
      = Ty.renameG (Ty.genFilter G τ) (Ty.genFilter Ws (Ty.renameG G Ws τ)) τ := by
    unfold PolyTy.openVars PolyTy.genGroup
    exact Ty.openVars_closeOver_rename hτlc hGFnodup hYlen hGF_disj
  rw [ha, ← hb] at h1
  have hYnodup : (Ty.genFilter Ws (Ty.renameG G Ws τ)).Nodup := by
    unfold Ty.genFilter; exact hWnodup.filter _
  have hVlen' : Vs.length = (Ty.genFilter Ws (Ty.renameG G Ws τ)).length := by
    rw [hVlen]; exact hYlen.symm
  have hY_Mbody : ∀ y ∈ Ty.genFilter Ws (Ty.renameG G Ws τ),
      y ∉ (PolyTy.genGroup G τ).body.freeVars :=
    fun y hy hc => hWavoid y (Ty.mem_of_mem_genFilter hy) (by simp only [List.mem_append]; tauto)
  have hY_Vs : ∀ y ∈ Ty.genFilter Ws (Ty.renameG G Ws τ), y ∉ Ty.freeVarsList Vs :=
    fun y hy hc => hWavoid y (Ty.mem_of_mem_genFilter hy) (by simp only [List.mem_append]; tauto)
  have hY_env : ∀ y ∈ Ty.genFilter Ws (Ty.renameG G Ws τ), y ∉ env.freeVars :=
    fun y hy hc => hWavoid y (Ty.mem_of_mem_genFilter hy) (by simp only [List.mem_append]; tauto)
  have hY_e : ∀ y ∈ Ty.genFilter Ws (Ty.renameG G Ws τ),
      y ∉ (Expr.letRec anns bindings e).tyFreeVars :=
    fun y hy hc => hWavoid y (Ty.mem_of_mem_genFilter hy) (by simp only [List.mem_append]; tauto)
  have hrewrite : (PolyTy.genGroup G τ).openWith Vs
      = Ty.substFvars ((Ty.genFilter Ws (Ty.renameG G Ws τ)).zip Vs)
          ((PolyTy.genGroup G τ).openVars (Ty.genFilter Ws (Ty.renameG G Ws τ))) := by
    unfold PolyTy.openWith PolyTy.openVars
    exact Ty.openWith_eq_substFvars_openVars ⟨hVlen', hVlc⟩ hYnodup hY_Mbody hY_Vs
  -- the re-wrapped `letRec` value is type-`bvar` closed, so `instTy` is a no-op.
  rw [Expr.instTy_eq_self_of_tyBvarBounded (TypeOfElabHM.tyBvarBounded h1), hrewrite]
  have hsub := TypeOfElabHM.typ_substs_preservation
      ((Ty.genFilter Ws (Ty.renameG G Ws τ)).zip Vs)
      (fun p hp => hY_env p.1 (List.of_mem_zip hp).1)
      (fun p hp => hVlc p.2 (List.of_mem_zip hp).2) h1
  rwa [Expr.substTyFvars_eq_self_of_not_mem_tyFreeVars
        (fun p hp => hY_e p.1 (List.of_mem_zip hp).1)] at hsub

/-- Each re-wrapped ANNOTATED member `letRec anns bindings e` (with declared
    scheme `σ`) has that scheme DIRECTLY (no generalisation): `e` already types
    at a fresh opening of `σ` via the poly cofinite premise, lifted to an
    arbitrary instance by `typ_substs_preservation`. The per-binding
    depth-shielding of `instTyAux` keeps the inner re-wrapped group `bindings`
    UNCHANGED across `instTy Vs` (each member is `TyBvarBounded` by its own
    annotation's arity — `0` for unannotated members), so the cofinite premises
    transfer verbatim into a `rec_rewrap_typed` re-derivation; only the BODY `e`
    is instantiated at `Vs`. -/
theorem TypeOfElabHM.rewrap_hasScheme_poly
    {ctors : CtorEnv} {env : Env} {anns : List (Option PolyTy)} {bindings : List Expr}
    {specs : List RecSpec} {G L : List Nat}
    (hwf : RecSpecs.WF anns bindings specs G)
    (hmono : RecSpecs.MonoTyped TypeOfElabHM ⟨env, ctors⟩ bindings specs G L)
    (hpoly : RecSpecs.PolyTyped TypeOfElabHM ⟨env, ctors⟩ bindings specs G L)
    {e : Expr} {σ : PolyTy} (hmem : (e, RecSpec.poly σ) ∈ bindings.zip specs) :
    HasScheme ⟨env, ctors⟩ (.letRec anns bindings e) σ := by
  intro Vs hVs
  obtain ⟨hVlen, hVlc⟩ := hVs
  -- Fix ONE pool opening for the whole construction.
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L G.length
  have hXfresh : FreshNames L G.length Xs := ⟨hXlen, hXnodup, hXavoid⟩
  -- Each member is type-`bvar`-bounded by its own annotation's arity.
  have hbnd : ∀ p ∈ bindings.zip specs, p.1.TyBvarBounded (RecAnn.params p.2.ann) := by
    intro p hp
    cases hspec : p.2 with
    | mono τ =>
      simp only [RecSpec.ann, RecAnn.params]
      exact TypeOfElabHM.tyBvarBounded (hmono Xs hXfresh p hp τ hspec)
    | poly σ' =>
      simp only [RecSpec.ann, RecAnn.params]
      obtain ⟨Ws, hWlen, hWnodup, hWavoid⟩ := exists_fresh_names (L ++ Xs) σ'.paramCount
      have hc := hpoly Xs hXfresh p hp σ' hspec Ws ⟨hWlen, hWnodup, hWavoid⟩
      have hb := Expr.tyBvarBounded_of_openTyVarsAux Ws p.1 0
        (by simpa only [Expr.openTyVars] using TypeOfElabHM.tyBvarBounded hc)
      simpa only [Nat.zero_add, hWlen] using hb
  -- Hence type-beta `instTy Vs` is a no-op on the inner re-wrapped group.
  have hRG : Expr.TyBvarBounded.RecGroup 0 anns bindings := by
    refine Expr.TyBvarBounded.RecGroup_of_zip
      (by rw [← hwf.anns_eq, List.length_map]; exact hwf.length) (fun p hp => ?_)
    rw [← hwf.anns_eq] at hp
    obtain ⟨a, b, hab, rfl⟩ := List.mem_zip_map_right_ex hp
    simpa using hbnd (a, b) hab
  have hRG' := Expr.TyBvarBounded.RecGroup_iff.mp hRG
  have hgroup : RecGroup.instTyAux 0 Vs anns bindings = bindings := by
    rw [RecGroup.instTyAux_eq_zip,
        List.map_congr_left (g := Prod.fst) (fun q hq =>
          Expr.instTyAux_eq_self_of_tyBvarBounded Vs q.1 q.2 (hRG' q hq))]
    exact RecGroup.zip_shieldDepths_map_fst 0 anns bindings
  -- Body: instantiate `e` at `Vs` from its scheme-relative opening.
  obtain ⟨Ys, hYslen, hYnodup, hYavoid⟩ :=
    exists_fresh_names
      ((L ++ Xs) ++ σ.body.freeVars ++ Ty.freeVarsList Vs
        ++ Env.freeVars (specs.map (RecSpec.rhsEntry G Xs) ++ env)
        ++ e.tyFreeVars) σ.paramCount
  have hYfresh : FreshNames (L ++ Xs) σ.paramCount Ys :=
    ⟨hYslen, hYnodup, fun x hx hc => hYavoid x hx (by simp only [List.mem_append] at hc ⊢; tauto)⟩
  have hetyped : TypeOfElabHM ⟨specs.map (RecSpec.rhsEntry G Xs) ++ env, ctors⟩
      (e.openTyVars Ys) (σ.openVars Ys) :=
    hpoly Xs hXfresh (e, .poly σ) hmem σ rfl Ys hYfresh
  have hYσ : ∀ y ∈ Ys, y ∉ σ.body.freeVars := fun y hy hc =>
    hYavoid y hy (by simp only [List.mem_append]; tauto)
  have hYVs : ∀ y ∈ Ys, y ∉ Ty.freeVarsList Vs := fun y hy hc =>
    hYavoid y hy (by simp only [List.mem_append]; tauto)
  have hYenv : ∀ y ∈ Ys, y ∉ Env.freeVars (specs.map (RecSpec.rhsEntry G Xs) ++ env) :=
    fun y hy hc => hYavoid y hy (by simp only [List.mem_append]; tauto)
  have hYe : ∀ y ∈ Ys, y ∉ e.tyFreeVars := fun y hy hc =>
    hYavoid y hy (by simp only [List.mem_append]; tauto)
  have hVlen' : Vs.length = Ys.length := by rw [hVlen, hYslen]
  have hrewrite : σ.openWith Vs = Ty.substFvars (Ys.zip Vs) (σ.openVars Ys) := by
    unfold PolyTy.openWith PolyTy.openVars
    exact Ty.openWith_eq_substFvars_openVars ⟨hVlen', hVlc⟩ hYnodup hYσ hYVs
  have hbody : TypeOfElabHM ⟨specs.map (RecSpec.rhsEntry G Xs) ++ env, ctors⟩
      (e.instTy Vs) (σ.openWith Vs) := by
    have hsub := TypeOfElabHM.typ_substs_preservation (Ys.zip Vs)
      (fun p hp => hYenv p.1 (List.of_mem_zip hp).1)
      (fun p hp => hVlc p.2 (List.of_mem_zip hp).2) hetyped
    rw [Expr.substTyFvars_zip_openTyVars_concrete hVlen' hYnodup hYe hYVs hVlc] at hsub
    rw [hrewrite]; exact hsub
  -- Assemble: `instTy Vs` leaves the group (closed) intact, only opens the body.
  have hannsid : RecGroup.instAnns 0 Vs anns = anns := by
    refine RecGroup.instAnns_eq_self_of_bvars (fun σ' hσ' => ?_)
    rw [← hwf.anns_eq] at hσ'
    obtain ⟨s, hs, hsa⟩ := List.mem_map.mp hσ'
    cases RecSpec.ann_eq_some hsa
    rw [Nat.zero_add]
    exact hwf.poly_wf σ' hs
  have hval : (Expr.letRec anns bindings e).instTy Vs
      = Expr.letRec anns bindings (e.instTy Vs) := by
    show Expr.letRec (RecGroup.instAnns 0 Vs anns)
        (RecGroup.instTyAux 0 Vs anns bindings) (e.instTy Vs) = _
    rw [hgroup, hannsid]
  rw [hval]
  exact TypeOfElabHM.rec_rewrap_typed hwf hmono hpoly hXfresh hbody

/-- Bridge a `let`-rule cofinite premise to `HasScheme` for the bound expression.
    For an annotated `let` the cofinite already opens the bound expression's scoped
    type variables (`openBoundTyVars (some _) = openTyVars`), so it *is* `HasSchemeVars`.
    For an unannotated `let` the bound expression is type-`bvar` closed (it is typed,
    so its annotations have no free `bvar`s), so opening is a no-op and the unopened
    premise is again `HasSchemeVars`. -/
theorem HasScheme.fromLetCofinite {ctx : Ctx} {M : PolyTy} {rhs : Expr}
    {ann : Option PolyTy} {L : List Nat}
    (hcofin : ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
        TypeOfElabHM ctx (Expr.openBoundTyVars ann Xs rhs) (M.openVars Xs)) :
    HasScheme ctx rhs M := by
  apply HasScheme.fromHasSchemeVars (L := L)
  intro Xs hfresh
  have hc := hcofin Xs hfresh
  rw [Expr.instTy_fvar_eq_openTyVars]
  cases ann with
  | some σ => simpa only [Expr.openBoundTyVars] using hc
  | none =>
    simp only [Expr.openBoundTyVars] at hc
    simp only [Expr.openTyVars]
    rw [Expr.openTyVarsAux_eq_self_of_tyBvarBounded Xs rhs 0 (TypeOfElabHM.tyBvarBounded hc)]
    exact hc

open SmallStep in
/-- Subject reduction for the genuine type-passing (call-by-name `let`) semantics.
    The reduction cases reduce to the substitution lemmas; there is no `letInRhs`
    case (we never reduce a `let`'s rhs in place), and `letReduce` fires on any
    `letIn`, getting `HasScheme` for the bound expression from the cofinite premise
    via `fromHasSchemeVars` (an unannotated `let`'s bound expression is type-`bvar`
    closed, so its unopened cofinite premise already *is* `HasSchemeVars`). -/
theorem TypeOfElabHM.preservation {ctx : Ctx} {e e' : Expr} {τ : Ty}
    (h_step : Step e e') (h_ty : TypeOfElabHM ctx e τ) :
    TypeOfElabHM ctx e' τ := by
  induction h_step generalizing τ with
  | beta hval =>
    cases h_ty with
    | app hf hi =>
      cases hf with
      | lambda hpc _ heq hbody =>
        subst heq
        exact TypeOfElabHM.subst_lemma (env_post := []) (M := PolyTy.mkTrivial _)
          hpc hbody (HasScheme.ofTypeOfElabHM hi)
  | letReduce =>
    cases h_ty with
    | letIn hwf _ hcofin heq hbody =>
      subst heq
      exact TypeOfElabHM.subst_lemma (env_post := []) hwf hbody
        (HasScheme.fromLetCofinite hcofin)
  | deltaIntAdd =>
    -- the result type is pinned to `int` by inverting the primop's typing;
    -- the reduct is an `int` literal.
    cases h_ty with
    | app h_f _ => cases h_f with
      | app h_pbo _ => cases h_pbo; exact .primLitInt
  | deltaIntSub =>
    cases h_ty with
    | app h_f _ => cases h_f with
      | app h_pbo _ => cases h_pbo; exact .primLitInt
  | deltaIntLt =>
    -- result type is `Bool`; the reduct is `.ctor "True"/"False"`, typed directly
    -- from the `primBinOpIntLt` premises (Bool present in the env).
    cases h_ty with
    | app h_f _ => cases h_f with
      | app h_pbo _ => cases h_pbo with
        | primBinOpIntLt htrue hfalse => split <;> assumption
  | matchReduce hval hctor hfirst =>
    rename_i scrut branches name args pat body
    cases h_ty with
    | match_ h_scrut h_ne h_brs =>
      have hmem := hfirst.mem
      have hpeq := hfirst.ctor_eq
      cases pat with
      | wildcard =>
        -- A wildcard binds nothing: the reduct is `body.substN 0 [] = body`, and
        -- the wildcard branch types `body` directly in `ctx`.
        simp only [MatchPattern.bindCount, List.take_zero]
        cases h_brs (.wildcard, body) hmem with
        | wildcard hbodyW =>
          exact TypeOfElabHM.subst_lemma_many (Ms := []) (by simp)
            List.Forall₂.nil body.size body (Nat.le_refl _) [] _ hbodyW
      | named c n =>
        -- A matched named branch binds exactly the chain's args
        -- (`n = args.length`), so `args.take pat.bindCount = args`.
        simp only [MatchPattern.matchesCtor, Bool.and_eq_true, beq_iff_eq] at hpeq
        obtain ⟨hcname, hnlen⟩ := hpeq
        simp only [MatchPattern.bindCount]
        rw [hnlen, List.take_length]
        cases h_brs (.named c n, body) hmem with
        | @mk _ _ _ _ ctorB _ _ _ tyArgsB instContents hspecB hctxB hbodyB =>
          subst hctxB
          have hlookB := hspecB.lookup
          have hScrutB := hspecB.scrut_eq
          have hpcB := hspecB.arity
          have hinstB := hspecB.fields
          -- the named branch pins the scrutinee's type to `customTy ctorB.tyName tyArgsB`,
          -- so the (value) scrutinee is a constructor chain.
          rw [hScrutB] at h_scrut
          have hchain := TypeOfElabHM.canonical_customTy h_scrut hval
          obtain ⟨name', args', ctorS, tyArgsS, consumedS, remainingS,
            hcatS, hlookS, htyargsS, hcontentsS, hforallS, hinstS⟩ :=
            TypeOfElabHM.ctor_chain_inversion hchain h_scrut
          obtain ⟨hnEq, haEq⟩ := hctor.det hcatS
          subst hnEq
          subst haEq
          rw [hcname] at hlookB
          have hcc := Option.some.inj (hlookS.symm.trans hlookB)
          subst ctorB
          cases remainingS with
          | cons d rest => simp only [Ty.wrapArrows] at hinstS; cases hinstS
          | nil =>
            rw [List.append_nil] at hcontentsS
            subst hcontentsS
            simp only [Ty.wrapArrows] at hinstS
            cases hinstS with
            | customTy hbvr =>
              have hpc_len : tyArgsB.length = ctorS.paramCount := hpcB.symm
              have hagree : ∀ k, k < ctorS.paramCount → tyArgsB[k]? = tyArgsS[k]? := by
                intro k hk
                have hkt : k < tyArgsB.length := by omega
                have hkr : k < (Ty.bvarRange ctorS.paramCount).length := by
                  rw [hbvr.length_eq]; exact hkt
                have hrel := List.Forall₂.get hbvr hkr hkt
                simp only [List.get_eq_getElem] at hrel
                have helem : (Ty.bvarRange ctorS.paramCount)[k] = Ty.bvar k := by
                  have h1 := Ty.bvarRange_getElem? (n := ctorS.paramCount) (k := k) hk
                  rw [List.getElem?_eq_getElem hkr] at h1
                  exact Option.some.inj h1
                rw [helem] at hrel
                cases hrel with
                | bvar hsome =>
                  rw [hsome]
                  exact List.getElem?_eq_getElem hkt
              have htyArgs_lc : ∀ t ∈ tyArgsB, ContainsBvarsUpTo 0 t := by
                intro t ht
                obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
                have hkpc : k < ctorS.paramCount := by omega
                have hag := hagree k hkpc
                rw [List.getElem?_eq_getElem hk] at hag
                exact htyargsS _ (List.mem_of_getElem? hag.symm)
              have h_Ms_wf : ∀ M ∈ instContents.map PolyTy.mkTrivial, M.WF := by
                intro M hM
                obtain ⟨ic, hic, rfl⟩ := List.mem_map.mp hM
                obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hic
                have hrel := List.Forall₂.get hinstB
                  (by have := hinstB.length_eq; omega) hi
                exact InstantiatesBy.preserves_bvars htyArgs_lc hrel
              have h_vs := InstantiatesBy.build_match_vs hagree ctorS.bound hinstB hforallS
              exact TypeOfElabHM.subst_lemma_many h_Ms_wf h_vs
                body.size body (Nat.le_refl _) [] _ hbodyB
  | matchWildReduce hval hnc =>
    rename_i scrut body rest
    cases h_ty with
    | match_ h_scrut h_ne h_brs =>
      -- the fired branch is the wildcard head; it types `body` directly in `ctx`.
      cases h_brs (.wildcard, body) (List.mem_cons_self ..) with
      | wildcard hbodyW => exact hbodyW
  | appFn _ ih =>
    cases h_ty with
    | app hf hi => exact .app (ih hf) hi
  | appArg hv _ ih =>
    cases h_ty with
    | app hf hi => exact .app hf (ih hi)
  | matchScrut _ ih =>
    cases h_ty with
    | match_ h_scrut h_ne h_brs => exact .match_ (ih h_scrut) h_ne h_brs
  | letRecUnfold =>
    rename_i anns bindings body
    cases h_ty with
    | letRec hwf hmonoP hpolyP heq hbodyT =>
      subst heq
      expose_names
      -- The body schemes: `genGroup G τ` for unannotated members, `σ` for
      -- annotated ones — all WF.
      have hMwf : ∀ M ∈ specs.map (RecSpec.bodyScheme G), M.WF := by
        intro M hM
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hM
        cases s with
        | mono τ => exact PolyTy.genGroup_wf (hwf.mono_lc τ hs)
        | poly σ => exact hwf.poly_wf σ hs
      -- Each re-wrapped `letRec anns bindings eⱼ` carries its body scheme:
      -- generalised for unannotated members, declared for annotated ones.
      have h_vs : List.Forall₂ (fun v M' => HasScheme ⟨ctx.env, ctx.ctors⟩ v M')
          (bindings.map (fun e => Expr.letRec anns bindings e))
          (specs.map (RecSpec.bodyScheme G)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        refine List.forall₂_of_mem_zip hwf.length ?_
        rintro ⟨a, b⟩ hp
        cases b with
        | mono τ =>
          simp only [RecSpec.bodyScheme]
          exact TypeOfElabHM.rewrap_hasScheme_mono hwf hmonoP hpolyP hp
        | poly σ =>
          simp only [RecSpec.bodyScheme]
          exact TypeOfElabHM.rewrap_hasScheme_poly hwf hmonoP hpolyP hp
      -- Discharge the body: substitute the re-wrapped group for the scheme block.
      have hfinal := TypeOfElabHM.subst_lemma_many (env := ctx.env)
        (Ms := specs.map (RecSpec.bodyScheme G))
        (ctors := ctx.ctors) hMwf h_vs body.size body (Nat.le_refl _) [] _ hbodyT
      simpa using hfinal

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
  | primBinOp op => intro h _ _; exact h
  | var m _ => intro _ threshold n; simp only [Expr.shiftFrom]; split <;> exact .var
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
  | primBinOp op => intro _ h; exact h
  | var i tyArgs => intro _ _; exact .var
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
  | primBinOp op => intro h _; exact h
  | var m _ =>
    intro _ k
    simp only [Expr.substN]
    split
    · exact .var
    · split
      · next h => exact ((hvs _ (List.getElem_mem h)).instTy _).shiftFrom 0 k
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

open SmallStep in
/-- **Iterated subject reduction.** Across any number of `Step`s, a closed
    well-typed term keeps its type and stays exhaustive (so `progress` can be
    re-applied at the end). Induction on the reflexive-transitive closure: each
    tail step uses single-step `preservation` and `Step.preserves_exhaustive`. -/
theorem TypeOfElabHM.preservation_star {ctors : CtorEnv} {e e' : Expr} {τ : Ty}
    (h_rtc : Relation.ReflTransGen Step e e')
    (h_ty : TypeOfElabHM ⟨[], ctors⟩ e τ)
    (h_exh : AllMatchesExhaustive ctors e) :
    TypeOfElabHM ⟨[], ctors⟩ e' τ ∧ AllMatchesExhaustive ctors e' := by
  induction h_rtc with
  | refl => exact ⟨h_ty, h_exh⟩
  | tail _ h_bc ih =>
    obtain ⟨h_ty_b, h_exh_b⟩ := ih
    exact ⟨TypeOfElabHM.preservation h_bc h_ty_b, Step.preserves_exhaustive h_exh_b h_bc⟩

open SmallStep in
/-- **Type safety** ("well-typed programs don't go wrong") for the genuine
    type-passing (call-by-name `let`) dynamic semantics: a closed, well-typed
    program whose matches are all exhaustive makes progress (it is a value or it
    steps) and every step preserves typing. No erasure — types are carried at run
    time and reduction (type-beta) keeps the program well-typed. -/
theorem TypeOfElabHM.type_safety {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h_ty : TypeOfElabHM ⟨[], ctors⟩ e τ)
    (h_exh : AllMatchesExhaustive ctors e) :
    (IsValue e ∨ ∃ e', Step e e') ∧
    (∀ e', Step e e' → TypeOfElabHM ⟨[], ctors⟩ e' τ) :=
  ⟨TypeOfElabHM.progress h_ty rfl h_exh,
   fun _ hstep => TypeOfElabHM.preservation hstep h_ty⟩

open SmallStep in
/-- **Iterated type safety.** A closed, well-typed exhaustive program never gets
    stuck across *any* number of steps and preserves its type throughout: every
    term `e'` reachable from `e` by the reflexive-transitive closure of `Step` is
    still well-typed at `τ` and is itself a value or can take another step. Lifts
    `type_safety` via `preservation_star` (iterated preservation, staying
    exhaustive) followed by `progress`. -/
theorem TypeOfElabHM.type_safety_star {ctors : CtorEnv} {e : Expr} {τ : Ty}
    (h_ty : TypeOfElabHM ⟨[], ctors⟩ e τ) (h_exh : AllMatchesExhaustive ctors e) :
    ∀ e', Relation.ReflTransGen Step e e' →
      TypeOfElabHM ⟨[], ctors⟩ e' τ ∧ (IsValue e' ∨ ∃ e'', Step e' e'') := by
  intro e' h_rtc
  obtain ⟨h_ty', h_exh'⟩ := TypeOfElabHM.preservation_star h_rtc h_ty h_exh
  exact ⟨h_ty', TypeOfElabHM.progress h_ty' rfl h_exh'⟩

/-! ## Annotated-recursion correctness smoke test (ported from `SpikeLetRecAnn`)

A genuine *polymorphic*-recursion witness types under the fused rule (all-`some`
groups — the historical `letRecAnn`), and a recursion scheme mentioning a scoped
(rigid) free `fvar` is supported. These are the proven spike's witnesses
re-checked against the real fused `TypeOfElabHM.letRec` constructor, confirming
the rule has the intended shape. -/

namespace LetRecAnnSmokeTest

/-- `σ = ∀a. a → a`. -/
def selfSig : PolyTy := ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

/-- `λx. let _ = f 0 in let _ = f () in x`. Under the λ, `f = var 1`; after the
    first `let`, `f = var 2`; the body returns `x`. -/
def polyRecRhs : Expr :=
  .lambda none
    (.letIn none (.app (.var 1 [.prim .int]) (.primLit (.int 0)))
      (.letIn none (.app (.var 2 [.prim .unit]) (.primLit .unit))
        (.var 2 [])))

/-- The RHS types at every skolem opening `X → X` of `σ`, with `f : σ` in scope
    (polymorphic recursion: `f` is used at `Int → Int` AND at `Unit → Unit`). -/
theorem polyRecRhs_typeable (X : Nat) :
    TypeOfElabHM ⟨[selfSig], []⟩ polyRecRhs (.arrow (.fvar X) (.fvar X)) := by
  refine TypeOfElabHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
  refine TypeOfElabHM.letIn (M := PolyTy.mkTrivial (.prim .int)) (L := [])
    .prim (fun σ h => Option.noConfusion h) ?_ rfl ?_
  · intro Xs hfresh
    obtain rfl : Xs = [] := List.eq_nil_of_length_eq_zero hfresh.length
    refine TypeOfElabHM.app ?_ TypeOfElabHM.primLitInt
    exact TypeOfElabHM.var (polyTy := selfSig) (tyArgs := [.prim .int]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))
  refine TypeOfElabHM.letIn (M := PolyTy.mkTrivial (.prim .unit)) (L := [])
    .prim (fun σ h => Option.noConfusion h) ?_ rfl ?_
  · intro Xs hfresh
    obtain rfl : Xs = [] := List.eq_nil_of_length_eq_zero hfresh.length
    refine TypeOfElabHM.app ?_ TypeOfElabHM.primLitUnit
    exact TypeOfElabHM.var (polyTy := selfSig) (tyArgs := [.prim .unit]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))
  exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) (tyArgs := []) rfl
    ⟨rfl, by intro t ht; cases ht⟩ .fvar

/-- The headline: the annotated group **types** at its principal-ish instance
    `(fvar 0) → (fvar 0)` — polymorphic recursion accepted by the fused
    `TypeOfElabHM.letRec` (all-`some` degenerate case). -/
theorem polyRec_typeable :
    TypeOfElabHM ⟨[], []⟩ (.letRec [some selfSig] [polyRecRhs] (.var 0 [.fvar 0]))
      (.arrow (.fvar 0) (.fvar 0)) := by
  refine TypeOfElabHM.letRec (specs := [.poly selfSig]) (G := []) (L := [])
    ⟨rfl, rfl, List.nodup_nil, fun τ hτ => by simp at hτ, ?_⟩ ?_ ?_ rfl ?_
  · intro σ hσ
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hσ; subst hσ
    show ContainsBvarsUpTo 1 (Ty.arrow (Ty.bvar 0) (Ty.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro Xs _hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact RecSpec.noConfusion hτ
  · intro Xs _hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    injection hσ with hσσ
    subst hσσ
    obtain ⟨X, rfl⟩ : ∃ X, Ys = [X] := List.length_eq_one_iff.mp hYs.length
    show TypeOfElabHM ⟨[selfSig], []⟩ (polyRecRhs.openTyVars [X]) ((Ty.fvar X).arrow (Ty.fvar X))
    exact polyRecRhs_typeable X
  · exact TypeOfElabHM.var (polyTy := selfSig) (tyArgs := [.fvar 0]) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .fvar⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-! ### Genuine OWN-variable polymorphic recursion.

A self-recursive binding whose recursive call instantiates the function's OWN
scheme variable `a` (stored scheme-relatively as `arrow (bvar 0) (bvar 0)`). This
is exactly the case the scheme-relative opened rule + `instTy`/`openTyVars`
depth-shielding were added to support: opening the binding at its own fresh `X`
turns the recursive tyArg into the closed `X → X`, and the shielding keeps the
re-wrapped group polymorphic on unfold (so subject reduction holds). -/

/-- `λx. let _ = (f [a→a]) (λy. y) in x`, with `f = var 1` under the λ and the
    recursive type argument `a→a = arrow (bvar 0) (bvar 0)` at `f`'s own variable. -/
def ownVarRhs : Expr :=
  .lambda none
    (.letIn none
      (.app (.var 1 [.arrow (.bvar 0) (.bvar 0)]) (.lambda none (.var 0 [])))
      (.var 1 []))

/-- Opening the single binding at `[X]` turns the recursive call's `bvar 0` into
    the fresh skolem `fvar X` (closed), which the `var` rule accepts. -/
theorem ownVarRhs_opened_typeable (X : Nat) :
    TypeOfElabHM ⟨[selfSig], []⟩ (ownVarRhs.openTyVars [X]) ((Ty.fvar X).arrow (Ty.fvar X)) := by
  show TypeOfElabHM ⟨[selfSig], []⟩
    (.lambda none
      (.letIn none
        (.app (.var 1 [.arrow (.fvar X) (.fvar X)]) (.lambda none (.var 0 [])))
        (.var 1 [])))
    ((Ty.fvar X).arrow (Ty.fvar X))
  refine TypeOfElabHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
  refine TypeOfElabHM.letIn (M := PolyTy.mkTrivial ((Ty.fvar X).arrow (.fvar X))) (L := [])
    (.arrow .fvar .fvar) (fun σ h => Option.noConfusion h) ?_ rfl ?_
  · intro Xs hfresh
    obtain rfl : Xs = [] := List.eq_nil_of_length_eq_zero hfresh.length
    show TypeOfElabHM ⟨[PolyTy.mkTrivial (.fvar X), selfSig], []⟩
      (.app (.var 1 [.arrow (.fvar X) (.fvar X)]) (.lambda none (.var 0 [])))
      ((Ty.fvar X).arrow (.fvar X))
    refine TypeOfElabHM.app (argTy := (Ty.fvar X).arrow (.fvar X)) ?_ ?_
    · exact TypeOfElabHM.var (polyTy := selfSig) rfl
        ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .arrow .fvar .fvar⟩
        (.arrow (.bvar rfl) (.bvar rfl))
    · refine TypeOfElabHM.lambda (paramTy := .fvar X) .fvar (fun T h => Option.noConfusion h) rfl ?_
      exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
        ⟨rfl, by intro t ht; cases ht⟩ .fvar
  · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar X)) rfl
      ⟨rfl, by intro t ht; cases ht⟩ .fvar

/-- **Genuine own-variable polymorphic recursion types** under the fused rule:
    the body uses `f` at the concrete `Int`, giving `Int → Int`. -/
theorem ownVarSelfRec_typeable :
    TypeOfElabHM ⟨[], []⟩ (.letRec [some selfSig] [ownVarRhs] (.var 0 [.prim .int]))
      ((Ty.prim .int).arrow (.prim .int)) := by
  refine TypeOfElabHM.letRec (specs := [.poly selfSig]) (G := []) (L := [])
    ⟨rfl, rfl, List.nodup_nil, fun τ hτ => by simp at hτ, ?_⟩ ?_ ?_ rfl ?_
  · intro σ hσ
    simp only [List.mem_singleton, RecSpec.poly.injEq] at hσ; subst hσ
    show ContainsBvarsUpTo 1 (Ty.arrow (Ty.bvar 0) (Ty.bvar 0))
    exact .arrow (.bvar (by omega)) (.bvar (by omega))
  · intro Xs _hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact RecSpec.noConfusion hτ
  · intro Xs _hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    injection hσ with hσσ
    subst hσσ
    obtain ⟨X, rfl⟩ : ∃ X, Ys = [X] := List.length_eq_one_iff.mp hYs.length
    exact ownVarRhs_opened_typeable X
  · exact TypeOfElabHM.var (polyTy := selfSig) rfl
      ⟨rfl, by intro t ht; simp only [List.mem_singleton] at ht; subst ht; exact .prim⟩
      (.arrow (.bvar rfl) (.bvar rfl))

/-- `Z → Z` with `Z` a free (scoped/rigid) type variable. -/
def rigidSig (Z : Nat) : PolyTy := ⟨0, .arrow (.fvar Z) (.fvar Z)⟩

/-- `λx. f x`, self-recursive at the rigid scheme `Z → Z`. -/
def scopedRhs : Expr := .lambda none (.app (.var 1 []) (.var 0 []))

theorem scopedRhs_typeable (Z : Nat) :
    TypeOfElabHM ⟨[rigidSig Z], []⟩ scopedRhs (.arrow (.fvar Z) (.fvar Z)) := by
  refine TypeOfElabHM.lambda .fvar (fun T h => Option.noConfusion h) rfl ?_
  refine TypeOfElabHM.app (argTy := .fvar Z) ?_ ?_
  · exact TypeOfElabHM.var (polyTy := rigidSig Z) (tyArgs := []) rfl
      ⟨rfl, by intro t ht; cases ht⟩ (.arrow .fvar .fvar)
  · exact TypeOfElabHM.var (polyTy := PolyTy.mkTrivial (.fvar Z)) (tyArgs := []) rfl
      ⟨rfl, by intro t ht; cases ht⟩ .fvar

/-- The kept scheme `Z → Z` mentions the free/rigid `Z`, is WF, and the group
    types — so a recursion scheme referencing a scoped variable is supported. -/
theorem scopedRec_typeable (Z : Nat) :
    TypeOfElabHM ⟨[], []⟩ (.letRec [some (rigidSig Z)] [scopedRhs] (.var 0 []))
      (.arrow (.fvar Z) (.fvar Z)) := by
  refine TypeOfElabHM.letRec (specs := [.poly (rigidSig Z)]) (G := []) (L := [])
    ⟨rfl, rfl, List.nodup_nil, fun τ hτ => by simp at hτ, ?_⟩ ?_ ?_ rfl ?_
  · intro σ hσ; simp only [List.mem_singleton, RecSpec.poly.injEq] at hσ; subst hσ
    exact .arrow .fvar .fvar
  · intro Xs _hfresh p hp τ hτ
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    exact RecSpec.noConfusion hτ
  · intro Xs _hfresh p hp σ hσ Ys hYs
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hp
    subst hp
    injection hσ with hσσ
    subst hσσ
    obtain rfl : Ys = [] := List.eq_nil_of_length_eq_zero hYs.length
    show TypeOfElabHM ⟨[rigidSig Z], []⟩ (scopedRhs.openTyVars []) ((Ty.fvar Z).arrow (Ty.fvar Z))
    exact scopedRhs_typeable Z
  · exact TypeOfElabHM.var (polyTy := rigidSig Z) (tyArgs := []) rfl
      ⟨rfl, by intro t ht; cases ht⟩ (.arrow .fvar .fvar)

end LetRecAnnSmokeTest
