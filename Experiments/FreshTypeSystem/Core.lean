import Mathlib
import Experiments.HasItem


/-- Name of a type -/
inductive TyName
  | mk (str : String)
  deriving DecidableEq, Repr

/-- Name of a type constructor -/
inductive CtorName
  | mk (str : String)
  deriving DecidableEq, Repr

/-- Name of a value binding -/
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
  | bool
  | str
  deriving DecidableEq, Repr


inductive Ty
  | prim : PrimTy → Ty
  | pair : (fst snd : Ty) → Ty
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

  | pair :
    ContainsBvarsUpTo n fst →
    ContainsBvarsUpTo n snd →
    ContainsBvarsUpTo n (.pair fst snd)

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

  | pair :
    NoFreeVars fst →
    NoFreeVars snd →
    NoFreeVars (.pair fst snd)

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
  | bool : Bool → PrimLitExpr
  | str : String → PrimLitExpr


/-- Only supporting type constructor name matches for now -/
structure MatchPattern where
  ctor : CtorName
  /-- this is basically just a binding range. i.e. if 2 this means we've bound 2 new "names" to the context -/
  contents : Nat


/-- An expression in our language -/
inductive Expr
  | primLit (prim : PrimLitExpr)
  | pair (a b : Expr)
  /-- A lambda. `paramAnn` is an optional type ascription on the parameter
      (surface `λ(x : T). body`); `none` means the param type is inferred. -/
  | lambda (paramAnn : Option Ty) (body : Expr)
  | app (f input : Expr)
  /-- A let binding. `ann` is an optional scheme ascription on the bound
      expression (surface `let x : σ = e in body`); `none` means the scheme is
      generalised by inference. -/
  | letIn (ann : Option PolyTy) (bindingExpr body : Expr)
  /-- Get the fst of a pair -/
  | fst (expr : Expr)
  /-- Get the snd of a pair -/
  | snd (expr : Expr)
  | var (deBruijnIndex : Nat)
  /-- A type constructor -/
  | ctor (name : CtorName)
  | match_ (scrutinee : Expr) (branches : List (MatchPattern × Expr))







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
  | .pair a b => (a.freeVars ++ b.freeVars).dedup
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
  | .pair a b        => a.isClosed && b.isClosed
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
  | .pair a b        => .pair (a.closeOver vars) (b.closeOver vars)
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
  | case2 a b aih bih
  | case3 a b aih bih =>
    cases prem
    tauto
  | case4 =>
    simp [closeOver]
    constructor
    cases prem
    omega
  | case5 nm tys ih =>
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
  | case6 n i hsome =>
    rw [Ty.closeOver.eq_6]
    simp [hsome]
    refine .bvar ?_
    exact List.idxOf?_lt_length hsome
  | case7 n hnone =>
    rw [Ty.closeOver.eq_6]
    simp [hnone]
    exact .fvar
  | case8 =>
    rename_i h
    simp at h
  | case9 arg rest ih_arg ih_rest =>
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
  case pair a b iha ihb => ...
  case arrow a b iha ihb => ...
  case bvar n           => ...
  case fvar n           => ...
  case customTy nm tys ih => ...   -- ih : ∀ t ∈ tys, P t
```
-/
@[elab_as_elim]
def Ty.rec_strong.{u} {motive : Ty → Sort u}
    (prim     : ∀ p, motive (.prim p))
    (pair     : ∀ a b, motive a → motive b → motive (.pair a b))
    (arrow    : ∀ a b, motive a → motive b → motive (.arrow a b))
    (bvar     : ∀ n, motive (.bvar n))
    (fvar     : ∀ n, motive (.fvar n))
    (customTy : ∀ nm tys, (∀ t ∈ tys, motive t) → motive (.customTy nm tys)) :
    (ty : Ty) → motive ty
  | .prim p          => prim p
  | .pair a b        =>
      pair a b
        (Ty.rec_strong prim pair arrow bvar fvar customTy a)
        (Ty.rec_strong prim pair arrow bvar fvar customTy b)
  | .arrow a b       =>
      arrow a b
        (Ty.rec_strong prim pair arrow bvar fvar customTy a)
        (Ty.rec_strong prim pair arrow bvar fvar customTy b)
  | .bvar n          => bvar n
  | .fvar n          => fvar n
  | .customTy nm tys =>
      customTy nm tys
        (fun t _ht => Ty.rec_strong prim pair arrow bvar fvar customTy t)
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
  | pair a b iha ihb =>
    simp only [Ty.isClosed, Bool.and_eq_true]
    rw [iha, ihb]
    constructor
    · rintro ⟨⟨na, ca⟩, nb, cb⟩; exact ⟨.pair na nb, .pair ca cb⟩
    · rintro ⟨hn, hc⟩
      cases hn with | pair na nb => cases hc with | pair ca cb => exact ⟨⟨na, ca⟩, nb, cb⟩
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
  case pair a b iha ihb                => ...
  case lambda paramAnn body ih         => ...
  case app f input ihf ihi             => ...
  case letIn ann be body ihbe ihbo     => ...
  case fst expr ih                     => ...
  case snd expr ih                     => ...
  case var n                           => ...
  case ctor nm                         => ...
  case match_ scrutinee branches ihs ihbs => ...
    -- ihbs : ∀ pat e, (pat, e) ∈ branches → P e
```
-/
@[elab_as_elim]
def Expr.rec_strong.{u} {motive : Expr → Sort u}
    (primLit    : ∀ p, motive (.primLit p))
    (pair       : ∀ a b, motive a → motive b → motive (.pair a b))
    (lambda     : ∀ paramAnn body, motive body → motive (.lambda paramAnn body))
    (app        : ∀ f input, motive f → motive input → motive (.app f input))
    (letIn      : ∀ ann bindingExpr body,
                    motive bindingExpr → motive body →
                    motive (.letIn ann bindingExpr body))
    (fst        : ∀ expr, motive expr → motive (.fst expr))
    (snd        : ∀ expr, motive expr → motive (.snd expr))
    (var        : ∀ n, motive (.var n))
    (ctor       : ∀ nm, motive (.ctor nm))
    (match_     : ∀ scrutinee branches,
                    motive scrutinee →
                    (∀ pat e, (pat, e) ∈ branches → motive e) →
                    motive (.match_ scrutinee branches)) :
    (e : Expr) → motive e
  | .primLit p          => primLit p
  | .pair a b           =>
      pair a b
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ a)
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ b)
  | .lambda paramAnn body        =>
      lambda paramAnn body
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ body)
  | .app f input        =>
      app f input
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ f)
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ input)
  | .letIn ann be body      =>
      letIn ann be body
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ be)
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ body)
  | .fst e              =>
      fst e
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ e)
  | .snd e              =>
      snd e
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ e)
  | .var n              => var n
  | .ctor nm            => ctor nm
  | .match_ scrutinee branches =>
      match_ scrutinee branches
        (Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ scrutinee)
        (fun _pat e _hb =>
          Expr.rec_strong primLit pair lambda app letIn fst snd var ctor match_ e)
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
  | .pair a b => .pair (a.instantiate subst) (b.instantiate subst)
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

@TODO: hm maybe should make the source type here be a PolyTy, and then we can also ensure that all bvars are within range of the original polyty paramCount? then it's also just nicer to work with tbh. instantiation is semantically always from a polyty to a monoty, so it's odd that as it is it is a monoty to another monoty.
-/
inductive InstantiatesBy (tyArgs : List Ty) : Ty → Ty → Prop
  | prim :
    InstantiatesBy tyArgs (.prim p) (.prim p)

  | pair :
    InstantiatesBy tyArgs fst instFst →
    InstantiatesBy tyArgs snd instSnd →
    InstantiatesBy tyArgs (.pair fst snd) (.pair instFst instSnd)

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








/-! ## Small-step operational semantics

Call-by-value reduction on closed terms. Uses de Bruijn *indices* for term-level
variables: `var 0` is the innermost binder. Substitution is the standard
"substitute-and-eliminate" variant that shifts other vars to account for the
disappearing binder.

The machine here is independent of type checking — it would run on any
syntactically well-formed `Expr`. Type soundness (progress + preservation) is
the bridge between this and `TypeOfHM`. -/

mutual

/--
Shift all `.var i` with `i ≥ threshold` up by `n`. Traverses into binders with
`threshold` incremented by the number of new bindings introduced.

Used by `substN`: when a value is inserted at substitution depth `k`, it has
to pass under `k` new binders, which shifts its free vars up by `k`.
-/
def Expr.shiftFrom (threshold : Nat) (n : Nat) : Expr → Expr
  | .var i             => if i < threshold then .var i else .var (i + n)
  | .primLit p         => .primLit p
  | .pair a b          => .pair (a.shiftFrom threshold n) (b.shiftFrom threshold n)
  | .lambda ann body   => .lambda ann (body.shiftFrom (threshold + 1) n)
  | .app f arg         => .app (f.shiftFrom threshold n) (arg.shiftFrom threshold n)
  | .letIn ann rhs body =>
      .letIn ann (rhs.shiftFrom threshold n) (body.shiftFrom (threshold + 1) n)
  | .fst e             => .fst (e.shiftFrom threshold n)
  | .snd e             => .snd (e.shiftFrom threshold n)
  | .ctor c            => .ctor c
  | .match_ scrut branches =>
      .match_ (scrut.shiftFrom threshold n)
        (BranchList.shiftFrom threshold n branches)

private def BranchList.shiftFrom (threshold : Nat) (n : Nat) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, body.shiftFrom (threshold + pat.contents) n)
        :: BranchList.shiftFrom threshold n rest

end

mutual

/--
Capture-avoiding multi-substitution under de Bruijn *indices* (innermost = 0).

Replaces `.var (k + j)` with `(vs[j]).shiftFrom 0 k` for `j ∈ [0, vs.length)`,
and shifts higher indices down by `vs.length`. The `shiftFrom 0 k` accounts
for the `k` binders the substitution has traversed into.

When traversing into a binder, `k` is incremented by the number of binders
introduced (1 for `lambda`/`letIn`, `pat.contents` for each match branch body).
`fst`/`snd` are non-binding projections, so `k` is unchanged.

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
  | .pair a b          => .pair (a.substN k vs) (b.substN k vs)
  | .lambda ann body   => .lambda ann (body.substN (k + 1) vs)
  | .app f arg         => .app (f.substN k vs) (arg.substN k vs)
  | .letIn ann rhs body =>
      .letIn ann (rhs.substN k vs) (body.substN (k + 1) vs)
  | .fst e             => .fst (e.substN k vs)
  | .snd e             => .snd (e.substN k vs)
  | .ctor n            => .ctor n
  | .match_ scrut branches =>
      .match_ (scrut.substN k vs) (BranchList.substN k vs branches)

private def BranchList.substN (k : Nat) (vs : List Expr) :
    List (MatchPattern × Expr) → List (MatchPattern × Expr)
  | []                  => []
  | (pat, body) :: rest =>
      (pat, body.substN (k + pat.contents) vs)
        :: BranchList.substN k vs rest

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
  | pair {v₁ v₂} :
      IsValue v₁ → IsValue v₂ →
      IsValue (.pair v₁ v₂)
  | ctor (name) :
      IsValue (.ctor name)
  | ctorApp {f v} :
      IsCtorChain f → IsValue v →
      IsValue (.app f v)

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
    pat.ctor = name →
    pat.contents = arity →
    FirstMatchingBranch name arity ((pat, body) :: rest) pat body
  | there :
    ¬(pat'.ctor = name ∧ pat'.contents = arity) →
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

  /-- Let reduction (after rhs has been reduced to a value). -/
  | letReduce {ann v body} :
      IsValue v →
      Step (.letIn ann v body) (body.substN 0 [v])

  /-- First projection of a fully-reduced pair. -/
  | fstReduce {v₁ v₂} :
      IsValue v₁ → IsValue v₂ →
      Step (.fst (.pair v₁ v₂)) v₁

  /-- Second projection of a fully-reduced pair. -/
  | sndReduce {v₁ v₂} :
      IsValue v₁ → IsValue v₂ →
      Step (.snd (.pair v₁ v₂)) v₂

  /-- Match reduction. The scrutinee must be a fully-evaluated ctor chain
      whose ctor name matches the *first* applicable branch pattern. -/
  | matchReduce {scrut branches name args pat body} :
      IsValue scrut →
      CtorAppliedTo scrut name args →
      FirstMatchingBranch name args.length branches pat body →
      Step (.match_ scrut branches) (body.substN 0 args)

  -- ─── congruence rules (enforce left-to-right CBV) ─────────────────

  /-- Reduce the first component of a pair. -/
  | pairFst {a a' b} :
      Step a a' →
      Step (.pair a b) (.pair a' b)

  /-- Once the first component is a value, reduce the second. -/
  | pairSnd {v b b'} :
      IsValue v → Step b b' →
      Step (.pair v b) (.pair v b')

  /-- Reduce the function position of an application. -/
  | appFn {f f' arg} :
      Step f f' →
      Step (.app f arg) (.app f' arg)

  /-- Once the function is a value, reduce the argument. -/
  | appArg {v arg arg'} :
      IsValue v → Step arg arg' →
      Step (.app v arg) (.app v arg')

  /-- Reduce the rhs of a let-binding. -/
  | letInRhs {ann rhs rhs' body} :
      Step rhs rhs' →
      Step (.letIn ann rhs body) (.letIn ann rhs' body)

  /-- Reduce the operand of a first projection. -/
  | fstCong {e e'} :
      Step e e' →
      Step (.fst e) (.fst e')

  /-- Reduce the operand of a second projection. -/
  | sndCong {e e'} :
      Step e e' →
      Step (.snd e) (.snd e')

  /-- Reduce the scrutinee of a match. -/
  | matchScrut {scrut scrut' branches} :
      Step scrut scrut' →
      Step (.match_ scrut branches) (.match_ scrut' branches)



/-! ### Decidable value / ctor-chain checks -/

mutual

def isValue : Expr → Bool
  | .primLit _ => true
  | .lambda _ _ => true
  | .pair a b => isValue a && isValue b
  | .ctor _ => true
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
    if pat.ctor = name ∧ pat.contents = args.length then
      some (body.substN 0 args)
    else
      findMatchingBranch name args rest

/-! ### Small-step evaluation function -/

/-- Compute one step of CBV reduction, returning `none` if the expression is
    already a value or is stuck (ill-typed / open term). -/
def step : Expr → Option Expr
  | .pair a b =>
    if isValue a then
      if isValue b then none
      else do let b' ← step b; return .pair a b'
    else do let a' ← step a; return .pair a' b

  | .app f arg =>
    if isValue f then
      if isValue arg then
        match f with
        | .lambda _ body => some (body.substN 0 [arg])
        | _ => none
      else do let arg' ← step arg; return .app f arg'
    else do let f' ← step f; return .app f' arg

  | .letIn ann rhs body =>
    if isValue rhs then some (body.substN 0 [rhs])
    else do let rhs' ← step rhs; return .letIn ann rhs' body

  | .fst e =>
    if isValue e then
      match e with
      | .pair v₁ _ => some v₁
      | _ => none
    else do let e' ← step e; return .fst e'

  | .snd e =>
    if isValue e then
      match e with
      | .pair _ v₂ => some v₂
      | _ => none
    else do let e' ← step e; return .snd e'

  | .match_ scrut branches =>
    if isValue scrut then
      match getCtorArgs scrut with
      | some (name, args) => findMatchingBranch name args branches
      | none => none
    else do let scrut' ← step scrut; return .match_ scrut' branches

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
  | lambda ann body _ => exact ⟨⟨fun _ => .lambda ann body, fun _ => rfl⟩, ⟨nofun, nofun⟩⟩
  | ctor name => exact ⟨⟨fun _ => .ctor name, fun _ => rfl⟩, ⟨fun _ => .ctor name, fun _ => rfl⟩⟩
  | pair a b iha ihb =>
    refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨nofun, nofun⟩⟩
    · simp only [isValue, Bool.and_eq_true] at h
      exact .pair (iha.1.mp h.1) (ihb.1.mp h.2)
    · cases h with | pair ha hb =>
      simp only [isValue, Bool.and_eq_true]
      exact ⟨iha.1.mpr ha, ihb.1.mpr hb⟩
  | app f arg ihf iharg =>
    simp only [isValue, isCtorChain, Bool.and_eq_true]
    exact ⟨⟨fun ⟨hf, ha⟩ => .ctorApp (ihf.2.mp hf) (iharg.1.mp ha),
            fun h => by cases h with | ctorApp hc hv => exact ⟨ihf.2.mpr hc, iharg.1.mpr hv⟩⟩,
           ⟨fun ⟨hf, ha⟩ => .app (ihf.2.mp hf) (iharg.1.mp ha),
            fun h => by cases h with | app hc hv => exact ⟨ihf.2.mpr hc, iharg.1.mpr hv⟩⟩⟩
  | var _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | letIn _ _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | fst _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | snd _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩
  | match_ _ _ _ _ => exact ⟨⟨nofun, nofun⟩, ⟨nofun, nofun⟩⟩

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

private theorem findMatchingBranch_to_FirstMatch {name args branches e'}
    (h : findMatchingBranch name args branches = some e') :
    ∃ pat body, FirstMatchingBranch name args.length branches pat body ∧
      e' = body.substN 0 args := by
  induction branches with
  | nil => simp [findMatchingBranch] at h
  | cons hd tl ih =>
    obtain ⟨pat, body⟩ := hd
    simp only [findMatchingBranch] at h
    split at h
    · rename_i hm
      simp at h
      exact ⟨pat, body, .here hm.1 hm.2, h.symm⟩
    · rename_i hnm
      obtain ⟨p, b, hfirst, heq⟩ := ih h
      exact ⟨p, b, .there hnm hfirst, heq⟩

private theorem FirstMatch_to_findMatchingBranch {name : CtorName} {arity : Nat}
    {branches : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (h : FirstMatchingBranch name arity branches pat body)
    {args : List Expr} (hlen : arity = args.length) :
    findMatchingBranch name args branches = some (body.substN 0 args) := by
  induction h with
  | here hctor harity =>
    subst hlen
    simp [findMatchingBranch, hctor, harity]
  | there hnot _ ih =>
    subst hlen
    simp only [findMatchingBranch, if_neg hnot]
    exact ih

private theorem isCtorChain_imp_isValue {e : Expr}
    (h : isCtorChain e = true) : isValue e = true := by
  cases e <;> simp_all [isValue, isCtorChain]

private theorem isValue_step_none {e : Expr} (hv : isValue e = true) :
    step e = none := by
  match e with
  | .primLit _ | .lambda _ _ | .ctor _ => rfl
  | .pair a b =>
    simp only [isValue, Bool.and_eq_true] at hv
    simp [step, hv.1, hv.2]
  | .app f arg =>
    simp only [isValue, Bool.and_eq_true] at hv
    simp only [step, isCtorChain_imp_isValue hv.1, hv.2, ite_true]
    cases f <;> (first | rfl | simp [isCtorChain] at hv)
  | .var _ | .letIn _ _ _ | .fst _ | .snd _ | .match_ _ _ => simp [isValue] at hv

private theorem step_some_not_isValue {e e' : Expr}
    (h : step e = some e') : isValue e = false := by
  cases hv : isValue e with
  | false => rfl
  | true => exact absurd h (by rw [isValue_step_none hv]; nofun)

/-! ### Soundness of `step` w.r.t. the `Step` relation -/

theorem step_sound {e e' : Expr} (h : step e = some e') : Step e e' := by
  induction e using Expr.rec_strong generalizing e' with
  | primLit _ | lambda _ _ _ | ctor _ | var _ => simp [step] at h
  | pair a b iha ihb =>
    unfold step at h
    split at h
    · rename_i hva
      split at h
      · exact nomatch h
      · match hb : step b with
        | .none => simp [hb] at h
        | .some b' =>
          simp [hb] at h; subst h; exact .pairSnd (isValue_iff_IsValue.mp hva) (ihb hb)
    · match ha : step a with
      | .none => simp [ha] at h
      | .some a' => simp [ha] at h; subst h; exact .pairFst (iha ha)
  | app f arg ihf iharg =>
    unfold step at h
    split at h
    · rename_i hvf
      split at h
      · rename_i hvarg
        split at h
        · simp at h; subst h
          exact .beta (isValue_iff_IsValue.mp hvarg)
        · exact nomatch h
      · match harg : step arg with
        | .none => simp [harg] at h
        | .some arg' =>
          simp [harg] at h; subst h; exact .appArg (isValue_iff_IsValue.mp hvf) (iharg harg)
    · match hf : step f with
      | .none => simp [hf] at h
      | .some f' => simp [hf] at h; subst h; exact .appFn (ihf hf)
  | letIn ann rhs body ihrhs _ =>
    unfold step at h
    split at h
    · rename_i hvrhs
      simp at h; subst h
      exact .letReduce (isValue_iff_IsValue.mp hvrhs)
    · match hrhs : step rhs with
      | .none => simp [hrhs] at h
      | .some rhs' => simp [hrhs] at h; subst h; exact .letInRhs (ihrhs hrhs)
  | fst e ih =>
    unfold step at h
    split at h
    · rename_i hve
      split at h
      · simp at h; subst h
        simp only [isValue, Bool.and_eq_true] at hve
        exact .fstReduce (isValue_iff_IsValue.mp hve.1) (isValue_iff_IsValue.mp hve.2)
      · exact nomatch h
    · match he : step e with
      | .none => simp [he] at h
      | .some e' => simp [he] at h; subst h; exact .fstCong (ih he)
  | snd e ih =>
    unfold step at h
    split at h
    · rename_i hve
      split at h
      · simp at h; subst h
        simp only [isValue, Bool.and_eq_true] at hve
        exact .sndReduce (isValue_iff_IsValue.mp hve.1) (isValue_iff_IsValue.mp hve.2)
      · exact nomatch h
    · match he : step e with
      | .none => simp [he] at h
      | .some e' => simp [he] at h; subst h; exact .sndCong (ih he)
  | match_ scrut branches ihscrut _ =>
    unfold step at h
    split at h
    · rename_i hvscrut
      revert h
      cases hga : getCtorArgs scrut with
      | none => intro h; exact nomatch h
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

/-! ### Completeness of `step` w.r.t. the `Step` relation -/

theorem step_complete {e e' : Expr} (h : Step e e') : step e = some e' := by
  induction h with
  | beta hval =>
    have := isValue_iff_IsValue.mpr hval
    unfold step; simp [isValue, this]
  | letReduce hval =>
    have := isValue_iff_IsValue.mpr hval
    unfold step; simp [this]
  | fstReduce hv1 hv2 =>
    have := isValue_iff_IsValue.mpr hv1
    have := isValue_iff_IsValue.mpr hv2
    unfold step; simp [isValue, *]
  | sndReduce hv1 hv2 =>
    have := isValue_iff_IsValue.mpr hv1
    have := isValue_iff_IsValue.mpr hv2
    unfold step; simp [isValue, *]
  | matchReduce hval hctor hfirst =>
    have := isValue_iff_IsValue.mpr hval
    have := getCtorArgs_of_CtorAppliedTo hctor
    have := FirstMatch_to_findMatchingBranch hfirst rfl
    unfold step; simp [*]
  | pairFst _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | pairSnd hval _ ih =>
    have := isValue_iff_IsValue.mpr hval
    have := step_some_not_isValue ih
    unfold step; simp [*]
  | appFn _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | appArg hval _ ih =>
    have hvf := isValue_iff_IsValue.mpr hval
    have hva := step_some_not_isValue ih
    unfold step; simp [hvf, hva, ih]
  | letInRhs _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | fstCong _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | sndCong _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]
  | matchScrut _ ih =>
    have := step_some_not_isValue ih
    unfold step; simp [this, ih]

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
raising the scope bound inside their body. `fst`/`snd` are non-binding
projections and introduce none. -/

mutual

inductive Expr.WellScopedUnder : Nat → Expr → Prop
  | primLit {n p}            : Expr.WellScopedUnder n (.primLit p)
  | ctor    {n c}            : Expr.WellScopedUnder n (.ctor c)
  | var     {n i}            : i < n → Expr.WellScopedUnder n (.var i)
  | pair    {n a b}          :
      Expr.WellScopedUnder n a → Expr.WellScopedUnder n b →
      Expr.WellScopedUnder n (.pair a b)
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
  | fst {n e} :
      Expr.WellScopedUnder n e →
      Expr.WellScopedUnder n (.fst e)
  | snd {n e} :
      Expr.WellScopedUnder n e →
      Expr.WellScopedUnder n (.snd e)
  | match_  {n scrut branches} :
      Expr.WellScopedUnder n scrut →
      Expr.BranchListWellScoped n branches →
      Expr.WellScopedUnder n (.match_ scrut branches)

inductive Expr.BranchListWellScoped : Nat → List (MatchPattern × Expr) → Prop
  | nil  {n}          : Expr.BranchListWellScoped n []
  | cons {n pat body rest} :
      Expr.WellScopedUnder (n + pat.contents) body →
      Expr.BranchListWellScoped n rest →
      Expr.BranchListWellScoped n ((pat, body) :: rest)

end


/-- Instantation doesn't add more bvars than are in `tyArgs` -/
theorem InstantiatesBy.preserves_bvars : (∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg) → InstantiatesBy tyArgs polyTy ty → ContainsBvarsUpTo 0 ty := by
  intro prem hinst
  cases hinst with
  | prim => constructor
  | pair a b
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
  | var : AllMatchesExhaustive ctors (.var n)
  | ctor : AllMatchesExhaustive ctors (.ctor name)
  | pair :
    AllMatchesExhaustive ctors a → AllMatchesExhaustive ctors b →
    AllMatchesExhaustive ctors (.pair a b)
  | lambda :
    AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.lambda ann body)
  | app :
    AllMatchesExhaustive ctors f → AllMatchesExhaustive ctors arg →
    AllMatchesExhaustive ctors (.app f arg)
  | letIn :
    AllMatchesExhaustive ctors rhs → AllMatchesExhaustive ctors body →
    AllMatchesExhaustive ctors (.letIn ann rhs body)
  | fst :
    AllMatchesExhaustive ctors e →
    AllMatchesExhaustive ctors (.fst e)
  | snd :
    AllMatchesExhaustive ctors e →
    AllMatchesExhaustive ctors (.snd e)
  /-- Exhaustiveness for match: every constructor in the ctor env whose type
      matches `tyName` has a corresponding branch. The `tyName` is existentially
      quantified — the caller picks it (typically from the typing derivation) —
      but it is pinned to the branches: every branch's pattern must be a
      constructor of `tyName`, so a bogus ctor-less type cannot be chosen. -/
  | match_ {tyName : TyName} :
    AllMatchesExhaustive ctors scrut →
    AllBranchBodiesExhaustive ctors branches →
    (∀ pat body, (pat, body) ∈ branches →
       ∃ ctor, LookupList.get? ctors pat.ctor = some ctor ∧ ctor.tyName = tyName) →
    (∀ (ctorName : CtorName) (ctor : Ctor),
      LookupList.get? ctors ctorName = some ctor →
      ctor.tyName = tyName →
      ∃ pat body, (pat, body) ∈ branches ∧ pat.ctor = ctorName ∧
        pat.contents = ctor.contents.length) →
    AllMatchesExhaustive ctors (.match_ scrut branches)

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
    (h : ∃ pat body, (pat, body) ∈ branches ∧ pat.ctor = name ∧
         pat.contents = args.length) :
    ∃ e', findMatchingBranch name args branches = some e' := by
  induction branches with
  | nil => obtain ⟨_, _, hmem, _⟩ := h; exact nomatch hmem
  | cons hd tl ih =>
    obtain ⟨pat, body, hmem, hctor, harity⟩ := h
    unfold findMatchingBranch
    split
    · exact ⟨_, rfl⟩
    · rename_i hnm
      cases hmem with
      | head _ => exact absurd (And.intro hctor harity) hnm
      | tail _ hmem' => exact ih ⟨pat, body, hmem', hctor, harity⟩


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
  | .pair a b        => .pair (Ty.substFvar Z U a) (Ty.substFvar Z U b)
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


/-! ### Freshness packaging. -/

/-- `Xs` is a list of `n` distinct names, all disjoint from `L`. -/
structure FreshNames (L : List Nat) (n : Nat) (Xs : List Nat) : Prop where
  length : Xs.length = n
  nodup  : Xs.Nodup
  avoid  : ∀ x ∈ Xs, x ∉ L


/-! ### Generic-instance ordering on schemes ("at least as general as"). -/

/-- **Generic-instance ordering** (Damas–Milner `⊑`): `σgen.AtLeastAsGeneralAs
    σann` says the inferred scheme `σgen` is *at least as general as* the
    annotation `σann` — equivalently, `σann` is a generic instance of `σgen`.

    Read it operationally: freeze `σann`'s quantifiers as fresh **rigid** names
    `Ys`; the resulting monotype must be reachable by **some** instantiation `Vs`
    of `σgen`. The `∀ fresh Ys / ∃ Vs` shape *is* the rigid (annotation) /
    flexible (inferred) asymmetry — both sides are just `fvar`s, only the
    quantifier differs. `Vs` may mention the `Ys` (that's how `∀a.a→a` is a
    generic instance of itself, via `Vs = [.fvar Y]`).

    This is the *declarative* condition a polymorphic `let` annotation must
    satisfy. By principal types it is equivalent to "`boundExpr` types at every
    fresh opening of `σann`", so the annotated `letIn` rule needs no new
    premise — but the **algorithm** can't quantify over all openings, so it
    decides this relation directly (`polyTyAtLeastAsGeneral?` in `InferW`).

    The cofinite `∃ L, ∀ Ys, FreshNames L …` wrapper matches the let rule's
    treatment of freshness, so this relation survives `weaken_env`/`subst_lemma`
    the same way. -/
def PolyTy.AtLeastAsGeneralAs (σgen σann : PolyTy) : Prop :=
  ∃ L : List Nat, ∀ Ys : List Nat, FreshNames L σann.paramCount Ys →
    ∃ Vs : List Ty, Ty.AreLC σgen.paramCount Vs ∧
      σgen.openWith Vs = σann.openVars Ys


/-! ### The declarative typing relation `TypeOfHM`.

Syntax-directed Hindley–Milner typing. All rules are standard except the
let-generalising rule (`letIn`), which uses a **cofinite**
"for-all-fresh" premise to express generalisation (see the module doc above):

```
  PolyTy.WF M →
  (∀ Xs, FreshNames L M.paramCount Xs → TypeOfHM ctx boundExpr (M.openVars Xs)) →
  bodyCtx = { ctx with env := M :: ctx.env } →
  TypeOfHM bodyCtx body bodyTy →
  TypeOfHM ctx (.letIn ann boundExpr body) bodyTy
```

The cofinite premise's IH is *universally quantified in `Xs`*, so when
`subst_lemma`/`weaken_env` descend through a `letIn` and the env grows, they
re-instantiate it at names fresh for the bigger env — no side conditions.

`var`/`ctor`/`match_` instantiate schemes via `InstantiatesBy` (equivalent to
`openWith` on a well-formed scheme). -/

mutual

/-- Cofinite (locally-nameless-style) declarative typing relation. -/
inductive TypeOfHM : Ctx → Expr → Ty → Prop
  | primLitUnit :
    TypeOfHM ctx (.primLit .unit) (.prim .unit)

  | primLitInt :
    TypeOfHM ctx (.primLit (.int n)) (.prim .int)

  | primLitNat :
    TypeOfHM ctx (.primLit (.nat n)) (.prim .nat)

  | primLitBool :
    TypeOfHM ctx (.primLit (.bool b)) (.prim .bool)

  | primLitStr :
    TypeOfHM ctx (.primLit (.str s)) (.prim .str)

  | pair :
    TypeOfHM ctx fst fstTy →
    TypeOfHM ctx snd sndTy →
    TypeOfHM ctx (.pair fst snd) (.pair fstTy sndTy)

  | lambda :
    ContainsBvarsUpTo 0 paramTy →
    -- When a parameter annotation is present it pins the param type, and that
    -- annotation must be a closed type (no free type vars) — this keeps the
    -- annotation stable under `typ_subst_preservation`. (HM param annotations
    -- are monotypes; closedness defers scoped-type-variable support.)
    --
    -- @TODO: drop the `NoFreeVars paramTy` conjunct to allow annotations that
    -- reference type variables from an enclosing scope (Elm/ScopedTypeVariables
    -- style). Doing so requires `typ_subst_preservation` to also substitute into
    -- the term's annotations (an `Expr.substTyFvar Z U` pushed through binders),
    -- so that `[Z↦U]` stays consistent with a non-closed annotation.
    (∀ T, ann = some T → paramTy = T ∧ NoFreeVars paramTy) →
    bodyCtx = { ctx with env := PolyTy.mkTrivial paramTy :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.lambda ann body) (.arrow paramTy bodyTy)

  | app :
    TypeOfHM ctx f (.arrow argTy retTy) →
    TypeOfHM ctx input argTy →
    TypeOfHM ctx (.app f input) retTy

  /-- Cofinite let-generalisation. See module doc above. `M` is the
      generalised scheme; the premise says `boundExpr` types at *every*
      sufficiently-fresh opening of `M`.

      NOTE: no value restriction — our language is pure (no effects/refs), so
      generalising an arbitrary let-bound expression is sound (plain
      Damas–Milner). Chargueraud needs `value boundExpr` only because mini-ML
      has mutable refs. -/
  | letIn {M : PolyTy} {L : List Nat} :
    PolyTy.WF M →
    -- When a scheme annotation is present, the generalised scheme *is* the
    -- annotation `σ`. The cofinite premise below (`boundExpr` types at every
    -- fresh opening of `M = σ`) then enforces "the annotation is not more
    -- general than `boundExpr` actually is" for free. `σ` must be a closed
    -- scheme (its body has no free type vars) to stay stable under
    -- `typ_subst_preservation`.
    --
    -- @TODO: drop the `NoFreeVars σ.body` conjunct to allow let-signatures that
    -- reference enclosing-scope type variables (see the matching note on the
    -- `lambda` rule); needs the same `Expr.substTyFvar` in preservation.
    (∀ σ, ann = some σ → M = σ ∧ NoFreeVars σ.body) →
    (∀ Xs : List Nat, FreshNames L M.paramCount Xs →
        TypeOfHM ctx boundExpr (M.openVars Xs)) →
    bodyCtx = { ctx with env := M :: ctx.env } →
    TypeOfHM bodyCtx body bodyTy →
    TypeOfHM ctx (.letIn ann boundExpr body) bodyTy

  /-- First projection: a monomorphic destructor of a pair type. -/
  | fst :
    TypeOfHM ctx e (.pair fstTy sndTy) →
    TypeOfHM ctx (.fst e) fstTy

  /-- Second projection: a monomorphic destructor of a pair type. -/
  | snd :
    TypeOfHM ctx e (.pair fstTy sndTy) →
    TypeOfHM ctx (.snd e) sndTy

  | var :
    ctx.env[dbl]? = some polyTy →
    (∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg) →
    InstantiatesBy tyArgs polyTy.body ty →
    TypeOfHM ctx (.var dbl) ty

  | ctor :
    LookupList.get? ctx.ctors name = some ctor →
    (∀ tyArg ∈ tyArgs, ContainsBvarsUpTo 0 tyArg) →
    InstantiatesBy tyArgs ctor.toTy.body ty →
    TypeOfHM ctx (.ctor name) ty

  | match_ :
    TypeOfHM ctx scrutinee (.customTy tyName tyArgs) →
    branches ≠ [] →
    (∀ branch ∈ branches, TypeOfMatchBranch ctx branch tyName tyArgs resultTy) →
    TypeOfHM ctx (.match_ scrutinee branches) resultTy


/-- Match-branch typing for `TypeOfHM`. Verbatim copy of `TypeOfMatchBranch`
    with the relation renamed: pattern bindings are monomorphic (`Sch 0`), so
    no cofinite type-var quantifier is needed, and the term-var quantifier
    vanishes under de Bruijn levels. -/
inductive TypeOfMatchBranch :
  (ctx : Ctx) → (MatchPattern × Expr) → (tyName : TyName) → (tyArgs : List Ty) → (resultTy : Ty) → Prop
  | mk {ctor : Ctor} {ctx : Ctx} {pattern : MatchPattern} :
    LookupList.get? ctx.ctors pattern.ctor = some ctor →
    ctor.tyName = tyName →
    ctor.paramCount = tyArgs.length →
    pattern.contents = ctor.contents.length →
    List.Forall₂ (InstantiatesBy tyArgs) ctor.contents instContents →
    patternBindings = instContents.map PolyTy.mkTrivial →
    bodyCtx = {ctx with env := patternBindings ++ ctx.env} →
    TypeOfHM bodyCtx bodyExpr resultTy →
    TypeOfMatchBranch ctx (pattern, bodyExpr) tyName tyArgs resultTy

end


/-! ### Cofinite typing-at-scheme predicates. -/

/-- `t` types at *every* opening of `M` by sufficiently-fresh names. The `L`
    is the cofinite exclusion set; existentially quantified at the use site.
    This is exactly the cofinite premise of `TypeOfHM.letIn`, packaged. -/
def HasSchemeVars (L : List Nat) (ctx : Ctx) (e : Expr) (M : PolyTy) : Prop :=
  ∀ Xs : List Nat, FreshNames L M.paramCount Xs →
    TypeOfHM ctx e (M.openVars Xs)

/-- `t` types at *every* type-level instance of `M` (by LC types of the
    right arity). This is what `subst_lemma`'s `u` premise demands. -/
def HasScheme (ctx : Ctx) (e : Expr) (M : PolyTy) : Prop :=
  ∀ Vs : List Ty, Ty.AreLC M.paramCount Vs →
    TypeOfHM ctx e (M.openWith Vs)


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
  | pair a b ih_a ih_b =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or] at h
    simp only [Ty.substFvar, Ty.pair.injEq]
    exact ⟨ih_a h.1, ih_b h.2⟩
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
  | pair a b ih_a ih_b =>
    cases h with
    | pair h_a h_b =>
      simp only [Ty.instantiate, Ty.pair.injEq]
      exact ⟨ih_a h_a, ih_b h_b⟩
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
  | pair a b ih_a ih_b =>
    simp only [Ty.instantiate, Ty.substFvar, Ty.pair.injEq]
    exact ⟨ih_a, ih_b⟩
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

theorem Ty.substFvars_pair {pairs : List (Nat × Ty)} {a b : Ty} :
    Ty.substFvars pairs (.pair a b)
      = .pair (Ty.substFvars pairs a) (Ty.substFvars pairs b) := by
  induction pairs generalizing a b with
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
  | pair a b ih_a ih_b =>
    simp only [Ty.instantiate]
    rw [Ty.substFvars_pair]
    have ha : ∀ X ∈ Xs, X ∉ a.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inl hc)
    have hb : ∀ X ∈ Xs, X ∉ b.freeVars := fun X hX hc =>
      h_Xs_fresh_ty X hX (by simp only [Ty.freeVars, List.mem_dedup, List.mem_append]; exact .inr hc)
    rw [ih_a ha, ih_b hb]
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


/-! ### `substFvar` interaction with the typing-side predicates.

Helpers needed by `typ_subst_preservation`. -/

/-- `substFvar` by an LC type preserves local-closedness. (The `bvar` case is
    vacuous: an LC type has no bvars.) -/
theorem Ty.IsLC.substFvar {Z : Nat} {U ty : Ty}
    (h_U : Ty.IsLC U) (h : Ty.IsLC ty) :
    Ty.IsLC (Ty.substFvar Z U ty) := by
  induction ty using Ty.rec_strong with
  | prim _ => exact .prim
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair a b iha ihb =>
    cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair _ _ iha ihb => exact .pair iha ihb
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
  | pair a b iha ihb => cases h with | pair ha hb => exact .pair (iha ha) (ihb hb)
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
  | pair _ _ iha ihb =>
    simp only [Ty.freeVars, List.mem_dedup, List.mem_append, not_or]; exact ⟨iha, ihb⟩
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

/-- Type-substitution preserves typing. Substituting a single fresh type
    variable `Z` (one not appearing in the outer env) by any LC type `U`
    preserves the typing derivation.

    Chargueraud's `typing_typ_subst`. -/
theorem TypeOfHM.typ_subst_preservation
    {ctors : CtorEnv} {env_post env_outer : Env}
    {e : Expr} {τ : Ty} {Z : Nat} {U : Ty}
    (h_Z_fresh_outer : Z ∉ env_outer.freeVars)
    (h_U_lc : U.IsLC)
    (h : TypeOfHM ⟨env_post ++ env_outer, ctors⟩ e τ) :
    TypeOfHM ⟨env_post.substFvar Z U ++ env_outer, ctors⟩ e (Ty.substFvar Z U τ) := by
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | pair a b ih_a ih_b =>
    cases h with
    | pair ha hb =>
      simp only [Ty.substFvar]
      exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h with
    | app hf hi =>
      have hf' := ih_f hf
      simp only [Ty.substFvar] at hf'
      exact .app hf' (ih_i hi)
  | lambda ann body ih =>
    cases h with
    | lambda hparamLC hann heq hbody =>
      subst heq
      simp only [Ty.substFvar]
      refine TypeOfHM.lambda (Ty.IsLC.substFvar h_U_lc hparamLC) ?_ rfl ?_
      · intro T hT
        obtain ⟨hpeq, hpnfv⟩ := hann T hT
        rw [Ty.substFvar_fresh (hpnfv.not_mem_freeVars Z)]
        exact ⟨hpeq, hpnfv⟩
      have hb := ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody
      simpa only [Env.substFvar, List.map_cons, PolyTy.substFvar, PolyTy.mkTrivial,
        List.cons_append] using hb
  | var dbl =>
    cases h with
    | var hlook htyargs hinst =>
      have hlook' := congrArg (Option.map (PolyTy.substFvar Z U)) hlook
      simp only [Option.map_some] at hlook'
      rw [← List.getElem?_map] at hlook'
      have henv : env_post.substFvar Z U ++ env_outer
          = (env_post ++ env_outer).map (PolyTy.substFvar Z U) := by
        show Env.substFvar Z U env_post ++ env_outer
          = Env.substFvar Z U (env_post ++ env_outer)
        rw [Env.substFvar_append, Env.substFvar_fresh h_Z_fresh_outer]
      rw [← henv] at hlook'
      refine TypeOfHM.var hlook' ?_ (InstantiatesBy.substFvar h_U_lc hinst)
      intro tyArg hmem
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
      exact Ty.IsLC.substFvar h_U_lc (htyargs t ht)
  | letIn ann boundExpr body ih_be ih_body =>
    cases h with
    | letIn hsch hann hcofin heq hbodyinner =>
      subst heq
      expose_names
      refine TypeOfHM.letIn (M := PolyTy.substFvar Z U M) (L := Z :: L)
        (PolyTy.WF.substFvar h_U_lc hsch) ?_ ?_ rfl ?_
      · intro σ hσ
        obtain ⟨hMeq, hnfv⟩ := hann σ hσ
        rw [hMeq]
        exact ⟨PolyTy.substFvar_eq_self_of_closed hnfv, hnfv⟩
      · intro Xs hfresh
        have hZ_notin : Z ∉ Xs := fun hc => hfresh.avoid Z hc List.mem_cons_self
        have hXs_freshL : FreshNames L M.paramCount Xs :=
          ⟨by simpa using hfresh.length, hfresh.nodup,
           fun x hx hc => hfresh.avoid x hx (List.mem_cons_of_mem _ hc)⟩
        have hbe := ih_be (hcofin Xs hXs_freshL)
        have hopen : (M.substFvar Z U).openVars Xs = Ty.substFvar Z U (M.openVars Xs) := by
          unfold PolyTy.openVars PolyTy.substFvar
          exact (Ty.substFvar_openVars h_U_lc hZ_notin).symm
        rw [hopen]
        exact hbe
      · have hb := ih_body (env_post := M :: env_post) hbodyinner
        simpa only [Env.substFvar, List.map_cons, List.cons_append] using hb
  | fst e ih =>
    cases h with
    | fst he =>
      have he' := ih he
      simp only [Ty.substFvar] at he'
      exact .fst he'
  | snd e ih =>
    cases h with
    | snd he =>
      have he' := ih he
      simp only [Ty.substFvar] at he'
      exact .snd he'
  | ctor name =>
    cases h with
    | ctor hlook htyargs hinst =>
      expose_names
      have hbody := InstantiatesBy.substFvar (Z := Z) (U := U) h_U_lc hinst
      rw [Ty.substFvar_fresh
          (NoFreeVars.not_mem_freeVars (Ctor.toTy_body_noFreeVars ctor) Z)] at hbody
      refine TypeOfHM.ctor hlook ?_ hbody
      intro tyArg hmem
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hmem
      exact Ty.IsLC.substFvar h_U_lc (htyargs t ht)
  | match_ scrut branches ih_scrut ih_branches =>
    cases h with
    | match_ hscrut hne hbrs =>
      have hscrut' := ih_scrut hscrut
      simp only [Ty.substFvar, TyList.substFvar_eq_map] at hscrut'
      refine TypeOfHM.match_ hscrut' hne ?_
      clear ih_scrut hscrut hscrut' hne
      revert hbrs ih_branches
      induction branches with
      | nil =>
        intro _ _ b hmem
        exact absurd hmem List.not_mem_nil
      | cons hd tl ih_tl =>
        intro ih_branches hbrs branch hmem
        obtain ⟨pat, body⟩ := hd
        simp only [List.mem_cons] at hmem
        cases hmem with
        | inl heq =>
          subst heq
          have hbranch := hbrs (pat, body) List.mem_cons_self
          cases hbranch with
          | mk hlook htyName hpc hcontents hinstC hpb hctx hbodyT =>
            subst hctx; subst hpb
            expose_names
            -- ctor.contents are closed, so substFvar leaves them fixed
            have hcc : ctor.contents.map (Ty.substFvar Z U) = ctor.contents := by
              have hpt : ∀ c ∈ ctor.contents, Ty.substFvar Z U c = id c := fun c hc =>
                Ty.substFvar_fresh ((ctor.closed c hc).not_mem_freeVars Z)
              rw [List.map_congr_left hpt, List.map_id]
            have hinstC' := InstantiatesBy.forall2_substFvar (Z := Z) (U := U) h_U_lc hinstC
            rw [hcc] at hinstC'
            -- recurse on the branch body (reassociate env first)
            rw [show instContents.map PolyTy.mkTrivial ++ (env_post ++ env_outer)
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ env_outer
                  from (List.append_assoc _ _ _).symm] at hbodyT
            have hib := ih_branches pat body List.mem_cons_self
              (env_post := instContents.map PolyTy.mkTrivial ++ env_post) hbodyT
            rw [Env.substFvar_append, Env.substFvar_map_mkTrivial,
                List.append_assoc] at hib
            exact TypeOfMatchBranch.mk hlook htyName (by simpa using hpc)
              hcontents hinstC' rfl rfl hib
        | inr hmem' =>
          exact ih_tl
            (fun pat' e' hm => ih_branches pat' e' (List.mem_cons_of_mem _ hm))
            (fun b hm => hbrs b (List.mem_cons_of_mem _ hm))
            branch hmem'

/- Values are preserved under `shiftFrom` (it only renumbers free term vars,
   leaving the value shape intact). Mutual with `IsCtorChain.shiftFrom`. -/
mutual
theorem SmallStep.IsValue.shiftFrom {e : Expr} (k n : Nat)
    (h : SmallStep.IsValue e) : SmallStep.IsValue (e.shiftFrom k n) := by
  cases h with
  | primLit p => exact .primLit p
  | lambda ann body => exact .lambda _ _
  | pair h1 h2 => exact .pair (h1.shiftFrom k n) (h2.shiftFrom k n)
  | ctor name => exact .ctor name
  | ctorApp hf hv => exact .ctorApp (hf.shiftFrom k n) (hv.shiftFrom k n)
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
theorem TypeOfHM.weaken_env
    {ctors : CtorEnv} {env_pre env_extra env : Env} {e : Expr} {τ : Ty}
    (h : TypeOfHM ⟨env_pre ++ env, ctors⟩ e τ) :
    TypeOfHM ⟨env_pre ++ env_extra ++ env, ctors⟩
      (e.shiftFrom env_pre.length env_extra.length) τ := by
  induction e using Expr.rec_strong generalizing env_pre τ with
  | primLit p =>
    cases h with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | pair a b ih_a ih_b =>
    cases h with
    | pair ha hb =>
      simp only [Expr.shiftFrom]
      exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h with
    | app hf hi =>
      simp only [Expr.shiftFrom]
      exact .app (ih_f hf) (ih_i hi)
  | var i =>
    cases h with
    | var h_lookup h_tyArgs_closed h_inst =>
      simp only [Expr.shiftFrom]
      by_cases h_lt : i < env_pre.length
      · rw [if_pos h_lt]
        refine .var ?_ h_tyArgs_closed h_inst
        show (env_pre ++ env_extra ++ env)[i]? = _
        rw [List.getElem?_append_left
              (by simp only [List.length_append]; omega :
                  i < (env_pre ++ env_extra).length)]
        rw [List.getElem?_append_left h_lt]
        have h_lookup' : (env_pre ++ env)[i]? = _ := h_lookup
        rw [List.getElem?_append_left h_lt] at h_lookup'
        exact h_lookup'
      · push_neg at h_lt
        rw [if_neg (Nat.not_lt.mpr h_lt)]
        refine .var ?_ h_tyArgs_closed h_inst
        show (env_pre ++ env_extra ++ env)[i + env_extra.length]? = _
        have h_left : (env_pre ++ env_extra).length ≤ i + env_extra.length := by
          simp only [List.length_append]; omega
        rw [List.getElem?_append_right h_left]
        have h_eq_idx :
            i + env_extra.length - (env_pre ++ env_extra).length
            = i - env_pre.length := by
          simp only [List.length_append]; omega
        rw [h_eq_idx]
        have h_lookup' : (env_pre ++ env)[i]? = _ := h_lookup
        rw [List.getElem?_append_right h_lt] at h_lookup'
        exact h_lookup'
  | lambda ann body ih =>
    cases h with
    | lambda h_paramTy_closed hann h_eq h_body_lam =>
      subst h_eq
      simp only [Expr.shiftFrom]
      refine TypeOfHM.lambda h_paramTy_closed hann rfl ?_
      exact ih (env_pre := PolyTy.mkTrivial _ :: env_pre) h_body_lam
  | letIn ann boundExpr body ih_be ih_body =>
    cases h with
    | letIn hsch hann hcofin heq hbodyinner =>
      subst heq
      expose_names
      simp only [Expr.shiftFrom]
      refine TypeOfHM.letIn (M := M) (L := L) hsch hann ?_ rfl ?_
      · intro Xs hfresh
        exact ih_be (hcofin Xs hfresh)
      · exact ih_body (env_pre := M :: env_pre) hbodyinner
  | fst e ih =>
    cases h with
    | fst he =>
      simp only [Expr.shiftFrom]
      exact .fst (ih he)
  | snd e ih =>
    cases h with
    | snd he =>
      simp only [Expr.shiftFrom]
      exact .snd (ih he)
  | ctor name =>
    cases h with
    | ctor hlook htyargs hinst =>
      exact .ctor hlook htyargs hinst
  | match_ scrutinee branches ihs ihbs =>
    cases h with
    | match_ h_scrut h_ne h_brs =>
      simp only [Expr.shiftFrom]
      have h_shift_nonempty :
          BranchList.shiftFrom env_pre.length env_extra.length branches ≠ [] := by
        intro h_eq
        cases branches with
        | nil => exact h_ne rfl
        | cons _ _ => simp [BranchList.shiftFrom] at h_eq
      refine TypeOfHM.match_ (ihs h_scrut) h_shift_nonempty ?_
      clear ihs h_scrut h_ne h_shift_nonempty
      revert h_brs ihbs
      induction branches with
      | nil =>
        intro _ _ b h_mem
        simp [BranchList.shiftFrom] at h_mem
      | cons hd tl ih_tl =>
        intro ihbs h_brs branch h_mem
        obtain ⟨pat, body⟩ := hd
        simp only [BranchList.shiftFrom, List.mem_cons] at h_mem
        cases h_mem with
        | inl h_eq =>
          subst h_eq
          have h_branch := h_brs (pat, body) List.mem_cons_self
          cases h_branch with
          | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body =>
            subst h_ctx
            subst h_pb
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_pre ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_pre) ++ env
                  from (List.append_assoc _ _ _).symm] at h_body
            have ih_body :=
              ihbs pat body List.mem_cons_self
                (env_pre := instContents.map PolyTy.mkTrivial ++ env_pre)
                h_body
            simp only [List.length_append, List.length_map] at ih_body
            rw [← h_inst.length_eq, ← h_contents] at ih_body
            rw [show pat.contents + env_pre.length = env_pre.length + pat.contents
                  from Nat.add_comm _ _] at ih_body
            refine TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
              h_inst rfl rfl ?_
            rw [List.append_assoc, List.append_assoc] at ih_body
            rw [show env_pre ++ env_extra ++ env = env_pre ++ (env_extra ++ env)
                  from List.append_assoc _ _ _]
            exact ih_body
        | inr h_mem' =>
          exact ih_tl
            (fun pat' e' hmem => ihbs pat' e' (List.mem_cons_of_mem _ hmem))
            (fun branch hmem => h_brs branch (List.mem_cons_of_mem _ hmem))
            branch h_mem'

/-- Iterated type substitution preserves typing: substituting each `(Zᵢ, Uᵢ)`
    in turn (with every `Zᵢ` fresh for the env and every `Uᵢ` locally closed)
    preserves the derivation. Chargueraud's `typing_typ_substs`. -/
theorem TypeOfHM.typ_substs_preservation {ctx : Ctx} {e : Expr}
    (pairs : List (Nat × Ty))
    (h_fresh : ∀ p ∈ pairs, p.1 ∉ ctx.env.freeVars)
    (h_lc : ∀ p ∈ pairs, Ty.IsLC p.2)
    {τ : Ty} (h : TypeOfHM ctx e τ) :
    TypeOfHM ctx e (Ty.substFvars pairs τ) := by
  induction pairs generalizing τ with
  | nil => exact h
  | cons hd tl ih =>
    obtain ⟨Z, U⟩ := hd
    simp only [Ty.substFvars]
    refine ih (fun p hp => h_fresh p (List.mem_cons_of_mem _ hp))
              (fun p hp => h_lc p (List.mem_cons_of_mem _ hp)) ?_
    have hZ : Z ∉ ctx.env.freeVars := h_fresh (Z, U) List.mem_cons_self
    have hU : Ty.IsLC U := h_lc (Z, U) List.mem_cons_self
    exact TypeOfHM.typ_subst_preservation (env_post := []) (env_outer := ctx.env)
      (ctors := ctx.ctors) hZ hU h

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

/-- The bridge: a cofinite-vars witness gives a "for-all-instances" witness.
    Chargueraud's `has_scheme_from_vars`. For any `Vs`, pick `Xs` fresh for
    everything relevant, use the cofinite witness at `Xs`, then iteratively
    `typ_subst_preservation`-substitute each `Xᵢ ↦ Vᵢ` (the
    `openWith = substFvars ∘ openVars` identity bridges the two openings). -/
theorem HasScheme.fromHasSchemeVars
    {L : List Nat} {ctx : Ctx} {e : Expr} {M : PolyTy}
    (h : HasSchemeVars L ctx e M) :
    HasScheme ctx e M := by
  intro Vs hVs
  obtain ⟨hVlen, hVlc⟩ := hVs
  obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ :=
    exists_fresh_names
      (L ++ M.body.freeVars ++ Ty.freeVarsList Vs ++ ctx.env.freeVars) M.paramCount
  -- split the combined freshness into its four parts
  have hX_L : ∀ x ∈ Xs, x ∉ L := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_Mbody : ∀ x ∈ Xs, x ∉ M.body.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_Vs : ∀ x ∈ Xs, x ∉ Ty.freeVarsList Vs := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hX_env : ∀ x ∈ Xs, x ∉ ctx.env.freeVars := fun x hx hc =>
    hXavoid x hx (by simp only [List.mem_append]; tauto)
  have hVlen' : Vs.length = Xs.length := by rw [hVlen, hXlen]
  -- the cofinite witness, instantiated at our fresh Xs
  have hwit := h Xs ⟨hXlen, hXnodup, hX_L⟩
  -- bridge openWith to substFvars ∘ openVars
  have hrewrite : M.openWith Vs = Ty.substFvars (Xs.zip Vs) (M.openVars Xs) := by
    unfold PolyTy.openWith PolyTy.openVars
    exact Ty.openWith_eq_substFvars_openVars ⟨hVlen', hVlc⟩ hXnodup hX_Mbody hX_Vs
  show TypeOfHM ctx e (M.openWith Vs)
  rw [hrewrite]
  refine TypeOfHM.typ_substs_preservation (Xs.zip Vs) ?_ ?_ hwit
  · intro p hp
    exact hX_env p.1 (List.of_mem_zip hp).1
  · intro p hp
    exact hVlc p.2 (List.of_mem_zip hp).2

/-- Instantiation with the "identity on bvars" substitution is a no-op. Used
    in `HasScheme.ofTypeOfHM` to show that opening an arity-0 scheme with the
    empty arg list returns the underlying type unchanged. -/
private theorem Ty.instantiate_bvar_id {ty : Ty} :
    Ty.instantiate (fun i => .bvar i) ty = ty := by
  induction ty using Ty.rec_strong with
  | prim _ => rfl
  | pair _ _ ih_a ih_b =>
    simp only [Ty.instantiate, Ty.pair.injEq]; exact ⟨ih_a, ih_b⟩
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
theorem HasScheme.ofTypeOfHM
    {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOfHM ctx e τ) :
    HasScheme ctx e (PolyTy.mkTrivial τ) := by
  intro Vs h_lc
  obtain ⟨h_len, _⟩ := h_lc
  -- PolyTy.mkTrivial τ has paramCount = 0, so Vs = []
  have h_vs_nil : Vs = [] := List.length_eq_zero_iff.mp h_len
  subst h_vs_nil
  show TypeOfHM ctx e (PolyTy.openWith [] (PolyTy.mkTrivial τ))
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
  | pair h1 h2 => exact .pair (h1.substN k vs) (h2.substN k vs)
  | ctor name => exact .ctor name
  | ctorApp hf hv => exact .ctorApp (hf.substN k vs) (hv.substN k vs)
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
  | pair a b iha ihb =>
    cases h_bv with
    | pair hba hbb =>
      cases h with
      | pair ha hb =>
        simp only [Ty.openWith, Ty.instantiate] at *
        rw [iha ha hba, ihb hb hbb]
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


/-! ### The clean substitution lemma (no side condition!). -/

/-- Chargueraud's `typing_trm_subst`, adapted to our de-Bruijn-level
    term-var encoding. Substituting `v` (a value) for the variable at
    position `env_post.length` preserves typing, provided `v` types at
    every instance of the scheme `M` that bound that variable.

    For beta-reduction, `M = PolyTy.mkTrivial paramTy` and
    `HasScheme ctx v (mkTrivial paramTy)` reduces to `TypeOfHM ctx v paramTy`
    via `HasScheme.ofTypeOfHM`.

    For let-reduction, `M` is the generalised scheme and `HasScheme` is
    obtained via `HasScheme.fromHasSchemeVars` from the cofinite premise of
    the `letIn` rule that introduced `M`. -/
theorem TypeOfHM.subst_lemma
    {ctors : CtorEnv} {env_post env : Env}
    {e : Expr} {τ : Ty} {M : PolyTy} {v : Expr}
    (h_M_wf : M.WF)
    (h_body : TypeOfHM ⟨env_post ++ [M] ++ env, ctors⟩ e τ)
    (h_v : HasScheme ⟨env, ctors⟩ v M) :
    TypeOfHM ⟨env_post ++ env, ctors⟩
      (e.substN env_post.length [v]) τ := by
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h_body with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | pair a b ih_a ih_b =>
    cases h_body with
    | pair ha hb =>
      simp only [Expr.substN]
      exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h_body with
    | app hf hi =>
      simp only [Expr.substN]
      exact .app (ih_f hf) (ih_i hi)
  | lambda ann body ih =>
    cases h_body with
    | lambda hpc hann heq hbody =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.lambda hpc hann rfl ?_
      exact ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody
  | letIn ann boundExpr body ih_be ih_body =>
    cases h_body with
    | letIn hsch hann hcofin heq hbodyinner =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.letIn hsch hann
        (fun Xs hfresh => ih_be (hcofin Xs hfresh)) rfl ?_
      exact ih_body (env_post := _ :: env_post) hbodyinner
  | fst e ih =>
    cases h_body with
    | fst he =>
      simp only [Expr.substN]
      exact .fst (ih he)
  | snd e ih =>
    cases h_body with
    | snd he =>
      simp only [Expr.substN]
      exact .snd (ih he)
  | ctor name =>
    cases h_body with
    | ctor hlook htyargs hinst =>
      exact .ctor hlook htyargs hinst
  | var i =>
    cases h_body with
    | var h_lookup h_tyArgs_closed h_inst =>
      rcases lt_trichotomy i env_post.length with h_lt | h_eq | h_gt
      · -- i < env_post.length: substN keeps `.var i`
        have h_subst : (Expr.var i).substN env_post.length [v] = .var i := by
          simp [Expr.substN, h_lt]
        rw [h_subst]
        refine .var ?_ h_tyArgs_closed h_inst
        show (env_post ++ env)[i]? = _
        rw [List.getElem?_append_left h_lt]
        rw [List.append_assoc, List.getElem?_append_left h_lt] at h_lookup
        exact h_lookup
      · -- i = env_post.length: the substituted position
        subst h_eq
        have h_subst : (Expr.var env_post.length).substN env_post.length [v]
            = v.shiftFrom 0 env_post.length := by simp [Expr.substN]
        rw [h_subst]
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _),
            Nat.sub_self] at h_lookup
        simp only [List.singleton_append, List.getElem?_cons_zero,
          Option.some.injEq] at h_lookup
        subst h_lookup
        expose_names
        -- `h_inst : InstantiatesBy tyArgs M.body τ`; produce `v : τ` from `h_v`
        set Vs := (List.range M.paramCount).map
            (fun i => (tyArgs[i]?).getD (Ty.prim PrimTy.unit)) with hVs
        have hVs_lc : Ty.AreLC M.paramCount Vs := by
          refine ⟨by simp [hVs], ?_⟩
          intro V hV
          simp only [hVs, List.mem_map, List.mem_range] at hV
          obtain ⟨j, _, rfl⟩ := hV
          cases htj : tyArgs[j]? with
          | none => simp only [Option.getD_none]; exact .prim
          | some t =>
            simp only [Option.getD_some]
            exact h_tyArgs_closed t (List.mem_of_getElem? htj)
        have hτ : τ = M.openWith Vs := by
          have := InstantiatesBy.eq_openWith_range h_inst h_M_wf
          simpa [hVs, PolyTy.openWith] using this
        have hv_typed : TypeOfHM ⟨env, ctors⟩ v τ := by
          rw [hτ]; exact h_v Vs hVs_lc
        have hw := TypeOfHM.weaken_env (env_pre := []) (env_extra := env_post)
          (env := env) hv_typed
        exact hw
      · -- i > env_post.length: substN returns `.var (i - 1)`
        have h_not_lt : ¬ (i < env_post.length) := by omega
        have h_not_lt' : ¬ (i - env_post.length < (1 : Nat)) := by omega
        have h_subst : (Expr.var i).substN env_post.length [v] = .var (i - 1) := by
          simp [Expr.substN, h_not_lt, h_not_lt']
        rw [h_subst]
        refine .var ?_ h_tyArgs_closed h_inst
        have h_le_i : env_post.length ≤ i := by omega
        rw [List.getElem?_append_right (by omega : env_post.length ≤ i - 1)]
        rw [List.append_assoc, List.getElem?_append_right h_le_i] at h_lookup
        rw [show ([M] ++ env) = (M :: env) from rfl] at h_lookup
        rw [show (i - env_post.length) = (i - env_post.length - 1) + 1 from by omega]
            at h_lookup
        simp only [List.getElem?_cons_succ] at h_lookup
        rw [show (i - 1 - env_post.length) = (i - env_post.length - 1) from by omega]
        exact h_lookup
  | match_ scrut branches ih_scrut ih_branches =>
    cases h_body with
    | match_ h_scrut h_ne h_brs =>
      simp only [Expr.substN]
      have h_subst_nonempty :
          BranchList.substN env_post.length [v] branches ≠ [] := by
        intro h_eq
        cases branches with
        | nil => exact h_ne rfl
        | cons _ _ => simp [BranchList.substN] at h_eq
      refine TypeOfHM.match_ (ih_scrut h_scrut) h_subst_nonempty ?_
      clear ih_scrut h_scrut h_ne h_subst_nonempty
      revert h_brs ih_branches
      induction branches with
      | nil =>
        intro _ _ b h_mem
        simp [BranchList.substN] at h_mem
      | cons hd tl ih_tl =>
        intro ih_branches h_brs branch h_mem
        obtain ⟨pat, body⟩ := hd
        simp only [BranchList.substN, List.mem_cons] at h_mem
        cases h_mem with
        | inl h_eq =>
          subst h_eq
          have h_branch := h_brs (pat, body) List.mem_cons_self
          cases h_branch with
          | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body =>
            subst h_ctx
            subst h_pb
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ [M] ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ [M] ++ env
                  by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
              at h_body
            have ih_body :=
              ih_branches pat body List.mem_cons_self
                (env_post := instContents.map PolyTy.mkTrivial ++ env_post)
                h_body
            simp only [List.length_append, List.length_map] at ih_body
            rw [← h_inst.length_eq, ← h_contents] at ih_body
            rw [show pat.contents + env_post.length = env_post.length + pat.contents
                  from Nat.add_comm _ _] at ih_body
            refine TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
              h_inst rfl rfl ?_
            rw [List.append_assoc] at ih_body
            exact ih_body
        | inr h_mem' =>
          exact ih_tl
            (fun pat' e' hmem => ih_branches pat' e' (List.mem_cons_of_mem _ hmem))
            (fun branch hmem => h_brs branch (List.mem_cons_of_mem _ hmem))
            branch h_mem'


/-- Multi-binding substitution: substitute a whole block of values `vs` for a
    block of schemes `Ms` (each `vs[j]` typing at every instance of `Ms[j]`).
    Generalises `subst_lemma` from `[v]`/`[M]` to lists — needed for the
    `match_` (n bindings) reduction case of
    preservation. Only the `var` case differs from `subst_lemma` (its
    trichotomy becomes three *ranges*); every other case is verbatim. -/
theorem TypeOfHM.subst_lemma_many
    {ctors : CtorEnv} {env_post env Ms : Env}
    {e : Expr} {τ : Ty} {vs : List Expr}
    (h_Ms_wf : ∀ M ∈ Ms, M.WF)
    (h_body : TypeOfHM ⟨env_post ++ Ms ++ env, ctors⟩ e τ)
    (h_vs : List.Forall₂ (fun v M => HasScheme ⟨env, ctors⟩ v M) vs Ms) :
    TypeOfHM ⟨env_post ++ env, ctors⟩ (e.substN env_post.length vs) τ := by
  have h_len : vs.length = Ms.length := h_vs.length_eq
  induction e using Expr.rec_strong generalizing env_post τ with
  | primLit p =>
    cases h_body with
    | primLitUnit => exact .primLitUnit
    | primLitInt  => exact .primLitInt
    | primLitNat  => exact .primLitNat
    | primLitBool => exact .primLitBool
    | primLitStr  => exact .primLitStr
  | pair a b ih_a ih_b =>
    cases h_body with
    | pair ha hb =>
      simp only [Expr.substN]
      exact .pair (ih_a ha) (ih_b hb)
  | app f inp ih_f ih_i =>
    cases h_body with
    | app hf hi =>
      simp only [Expr.substN]
      exact .app (ih_f hf) (ih_i hi)
  | lambda ann body ih =>
    cases h_body with
    | lambda hpc hann heq hbody =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.lambda hpc hann rfl ?_
      exact ih (env_post := PolyTy.mkTrivial _ :: env_post) hbody
  | letIn ann boundExpr body ih_be ih_body =>
    cases h_body with
    | letIn hsch hann hcofin heq hbodyinner =>
      subst heq
      simp only [Expr.substN]
      refine TypeOfHM.letIn hsch hann
        (fun Xs hfresh => ih_be (hcofin Xs hfresh)) rfl ?_
      exact ih_body (env_post := _ :: env_post) hbodyinner
  | fst e ih =>
    cases h_body with
    | fst he =>
      simp only [Expr.substN]
      exact .fst (ih he)
  | snd e ih =>
    cases h_body with
    | snd he =>
      simp only [Expr.substN]
      exact .snd (ih he)
  | ctor name =>
    cases h_body with
    | ctor hlook htyargs hinst =>
      exact .ctor hlook htyargs hinst
  | var i =>
    cases h_body with
    | var h_lookup h_tyArgs_closed h_inst =>
      by_cases h_lt : i < env_post.length
      · -- below the substituted block: keep `.var i`
        have h_subst : (Expr.var i).substN env_post.length vs = .var i := by
          simp [Expr.substN, h_lt]
        rw [h_subst]
        refine .var ?_ h_tyArgs_closed h_inst
        show (env_post ++ env)[i]? = _
        rw [List.getElem?_append_left h_lt]
        rw [List.append_assoc, List.getElem?_append_left h_lt] at h_lookup
        exact h_lookup
      · push_neg at h_lt
        by_cases h_in : i - env_post.length < vs.length
        · -- inside the substituted block: pick `vs[i - env_post.length]`
          have hj_Ms : i - env_post.length < Ms.length := by omega
          have h_subst : (Expr.var i).substN env_post.length vs
              = (vs[i - env_post.length]).shiftFrom 0 env_post.length := by
            simp only [Expr.substN]
            rw [if_neg (by omega), dif_pos h_in]
          rw [h_subst]
          rw [List.append_assoc, List.getElem?_append_right h_lt,
              List.getElem?_append_left hj_Ms,
              List.getElem?_eq_getElem hj_Ms] at h_lookup
          simp only [Option.some.injEq] at h_lookup
          subst h_lookup
          expose_names
          have hMj_wf : (Ms[i - env_post.length]).WF :=
            h_Ms_wf _ (List.getElem_mem hj_Ms)
          have hvj : HasScheme ⟨env, ctors⟩ (vs[i - env_post.length])
              (Ms[i - env_post.length]) := h_vs.get h_in hj_Ms
          set Vs := (List.range (Ms[i - env_post.length]).paramCount).map
              (fun k => (tyArgs[k]?).getD (Ty.prim PrimTy.unit)) with hVs
          have hVs_lc : Ty.AreLC (Ms[i - env_post.length]).paramCount Vs := by
            refine ⟨by simp [hVs], ?_⟩
            intro V hV
            simp only [hVs, List.mem_map, List.mem_range] at hV
            obtain ⟨k, _, rfl⟩ := hV
            cases htk : tyArgs[k]? with
            | none => simp only [Option.getD_none]; exact .prim
            | some t =>
              simp only [Option.getD_some]
              exact h_tyArgs_closed t (List.mem_of_getElem? htk)
          have hτ : τ = (Ms[i - env_post.length]).openWith Vs := by
            have := InstantiatesBy.eq_openWith_range h_inst hMj_wf
            simpa [hVs, PolyTy.openWith] using this
          have hv_typed : TypeOfHM ⟨env, ctors⟩ (vs[i - env_post.length]) τ := by
            rw [hτ]; exact hvj Vs hVs_lc
          exact TypeOfHM.weaken_env (env_pre := []) (env_extra := env_post)
            (env := env) hv_typed
        · -- above the block: shift down by `vs.length`
          push_neg at h_in
          have h_subst : (Expr.var i).substN env_post.length vs
              = .var (i - vs.length) := by
            simp only [Expr.substN]
            rw [if_neg (by omega), dif_neg (by omega)]
          rw [h_subst]
          refine .var ?_ h_tyArgs_closed h_inst
          rw [List.getElem?_append_right (by omega : env_post.length ≤ i - vs.length)]
          rw [List.append_assoc, List.getElem?_append_right h_lt,
              List.getElem?_append_right (by omega : Ms.length ≤ i - env_post.length)]
            at h_lookup
          rw [show (i - vs.length) - env_post.length
                = (i - env_post.length) - Ms.length by omega]
          exact h_lookup
  | match_ scrut branches ih_scrut ih_branches =>
    cases h_body with
    | match_ h_scrut h_ne h_brs =>
      simp only [Expr.substN]
      have h_subst_nonempty :
          BranchList.substN env_post.length vs branches ≠ [] := by
        intro h_eq
        cases branches with
        | nil => exact h_ne rfl
        | cons _ _ => simp [BranchList.substN] at h_eq
      refine TypeOfHM.match_ (ih_scrut h_scrut) h_subst_nonempty ?_
      clear ih_scrut h_scrut h_ne h_subst_nonempty
      revert h_brs ih_branches
      induction branches with
      | nil =>
        intro _ _ b h_mem
        simp [BranchList.substN] at h_mem
      | cons hd tl ih_tl =>
        intro ih_branches h_brs branch h_mem
        obtain ⟨pat, body⟩ := hd
        simp only [BranchList.substN, List.mem_cons] at h_mem
        cases h_mem with
        | inl h_eq =>
          subst h_eq
          have h_branch := h_brs (pat, body) List.mem_cons_self
          cases h_branch with
          | mk h_lookup h_tyName h_paramCount h_contents h_inst h_pb h_ctx h_body =>
            subst h_ctx
            subst h_pb
            expose_names
            rw [show (instContents.map PolyTy.mkTrivial ++ (env_post ++ Ms ++ env))
                  = (instContents.map PolyTy.mkTrivial ++ env_post) ++ Ms ++ env
                  by rw [List.append_assoc, List.append_assoc, List.append_assoc]]
              at h_body
            have ih_body :=
              ih_branches pat body List.mem_cons_self
                (env_post := instContents.map PolyTy.mkTrivial ++ env_post)
                h_body
            simp only [List.length_append, List.length_map] at ih_body
            rw [← h_inst.length_eq, ← h_contents] at ih_body
            rw [show pat.contents + env_post.length = env_post.length + pat.contents
                  from Nat.add_comm _ _] at ih_body
            refine TypeOfMatchBranch.mk h_lookup h_tyName h_paramCount h_contents
              h_inst rfl rfl ?_
            rw [List.append_assoc] at ih_body
            exact ih_body
        | inr h_mem' =>
          exact ih_tl
            (fun pat' e' hmem => ih_branches pat' e' (List.mem_cons_of_mem _ hmem))
            (fun branch hmem => h_brs branch (List.mem_cons_of_mem _ hmem))
            branch h_mem'


/-! ## Canonical forms

Inversion lemmas: a *value* of a given type has a particular syntactic shape.
Used by progress to conclude the next step exists when a value sits in a given
type position. These only invert the value constructors (`lambda`/`pair`/
`ctor`/ctor-chains), so they're unaffected by the cofinite `let` rules. -/

/-- A well-typed constructor chain has a `wrapArrows … (customTy …)` type:
    a prefix of arrows ending in a `customTy`.

    Inducts syntactically on `e` (rather than on `h_chain`) because `IsCtorChain`
    is mutually defined with `IsValue`, so the `induction` tactic refuses it. -/
private lemma TypeOfHM.ctor_chain_has_customTy_form
    {ctx e τ}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : TypeOfHM ctx e τ) :
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
  | pair _ _ _ _   => cases h_chain
  | lambda _ _ _   => cases h_chain
  | letIn _ _ _ _ _ => cases h_chain
  | fst _ _        => cases h_chain
  | snd _ _        => cases h_chain
  | var _          => cases h_chain
  | match_ _ _ _ _ => cases h_chain

theorem TypeOfHM.canonical_pair {ctx e fstTy sndTy}
    (h_ty : TypeOfHM ctx e (.pair fstTy sndTy))
    (h_val : SmallStep.IsValue e) :
    ∃ a b, e = .pair a b ∧ SmallStep.IsValue a ∧ SmallStep.IsValue b := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda _ _ => cases h_ty
  | pair h_a h_b => exact ⟨_, _, rfl, h_a, h_b⟩
  | ctor name =>
    exfalso
    have ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.ctor name) h_ty
    cases tys with
    | nil => simp [Ty.wrapArrows] at h_eq
    | cons _ _ => simp [Ty.wrapArrows] at h_eq
  | ctorApp h_chain h_v =>
    exfalso
    have ⟨_, _, tys, h_eq⟩ :=
      TypeOfHM.ctor_chain_has_customTy_form (.app h_chain h_v) h_ty
    cases tys with
    | nil => simp [Ty.wrapArrows] at h_eq
    | cons _ _ => simp [Ty.wrapArrows] at h_eq

theorem TypeOfHM.canonical_arrow {ctx e argTy retTy}
    (h_ty : TypeOfHM ctx e (.arrow argTy retTy))
    (h_val : SmallStep.IsValue e) :
    (∃ ann body, e = .lambda ann body) ∨ SmallStep.IsCtorChain e := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda ann body => exact .inl ⟨ann, body, rfl⟩
  | pair _ _ => cases h_ty
  | ctor name => exact .inr (.ctor name)
  | ctorApp h_chain h_v => exact .inr (.app h_chain h_v)

theorem TypeOfHM.canonical_customTy {ctx e tyName tyArgs}
    (h_ty : TypeOfHM ctx e (.customTy tyName tyArgs))
    (h_val : SmallStep.IsValue e) :
    SmallStep.IsCtorChain e := by
  cases h_val with
  | primLit _ => cases h_ty
  | lambda _ _ => cases h_ty
  | pair _ _ => cases h_ty
  | ctor name => exact .ctor name
  | ctorApp h_chain h_v => exact .app h_chain h_v


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
theorem TypeOfHM.ctor_chain_inversion {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_chain : SmallStep.IsCtorChain e) (h_ty : TypeOfHM ctx e τ) :
    ∃ (name : CtorName) (args : List Expr) (ctor : Ctor)
      (tyArgs consumed remaining : List Ty),
      SmallStep.CtorAppliedTo e name args ∧
      LookupList.get? ctx.ctors name = some ctor ∧
      (∀ t ∈ tyArgs, ContainsBvarsUpTo 0 t) ∧
      ctor.contents = consumed ++ remaining ∧
      List.Forall₂ (fun a c => ∃ ct, InstantiatesBy tyArgs c ct ∧ TypeOfHM ctx a ct)
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
  | pair _ _ _ _ => cases h_chain
  | lambda _ _ _ => cases h_chain
  | letIn _ _ _ _ _ => cases h_chain
  | fst _ _ => cases h_chain
  | snd _ _ => cases h_chain
  | var _ => cases h_chain
  | match_ _ _ _ _ => cases h_chain


/-! ## Progress

A well-typed, closed term whose matches are all exhaustive is either a value or
can take a step. The interesting case is `match_`: the scrutinee value is a
constructor chain (`canonical_customTy` + `ctor_chain_inversion`), and the
strengthened `AllMatchesExhaustive.match_` guarantees that the head constructor's
type — which is pinned to the branches — has a covering branch. -/

open SmallStep in
theorem TypeOfHM.progress {ctx : Ctx} {e : Expr} {τ : Ty}
    (h_ty : TypeOfHM ctx e τ) (h_closed : ctx.env = [])
    (h_exh : AllMatchesExhaustive ctx.ctors e) :
    IsValue e ∨ ∃ e', Step e e' := by
  induction e using Expr.rec_strong generalizing ctx τ with
  | primLit p => exact .inl (.primLit p)
  | lambda _ _ _ => exact .inl (.lambda _ _)
  | ctor name => exact .inl (.ctor name)
  | var n =>
    cases h_ty with
    | var h_lookup _ _ => rw [h_closed] at h_lookup; simp at h_lookup
  | pair a b iha ihb =>
    cases h_exh with
    | pair h_exh_a h_exh_b =>
      cases h_ty with
      | pair h_a h_b =>
        rcases iha h_a h_closed h_exh_a with hva | ⟨a', ha⟩
        · rcases ihb h_b h_closed h_exh_b with hvb | ⟨b', hb⟩
          · exact .inl (.pair hva hvb)
          · exact .inr ⟨_, .pairSnd hva hb⟩
        · exact .inr ⟨_, .pairFst ha⟩
  | app f arg ihf iharg =>
    cases h_exh with
    | app h_exh_f h_exh_arg =>
      cases h_ty with
      | app h_f h_arg =>
        rcases ihf h_f h_closed h_exh_f with hvf | ⟨f', hf⟩
        · rcases iharg h_arg h_closed h_exh_arg with hva | ⟨arg', harg⟩
          · rcases TypeOfHM.canonical_arrow h_f hvf with ⟨ann, body, rfl⟩ | hchain
            · exact .inr ⟨_, .beta hva⟩
            · exact .inl (.ctorApp hchain hva)
          · exact .inr ⟨_, .appArg hvf harg⟩
        · exact .inr ⟨_, .appFn hf⟩
  | letIn ann rhs body ihrhs _ =>
    cases h_exh with
    | letIn h_exh_rhs _ =>
      cases h_ty with
      | letIn hwf _ hcofin heq hbody =>
        expose_names
        obtain ⟨Xs, hXlen, hXnodup, hXavoid⟩ := exists_fresh_names L M.paramCount
        have h_rhs := hcofin Xs ⟨hXlen, hXnodup, hXavoid⟩
        rcases ihrhs h_rhs h_closed h_exh_rhs with hvr | ⟨rhs', hrhs⟩
        · exact .inr ⟨_, .letReduce hvr⟩
        · exact .inr ⟨_, .letInRhs hrhs⟩
  | fst e ih =>
    cases h_exh with
    | fst h_exh_e =>
      cases h_ty with
      | fst he =>
        rcases ih he h_closed h_exh_e with hve | ⟨e', he'⟩
        · obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := TypeOfHM.canonical_pair he hve
          exact .inr ⟨_, .fstReduce hv₁ hv₂⟩
        · exact .inr ⟨_, .fstCong he'⟩
  | snd e ih =>
    cases h_exh with
    | snd h_exh_e =>
      cases h_ty with
      | snd he =>
        rcases ih he h_closed h_exh_e with hve | ⟨e', he'⟩
        · obtain ⟨v₁, v₂, rfl, hv₁, hv₂⟩ := TypeOfHM.canonical_pair he hve
          exact .inr ⟨_, .sndReduce hv₁ hv₂⟩
        · exact .inr ⟨_, .sndCong he'⟩
  | match_ scrut branches ihscrut _ =>
    cases h_exh with
    | match_ h_exh_scrut _ h_branch_ty h_match_exh =>
      cases h_ty with
      | match_ h_scrut h_ne h_brs =>
        rcases ihscrut h_scrut h_closed h_exh_scrut with hvs | ⟨scrut', hscrut⟩
        · -- scrutinee is a value of customTy type ⇒ a constructor chain
          have hchain := TypeOfHM.canonical_customTy h_scrut hvs
          obtain ⟨name, args, ctor, tyArgs', consumed, remaining,
            hcat, hlook, _, hcontents, hforall, hinst⟩ :=
            TypeOfHM.ctor_chain_inversion hchain h_scrut
          cases remaining with
          | cons c rest => simp only [Ty.wrapArrows] at hinst; cases hinst
          | nil =>
            simp only [Ty.wrapArrows] at hinst
            rw [List.append_nil] at hcontents
            have hlen : args.length = ctor.contents.length := by
              rw [hcontents]; exact hforall.length_eq
            -- `hinst : InstantiatesBy _ (.customTy ctor.tyName _) (.customTy Tscrut tyArgs)`;
            -- inverting it unifies the scrutinee's type name with `ctor.tyName`.
            cases hinst with
            | customTy _ =>
              -- the scrutinee's type name is now `ctor.tyName`; reconcile it with
              -- the exhaustiveness type name via any branch (`branches ≠ []`).
              obtain ⟨pat, body, hmem, hpctor, hparity⟩ :=
                h_match_exh name ctor hlook (by
                  obtain ⟨⟨pat0, body0⟩, htl0, hbeq⟩ :=
                    List.exists_cons_of_ne_nil h_ne
                  have hb0 : (pat0, body0) ∈ branches := by simp [hbeq]
                  obtain ⟨ctorB, hlookB, htyB⟩ := h_branch_ty pat0 body0 hb0
                  cases h_brs (pat0, body0) hb0 with
                  | mk hlookA htyA _ _ _ _ _ _ =>
                    rw [← htyA, Option.some.inj (hlookA.symm.trans hlookB)]
                    exact htyB)
              obtain ⟨e', hfmb⟩ := findMatchingBranch_of_exists
                ⟨pat, body, hmem, hpctor, hparity.trans hlen.symm⟩
              obtain ⟨pat', body', hfirst, _⟩ := findMatchingBranch_to_FirstMatch hfmb
              exact .inr ⟨_, .matchReduce hvs hcat hfirst⟩
        · exact .inr ⟨_, .matchScrut hscrut⟩


/-! ## Preservation

Subject reduction: a well-typed term that takes a step stays well-typed at the
same type. The reduction cases reuse the substitution lemmas; the `matchReduce`
case is the substantial one — it lines up the scrutinee's constructor-chain
typing (`ctor_chain_inversion`) with the matched branch's typing
(`TypeOfMatchBranch`), proving that the two type-argument lists agree on the
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
  | here _ _ => exact List.mem_cons_self
  | there _ _ ih => exact List.mem_cons_of_mem _ ih

open SmallStep in
/-- The matched branch's pattern names the matched constructor. -/
theorem SmallStep.FirstMatchingBranch.ctor_eq {name arity branches pat body}
    (h : FirstMatchingBranch name arity branches pat body) : pat.ctor = name := by
  induction h with
  | here hc _ => exact hc
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
  | pair a b iha ihb =>
    intro t1 t2 hbv h1 h2
    cases hbv with
    | pair hba hbb =>
      cases h1 with
      | pair h1a h1b =>
        cases h2 with
        | pair h2a h2b => rw [iha hba h1a h2a, ihb hbb h1b h2b]
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
      List.Forall₂ (fun a c => ∃ ct, InstantiatesBy tyArgsS c ct ∧ TypeOfHM ctx a ct)
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
        exact HasScheme.ofTypeOfHM htyA

open SmallStep in
theorem TypeOfHM.preservation {ctx : Ctx} {e e' : Expr} {τ : Ty}
    (h_step : Step e e') (h_ty : TypeOfHM ctx e τ) :
    TypeOfHM ctx e' τ := by
  induction h_step generalizing τ with
  | beta hval =>
    cases h_ty with
    | app hf hi =>
      cases hf with
      | lambda hpc _ heq hbody =>
        subst heq
        exact TypeOfHM.subst_lemma (env_post := []) (M := PolyTy.mkTrivial _)
          hpc hbody (HasScheme.ofTypeOfHM hi)
  | letReduce hval =>
    cases h_ty with
    | letIn hwf _ hcofin heq hbody =>
      subst heq
      exact TypeOfHM.subst_lemma (env_post := []) hwf hbody
        (HasScheme.fromHasSchemeVars hcofin)
  | fstReduce _ _ =>
    cases h_ty with
    | fst he =>
      cases he with
      | pair h1 _ => exact h1
  | sndReduce _ _ =>
    cases h_ty with
    | snd he =>
      cases he with
      | pair _ h2 => exact h2
  | matchReduce hval hctor hfirst =>
    rename_i scrut branches name args pat body
    cases h_ty with
    | match_ h_scrut h_ne h_brs =>
      rename_i tyName tyArgs
      have hmem := hfirst.mem
      have hpeq := hfirst.ctor_eq
      have hbranch := h_brs (pat, body) hmem
      cases hbranch with
      | mk hlookB htyNameB hpcB hcontentsB hinstB hpbB hctxB hbodyB =>
        subst hctxB
        subst hpbB
        have hchain := TypeOfHM.canonical_customTy h_scrut hval
        obtain ⟨name', args', ctorS, tyArgsS, consumedS, remainingS,
          hcatS, hlookS, htyargsS, hcontentsS, hforallS, hinstS⟩ :=
          TypeOfHM.ctor_chain_inversion hchain h_scrut
        obtain ⟨hnEq, haEq⟩ := hctor.det hcatS
        subst hnEq
        subst haEq
        rw [hpeq] at hlookB
        have hcc := Option.some.inj (hlookS.symm.trans hlookB)
        obtain ⟨instCts, hinstB', hbodyB'⟩ :
            ∃ ic, List.Forall₂ (InstantiatesBy tyArgs) ctorS.contents ic ∧
              TypeOfHM ⟨ic.map PolyTy.mkTrivial ++ ctx.env, ctx.ctors⟩ body τ := by
          refine ⟨_, ?_, hbodyB⟩
          rw [hcc]; exact hinstB
        cases remainingS with
        | cons c rest => simp only [Ty.wrapArrows] at hinstS; cases hinstS
        | nil =>
          rw [List.append_nil] at hcontentsS
          subst hcontentsS
          simp only [Ty.wrapArrows] at hinstS
          cases hinstS with
          | customTy hbvr =>
            have hpc_len : tyArgs.length = ctorS.paramCount := by
              rw [hcc]; exact hpcB.symm
            have hagree : ∀ k, k < ctorS.paramCount → tyArgs[k]? = tyArgsS[k]? := by
              intro k hk
              have hkt : k < tyArgs.length := by omega
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
            have htyArgs_lc : ∀ t ∈ tyArgs, ContainsBvarsUpTo 0 t := by
              intro t ht
              obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht
              have hkpc : k < ctorS.paramCount := by omega
              have hag := hagree k hkpc
              rw [List.getElem?_eq_getElem hk] at hag
              exact htyargsS _ (List.mem_of_getElem? hag.symm)
            have h_Ms_wf : ∀ M ∈ instCts.map PolyTy.mkTrivial, M.WF := by
              intro M hM
              obtain ⟨ic, hic, rfl⟩ := List.mem_map.mp hM
              obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hic
              have hrel := List.Forall₂.get hinstB'
                (by have := hinstB'.length_eq; omega) hi
              exact InstantiatesBy.preserves_bvars htyArgs_lc hrel
            have h_vs := InstantiatesBy.build_match_vs hagree ctorS.bound hinstB' hforallS
            exact TypeOfHM.subst_lemma_many (env_post := [])
              h_Ms_wf hbodyB' h_vs
  | pairFst _ ih =>
    cases h_ty with
    | pair ha hb => exact .pair (ih ha) hb
  | pairSnd hv _ ih =>
    cases h_ty with
    | pair ha hb => exact .pair ha (ih hb)
  | appFn _ ih =>
    cases h_ty with
    | app hf hi => exact .app (ih hf) hi
  | appArg hv _ ih =>
    cases h_ty with
    | app hf hi => exact .app hf (ih hi)
  | letInRhs _ ih =>
    cases h_ty with
    | letIn hwf hann hcofin heq hbody =>
      exact .letIn hwf hann (fun Xs hfresh => ih (hcofin Xs hfresh)) heq hbody
  | fstCong _ ih =>
    cases h_ty with
    | fst he => exact .fst (ih he)
  | sndCong _ ih =>
    cases h_ty with
    | snd he => exact .snd (ih he)
  | matchScrut _ ih =>
    cases h_ty with
    | match_ h_scrut h_ne h_brs => exact .match_ (ih h_scrut) h_ne h_brs
