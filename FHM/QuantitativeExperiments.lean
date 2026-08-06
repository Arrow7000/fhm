namespace QuantitativeExperiments

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





inductive PrimTy
  | unit
  | int
  deriving DecidableEq, Repr


/-! ## Data shapes, full types, and uniqueness scopes -/

/-- Nominal name of a persistable entity table. -/
inductive EntityName
  | mk (str : String)
  deriving Repr, DecidableEq

/-- Name of a field of an entity. -/
inductive FieldName
  | mk (str : String)
  deriving Repr, DecidableEq

/-- A provenance path through an entity graph.

    These paths name *which database key is being used to distinguish values*.
    They do not yet encode the later, stronger resource/footprint discipline
    where a path and one of its descendants cannot both be exported. -/
inductive KeyPath
  | entity (name : EntityName)
  | field (parent : KeyPath) (field : FieldName)
  deriving Repr, DecidableEq

/-- Persistable data shapes. Unlike `Ty`, these have no functions.

    A `unique` annotation says that occurrences of `inner` in the referenced
    scope are pairwise distinct under `key`. `scope = 0` denotes the
    innermost enclosing `Ty.uniqueScope`. -/
inductive DataTy
  | prim : PrimTy → DataTy
  | entity : EntityName → DataTy
  | product : DataTy → DataTy → DataTy
  | list : DataTy → DataTy
  | unique (scope : Nat) (key : KeyPath) (inner : DataTy) : DataTy
  deriving Repr, DecidableEq

/-- Full types. Persistable data embeds into the full language; arrows do not. -/
inductive Ty
  | data : DataTy → Ty
  | arrow : (from_ to_ : Ty) → Ty
  /-- Binds a fresh database-key uniqueness scope in `contents`. -/
  | uniqueScope (contents : Ty) : Ty
  deriving Repr, DecidableEq

/-- A persistable type with no uniqueness annotation. -/
inductive DataTy.NoUnique : DataTy → Prop
  | prim : DataTy.NoUnique (.prim _)
  | entity : DataTy.NoUnique (.entity _)
  | product :
    DataTy.NoUnique fst →
    DataTy.NoUnique snd →
    DataTy.NoUnique (.product fst snd)
  | list :
    DataTy.NoUnique elem →
    DataTy.NoUnique (.list elem)

/-- Every uniqueness index must refer to an enclosing `uniqueScope`. -/
inductive DataTy.WellScopedUnder : Nat → DataTy → Prop
  | prim : DataTy.WellScopedUnder depth (.prim _)
  | entity : DataTy.WellScopedUnder depth (.entity _)
  | product :
    DataTy.WellScopedUnder depth fst →
    DataTy.WellScopedUnder depth snd →
    DataTy.WellScopedUnder depth (.product fst snd)
  | list :
    DataTy.WellScopedUnder depth elem →
    DataTy.WellScopedUnder depth (.list elem)
  | unique :
    scope < depth →
    DataTy.WellScopedUnder depth inner →
    DataTy.WellScopedUnder depth (.unique scope key inner)

/-- Every uniqueness index in a full type is bound by an enclosing scope. -/
inductive Ty.WellScopedUnder : Nat → Ty → Prop
  | data {depth : Nat} {contents : DataTy} :
    DataTy.WellScopedUnder depth contents →
    Ty.WellScopedUnder depth (.data contents)
  | arrow :
    Ty.WellScopedUnder depth from_ →
    Ty.WellScopedUnder depth to_ →
    Ty.WellScopedUnder depth (.arrow from_ to_)
  | uniqueScope :
    Ty.WellScopedUnder (depth + 1) contents →
    Ty.WellScopedUnder depth (.uniqueScope contents)

/-- A type which does not open a scope and cannot mention a scoped key.

    Lambda annotations use this initial conservative restriction: functions do
    not yet take or return scoped data. -/
inductive Ty.NoScopes : Ty → Prop
  | data {contents : DataTy} :
    DataTy.NoUnique contents →
    Ty.NoScopes (.data contents)
  | arrow :
    Ty.NoScopes from_ →
    Ty.NoScopes to_ →
    Ty.NoScopes (.arrow from_ to_)






/-- Primitive literals -/
inductive PrimLitExpr
  | unit : PrimLitExpr
  | int : Int → PrimLitExpr
  deriving Repr, DecidableEq


/-- An expression in our language -/
inductive Expr
  | primLit (prim : PrimLitExpr)
  /-- A lambda – parameters mustn't open up any new scopes (a restriction analogous to HM's prenex polymorphism) -/
  | lambda (ann : Ty) (no_scopes : ann.NoScopes) (body : Expr)
  /-- A function application -/
  | app (f input : Expr)
  /-- A let binding -/
  | letIn (bindingExpr body : Expr)
  /-- A variable use -/
  | var (deBruijnIndex : Nat)
  deriving Repr, DecidableEq

namespace Expr

/-- Shift free de Bruijn indices by `amount`, starting at `cutoff`. -/
def shift (amount cutoff : Nat) : Expr → Expr
  | .primLit prim => .primLit prim
  | .lambda ann no_scopes body =>
      .lambda ann no_scopes (shift amount (cutoff + 1) body)
  | .app f input => .app (shift amount cutoff f) (shift amount cutoff input)
  | .letIn bindingExpr body =>
      .letIn (shift amount cutoff bindingExpr) (shift amount (cutoff + 1) body)
  | .var index =>
      if cutoff ≤ index then .var (index + amount) else .var index

/-- Substitute `replacement` for the variable at de Bruijn index `index`.

The substituted binder is removed, so indices above it are shifted down. -/
def subst (index : Nat) (replacement : Expr) : Expr → Expr
  | .primLit prim => .primLit prim
  | .lambda ann no_scopes body =>
      .lambda ann no_scopes (subst (index + 1) (shift 1 0 replacement) body)
  | .app f input =>
      .app (subst index replacement f) (subst index replacement input)
  | .letIn bindingExpr body =>
      .letIn (subst index replacement bindingExpr)
        (subst (index + 1) (shift 1 0 replacement) body)
  | .var current =>
      if current = index then replacement
      else if index < current then .var (current - 1)
      else .var current

end Expr

/-- Expressions that are values under call-by-value evaluation. -/
inductive IsValue : Expr → Prop
  | primLit (prim : PrimLitExpr) : IsValue (.primLit prim)
  | lambda (ann : Ty) (no_scopes : ann.NoScopes) (body : Expr) :
      IsValue (.lambda ann no_scopes body)

/-- One call-by-value evaluation step. -/
inductive Step : Expr → Expr → Prop
  | appFn {f f' input : Expr} :
      Step f f' →
      Step (.app f input) (.app f' input)
  | appArg {f input input' : Expr} :
      IsValue f →
      Step input input' →
      Step (.app f input) (.app f input')
  | beta {ann : Ty} {no_scopes : ann.NoScopes} {body value : Expr} :
      IsValue value →
      Step (.app (.lambda ann no_scopes body) value) (Expr.subst 0 value body)
  | letBinding {bindingExpr bindingExpr' body : Expr} :
      Step bindingExpr bindingExpr' →
      Step (.letIn bindingExpr body) (.letIn bindingExpr' body)
  | letValue {bindingExpr body : Expr} :
      IsValue bindingExpr →
      Step (.letIn bindingExpr body) (Expr.subst 0 bindingExpr body)

/-- Zero or more small steps ending at a value. -/
inductive StepsToValue : Expr → Expr → Prop
  | done {value : Expr} :
      IsValue value →
      StepsToValue value value
  | step {expr expr' value : Expr} :
      Step expr expr' →
      StepsToValue expr' value →
      StepsToValue expr value







-- def PrimLitExpr.ty : PrimLitExpr → Ty
--   | .unit => .data (.prim .unit)
--   | .int _ => .data (.prim .int)

/-- Value typing context: de Bruijn index `i` looks up `ctx[i]`. -/
abbrev Ctx := List Ty

/-- Insert a block of types at de Bruijn cutoff `cutoff`. -/
def Ctx.insertAt (cutoff : Nat) (inserted ctx : Ctx) : Ctx :=
  ctx.take cutoff ++ inserted ++ ctx.drop cutoff

/-- Which exprs already exist in this uniqueness scope – keyed by uniqueness-scope de bruijn index. This only makes sense to do when we are within a uniqueness scope -/
abbrev UniqCtx := List (Expr × Nat)




/-- Declarative typing. `uniqueScope` / `uniqueTy` appear only in `Ty`; this
    relation does not enforce uniqueness yet — it is ordinary structural typing. -/
inductive TypeOf : Ctx → Expr → Ty → Prop
  | primLitUnit (prim : PrimLitExpr) :
      TypeOf ctx (.primLit .unit) (.data (.prim .unit))

  | primLitInt (prim : PrimLitExpr) :
      TypeOf ctx (.primLit (.int _)) (.data (.prim .int))

  | lambda {ann bodyTy : Ty} {prf : ann.NoScopes} :
      TypeOf (ann :: ctx) body bodyTy →
      TypeOf ctx (.lambda ann prf body) (.arrow ann bodyTy)

  | app {argTy retTy : Ty} :
      TypeOf ctx f (.arrow argTy retTy) →
      TypeOf ctx input argTy →
      TypeOf ctx (.app f input) retTy

  | letIn {bindingTy bodyTy : Ty} :
      TypeOf ctx bindingExpr bindingTy →
      TypeOf (bindingTy :: ctx) body bodyTy →
      TypeOf ctx (.letIn bindingExpr body) bodyTy

  | var {τ : Ty} (i : Nat) :
      ctx[i]? = some τ →
      TypeOf ctx (.var i) τ














/-! ## Shifting and substitution -/

theorem append_shift_lookup (inserted ctx : Ctx) (i : Nat) (τ : Ty)
    (h : ctx[i]? = some τ) :
    (inserted ++ ctx)[i + inserted.length]? = some τ := by
  rw [List.getElem?_append]
  simp [Nat.not_lt_of_ge (Nat.le_add_left inserted.length i), h]

theorem insertAt_preserves_lookup (ctx inserted : Ctx) (cutoff i : Nat) (τ : Ty)
    (hi : i < cutoff) (h : ctx[i]? = some τ) :
    (Ctx.insertAt cutoff inserted ctx)[i]? = some τ := by
  induction cutoff generalizing ctx i with
  | zero => simp at hi
  | succ cutoff ih =>
      cases ctx with
      | nil => simp at h
      | cons head tail =>
          cases i with
          | zero => simpa [Ctx.insertAt] using h
          | succ i =>
              have hi' : i < cutoff := by simpa using hi
              simpa [Ctx.insertAt, hi'] using ih tail i hi' h

theorem shift_lookup (ctx inserted : Ctx) (cutoff i : Nat) (τ : Ty)
    (h : ctx[i]? = some τ) :
    (Ctx.insertAt cutoff inserted ctx)[if cutoff ≤ i then i + inserted.length else i]? =
      some τ := by
  induction cutoff generalizing ctx i with
  | zero =>
      simpa [Ctx.insertAt] using append_shift_lookup inserted ctx i τ h
  | succ cutoff ih =>
      cases ctx with
      | nil => simp at h
      | cons head tail =>
          cases i with
          | zero => simpa [Ctx.insertAt] using h
          | succ i =>
              by_cases hc : cutoff ≤ i
              · have hc' : cutoff + 1 ≤ i + 1 := Nat.succ_le_succ hc
                simpa [Ctx.insertAt, hc, hc', Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm] using ih tail i h
              · have hci : i < cutoff := Nat.lt_of_not_ge hc
                have hc' : ¬cutoff + 1 ≤ i + 1 := by
                  simpa [Nat.succ_le_succ_iff] using hc
                simpa [Ctx.insertAt, hc, hc', hci] using
                  insertAt_preserves_lookup tail inserted cutoff i τ hci h

/-- Shifting an expression corresponds to inserting types into its context. -/
theorem shift_typeOf {ctx : Ctx} {e : Expr} {τ : Ty}
    (h : TypeOf ctx e τ) (cutoff : Nat) (inserted : Ctx) :
    TypeOf (Ctx.insertAt cutoff inserted ctx)
      (Expr.shift inserted.length cutoff e) τ := by
  induction h generalizing cutoff inserted with
  | primLitUnit prim => exact TypeOf.primLitUnit prim
  | primLitInt prim => exact TypeOf.primLitInt prim
  | lambda h ih =>
      apply TypeOf.lambda
      simpa [Ctx.insertAt] using ih (cutoff + 1) inserted
  | app hf hi ihf ihi =>
      exact TypeOf.app (ihf cutoff inserted) (ihi cutoff inserted)
  | letIn hb hbody ihb ihbody =>
      apply TypeOf.letIn
      · exact ihb cutoff inserted
      · simpa [Ctx.insertAt] using ihbody (cutoff + 1) inserted
  | var i hlookup =>
      by_cases hc : cutoff ≤ i
      · simp [Expr.shift, hc]
        apply TypeOf.var
        simpa [hc] using shift_lookup _ inserted cutoff i _ hlookup
      · simp [Expr.shift, hc]
        apply TypeOf.var
        simpa [hc] using shift_lookup _ inserted cutoff i _ hlookup

theorem subst_var_typeOf_at {pre : Ctx} {suffix : Ctx} {value : Expr} {τ σ : Ty}
    (i : Nat) (he : TypeOf (pre ++ τ :: suffix) (.var i) σ)
    (hv : TypeOf (pre ++ suffix) value τ) :
    TypeOf (pre ++ suffix)
      (Expr.subst pre.length value (.var i)) σ := by
  cases he with
  | var i hlookup =>
      by_cases hi : i < pre.length
      · have hprefix : (pre ++ suffix)[i]? = some σ := by
          rw [List.getElem?_append]
          rw [List.getElem?_append] at hlookup
          simp [hi] at hlookup ⊢
          exact hlookup
        have hne : i ≠ pre.length := Nat.ne_of_lt hi
        have hnot : ¬pre.length < i := by
          intro hli
          exact (Nat.lt_asymm hi hli).elim
        simp [Expr.subst, hne, hnot]
        exact TypeOf.var i hprefix
      · have hle : pre.length ≤ i := Nat.le_of_not_gt hi
        by_cases heq : i = pre.length
        · subst i
          simp at hlookup
          cases hlookup
          simpa [Expr.subst] using hv
        · have hgt : pre.length < i := Nat.lt_of_le_of_ne hle (Ne.symm heq)
          have hlookup' := hlookup
          rw [List.getElem?_append] at hlookup'
          simp [Expr.subst, hgt, heq]
          apply TypeOf.var (i - 1)
          rw [List.getElem?_append]
          have hpre : pre.length ≤ i - 1 := Nat.le_sub_one_of_lt hgt
          simp only [if_neg (Nat.not_lt_of_ge hpre)]
          have hjpos : 0 < i - pre.length := Nat.sub_pos_of_lt hgt
          cases hj : i - pre.length with
          | zero =>
              simp [hj] at hjpos
          | succ j =>
              have hlookup'' := hlookup'
              simp only [if_neg (Nat.not_lt_of_ge hle), hj,
                List.getElem?_cons_succ] at hlookup''
              have hidx : i - 1 - pre.length = j := by
                rw [Nat.sub_sub, Nat.add_comm, ← Nat.sub_sub, hj]
                simp
              simpa [hidx] using hlookup''

theorem subst_typeOf_at {pre : Ctx} {suffix : Ctx} {e value : Expr} {τ σ : Ty}
    (he : TypeOf (pre ++ τ :: suffix) e σ)
    (hv : TypeOf (pre ++ suffix) value τ) :
    TypeOf (pre ++ suffix) (Expr.subst pre.length value e) σ := by
  induction e generalizing pre suffix value τ σ with
  | primLit _ =>
      cases he with
      | primLitUnit => exact TypeOf.primLitUnit .unit
      | primLitInt => exact TypeOf.primLitInt (.int 0)
  | lambda ann no_scopes body ih =>
      cases he with
      | lambda h =>
          apply TypeOf.lambda
          simpa [Expr.subst] using
            ih (pre := _ :: pre) (suffix := suffix) (τ := τ)
              (value := Expr.shift 1 0 value) h
              (shift_typeOf hv 0 [_])
  | app f input ihf ihi =>
      cases he with
      | app hf hi =>
          simpa [Expr.subst] using TypeOf.app (ihf hf hv) (ihi hi hv)
  | letIn bindingExpr body ihb ihbody =>
      cases he with
      | letIn hb hbody =>
          apply TypeOf.letIn
          · exact ihb hb hv
          · simpa [Expr.subst] using
              ihbody (pre := _ :: pre) (suffix := suffix) (τ := τ)
                (value := Expr.shift 1 0 value) hbody
                (shift_typeOf hv 0 [_])
  | var i =>
      exact subst_var_typeOf_at i he hv

/-- Well-typed substitution preserves the type of the substituted expression. -/
theorem subst_typeOf {ctx : Ctx} {e value : Expr} {τ σ : Ty}
    (he : TypeOf (τ :: ctx) e σ) (hv : TypeOf ctx value τ) :
    TypeOf ctx (Expr.subst 0 value e) σ := by
  simpa using (subst_typeOf_at (pre := []) (suffix := ctx) he hv)

/-- A complete evaluation always ends at a value. -/
theorem StepsToValue.isValue {e value : Expr} :
    StepsToValue e value → IsValue value := by
  intro h
  induction h with
  | done hv => exact hv
  | step _ _ ih => exact ih

end QuantitativeExperiments
