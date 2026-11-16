import EPL2.Syntax

/-!
# The type-level library

Every variable-replacing operation is `Ty.subst`, so this file is short:
three laws of `subst` (`subst_subst`, `subst_congr`, `scoped_subst`), and the
facts about the derived operations that the rest of the development uses,
each provable from those laws plus `simp`/`omega` on the pointwise maps.

**Proof guidance.** Prove the laws of `subst` by induction on the type. Prefer
proving the other lemmas by rewriting with them (`Ty.bind`, `Ty.instantiate`,
... are all `subst` by definition); a fresh induction on the type is fine
where that is shorter.

Substitution under a scheme's binders is not capture-avoiding (`bvar`s are
not shifted), so the lemmas that push a substitution through `instantiate`
ask the substituted images to be free of `bvar`s (`Scoped _ 0`). Images are
always semantic types well-formed at some depth, so this always holds.
-/

namespace EPL2
namespace Ty

theorem subst_subst (σ : Subst U V) (τ : Subst V W) (ty : Ty U) :
    (ty.subst σ).subst τ = ty.subst (σ.comp τ) := by
  sorry

theorem subst_id (ty : Ty V) : ty.subst Subst.id = ty := by
  sorry

/-- Substitutions that agree on the variables a type mentions agree on it. -/
theorem subst_congr {σ τ : Subst V W} {ty : Ty V} (inScope : ty.Scoped rigids binders)
    (onBvar : ∀ i < binders, σ.bvar i = τ.bvar i)
    (onRigid : ∀ l < rigids, σ.rigid l = τ.rigid l)
    (onVar : ∀ v ∈ ty.vars, σ.var v = τ.var v) :
    ty.subst σ = ty.subst τ := by
  sorry

/-- `subst_congr` for a type of unknown scope. -/
theorem subst_ext {σ τ : Subst V W} {ty : Ty V}
    (onBvar : ∀ i, σ.bvar i = τ.bvar i) (onRigid : ∀ l, σ.rigid l = τ.rigid l)
    (onVar : ∀ v ∈ ty.vars, σ.var v = τ.var v) :
    ty.subst σ = ty.subst τ := by
  sorry

theorem scoped_subst {σ : Subst V W} {ty : Ty V} (inScope : ty.Scoped rigids binders)
    (onBvar : ∀ i < binders, (σ.bvar i).Scoped rigids' binders')
    (onRigid : ∀ l < rigids, (σ.rigid l).Scoped rigids' binders')
    (onVar : ∀ v ∈ ty.vars, (σ.var v).Scoped rigids' binders') :
    (ty.subst σ).Scoped rigids' binders' := by
  sorry

theorem Scoped.mono {ty : Ty V} (inScope : ty.Scoped rigids binders)
    (rigidsLe : rigids ≤ rigids') (bindersLe : binders ≤ binders') :
    ty.Scoped rigids' binders' := by
  sorry

theorem mem_vars_bind {ty : Ty V} {f : V → Ty W} {w : W} :
    w ∈ (ty.bind f).vars ↔ ∃ v ∈ ty.vars, w ∈ (f v).vars := by
  sorry

theorem bind_bind (ty : Ty U) (f : U → Ty V) (g : V → Ty W) :
    (ty.bind f).bind g = ty.bind fun u => (f u).bind g := by
  sorry

theorem bind_var (ty : Ty V) : ty.bind .var = ty := by
  sorry

theorem bind_congr {ty : Ty V} {f g : V → Ty W} (agree : ∀ v ∈ ty.vars, f v = g v) :
    ty.bind f = ty.bind g := by
  sorry

theorem scoped_bind {ty : Ty V} {f : V → Ty W} (inScope : ty.Scoped rigids binders)
    (images : ∀ v ∈ ty.vars, (f v).Scoped rigids binders) :
    (ty.bind f).Scoped rigids binders := by
  sorry

/-- A bind keeps bound and rigid variables and embeds every image, so the
scope of the result bounds the scope of the type and of every image. -/
theorem scoped_of_bind {ty : Ty V} {f : V → Ty W} (inScope : (ty.bind f).Scoped rigids binders) :
    ty.Scoped rigids binders ∧ ∀ v ∈ ty.vars, (f v).Scoped rigids binders := by
  sorry

/-- If two binds agree, the maps agree on every variable of the type. -/
theorem bind_eq_bind_vars {ty : Ty V} {f g : V → Ty W} (equal : ty.bind f = ty.bind g) :
    ∀ v ∈ ty.vars, f v = g v := by
  sorry

theorem vars_lift (ty : SemTy) : (ty.lift : Ty V).vars = [] := by
  sorry

theorem lift_bind (ty : SemTy) (f : V → Ty W) : (ty.lift : Ty V).bind f = ty.lift := by
  sorry

theorem lift_self (ty : SemTy) : (ty.lift : SemTy) = ty := by
  sorry

theorem scoped_lift {ty : SemTy} : (ty.lift : Ty V).Scoped rigids binders ↔ ty.Scoped rigids binders := by
  sorry

theorem ground_eq_some {ty : Ty V} {sem : SemTy} : ty.ground = some sem ↔ ty = sem.lift := by
  sorry

theorem ground_eq_none {ty : Ty V} : ty.ground = none ↔ ty.vars ≠ [] := by
  sorry

theorem instantiate_nil (ty : Ty V) : ty.instantiate [] = ty := by
  sorry

theorem instantiate_bind (args : List (Ty V)) {ty : Ty V} {f : V → Ty W}
    (closed : ∀ v ∈ ty.vars, (f v).Scoped rigids 0) :
    (ty.instantiate args).bind f = (ty.bind f).instantiate (args.map (·.bind f)) := by
  sorry

theorem instantiate_scoped {ty : Ty V} (inScope : ty.Scoped rigids args.length)
    (argsScoped : ∀ arg ∈ args, arg.Scoped rigids binders) :
    (ty.instantiate args).Scoped rigids binders := by
  sorry

theorem vars_closeRigids (k n : Nat) (ty : Ty V) : (ty.closeRigids k n).vars = ty.vars := by
  sorry

theorem substRigids_wf {ty : Ty V} {f : Nat → Ty V} (wf : ty.WF k)
    (images : ∀ l < k, (f l).WF k') : (ty.substRigids f).WF k' := by
  sorry

/-- Closing a block commutes with a bind whose images do not mention the
block. -/
theorem closeRigids_bind {ty : Ty V} {f : V → Ty W}
    (images : ∀ v ∈ ty.vars, (f v).WF k) :
    (ty.closeRigids k n).bind f = (ty.bind f).closeRigids k n := by
  sorry

end Ty

/-- Rigid levels below `k` are kept; level `k + i` becomes `args[i]`. -/
def blockSubst (k : Nat) (args : List (Ty V)) : Nat → Ty V :=
  fun l => if l < k then .rigid l else args.getD (l - k) (.rigid l)

namespace Scheme

theorem skolemize_wf {scheme : Scheme V} (wf : scheme.WF k) :
    (scheme.skolemize k).WF (k + scheme.arity) := by
  sorry

theorem inst_wf {scheme : Scheme V} (wf : scheme.WF k) (le : k ≤ k')
    (length : args.length = scheme.arity) (argsWF : ∀ arg ∈ args, arg.WF k') :
    (scheme.inst args).WF k' := by
  sorry

/-- The generic instance is an instance, one block deeper. -/
theorem skolemize_instance {scheme : Scheme V} (wf : scheme.WF k) :
    scheme.Instance (k + scheme.arity) (scheme.skolemize k) := by
  sorry

theorem Instance.mono {scheme : Scheme V} {ty : Ty V} (inst : scheme.Instance k ty)
    (le : k ≤ k') : scheme.Instance k' ty := by
  sorry

/-- A monomorphic scheme's only instance is its type. -/
theorem instance_mono {ty ty' : Ty V} : (Scheme.mono ty').Instance k ty ↔ ty = ty' := by
  sorry

theorem skolemize_bind (scheme : Scheme V) {f : V → Ty W} (k : Nat)
    (closed : ∀ v ∈ scheme.body.vars, (f v).Scoped rigids 0) :
    (scheme.bind f).skolemize k = (scheme.skolemize k).bind f := by
  sorry

theorem inst_bind (scheme : Scheme V) (args : List (Ty V)) {f : V → Ty W}
    (closed : ∀ v ∈ scheme.body.vars, (f v).Scoped rigids 0) :
    (scheme.inst args).bind f = (scheme.bind f).inst (args.map (·.bind f)) := by
  sorry

/-- Every instance is a type substitution of the generic instance. -/
theorem skolemize_substRigids {scheme : Scheme V} (wf : scheme.WF k)
    (length : args.length = scheme.arity) :
    (scheme.skolemize k).substRigids (blockSubst k args) = scheme.inst args := by
  sorry

/-- Every instance of a type substitution of a scheme is one type
substitution of the generic instance: `f` below `k`, the instance's arguments
on the block. (`skolemize_substRigids` is the case `f = .rigid`.) -/
theorem skolemize_substRigids_inst {scheme : Scheme V} {f : Nat → Ty V} (wf : scheme.WF k)
    (length : args.length = scheme.arity) (closed : ∀ l < k, (f l).Scoped rigids 0) :
    (scheme.skolemize k).substRigids
        (fun l => if l < k then f l else args.getD (l - k) (.rigid l)) =
      (scheme.substRigids f).inst args := by
  sorry

theorem substRigids_congr {scheme : Scheme V} {f g : Nat → Ty V} (wf : scheme.WF k)
    (agree : ∀ l < k, f l = g l) : scheme.substRigids f = scheme.substRigids g := by
  sorry

theorem substRigids_wf {scheme : Scheme V} {f : Nat → Ty V} (wf : scheme.WF k)
    (images : ∀ l < k, (f l).WF k') : (scheme.substRigids f).WF k' := by
  sorry

/-- A scheme well-formed at `k` is untouched by a type substitution that is
the identity below `k`. -/
theorem substRigids_eq_self {scheme : Scheme V} (wf : scheme.WF k)
    (identity : ∀ l < k, f l = .rigid l) :
    scheme.substRigids f = scheme := by
  sorry

theorem inst_substRigids {scheme : Scheme V} (args : List (Ty V)) {f : Nat → Ty V}
    (wf : scheme.WF k) (closed : ∀ l < k, (f l).Scoped rigids 0) :
    (scheme.inst args).substRigids f =
      (scheme.substRigids f).inst (args.map (·.substRigids f)) := by
  sorry

/-- Closing a generic type and reopening it at the same depth is the identity. -/
theorem skolemize_closeRigids {ty : Ty V} (wf : ty.WF (k + n)) :
    (⟨n, ty.closeRigids k n⟩ : Scheme V).skolemize k = ty := by
  sorry

theorem closeRigids_wf {ty : Ty V} (wf : ty.WF (k + n)) :
    (⟨n, ty.closeRigids k n⟩ : Scheme V).WF k := by
  sorry

/-- Opening a well-formed scheme and closing it at the same depth is the
identity. -/
theorem closeRigids_skolemize {scheme : Scheme V} (wf : scheme.WF k) :
    (scheme.skolemize k).closeRigids k scheme.arity = scheme.body := by
  sorry

/-- A well-formed scheme is determined by its generic instance. -/
theorem skolemize_injective {first second : Scheme V} (firstWF : first.WF k)
    (secondWF : second.WF k) (arity : first.arity = second.arity)
    (equal : first.skolemize k = second.skolemize k) : first = second := by
  sorry

end Scheme

theorem Ctx.WF.mono {ctx : Ctx V} (wf : ctx.WF k) (le : k ≤ k') : ctx.WF k' := by
  sorry

namespace Expr

theorem anns_mapAnn (f : A → B) (expr : Expr A) : (expr.mapAnn f).anns = expr.anns.map f := by
  sorry

theorem mapAnn_congr {f g : A → B} {expr : Expr A} (agree : ∀ ann ∈ expr.anns, f ann = g ann) :
    expr.mapAnn f = expr.mapAnn g := by
  sorry

/-- If two maps of an expression agree, the functions agree on every
annotation. -/
theorem mapAnn_eq_anns {f g : A → B} {expr : Expr A} (equal : expr.mapAnn f = expr.mapAnn g) :
    ∀ ann ∈ expr.anns, f ann = g ann := by
  sorry

theorem traverseAnn_ground_eq_some {expr : Expr (Ty V)} {elaboration : Elab} :
    expr.traverseAnn Ty.ground = some elaboration ↔ expr = elaboration.mapAnn Ty.lift := by
  sorry

theorem traverseAnn_ground_eq_none {expr : Expr (Ty V)} :
    expr.traverseAnn Ty.ground = none ↔ ∃ ann ∈ expr.anns, ann.vars ≠ [] := by
  sorry

end Expr

namespace Template

/-- A completed annotation's type determines the annotation's scope. -/
theorem Matches.wf {template : Template} {ty : SemTy} (fits : template.Matches ty)
    (wf : ty.WF k) : template.WF k := by
  sorry

/-- An annotation matches any realization of itself. -/
theorem matches_bind {template : Template} (f : String → SemTy) :
    template.Matches (template.bind f) :=
  ⟨f, rfl⟩

end Template

end EPL2
