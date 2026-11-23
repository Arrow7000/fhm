import EPL.Syntax

/-!
# The type-level library

Every variable-replacing operation is `Ty.subst`, so this file is short:
three laws of `subst` (`subst_subst`, `subst_congr`, `scoped_subst`), and the
facts about the derived operations that the rest of the development uses,
each provable from those laws plus `simp`/`omega` on the pointwise maps.

The laws of `subst` are proved by induction on the type. Most other lemmas
follow by rewriting with them (`Ty.bind`, `Ty.instantiate`, ... are all
`subst` by definition), a few by a fresh induction where that is shorter.

Substitution under a scheme's binders is not capture-avoiding (`bvar`s are
not shifted), so the lemmas that push a substitution through `instantiate`
ask the substituted images to be free of `bvar`s (`Scoped _ 0`). Images are
always semantic types well-formed at some depth, so this always holds.
-/

namespace EPL
namespace Ty

/-- Membership in an appended list, split into the two summands. -/
private theorem exists_mem_append {α : Type} {l₁ l₂ : List α} {p : α → Prop} :
    (∃ v ∈ l₁ ++ l₂, p v) ↔ (∃ v ∈ l₁, p v) ∨ (∃ v ∈ l₂, p v) := by
  simp only [List.mem_append, or_and_right, exists_or]

/-- Indexing a list with a proof of the bound. -/
private theorem getD_eq_getElem {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem subst_subst (σ : Subst U V) (τ : Subst V W) (ty : Ty U) :
    (ty.subst σ).subst τ = ty.subst (σ.comp τ) := by
  induction ty with
  | prim _ | con _ | bvar _ | rigid _ | var _ => rfl
  | arrow domain codomain ihd ihc | app domain codomain ihd ihc =>
      simp only [Ty.subst, ihd, ihc]

theorem subst_id (ty : Ty V) : ty.subst Subst.id = ty := by
  induction ty with
  | prim _ | con _ | bvar _ | rigid _ | var _ => rfl
  | arrow domain codomain ihd ihc | app domain codomain ihd ihc =>
      simp only [Ty.subst, ihd, ihc]

/-- Substitutions that agree on the variables a type mentions agree on it. -/
theorem subst_congr {σ τ : Subst V W} {ty : Ty V} (inScope : ty.Scoped rigids binders)
    (onBvar : ∀ i < binders, σ.bvar i = τ.bvar i)
    (onRigid : ∀ l < rigids, σ.rigid l = τ.rigid l)
    (onVar : ∀ v ∈ ty.vars, σ.var v = τ.var v) :
    ty.subst σ = ty.subst τ := by
  induction ty generalizing rigids binders with
  | prim _ | con _ => rfl
  | bvar index =>
      exact onBvar index inScope
  | rigid level =>
      exact onRigid level inScope
  | var v =>
      exact onVar v (by simp [Ty.vars])
  | arrow domain codomain ihd ihc | app domain codomain ihd ihc =>
      have hd : domain.subst σ = domain.subst τ :=
        ihd inScope.1 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv]))
      have hc : codomain.subst σ = codomain.subst τ :=
        ihc inScope.2 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv]))
      simp only [Ty.subst, hd, hc]

/-- `subst_congr` for a type of unknown scope. -/
theorem subst_ext {σ τ : Subst V W} {ty : Ty V}
    (onBvar : ∀ i, σ.bvar i = τ.bvar i) (onRigid : ∀ l, σ.rigid l = τ.rigid l)
    (onVar : ∀ v ∈ ty.vars, σ.var v = τ.var v) :
    ty.subst σ = ty.subst τ := by
  induction ty with
  | prim _ | con _ => rfl
  | bvar index => exact onBvar index
  | rigid level => exact onRigid level
  | var v => exact onVar v (by simp [Ty.vars])
  | arrow domain codomain ihd ihc | app domain codomain ihd ihc =>
      have hd : domain.subst σ = domain.subst τ :=
        ihd (fun v hv => onVar v (by simp [Ty.vars, hv]))
      have hc : codomain.subst σ = codomain.subst τ :=
        ihc (fun v hv => onVar v (by simp [Ty.vars, hv]))
      simp only [Ty.subst, hd, hc]

theorem scoped_subst {σ : Subst V W} {ty : Ty V} (inScope : ty.Scoped rigids binders)
    (onBvar : ∀ i < binders, (σ.bvar i).Scoped rigids' binders')
    (onRigid : ∀ l < rigids, (σ.rigid l).Scoped rigids' binders')
    (onVar : ∀ v ∈ ty.vars, (σ.var v).Scoped rigids' binders') :
    (ty.subst σ).Scoped rigids' binders' := by
  induction ty generalizing rigids binders with
  | prim _ | con _ => trivial
  | bvar index => exact onBvar index inScope
  | rigid level => exact onRigid level inScope
  | var v => exact onVar v (by simp [Ty.vars])
  | arrow domain codomain ihd ihc | app domain codomain ihd ihc =>
      exact ⟨ihd inScope.1 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv])),
             ihc inScope.2 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv]))⟩

theorem Scoped.mono {ty : Ty V} (inScope : ty.Scoped rigids binders)
    (rigidsLe : rigids ≤ rigids') (bindersLe : binders ≤ binders') :
    ty.Scoped rigids' binders' := by
  induction ty generalizing rigids binders with
  | prim _ | con _ | var _ => trivial
  | bvar index => exact Nat.lt_of_lt_of_le inScope bindersLe
  | rigid level => exact Nat.lt_of_lt_of_le inScope rigidsLe
  | arrow domain codomain ihd ihc | app domain codomain ihd ihc =>
      exact ⟨ihd inScope.1 rigidsLe bindersLe, ihc inScope.2 rigidsLe bindersLe⟩

theorem mem_vars_bind {ty : Ty V} {f : V → Ty W} {w : W} :
    w ∈ (ty.bind f).vars ↔ ∃ v ∈ ty.vars, w ∈ (f v).vars := by
  induction ty with
  | prim _ | con _ | bvar _ | rigid _ | var _ => simp [Ty.bind, Ty.subst, Ty.vars]
  | arrow d c ihd ihc | app d c ihd ihc =>
      change w ∈ ((d.bind f).vars ++ (c.bind f).vars) ↔
        ∃ v ∈ d.vars ++ c.vars, w ∈ (f v).vars
      rw [List.mem_append, ihd, ihc, exists_mem_append]

theorem bind_bind (ty : Ty U) (f : U → Ty V) (g : V → Ty W) :
    (ty.bind f).bind g = ty.bind fun u => (f u).bind g :=
  Ty.subst_subst ⟨.bvar, .rigid, f⟩ ⟨.bvar, .rigid, g⟩ ty

theorem bind_var (ty : Ty V) : ty.bind .var = ty :=
  Ty.subst_id ty

theorem bind_congr {ty : Ty V} {f g : V → Ty W} (agree : ∀ v ∈ ty.vars, f v = g v) :
    ty.bind f = ty.bind g :=
  Ty.subst_ext (fun _ => rfl) (fun _ => rfl) agree

theorem scoped_bind {ty : Ty V} {f : V → Ty W} (inScope : ty.Scoped rigids binders)
    (images : ∀ v ∈ ty.vars, (f v).Scoped rigids binders) :
    (ty.bind f).Scoped rigids binders :=
  Ty.scoped_subst inScope (fun _ hi => hi) (fun _ hl => hl) images

/-- A bind keeps bound and rigid variables and embeds every image, so the
scope of the result bounds the scope of the type and of every image. -/
theorem scoped_of_bind {ty : Ty V} {f : V → Ty W} (inScope : (ty.bind f).Scoped rigids binders) :
    ty.Scoped rigids binders ∧ ∀ v ∈ ty.vars, (f v).Scoped rigids binders := by
  induction ty with
  | prim _ | con _ => exact ⟨trivial, fun v hv => by simp [Ty.vars] at hv⟩
  | bvar _ | rigid _ => exact ⟨inScope, fun v hv => by simp [Ty.vars] at hv⟩
  | var v =>
      refine ⟨trivial, ?_⟩
      intro w hw
      simp [Ty.vars] at hw
      subst hw
      exact inScope
  | arrow d c ihd ihc | app d c ihd ihc =>
      obtain ⟨hd1, hd2⟩ := ihd inScope.1
      obtain ⟨hc1, hc2⟩ := ihc inScope.2
      exact ⟨⟨hd1, hc1⟩, fun v hv => (List.mem_append.mp hv).elim (hd2 v) (hc2 v)⟩

/-- If two binds agree, the maps agree on every variable of the type. -/
theorem bind_eq_bind_vars {ty : Ty V} {f g : V → Ty W} (equal : ty.bind f = ty.bind g) :
    ∀ v ∈ ty.vars, f v = g v := by
  induction ty with
  | prim _ | con _ | bvar _ | rigid _ => intro v hv; simp [Ty.vars] at hv
  | var v =>
      intro w hw
      simp [Ty.vars] at hw
      subst hw
      exact equal
  | arrow d c ihd ihc | app d c ihd ihc =>
      simp only [Ty.bind, Ty.subst] at equal
      injection equal with hd hc
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact ihd hd v hv
      · exact ihc hc v hv

theorem vars_lift (ty : SemTy) : (ty.lift : Ty V).vars = [] := by
  induction ty with
  | prim _ | con _ | bvar _ | rigid _ => rfl
  | var v => exact Empty.elim v
  | arrow d c ihd ihc | app d c ihd ihc =>
      change (d.lift : Ty V).vars ++ (c.lift : Ty V).vars = []
      rw [ihd, ihc, List.append_nil]

theorem lift_bind (ty : SemTy) (f : V → Ty W) : (ty.lift : Ty V).bind f = ty.lift := by
  change (ty.bind Empty.elim).bind f = ty.bind (Empty.elim : Empty → Ty W)
  rw [Ty.bind_bind]
  exact Ty.bind_congr fun v _ => Empty.elim v

theorem lift_self (ty : SemTy) : (ty.lift : SemTy) = ty := by
  change ty.bind (Empty.elim : Empty → Ty Empty) = ty
  have h : ty.bind (Empty.elim : Empty → Ty Empty) = ty.bind (fun v => .var v) :=
    Ty.bind_congr fun v _ => Empty.elim v
  rw [h, Ty.bind_var]

theorem scoped_lift {ty : SemTy} : (ty.lift : Ty V).Scoped rigids binders ↔ ty.Scoped rigids binders := by
  induction ty with
  | prim _ | con _ | bvar _ | rigid _ => rfl
  | var v => exact Empty.elim v
  | arrow d c ihd ihc | app d c ihd ihc =>
      change ((d.lift : Ty V).Scoped rigids binders ∧ (c.lift : Ty V).Scoped rigids binders) ↔
        (d.Scoped rigids binders ∧ c.Scoped rigids binders)
      exact and_congr ihd ihc

private theorem lift_ground (sem : SemTy) : (sem.lift : Ty V).ground = some sem := by
  induction sem with
  | prim _ => rfl
  | con _ => rfl
  | bvar _ => rfl
  | rigid _ => rfl
  | var v => exact Empty.elim v
  | arrow d c ihd ihc =>
      change ((d.lift : Ty V).ground >>= fun x =>
        ((c.lift : Ty V).ground >>= fun y => some (Ty.arrow x y))) = some (Ty.arrow d c)
      rw [ihd, ihc]
      rfl
  | app fn arg ihf iha =>
      change ((fn.lift : Ty V).ground >>= fun x =>
        ((arg.lift : Ty V).ground >>= fun y => some (Ty.app x y))) = some (Ty.app fn arg)
      rw [ihf, iha]
      rfl

private theorem option_bind_some_eq_none {α β : Type} {o : Option α} {g : α → β} :
    (o >>= fun a => some (g a)) = none ↔ o = none := by
  cases o <;> simp

private theorem option_bind2_none {α β γ : Type} {o1 : Option α} {o2 : Option β}
    {g : α → β → γ} :
    (o1 >>= fun x => o2 >>= fun y => some (g x y)) = none ↔ o1 = none ∨ o2 = none := by
  cases o1 <;> cases o2 <;> simp

private theorem ground_eq_some_aux (ty : Ty V) :
    ∀ sem : SemTy, ty.ground = some sem ↔ ty = sem.lift := by
  induction ty with
  | prim _ | con _ | bvar _ | rigid _ =>
      intro sem
      exact ⟨fun h => by rw [← Option.some.inj h]; rfl,
        fun h => by rw [h]; exact lift_ground sem⟩
  | var _ =>
      intro sem
      constructor
      · intro h
        change none = some sem at h
        cases h
      · intro h; rw [h]; exact lift_ground sem
  | arrow d c ihd ihc | app d c ihd ihc =>
      intro sem
      constructor
      · intro h
        simp only [Ty.ground] at h
        obtain ⟨ds, hd, h2⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨cs, hc, h3⟩ := Option.bind_eq_some_iff.mp h2
        obtain rfl := Option.some.inj h3
        rw [(ihd ds).mp hd, (ihc cs).mp hc]
        rfl
      · intro h; rw [h]; exact lift_ground sem

theorem ground_eq_some {ty : Ty V} {sem : SemTy} : ty.ground = some sem ↔ ty = sem.lift :=
  ground_eq_some_aux ty sem

theorem ground_eq_none {ty : Ty V} : ty.ground = none ↔ ty.vars ≠ [] := by
  induction ty with
  | prim _ | con _ | bvar _ | rigid _ | var _ => simp [Ty.ground, Ty.vars]
  | arrow d c ihd ihc | app d c ihd ihc =>
      simp only [Ty.ground, Ty.vars, option_bind2_none, ihd, ihc, ne_eq,
        List.append_eq_nil_iff, not_and_or]

theorem instantiate_nil (ty : Ty V) : ty.instantiate [] = ty := by
  change ty.subst ⟨fun i => ([] : List (Ty V)).getD i (.bvar i), .rigid, .var⟩ = ty
  exact Ty.subst_id ty

/-- A type with no bound variables is unchanged by `instantiate`. -/
private theorem instantiate_closed {ty : Ty V} {args : List (Ty V)} {rigids : Nat}
    (h : ty.Scoped rigids 0) : ty.instantiate args = ty := by
  induction ty with
  | prim _ | con _ | rigid _ | var _ => rfl
  | bvar i => exact absurd h (Nat.not_lt_zero i)
  | arrow d c ihd ihc =>
      change Ty.arrow (d.instantiate args) (c.instantiate args) = Ty.arrow d c
      rw [ihd h.1, ihc h.2]
  | app fn arg ihf iha =>
      change Ty.app (fn.instantiate args) (arg.instantiate args) = Ty.app fn arg
      rw [ihf h.1, iha h.2]

private theorem getD_map_bind (args : List (Ty V)) (f : V → Ty W) (i : Nat) :
    (args.getD i (.bvar i)).bind f = (args.map (·.bind f)).getD i (.bvar i) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases args[i]? <;> simp [Ty.bind, Ty.subst]

theorem instantiate_bind (args : List (Ty V)) {ty : Ty V} {f : V → Ty W}
    (closed : ∀ v ∈ ty.vars, (f v).Scoped rigids 0) :
    (ty.instantiate args).bind f = (ty.bind f).instantiate (args.map (·.bind f)) := by
  rw [Ty.bind, Ty.bind, Ty.instantiate, Ty.instantiate, Ty.subst_subst, Ty.subst_subst]
  refine Ty.subst_ext (fun i => getD_map_bind args f i) (fun _ => rfl) ?_
  intro v hv
  show f v = (f v).instantiate (args.map (fun a => a.bind f))
  exact (instantiate_closed (closed v hv)).symm

theorem instantiate_scoped {ty : Ty V} (inScope : ty.Scoped rigids args.length)
    (argsScoped : ∀ arg ∈ args, arg.Scoped rigids binders) :
    (ty.instantiate args).Scoped rigids binders := by
  induction ty with
  | prim _ | con _ | var _ => trivial
  | bvar i =>
      show (args.getD i (.bvar i)).Scoped rigids binders
      rw [getD_eq_getElem inScope]
      exact argsScoped _ (List.getElem_mem inScope)
  | rigid _ => exact inScope
  | arrow d c ihd ihc | app d c ihd ihc =>
      exact ⟨ihd inScope.1, ihc inScope.2⟩

theorem vars_closeRigids (k n : Nat) (ty : Ty V) : (ty.closeRigids k n).vars = ty.vars := by
  induction ty with
  | prim _ | con _ | bvar _ | var _ => rfl
  | rigid level =>
      by_cases h : k ≤ level ∧ level < k + n <;>
        simp [Ty.closeRigids, Ty.substRigids, Ty.subst, Ty.vars, h]
  | arrow d c ihd ihc | app d c ihd ihc =>
      change ((d.closeRigids k n).vars ++ (c.closeRigids k n).vars) = d.vars ++ c.vars
      rw [ihd, ihc]

theorem substRigids_wf {ty : Ty V} {f : Nat → Ty V} (wf : ty.WF k)
    (images : ∀ l < k, (f l).WF k') : (ty.substRigids f).WF k' :=
  Ty.scoped_subst (rigids := k) (binders := 0) (rigids' := k') (binders' := 0)
    wf (fun i hi => absurd hi (Nat.not_lt_zero i)) images (fun _ _ => trivial)

/-- Closing rigid levels absent from a type leaves it unchanged. -/
private theorem closeRigids_closed {ty : Ty V} (h : ty.WF k) (n : Nat) :
    ty.closeRigids k n = ty := by
  change ty.subst ⟨.bvar, (fun l => if k ≤ l ∧ l < k + n then .bvar (l - k) else .rigid l),
    .var⟩ = ty
  have hcongr : ty.subst ⟨.bvar,
      (fun l => if k ≤ l ∧ l < k + n then .bvar (l - k) else .rigid l), .var⟩ =
      ty.subst Subst.id := by
    refine Ty.subst_congr h ?_ ?_ ?_
    · intro i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro l hl
      have hnot : ¬ (k ≤ l ∧ l < k + n) := by omega
      change (if k ≤ l ∧ l < k + n then Ty.bvar (l - k) else Ty.rigid l) = Ty.rigid l
      rw [if_neg hnot]
    · intro v hv; rfl
  rw [hcongr, Ty.subst_id]

/-- Closing a block commutes with a bind whose images do not mention the
block. -/
theorem closeRigids_bind {ty : Ty V} {f : V → Ty W}
    (images : ∀ v ∈ ty.vars, (f v).WF k) :
    (ty.closeRigids k n).bind f = (ty.bind f).closeRigids k n := by
  rw [Ty.bind, Ty.bind, Ty.closeRigids, Ty.closeRigids, Ty.substRigids, Ty.substRigids,
    Ty.subst_subst, Ty.subst_subst]
  refine Ty.subst_ext (fun _ => rfl) ?_ ?_
  · intro l
    by_cases h : k ≤ l ∧ l < k + n <;> simp [Ty.Subst.comp, Ty.subst, h]
  · intro v hv
    show f v = (f v).closeRigids k n
    exact (closeRigids_closed (images v hv) n).symm

end Ty

/-- Rigid levels below `k` are kept; level `k + i` becomes `args[i]`. -/
def blockSubst (k : Nat) (args : List (Ty V)) : Nat → Ty V :=
  fun l => if l < k then .rigid l else args.getD (l - k) (.rigid l)

/-- A level of the block is replaced by the corresponding argument; the value
substituted below `k` is irrelevant. -/
private theorem blockSubst_add {k i : Nat} {args : List (Ty V)} {g : Nat → Ty V}
    (h : i < args.length) :
    (if k + i < k then g (k + i) else args.getD (k + i - k) (.rigid (k + i))) =
      args.getD i (.bvar i) := by
  rw [if_neg (by omega : ¬ k + i < k), show k + i - k = i by omega,
    Ty.getD_eq_getElem h, Ty.getD_eq_getElem h]

/-- Levels below `k` are untouched by `blockSubst`. -/
private theorem blockSubst_lt {k l : Nat} {args : List (Ty V)} (h : l < k) :
    blockSubst k args l = .rigid l := by
  unfold blockSubst
  rw [if_pos h]

private theorem rigidBlock_length (k n : Nat) : (rigidBlock k n : List (Ty V)).length = n := by
  simp [rigidBlock]

private theorem rigidBlock_getD {k n i : Nat} {d : Ty V} (h : i < n) :
    (rigidBlock k n).getD i d = .rigid (k + i) := by
  simp only [rigidBlock, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

private theorem rigidBlock_mem {k n : Nat} {ty : Ty V} :
    ty ∈ rigidBlock k n ↔ ∃ i, i < n ∧ ty = .rigid (k + i) := by
  simp only [rigidBlock, List.mem_map, List.mem_range]
  constructor <;> rintro ⟨i, hi, rfl⟩ <;> exact ⟨i, hi, rfl⟩

/-- Every member of a rigid block is a rigid variable below `k + n`. -/
private theorem rigidBlock_wf {k n : Nat} {arg : Ty V} (harg : arg ∈ rigidBlock k n) :
    arg.WF (k + n) := by
  rw [rigidBlock_mem] at harg
  obtain ⟨i, hi, rfl⟩ := harg
  show k + i < k + n
  omega

private theorem rigidBlock_bind (k n : Nat) (f : V → Ty W) :
    (rigidBlock k n).map (·.bind f) = (rigidBlock k n : List (Ty W)) := by
  simp [rigidBlock, Ty.bind, Ty.subst]

namespace Scheme

theorem skolemize_wf {scheme : Scheme V} (wf : scheme.WF k) :
    (scheme.skolemize k).WF (k + scheme.arity) := by
  show (scheme.body.instantiate (rigidBlock k scheme.arity)).Scoped (k + scheme.arity) 0
  refine Ty.instantiate_scoped (rigids := k + scheme.arity) (binders := 0) ?_ ?_
  · rw [rigidBlock_length]
    exact Ty.Scoped.mono wf (by omega) (le_refl _)
  · exact fun _ harg => rigidBlock_wf harg

theorem inst_wf {scheme : Scheme V} (wf : scheme.WF k) (le : k ≤ k')
    (length : args.length = scheme.arity) (argsWF : ∀ arg ∈ args, arg.WF k') :
    (scheme.inst args).WF k' := by
  show (scheme.body.instantiate args).Scoped k' 0
  refine Ty.instantiate_scoped (rigids := k') (binders := 0) ?_ ?_
  · rw [length]
    exact Ty.Scoped.mono wf le (le_refl _)
  · exact argsWF

/-- The generic instance is an instance, one block deeper. -/
theorem skolemize_instance (scheme : Scheme V) (k : Nat) :
    scheme.Instance (k + scheme.arity) (scheme.skolemize k) :=
  ⟨rigidBlock k scheme.arity, rigidBlock_length k scheme.arity,
    fun _ harg => rigidBlock_wf harg, rfl⟩

theorem Instance.mono {scheme : Scheme V} {ty : Ty V} (inst : scheme.Instance k ty)
    (le : k ≤ k') : scheme.Instance k' ty := by
  obtain ⟨args, length, wf, h⟩ := inst
  exact ⟨args, length, fun arg harg => Ty.Scoped.mono (wf arg harg) le (le_refl _), h⟩

/-- A monomorphic scheme's only instance is its type. -/
theorem instance_mono {ty ty' : Ty V} : (Scheme.mono ty').Instance k ty ↔ ty = ty' := by
  constructor
  · rintro ⟨args, length, _, h⟩
    cases args with
    | nil => simpa [Scheme.inst, Scheme.mono, Ty.instantiate_nil] using h.symm
    | cons a as => simp [Scheme.mono] at length
  · rintro rfl
    exact ⟨[], rfl, by simp, by simp [Scheme.inst, Scheme.mono, Ty.instantiate_nil]⟩

theorem skolemize_bind (scheme : Scheme V) {f : V → Ty W} (k : Nat)
    (closed : ∀ v ∈ scheme.body.vars, (f v).Scoped rigids 0) :
    (scheme.bind f).skolemize k = (scheme.skolemize k).bind f := by
  show (scheme.body.bind f).instantiate (rigidBlock k scheme.arity) =
    (scheme.body.instantiate (rigidBlock k scheme.arity)).bind f
  rw [Ty.instantiate_bind (args := rigidBlock k scheme.arity) (ty := scheme.body) (f := f) closed]
  rw [rigidBlock_bind]

theorem inst_bind (scheme : Scheme V) (args : List (Ty V)) {f : V → Ty W}
    (closed : ∀ v ∈ scheme.body.vars, (f v).Scoped rigids 0) :
    (scheme.inst args).bind f = (scheme.bind f).inst (args.map (·.bind f)) := by
  show (scheme.body.instantiate args).bind f =
    (scheme.body.bind f).instantiate (args.map (·.bind f))
  exact Ty.instantiate_bind args closed

/-- Every instance is a type substitution of the generic instance. -/
theorem skolemize_substRigids {scheme : Scheme V} (wf : scheme.WF k)
    (length : args.length = scheme.arity) :
    (scheme.skolemize k).substRigids (blockSubst k args) = scheme.inst args := by
  show (scheme.body.subst ⟨fun i => (rigidBlock k scheme.arity).getD i (.bvar i), .rigid, .var⟩).subst
      ⟨.bvar, blockSubst k args, .var⟩ =
    scheme.body.subst ⟨fun i => args.getD i (.bvar i), .rigid, .var⟩
  rw [Ty.subst_subst]
  refine Ty.subst_congr wf ?_ ?_ ?_
  · intro i hi
    show ((rigidBlock k scheme.arity).getD i (.bvar i)).subst
      ⟨.bvar, blockSubst k args, .var⟩ = args.getD i (.bvar i)
    rw [rigidBlock_getD (k := k) (n := scheme.arity) (i := i) (d := .bvar i) (by omega)]
    show blockSubst k args (k + i) = args.getD i (.bvar i)
    exact blockSubst_add (by omega)
  · intro l hl
    show blockSubst k args l = Ty.rigid l
    exact blockSubst_lt hl
  · intro v hv; rfl

/-- Every instance of a type substitution of a scheme is one type
substitution of the generic instance: `f` below `k`, the instance's arguments
on the block. (`skolemize_substRigids` is the case `f = .rigid`.) -/
theorem skolemize_substRigids_inst {scheme : Scheme V} {f : Nat → Ty V} (wf : scheme.WF k)
    (length : args.length = scheme.arity) (closed : ∀ l < k, (f l).Scoped rigids 0) :
    (scheme.skolemize k).substRigids
        (fun l => if l < k then f l else args.getD (l - k) (.rigid l)) =
      (scheme.substRigids f).inst args := by
  show (scheme.body.subst ⟨fun i => (rigidBlock k scheme.arity).getD i (.bvar i), .rigid, .var⟩).subst
      ⟨.bvar, (fun l => if l < k then f l else args.getD (l - k) (.rigid l)), .var⟩ =
    (scheme.body.subst ⟨.bvar, f, .var⟩).subst ⟨fun i => args.getD i (.bvar i), .rigid, .var⟩
  rw [Ty.subst_subst, Ty.subst_subst]
  refine Ty.subst_congr wf ?_ ?_ ?_
  · intro i hi
    show ((rigidBlock k scheme.arity).getD i (.bvar i)).subst
      ⟨.bvar, (fun l => if l < k then f l else args.getD (l - k) (.rigid l)), .var⟩ =
      args.getD i (.bvar i)
    rw [rigidBlock_getD (k := k) (n := scheme.arity) (i := i) (d := .bvar i) (by omega)]
    show (if k + i < k then f (k + i) else args.getD (k + i - k) (.rigid (k + i))) =
      args.getD i (.bvar i)
    exact blockSubst_add (by omega)
  · intro l hl
    show (if l < k then f l else args.getD (l - k) (.rigid l)) =
      (f l).subst ⟨fun i => args.getD i (.bvar i), .rigid, .var⟩
    rw [if_pos hl]
    exact (Ty.instantiate_closed (args := args) (closed l hl)).symm
  · intro v hv; rfl

theorem substRigids_congr {scheme : Scheme V} {f g : Nat → Ty V} (wf : scheme.WF k)
    (agree : ∀ l < k, f l = g l) : scheme.substRigids f = scheme.substRigids g := by
  have h : scheme.body.substRigids f = scheme.body.substRigids g := by
    show scheme.body.subst ⟨.bvar, f, .var⟩ = scheme.body.subst ⟨.bvar, g, .var⟩
    exact Ty.subst_congr wf (fun _ _ => rfl) (fun l hl => agree l hl) (fun _ _ => rfl)
  cases scheme with
  | mk arity body => simp only [Scheme.substRigids, h]

theorem substRigids_wf {scheme : Scheme V} {f : Nat → Ty V} (wf : scheme.WF k)
    (images : ∀ l < k, (f l).WF k') : (scheme.substRigids f).WF k' := by
  show (scheme.body.subst ⟨.bvar, f, .var⟩).Scoped k' scheme.arity
  refine Ty.scoped_subst (rigids := k) (binders := scheme.arity) (rigids' := k')
    (binders' := scheme.arity) wf ?_ ?_ ?_
  · intro i hi; exact hi
  · intro l hl
    exact Ty.Scoped.mono (images l hl) (le_refl k') (Nat.zero_le scheme.arity)
  · intro v hv; trivial

/-- A scheme well-formed at `k` is untouched by a type substitution that is
the identity below `k`. -/
theorem substRigids_eq_self {scheme : Scheme V} (wf : scheme.WF k)
    (identity : ∀ l < k, f l = .rigid l) :
    scheme.substRigids f = scheme := by
  have h : scheme.body.substRigids f = scheme.body := by
    show scheme.body.subst ⟨.bvar, f, .var⟩ = scheme.body
    have hc : scheme.body.subst ⟨.bvar, f, .var⟩ = scheme.body.subst Ty.Subst.id :=
      Ty.subst_congr wf (fun _ _ => rfl) (fun l hl => identity l hl) (fun _ _ => rfl)
    rw [hc, Ty.subst_id]
  cases scheme with
  | mk arity body => simp only [Scheme.substRigids, h]

private theorem getD_map_substRigids (args : List (Ty V)) (f : Nat → Ty V) (i : Nat) :
    (args.getD i (.bvar i)).substRigids f =
      (args.map (·.substRigids f)).getD i (.bvar i) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases args[i]? <;> simp [Ty.substRigids, Ty.subst]

theorem inst_substRigids {scheme : Scheme V} (args : List (Ty V)) {f : Nat → Ty V}
    (wf : scheme.WF k) (closed : ∀ l < k, (f l).Scoped rigids 0) :
    (scheme.inst args).substRigids f =
      (scheme.substRigids f).inst (args.map (·.substRigids f)) := by
  show (scheme.body.subst ⟨fun i => args.getD i (.bvar i), .rigid, .var⟩).subst ⟨.bvar, f, .var⟩ =
    (scheme.body.subst ⟨.bvar, f, .var⟩).subst
      ⟨fun i => (args.map (·.substRigids f)).getD i (.bvar i), .rigid, .var⟩
  rw [Ty.subst_subst, Ty.subst_subst]
  refine Ty.subst_congr wf ?_ ?_ ?_
  · intro i hi
    show (args.getD i (.bvar i)).substRigids f =
      (args.map (·.substRigids f)).getD i (.bvar i)
    exact getD_map_substRigids args f i
  · intro l hl
    show f l = (f l).subst
      ⟨fun i => (args.map (·.substRigids f)).getD i (.bvar i), .rigid, .var⟩
    exact (Ty.instantiate_closed (args := args.map (·.substRigids f)) (closed l hl)).symm
  · intro v hv; rfl

/-- Closing a generic type and reopening it at the same depth is the identity. -/
theorem skolemize_closeRigids {ty : Ty V} (wf : ty.WF (k + n)) :
    (⟨n, ty.closeRigids k n⟩ : Scheme V).skolemize k = ty := by
  let σ : Ty.Subst V V :=
    ⟨.bvar, (fun l => if k ≤ l ∧ l < k + n then .bvar (l - k) else .rigid l), .var⟩
  let τ : Ty.Subst V V := ⟨fun i => (rigidBlock k n).getD i (.bvar i), .rigid, .var⟩
  show (ty.subst σ).subst τ = ty
  rw [Ty.subst_subst]
  have h : ty.subst (σ.comp τ) = ty.subst Ty.Subst.id := by
    refine Ty.subst_congr wf ?_ ?_ ?_
    · intro i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro l hl
      show ((if k ≤ l ∧ l < k + n then Ty.bvar (l - k) else Ty.rigid l) : Ty V).subst τ = Ty.rigid l
      split_ifs with hcond
      · show (rigidBlock k n).getD (l - k) (.bvar (l - k)) = Ty.rigid l
        rw [rigidBlock_getD (k := k) (n := n) (i := l - k) (d := .bvar (l - k)) (by omega),
          show k + (l - k) = l by omega]
      · rfl
    · intro v hv; rfl
  rw [h, Ty.subst_id]

theorem closeRigids_wf {ty : Ty V} (wf : ty.WF (k + n)) :
    (⟨n, ty.closeRigids k n⟩ : Scheme V).WF k := by
  let σ : Ty.Subst V V :=
    ⟨.bvar, (fun l => if k ≤ l ∧ l < k + n then .bvar (l - k) else .rigid l), .var⟩
  show (ty.subst σ).Scoped k n
  refine Ty.scoped_subst (rigids := k + n) (binders := 0) (rigids' := k) (binders' := n) wf ?_ ?_ ?_
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)
  · intro l hl
    show Ty.Scoped k n (if k ≤ l ∧ l < k + n then Ty.bvar (l - k) else Ty.rigid l)
    split_ifs with hcond <;> simp only [Ty.Scoped] <;> omega
  · intro v hv; trivial

/-- Opening a well-formed scheme and closing it at the same depth is the
identity. -/
theorem closeRigids_skolemize {scheme : Scheme V} (wf : scheme.WF k) :
    (scheme.skolemize k).closeRigids k scheme.arity = scheme.body := by
  let σ : Ty.Subst V V :=
    ⟨fun i => (rigidBlock k scheme.arity).getD i (.bvar i), .rigid, .var⟩
  let τ : Ty.Subst V V :=
    ⟨.bvar, (fun l => if k ≤ l ∧ l < k + scheme.arity then .bvar (l - k) else .rigid l), .var⟩
  show (scheme.body.subst σ).subst τ = scheme.body
  rw [Ty.subst_subst]
  have h : scheme.body.subst (σ.comp τ) = scheme.body.subst Ty.Subst.id := by
    refine Ty.subst_congr wf ?_ ?_ ?_
    · intro i hi
      show ((rigidBlock k scheme.arity).getD i (.bvar i)).subst τ = Ty.bvar i
      by_cases hlt : i < scheme.arity
      · rw [rigidBlock_getD (k := k) (n := scheme.arity) (i := i) (d := .bvar i) hlt]
        show (if k ≤ k + i ∧ k + i < k + scheme.arity then Ty.bvar (k + i - k) else Ty.rigid (k + i)) =
          Ty.bvar i
        rw [if_pos (by omega)]
        rw [show k + i - k = i by omega]
      · have hge : (rigidBlock k scheme.arity : List (Ty V)).length ≤ i := by
          rw [rigidBlock_length]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
        rfl
    · intro l hl
      show (if k ≤ l ∧ l < k + scheme.arity then Ty.bvar (l - k) else Ty.rigid l) = Ty.rigid l
      rw [if_neg (by omega)]
    · intro v hv; rfl
  rw [h, Ty.subst_id]

/-- A well-formed scheme is determined by its generic instance. -/
theorem skolemize_injective {first second : Scheme V} (firstWF : first.WF k)
    (secondWF : second.WF k) (arity : first.arity = second.arity)
    (equal : first.skolemize k = second.skolemize k) : first = second := by
  have hfirst := Scheme.closeRigids_skolemize firstWF
  have hsecond := Scheme.closeRigids_skolemize secondWF
  have hbody : first.body = second.body := by
    rw [← hfirst, ← hsecond, equal, arity]
  obtain ⟨fa, fb⟩ := first
  obtain ⟨sa, sb⟩ := second
  simp_all

end Scheme

theorem Ctx.WF.mono {ctx : Ctx V} (wf : ctx.WF k) (le : k ≤ k') : ctx.WF k' := by
  intro scheme hmem
  exact Ty.Scoped.mono (wf scheme hmem) le (le_refl _)

namespace Expr

/-! ### Branch lists

Each `…Branches` companion is the obvious `List.map` (or `flatMap`); these
`simp` lemmas let proofs work with `List` lemmas instead of the mutual
recursion. -/

@[simp] theorem mapAnnBranches_eq (f : A → B) (branches : List (Pattern × Expr A)) :
    Expr.mapAnnBranches f branches = branches.map fun branch => (branch.1, branch.2.mapAnn f) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih => simp [Expr.mapAnnBranches, ih]

@[simp] theorem annsBranches_eq (branches : List (Pattern × Expr A)) :
    Expr.annsBranches branches = branches.flatMap (·.2.anns) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih => simp [Expr.annsBranches, ih]

@[simp] theorem eraseBranches_eq (branches : List (Pattern × Expr A)) :
    Expr.eraseBranches branches = branches.map fun branch => (branch.1, branch.2.erase) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih => simp [Expr.eraseBranches, ih]

@[simp] theorem shiftBranches_eq (cutoff amount : Nat) (branches : List (Pattern × Expr A)) :
    Expr.shiftBranches cutoff amount branches =
      branches.map fun branch => (branch.1, branch.2.shift (cutoff + branch.1.binders) amount) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih => simp [Expr.shiftBranches, ih]

@[simp] theorem substAtBranches_eq (branches : List (Pattern × Expr A)) (depth : Nat)
    (value : Expr A) :
    Expr.substAtBranches branches depth value =
      branches.map fun branch => (branch.1, branch.2.substAt (depth + branch.1.binders) value) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih => simp [Expr.substAtBranches, ih]

theorem traverseAnnBranches_eq (f : A → Option B) (branches : List (Pattern × Expr A)) :
    Expr.traverseAnnBranches f branches =
      branches.mapM fun branch => (branch.2.traverseAnn f).map (branch.1, ·) := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      obtain ⟨pattern, body⟩ := branch
      simp only [Expr.traverseAnnBranches, ih, List.mapM_cons]
      cases body.traverseAnn f <;> simp

/-- Mapping the bodies commutes with looking up a branch. -/
theorem findBranch_map (g : Expr A → Expr B) (ref : CtorRef) (branches : List (Pattern × Expr A)) :
    findBranch ref (branches.map fun branch => (branch.1, g branch.2)) =
      (findBranch ref branches).map g := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      by_cases h : branch.1.ctor = ref <;> simp_all [findBranch]

/-- The branch found is one of the branches, and its pattern is for `ref`. -/
theorem findBranch_mem {ref : CtorRef} {branches : List (Pattern × Expr A)} {body : Expr A}
    (found : findBranch ref branches = some body) :
    ∃ pattern, pattern.ctor = ref ∧ (pattern, body) ∈ branches := by
  simp only [findBranch, Option.map_eq_some_iff] at found
  obtain ⟨⟨pattern, body'⟩, find, rfl⟩ := found
  have := List.find?_some find
  simp at this
  exact ⟨pattern, this, List.mem_of_find?_eq_some find⟩


/-- A branch body's annotations are among the annotations of the branch list. -/
private theorem mem_annsBranches_of_mem {branch : Pattern × Expr A}
    {branches : List (Pattern × Expr A)} {ann : A} (mem : branch ∈ branches)
    (inBody : ann ∈ branch.2.anns) : ann ∈ Expr.annsBranches branches := by
  rw [Expr.annsBranches_eq]
  exact List.mem_flatMap_of_mem mem inBody

/-- The branch-list form of `anns_mapAnn`. -/
private theorem annsBranches_mapAnnBranches {f : A → B} {branches : List (Pattern × Expr A)}
    (hbranch : ∀ branch ∈ branches, (branch.2.mapAnn f).anns = branch.2.anns.map f) :
    Expr.annsBranches (Expr.mapAnnBranches f branches) = (Expr.annsBranches branches).map f := by
  induction branches with
  | nil => rfl
  | cons branch rest ihrest =>
      obtain ⟨pattern, body⟩ := branch
      have ih := ihrest fun branch mem => hbranch branch (List.mem_cons_of_mem _ mem)
      simp only [Expr.annsBranches_eq, Expr.mapAnnBranches_eq, List.map_cons, List.flatMap_cons,
        List.map_append]
      rw [hbranch (pattern, body) (by simp)]
      congr 1
      simpa only [← Expr.annsBranches_eq, ← Expr.mapAnnBranches_eq] using ih

/-- Pointwise equality of mapped branch bodies is equality of the branch lists. -/
private theorem mapAnnBranches_congr {f g : A → B} {branches : List (Pattern × Expr A)}
    (hbranch : ∀ branch ∈ branches, branch.2.mapAnn f = branch.2.mapAnn g) :
    Expr.mapAnnBranches f branches = Expr.mapAnnBranches g branches := by
  induction branches with
  | nil => rfl
  | cons branch rest ihrest =>
      obtain ⟨pattern, body⟩ := branch
      have ih := ihrest fun branch mem => hbranch branch (List.mem_cons_of_mem _ mem)
      simp only [Expr.mapAnnBranches_eq, List.map_cons]
      rw [hbranch (pattern, body) (by simp)]
      congr 1
      simpa only [← Expr.mapAnnBranches_eq] using ih

/-- Equality of mapped branch lists makes the maps agree on the branch bodies'
annotations. -/
private theorem annsBranches_mapAnn_eq {f g : A → B} {branches : List (Pattern × Expr A)}
    (equal : Expr.mapAnnBranches f branches = Expr.mapAnnBranches g branches)
    (hbranch : ∀ branch ∈ branches, branch.2.mapAnn f = branch.2.mapAnn g →
      ∀ ann ∈ branch.2.anns, f ann = g ann) :
    ∀ ann ∈ Expr.annsBranches branches, f ann = g ann := by
  induction branches with
  | nil => intro ann mem; simp at mem
  | cons branch rest ihrest =>
      obtain ⟨pattern, body⟩ := branch
      simp only [Expr.mapAnnBranches_eq, List.map_cons, List.cons.injEq] at equal
      obtain ⟨hhead, htail⟩ := equal
      have hbody : body.mapAnn f = body.mapAnn g := congrArg Prod.snd hhead
      have ih := ihrest (by simpa only [Expr.mapAnnBranches_eq] using htail)
        fun branch mem => hbranch branch (List.mem_cons_of_mem _ mem)
      intro ann mem
      rw [show Expr.annsBranches ((pattern, body) :: rest) =
        body.anns ++ Expr.annsBranches rest by
          simp only [Expr.annsBranches_eq, List.flatMap_cons]] at mem
      rcases List.mem_append.mp mem with mem | mem
      · exact hbranch (pattern, body) (by simp) hbody ann mem
      · exact ih ann mem

theorem anns_mapAnn (f : A → B) (expr : Expr A) : (expr.mapAnn f).anns = expr.anns.map f := by
  induction expr with
  | «match» scrutinee branches ih ihs =>
      have hbranches := annsBranches_mapAnnBranches (f := f) (branches := branches)
        fun branch mem => ihs branch mem
      rw [Expr.mapAnn, Expr.anns, Expr.anns, ih, hbranches, List.map_append]
  | lit _ | primOp _ | ctor _ | var _ => rfl
  | lambda param body ih =>
      cases param <;> simp [Expr.mapAnn, Expr.anns, ih]
  | app fn arg ihf iha =>
      simp [Expr.mapAnn, Expr.anns, ihf, iha, List.map_append]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none => simp [Expr.mapAnn, Expr.anns, ihr, ihb, List.map_append]
      | some a => simp [Expr.mapAnn, Expr.anns, ihr, ihb, List.map_append, PolyAnn.map]
  | fix self body ih =>
      cases self <;> simp [Expr.mapAnn, Expr.anns, ih]

theorem mapAnn_congr {f g : A → B} {expr : Expr A} (agree : ∀ ann ∈ expr.anns, f ann = g ann) :
    expr.mapAnn f = expr.mapAnn g := by
  induction expr with
  | «match» scrutinee branches ih ihs =>
      have hscrutinee : scrutinee.mapAnn f = scrutinee.mapAnn g :=
        ih fun ann mem => agree ann (by simp [Expr.anns, mem])
      have hbranches : Expr.mapAnnBranches f branches = Expr.mapAnnBranches g branches :=
        mapAnnBranches_congr fun branch mem =>
          ihs branch mem fun ann hann => agree ann (by
            rw [Expr.anns, List.mem_append]
            exact Or.inr (mem_annsBranches_of_mem mem hann))
      simp only [Expr.mapAnn, hscrutinee, hbranches]
  | lit _ | primOp _ | ctor _ | var _ => rfl
  | lambda param body ih =>
      cases param with
      | none =>
          simp [Expr.mapAnn, ih (fun ann hann => agree ann (by simp [Expr.anns, hann]))]
      | some a =>
          simp [Expr.mapAnn, agree a (by simp [Expr.anns]),
            ih (fun ann hann => agree ann (by simp [Expr.anns, hann]))]
  | app fn arg ihf iha =>
      simp [Expr.mapAnn, ihf (fun ann hann => agree ann (by simp [Expr.anns, hann])),
        iha (fun ann hann => agree ann (by simp [Expr.anns, hann]))]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp [Expr.mapAnn, ihr (fun ann hann => agree ann (by simp [Expr.anns, hann])),
            ihb (fun ann hann => agree ann (by simp [Expr.anns, hann]))]
      | some a =>
          simp [Expr.mapAnn, PolyAnn.map, agree a.body (by simp [Expr.anns]),
            ihr (fun ann hann => agree ann (by simp [Expr.anns, hann])),
            ihb (fun ann hann => agree ann (by simp [Expr.anns, hann]))]
  | fix self body ih =>
      cases self with
      | none =>
          simp [Expr.mapAnn, ih (fun ann hann => agree ann (by simp [Expr.anns, hann]))]
      | some a =>
          simp [Expr.mapAnn, agree a (by simp [Expr.anns]),
            ih (fun ann hann => agree ann (by simp [Expr.anns, hann]))]

/-- If two maps of an expression agree, the functions agree on every
annotation. -/
theorem mapAnn_eq_anns {f g : A → B} {expr : Expr A} (equal : expr.mapAnn f = expr.mapAnn g) :
    ∀ ann ∈ expr.anns, f ann = g ann := by
  induction expr with
  | «match» scrutinee branches ih ihs =>
      injection equal with hscrutinee hbranches
      have hbodies := annsBranches_mapAnn_eq hbranches fun branch mem => ihs branch mem
      intro ann mem
      rw [Expr.anns, List.mem_append] at mem
      rcases mem with mem | mem
      · exact ih hscrutinee ann mem
      · exact hbodies ann mem
  | lit _ | primOp _ | ctor _ | var _ => intro ann h; simp [Expr.anns] at h
  | lambda param body ih =>
      intro ann hmem
      cases param with
      | none =>
          simp only [Expr.anns] at hmem
          have hb : body.mapAnn f = body.mapAnn g := by
            injection equal with _ _
          exact ih hb ann hmem
      | some a =>
          simp only [Expr.anns, List.mem_cons] at hmem
          rcases hmem with h | h
          · subst h
            injection equal with hp _
            exact Option.some.inj hp
          · have hb : body.mapAnn f = body.mapAnn g := by
              injection equal with _ _
            exact ih hb ann h
  | app fn arg ihf iha =>
      have hf : fn.mapAnn f = fn.mapAnn g := by injection equal with _ _
      have ha : arg.mapAnn f = arg.mapAnn g := by injection equal with _ _
      intro ann hmem
      simp only [Expr.anns, List.mem_append] at hmem
      rcases hmem with h | h
      · exact ihf hf ann h
      · exact iha ha ann h
  | letIn ann rhs body ihr ihb =>
      have hr : rhs.mapAnn f = rhs.mapAnn g := by injection equal with _ _ _
      have hb : body.mapAnn f = body.mapAnn g := by injection equal with _ _ _
      cases ann with
      | none =>
          intro ann' hmem
          simp only [Expr.anns, List.mem_append] at hmem
          rcases hmem with h | h
          · exact ihr hr ann' h
          · exact ihb hb ann' h
      | some a =>
          have hann : f a.body = g a.body := by
            injection equal with hann _ _
            have h1 : (⟨a.arity, f a.body⟩ : PolyAnn B) = ⟨a.arity, g a.body⟩ :=
              Option.some.inj hann
            injection h1 with _ _
          intro ann' hmem
          simp only [Expr.anns, List.mem_cons, List.mem_append] at hmem
          rcases hmem with h | h | h
          · subst h; exact hann
          · exact ihr hr ann' h
          · exact ihb hb ann' h
  | fix self body ih =>
      intro ann hmem
      cases self with
      | none =>
          simp only [Expr.anns] at hmem
          have hb : body.mapAnn f = body.mapAnn g := by
            injection equal with _ _
          exact ih hb ann hmem
      | some a =>
          simp only [Expr.anns, List.mem_cons] at hmem
          rcases hmem with h | h
          · subst h
            injection equal with hp _
            exact Option.some.inj hp
          · have hb : body.mapAnn f = body.mapAnn g := by
              injection equal with _ _
            exact ih hb ann h

private theorem option_bind_some_eq_some {α γ : Type} {o : Option α} {g : α → γ} {c : γ} :
    (o >>= fun a => some (g a)) = some c ↔ ∃ a, o = some a ∧ g a = c := by
  cases o <;> simp [eq_comm]

private theorem option_bind2_some {α β γ : Type} {o1 : Option α} {o2 : Option β}
    {g : α → β → γ} {c : γ} :
    (o1 >>= fun x => o2 >>= fun y => some (g x y)) = some c ↔
      ∃ x y, o1 = some x ∧ o2 = some y ∧ g x y = c := by
  cases o1 <;> cases o2 <;> simp [eq_comm]

private theorem option_bind3_some {α β γ δ : Type} {o1 : Option α} {o2 : Option β} {o3 : Option γ}
    {g : α → β → γ → δ} {c : δ} :
    (o1 >>= fun x => o2 >>= fun y => o3 >>= fun z => some (g x y z)) = some c ↔
      ∃ x y z, o1 = some x ∧ o2 = some y ∧ o3 = some z ∧ g x y z = c := by
  cases o1 <;> cases o2 <;> cases o3 <;> simp [eq_comm]

private theorem option_bind3_none {α β γ δ : Type} {o1 : Option α} {o2 : Option β} {o3 : Option γ}
    {g : α → β → γ → δ} :
    (o1 >>= fun x => o2 >>= fun y => o3 >>= fun z => some (g x y z)) = none ↔
      o1 = none ∨ o2 = none ∨ o3 = none := by
  cases o1 <;> cases o2 <;> cases o3 <;> simp

/-- The branch-list form of `traverseAnn_eq_none_iff`. -/
private theorem traverseAnnBranches_eq_none_iff {f : Ty V → Option SemTy}
    {branches : List (Pattern × Expr (Ty V))}
    (hbranch : ∀ branch ∈ branches,
      branch.2.traverseAnn f = none ↔ ∃ ann ∈ branch.2.anns, f ann = none) :
    Expr.traverseAnnBranches f branches = none ↔
      ∃ ann ∈ Expr.annsBranches branches, f ann = none := by
  induction branches with
  | nil => simp [Expr.traverseAnnBranches, Expr.annsBranches]
  | cons branch rest ihrest =>
      obtain ⟨pattern, body⟩ := branch
      have ih := ihrest fun branch mem => hbranch branch (List.mem_cons_of_mem _ mem)
      have hstep : Expr.traverseAnnBranches f ((pattern, body) :: rest) =
          (body.traverseAnn f >>= fun b =>
            Expr.traverseAnnBranches f rest >>= fun bs => some ((pattern, b) :: bs)) := rfl
      rw [hstep, Ty.option_bind2_none, hbranch (pattern, body) (by simp), ih,
        show Expr.annsBranches ((pattern, body) :: rest) = body.anns ++ Expr.annsBranches rest by
          simp only [Expr.annsBranches_eq, List.flatMap_cons],
        Ty.exists_mem_append]

private theorem traverseAnn_eq_none_iff {f : Ty V → Option SemTy} :
    ∀ (expr : Expr (Ty V)), expr.traverseAnn f = none ↔ ∃ ann ∈ expr.anns, f ann = none := by
  intro expr
  induction expr with
  | «match» scrutinee branches ih ihs =>
      have hbranches := traverseAnnBranches_eq_none_iff (f := f) (branches := branches)
        fun branch mem => ihs branch mem
      rw [Expr.traverseAnn, Ty.option_bind2_none, ih, hbranches, Expr.anns, Ty.exists_mem_append]
  | lit _ | primOp _ | ctor _ | var _ => simp [Expr.traverseAnn, Expr.anns]
  | lambda param body ih =>
      cases param with
      | none =>
          simp only [Expr.traverseAnn, Expr.anns]
          rw [Ty.option_bind_some_eq_none, ih]
      | some a =>
          simp only [Expr.traverseAnn, Expr.anns]
          rw [Ty.option_bind2_none, ih, List.exists_mem_cons_iff]
  | app fn arg ihf iha =>
      simp only [Expr.traverseAnn, Expr.anns, Ty.option_bind2_none, ihf, iha, Ty.exists_mem_append]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp only [Expr.traverseAnn, Expr.anns, Ty.option_bind2_none, ihr, ihb, Ty.exists_mem_append]
      | some a =>
          simp only [Expr.traverseAnn, Expr.anns, option_bind3_none, ihr, ihb,
            List.exists_mem_cons_iff, Ty.exists_mem_append]
  | fix self body ih =>
      cases self with
      | none =>
          simp only [Expr.traverseAnn, Expr.anns]
          rw [Ty.option_bind_some_eq_none, ih]
      | some a =>
          simp only [Expr.traverseAnn, Expr.anns]
          rw [Ty.option_bind2_none, ih, List.exists_mem_cons_iff]

/-- The branch-list form of `traverseAnn_eq_some_iff`. -/
private theorem traverseAnnBranches_eq_some_iff {f : Ty V → Option SemTy} {r : SemTy → Ty V}
    {branches : List (Pattern × Expr (Ty V))}
    (hbranch : ∀ branch ∈ branches, ∀ el : Elab,
      branch.2.traverseAnn f = some el ↔ branch.2 = el.mapAnn r) :
    ∀ ys : List (Pattern × Elab),
      Expr.traverseAnnBranches f branches = some ys ↔ branches = Expr.mapAnnBranches r ys := by
  induction branches with
  | nil =>
      intro ys
      rw [Expr.mapAnnBranches_eq]
      simp [Expr.traverseAnnBranches]
  | cons branch rest ihrest =>
      obtain ⟨pattern, body⟩ := branch
      have hhead : ∀ el : Elab, body.traverseAnn f = some el ↔ body = el.mapAnn r :=
        hbranch (pattern, body) (by simp)
      have hrest := ihrest fun branch mem => hbranch branch (List.mem_cons_of_mem _ mem)
      have hstep : Expr.traverseAnnBranches f ((pattern, body) :: rest) =
          (body.traverseAnn f >>= fun b =>
            Expr.traverseAnnBranches f rest >>= fun bs => some ((pattern, b) :: bs)) := rfl
      intro ys
      constructor
      · intro h
        rw [hstep] at h
        obtain ⟨b, bs, hb, hbs, rfl⟩ := option_bind2_some.mp h
        rw [(hhead b).mp hb, (hrest bs).mp hbs]
        simp only [Expr.mapAnnBranches_eq, List.map_cons]
      · intro h
        cases ys with
        | nil =>
            rw [Expr.mapAnnBranches_eq, List.map_nil] at h
            cases h
        | cons y ys' =>
            rw [Expr.mapAnnBranches_eq, List.map_cons, List.cons.injEq] at h
            obtain ⟨hpair, htail⟩ := h
            have hbody : body = y.2.mapAnn r := congrArg Prod.snd hpair
            have hpat : pattern = y.1 := congrArg Prod.fst hpair
            have htail' : rest = Expr.mapAnnBranches r ys' := by
              simpa only [Expr.mapAnnBranches_eq] using htail
            rw [hstep, (hhead y.2).mpr hbody, (hrest ys').mpr htail', hpat]
            rfl

private theorem traverseAnn_eq_some_iff {f : Ty V → Option SemTy} {r : SemTy → Ty V}
    (hf : ∀ (ty : Ty V) (sem : SemTy), f ty = some sem ↔ ty = r sem) :
    ∀ (expr : Expr (Ty V)) (el : Elab),
      expr.traverseAnn f = some el ↔ expr = el.mapAnn r := by
  intro expr
  induction expr with
  | «match» scrutinee branches ih ihs =>
      have hbranches := traverseAnnBranches_eq_some_iff (f := f) (r := r) (branches := branches)
        fun branch mem => ihs branch mem
      intro el
      constructor
      · intro h
        rw [Expr.traverseAnn] at h
        obtain ⟨s, bs, hs, hbs, rfl⟩ := option_bind2_some.mp h
        have hscrutinee : scrutinee = s.mapAnn r := (ih s).mp hs
        have hbranches' : branches = Expr.mapAnnBranches r bs := (hbranches bs).mp hbs
        simp only [Expr.mapAnn, hscrutinee, hbranches']
      · intro h
        cases el <;> try simp [Expr.mapAnn] at h
        case «match» elScrutinee elBranches =>
          obtain ⟨hscrutinee, hbranches'⟩ := h
          have hbranches'' : branches = Expr.mapAnnBranches r elBranches := by
            simpa only [Expr.mapAnnBranches_eq] using hbranches'
          rw [Expr.traverseAnn, (ih elScrutinee).mpr hscrutinee,
            (hbranches elBranches).mpr hbranches'']
          rfl
  | lit l | primOp l | ctor l | var l =>
      intro el
      constructor
      · intro h
        rw [Expr.traverseAnn] at h
        obtain rfl := (Option.some.inj h).symm
        simp [Expr.mapAnn]
      · intro h
        cases el <;> simp_all [Expr.traverseAnn, Expr.mapAnn]
  | lambda param body ih =>
      intro el
      cases param with
      | none =>
          constructor
          · intro h
            rw [Expr.traverseAnn] at h
            obtain ⟨e, hb, he⟩ := option_bind_some_eq_some.mp h
            have hbody : body = e.mapAnn r := (ih e).mp hb
            subst he
            simp [Expr.mapAnn, hbody]
          · intro h
            cases el <;> try simp [Expr.mapAnn] at h
            case lambda p ebody =>
              cases p with
              | none =>
                  simp only [Option.map_none] at h
                  obtain ⟨-, hbody⟩ := h
                  simp [Expr.traverseAnn, (ih ebody).mpr hbody]
              | some b => simp at h
      | some a =>
          constructor
          · intro h
            rw [Expr.traverseAnn] at h
            obtain ⟨x, y, ha, hb, he⟩ := option_bind2_some.mp h
            have hax : a = r x := (hf a x).mp ha
            have hbody : body = y.mapAnn r := (ih y).mp hb
            subst he
            simp [Expr.mapAnn, hax, hbody]
          · intro h
            cases el <;> try simp [Expr.mapAnn] at h
            case lambda p ebody =>
              cases p with
              | none => simp at h
              | some b =>
                  simp only [Option.map_some, Option.some.injEq] at h
                  obtain ⟨ha, hbody⟩ := h
                  have hfa : f a = some b := (hf a b).mpr ha
                  simp [Expr.traverseAnn, hfa, (ih ebody).mpr hbody]
  | app fn arg ihf iha =>
      intro el
      constructor
      · intro h
        rw [Expr.traverseAnn] at h
        obtain ⟨x, y, hx, hy, he⟩ := option_bind2_some.mp h
        have hfn : fn = x.mapAnn r := (ihf x).mp hx
        have harg : arg = y.mapAnn r := (iha y).mp hy
        subst he
        simp [Expr.mapAnn, hfn, harg]
      · intro h
        cases el <;> try simp [Expr.mapAnn] at h
        case app e1 e2 =>
            obtain ⟨h1, h2⟩ := h
            simp [Expr.traverseAnn, (ihf e1).mpr h1, (iha e2).mpr h2]
  | letIn ann rhs body ihr ihb =>
      intro el
      cases ann with
      | none =>
          constructor
          · intro h
            rw [Expr.traverseAnn] at h
            obtain ⟨x, y, hx, hy, he⟩ := option_bind2_some.mp h
            have hr : rhs = x.mapAnn r := (ihr x).mp hx
            have hb : body = y.mapAnn r := (ihb y).mp hy
            subst he
            simp [Expr.mapAnn, hr, hb]
          · intro h
            cases el <;> try simp [Expr.mapAnn] at h
            case letIn p erhs ebody =>
              cases p with
              | none =>
                  simp only [Option.map_none] at h
                  obtain ⟨-, hr, hb⟩ := h
                  simp [Expr.traverseAnn, (ihr erhs).mpr hr, (ihb ebody).mpr hb]
              | some c => simp at h
      | some a =>
          cases a with
          | mk ar bd =>
            constructor
            · intro h
              rw [Expr.traverseAnn] at h
              obtain ⟨x, y, z, ha, hr, hb, he⟩ := option_bind3_some.mp h
              have hbd : bd = r x := (hf bd x).mp ha
              have hrhs : rhs = y.mapAnn r := (ihr y).mp hr
              have hbody : body = z.mapAnn r := (ihb z).mp hb
              subst he
              simp [Expr.mapAnn, PolyAnn.map, hbd, hrhs, hbody]
            · intro h
              cases el <;> try simp [Expr.mapAnn] at h
              case letIn p erhs ebody =>
                cases p with
                | none => simp at h
                | some an =>
                    cases an with
                    | mk anar anbody =>
                      simp only [Option.map_some] at h
                      obtain ⟨hann, hr, hb⟩ := h
                      have h1 : (⟨ar, bd⟩ : PolyAnn (Ty V)) = ⟨anar, r anbody⟩ :=
                        Option.some.inj hann
                      have har : ar = anar := by
                        simpa using congrArg (fun p : PolyAnn (Ty V) => p.arity) h1
                      have hbd : bd = r anbody := by
                        simpa using congrArg (fun p : PolyAnn (Ty V) => p.body) h1
                      have hfa : f bd = some anbody := (hf bd anbody).mpr hbd
                      simp [Expr.traverseAnn, har, hfa, (ihr erhs).mpr hr, (ihb ebody).mpr hb]
  | fix self body ih =>
      intro el
      cases self with
      | none =>
          constructor
          · intro h
            rw [Expr.traverseAnn] at h
            obtain ⟨e, hb, he⟩ := option_bind_some_eq_some.mp h
            have hbody : body = e.mapAnn r := (ih e).mp hb
            subst he
            simp [Expr.mapAnn, hbody]
          · intro h
            cases el <;> try simp [Expr.mapAnn] at h
            case fix p ebody =>
              cases p with
              | none =>
                  simp only [Option.map_none] at h
                  obtain ⟨-, hbody⟩ := h
                  simp [Expr.traverseAnn, (ih ebody).mpr hbody]
              | some b => simp at h
      | some a =>
          constructor
          · intro h
            rw [Expr.traverseAnn] at h
            obtain ⟨x, y, ha, hb, he⟩ := option_bind2_some.mp h
            have hax : a = r x := (hf a x).mp ha
            have hbody : body = y.mapAnn r := (ih y).mp hb
            subst he
            simp [Expr.mapAnn, hax, hbody]
          · intro h
            cases el <;> try simp [Expr.mapAnn] at h
            case fix p ebody =>
              cases p with
              | none => simp at h
              | some b =>
                  simp only [Option.map_some, Option.some.injEq] at h
                  obtain ⟨ha, hbody⟩ := h
                  have hfa : f a = some b := (hf a b).mpr ha
                  simp [Expr.traverseAnn, hfa, (ih ebody).mpr hbody]

theorem traverseAnn_ground_eq_some {expr : Expr (Ty V)} {elaboration : Elab} :
    expr.traverseAnn Ty.ground = some elaboration ↔ expr = elaboration.mapAnn Ty.lift :=
  traverseAnn_eq_some_iff (f := Ty.ground) (r := Ty.lift)
    (fun _ _ => Ty.ground_eq_some) expr elaboration

theorem traverseAnn_ground_eq_none {expr : Expr (Ty V)} :
    expr.traverseAnn Ty.ground = none ↔ ∃ ann ∈ expr.anns, ann.vars ≠ [] := by
  simp only [traverseAnn_eq_none_iff, Ty.ground_eq_none]

end Expr

namespace Template

/-- A completed annotation's type determines the annotation's scope. -/
theorem Matches.wf {template : Template} {ty : SemTy} (fits : template.Matches ty)
    (wf : ty.WF k) : template.WF k := by
  obtain ⟨holes, h⟩ := fits
  rw [← h] at wf
  exact (Ty.scoped_of_bind wf).1

/-- An annotation matches any realization of itself. -/
theorem matches_bind {template : Template} (f : String → SemTy) :
    template.Matches (template.bind f) :=
  ⟨f, rfl⟩

end Template

end EPL
