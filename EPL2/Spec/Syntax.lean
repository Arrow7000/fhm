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

/-- Membership in an appended list, split into the two summands. -/
private theorem exists_mem_append {α : Type} {l₁ l₂ : List α} {p : α → Prop} :
    (∃ v ∈ l₁ ++ l₂, p v) ↔ (∃ v ∈ l₁, p v) ∨ (∃ v ∈ l₂, p v) := by
  simp only [List.mem_append]
  constructor
  · rintro ⟨v, hv, hp⟩
    rcases hv with hv | hv
    · exact Or.inl ⟨v, hv, hp⟩
    · exact Or.inr ⟨v, hv, hp⟩
  · rintro (⟨v, hv, hp⟩ | ⟨v, hv, hp⟩)
    · exact ⟨v, Or.inl hv, hp⟩
    · exact ⟨v, Or.inr hv, hp⟩

private theorem append_ne_nil_left {α : Type} {l₁ l₂ : List α} (h : l₁ ≠ []) : l₁ ++ l₂ ≠ [] := by
  cases l₁ with
  | nil => exact absurd rfl h
  | cons x xs => intro hnil; exact List.cons_ne_nil x _ hnil

private theorem append_ne_nil_right {α : Type} {l₁ l₂ : List α} (h : l₂ ≠ []) : l₁ ++ l₂ ≠ [] := by
  cases l₁ with
  | nil => simpa using h
  | cons x xs => intro hnil; exact List.cons_ne_nil x _ hnil

/-- Indexing a list with a proof of the bound. -/
private theorem getD_eq_getElem {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem subst_subst (σ : Subst U V) (τ : Subst V W) (ty : Ty U) :
    (ty.subst σ).subst τ = ty.subst (σ.comp τ) := by
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihd ihc =>
      simp only [Ty.subst, ihd, ihc]
  | con id => rfl
  | app function argument ihf iha =>
      simp only [Ty.subst, ihf, iha]
  | bvar index => rfl
  | rigid level => rfl
  | var v => rfl

theorem subst_id (ty : Ty V) : ty.subst Subst.id = ty := by
  induction ty with
  | prim name => rfl
  | arrow domain codomain ihd ihc =>
      change Ty.arrow (domain.subst Subst.id) (codomain.subst Subst.id) =
        Ty.arrow domain codomain
      rw [ihd, ihc]
  | con id => rfl
  | app function argument ihf iha =>
      change Ty.app (function.subst Subst.id) (argument.subst Subst.id) =
        Ty.app function argument
      rw [ihf, iha]
  | bvar index => rfl
  | rigid level => rfl
  | var v => rfl

/-- Substitutions that agree on the variables a type mentions agree on it. -/
theorem subst_congr {σ τ : Subst V W} {ty : Ty V} (inScope : ty.Scoped rigids binders)
    (onBvar : ∀ i < binders, σ.bvar i = τ.bvar i)
    (onRigid : ∀ l < rigids, σ.rigid l = τ.rigid l)
    (onVar : ∀ v ∈ ty.vars, σ.var v = τ.var v) :
    ty.subst σ = ty.subst τ := by
  induction ty generalizing rigids binders with
  | prim name => rfl
  | con id => rfl
  | bvar index =>
      exact onBvar index inScope
  | rigid level =>
      exact onRigid level inScope
  | var v =>
      exact onVar v (by simp [Ty.vars])
  | arrow domain codomain ihd ihc =>
      have hd : domain.subst σ = domain.subst τ :=
        ihd inScope.1 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv]))
      have hc : codomain.subst σ = codomain.subst τ :=
        ihc inScope.2 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv]))
      simp only [Ty.subst, hd, hc]
  | app function argument ihf iha =>
      have hf : function.subst σ = function.subst τ :=
        ihf inScope.1 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv]))
      have ha : argument.subst σ = argument.subst τ :=
        iha inScope.2 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv]))
      simp only [Ty.subst, hf, ha]

/-- `subst_congr` for a type of unknown scope. -/
theorem subst_ext {σ τ : Subst V W} {ty : Ty V}
    (onBvar : ∀ i, σ.bvar i = τ.bvar i) (onRigid : ∀ l, σ.rigid l = τ.rigid l)
    (onVar : ∀ v ∈ ty.vars, σ.var v = τ.var v) :
    ty.subst σ = ty.subst τ := by
  induction ty with
  | prim name => rfl
  | con id => rfl
  | bvar index => exact onBvar index
  | rigid level => exact onRigid level
  | var v => exact onVar v (by simp [Ty.vars])
  | arrow domain codomain ihd ihc =>
      have hd : domain.subst σ = domain.subst τ :=
        ihd (fun v hv => onVar v (by simp [Ty.vars, hv]))
      have hc : codomain.subst σ = codomain.subst τ :=
        ihc (fun v hv => onVar v (by simp [Ty.vars, hv]))
      simp only [Ty.subst, hd, hc]
  | app function argument ihf iha =>
      have hf : function.subst σ = function.subst τ :=
        ihf (fun v hv => onVar v (by simp [Ty.vars, hv]))
      have ha : argument.subst σ = argument.subst τ :=
        iha (fun v hv => onVar v (by simp [Ty.vars, hv]))
      simp only [Ty.subst, hf, ha]

theorem scoped_subst {σ : Subst V W} {ty : Ty V} (inScope : ty.Scoped rigids binders)
    (onBvar : ∀ i < binders, (σ.bvar i).Scoped rigids' binders')
    (onRigid : ∀ l < rigids, (σ.rigid l).Scoped rigids' binders')
    (onVar : ∀ v ∈ ty.vars, (σ.var v).Scoped rigids' binders') :
    (ty.subst σ).Scoped rigids' binders' := by
  induction ty generalizing rigids binders with
  | prim name => trivial
  | con id => trivial
  | bvar index => exact onBvar index inScope
  | rigid level => exact onRigid level inScope
  | var v => exact onVar v (by simp [Ty.vars])
  | arrow domain codomain ihd ihc =>
      exact ⟨ihd inScope.1 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv])),
             ihc inScope.2 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv]))⟩
  | app function argument ihf iha =>
      exact ⟨ihf inScope.1 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv])),
             iha inScope.2 onBvar onRigid (fun v hv => onVar v (by simp [Ty.vars, hv]))⟩

theorem Scoped.mono {ty : Ty V} (inScope : ty.Scoped rigids binders)
    (rigidsLe : rigids ≤ rigids') (bindersLe : binders ≤ binders') :
    ty.Scoped rigids' binders' := by
  induction ty generalizing rigids binders with
  | prim name => trivial
  | con id => trivial
  | var v => trivial
  | bvar index => exact Nat.lt_of_lt_of_le inScope bindersLe
  | rigid level => exact Nat.lt_of_lt_of_le inScope rigidsLe
  | arrow domain codomain ihd ihc =>
      exact ⟨ihd inScope.1 rigidsLe bindersLe, ihc inScope.2 rigidsLe bindersLe⟩
  | app function argument ihf iha =>
      exact ⟨ihf inScope.1 rigidsLe bindersLe, iha inScope.2 rigidsLe bindersLe⟩

theorem mem_vars_bind {ty : Ty V} {f : V → Ty W} {w : W} :
    w ∈ (ty.bind f).vars ↔ ∃ v ∈ ty.vars, w ∈ (f v).vars := by
  induction ty with
  | prim _ => simp [Ty.bind, Ty.subst, Ty.vars]
  | con _ => simp [Ty.bind, Ty.subst, Ty.vars]
  | bvar _ => simp [Ty.bind, Ty.subst, Ty.vars]
  | rigid _ => simp [Ty.bind, Ty.subst, Ty.vars]
  | var v => simp [Ty.bind, Ty.subst, Ty.vars]
  | arrow d c ihd ihc =>
      change w ∈ ((d.bind f).vars ++ (c.bind f).vars) ↔
        ∃ v ∈ d.vars ++ c.vars, w ∈ (f v).vars
      rw [List.mem_append, ihd, ihc, exists_mem_append]
  | app fn arg ihf iha =>
      change w ∈ ((fn.bind f).vars ++ (arg.bind f).vars) ↔
        ∃ v ∈ fn.vars ++ arg.vars, w ∈ (f v).vars
      rw [List.mem_append, ihf, iha, exists_mem_append]

theorem bind_bind (ty : Ty U) (f : U → Ty V) (g : V → Ty W) :
    (ty.bind f).bind g = ty.bind fun u => (f u).bind g :=
  Ty.subst_subst ⟨.bvar, .rigid, f⟩ ⟨.bvar, .rigid, g⟩ ty

theorem bind_var (ty : Ty V) : ty.bind .var = ty :=
  Ty.subst_id ty

theorem bind_congr {ty : Ty V} {f g : V → Ty W} (agree : ∀ v ∈ ty.vars, f v = g v) :
    ty.bind f = ty.bind g := by
  induction ty with
  | prim _ => rfl
  | con _ => rfl
  | bvar _ => rfl
  | rigid _ => rfl
  | var v => exact agree v (by simp [Ty.vars])
  | arrow d c ihd ihc =>
      have hd : ∀ v ∈ d.vars, f v = g v := fun v hv => agree v (by simp [Ty.vars, hv])
      have hc : ∀ v ∈ c.vars, f v = g v := fun v hv => agree v (by simp [Ty.vars, hv])
      change Ty.arrow (d.bind f) (c.bind f) = Ty.arrow (d.bind g) (c.bind g)
      rw [ihd hd, ihc hc]
  | app fn arg ihf iha =>
      have hf : ∀ v ∈ fn.vars, f v = g v := fun v hv => agree v (by simp [Ty.vars, hv])
      have ha : ∀ v ∈ arg.vars, f v = g v := fun v hv => agree v (by simp [Ty.vars, hv])
      change Ty.app (fn.bind f) (arg.bind f) = Ty.app (fn.bind g) (arg.bind g)
      rw [ihf hf, iha ha]

theorem scoped_bind {ty : Ty V} {f : V → Ty W} (inScope : ty.Scoped rigids binders)
    (images : ∀ v ∈ ty.vars, (f v).Scoped rigids binders) :
    (ty.bind f).Scoped rigids binders := by
  induction ty with
  | prim _ => trivial
  | con _ => trivial
  | bvar _ => exact inScope
  | rigid _ => exact inScope
  | var v => exact images v (by simp [Ty.vars])
  | arrow d c ihd ihc =>
      exact ⟨ihd inScope.1 (fun v hv => images v (by simp [Ty.vars, hv])),
             ihc inScope.2 (fun v hv => images v (by simp [Ty.vars, hv]))⟩
  | app fn arg ihf iha =>
      exact ⟨ihf inScope.1 (fun v hv => images v (by simp [Ty.vars, hv])),
             iha inScope.2 (fun v hv => images v (by simp [Ty.vars, hv]))⟩

/-- A bind keeps bound and rigid variables and embeds every image, so the
scope of the result bounds the scope of the type and of every image. -/
theorem scoped_of_bind {ty : Ty V} {f : V → Ty W} (inScope : (ty.bind f).Scoped rigids binders) :
    ty.Scoped rigids binders ∧ ∀ v ∈ ty.vars, (f v).Scoped rigids binders := by
  induction ty with
  | prim _ => exact ⟨trivial, fun v hv => by simp [Ty.vars] at hv⟩
  | con _ => exact ⟨trivial, fun v hv => by simp [Ty.vars] at hv⟩
  | bvar _ => exact ⟨inScope, fun v hv => by simp [Ty.vars] at hv⟩
  | rigid _ => exact ⟨inScope, fun v hv => by simp [Ty.vars] at hv⟩
  | var v =>
      refine ⟨trivial, ?_⟩
      intro w hw
      simp [Ty.vars] at hw
      subst hw
      exact inScope
  | arrow d c ihd ihc =>
      obtain ⟨hd1, hd2⟩ := ihd inScope.1
      obtain ⟨hc1, hc2⟩ := ihc inScope.2
      refine ⟨⟨hd1, hc1⟩, ?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hd2 v hv
      · exact hc2 v hv
  | app fn arg ihf iha =>
      obtain ⟨hf1, hf2⟩ := ihf inScope.1
      obtain ⟨ha1, ha2⟩ := iha inScope.2
      refine ⟨⟨hf1, ha1⟩, ?_⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hf2 v hv
      · exact ha2 v hv

/-- If two binds agree, the maps agree on every variable of the type. -/
theorem bind_eq_bind_vars {ty : Ty V} {f g : V → Ty W} (equal : ty.bind f = ty.bind g) :
    ∀ v ∈ ty.vars, f v = g v := by
  induction ty with
  | prim _ => intro v hv; simp [Ty.vars] at hv
  | con _ => intro v hv; simp [Ty.vars] at hv
  | bvar _ => intro v hv; simp [Ty.vars] at hv
  | rigid _ => intro v hv; simp [Ty.vars] at hv
  | var v =>
      intro w hw
      simp [Ty.vars] at hw
      subst hw
      exact equal
  | arrow d c ihd ihc =>
      change Ty.arrow (d.bind f) (c.bind f) = Ty.arrow (d.bind g) (c.bind g) at equal
      injection equal with hd hc
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact ihd hd v hv
      · exact ihc hc v hv
  | app fn arg ihf iha =>
      change Ty.app (fn.bind f) (arg.bind f) = Ty.app (fn.bind g) (arg.bind g) at equal
      injection equal with hf ha
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact ihf hf v hv
      · exact iha ha v hv

theorem vars_lift (ty : SemTy) : (ty.lift : Ty V).vars = [] := by
  induction ty with
  | prim _ => rfl
  | con _ => rfl
  | bvar _ => rfl
  | rigid _ => rfl
  | var v => exact Empty.elim v
  | arrow d c ihd ihc =>
      change (d.lift : Ty V).vars ++ (c.lift : Ty V).vars = []
      rw [ihd, ihc, List.append_nil]
  | app fn arg ihf iha =>
      change (fn.lift : Ty V).vars ++ (arg.lift : Ty V).vars = []
      rw [ihf, iha, List.append_nil]

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
  | prim _ => rfl
  | con _ => rfl
  | bvar _ => rfl
  | rigid _ => rfl
  | var v => exact Empty.elim v
  | arrow d c ihd ihc =>
      change ((d.lift : Ty V).Scoped rigids binders ∧ (c.lift : Ty V).Scoped rigids binders) ↔
        (d.Scoped rigids binders ∧ c.Scoped rigids binders)
      exact and_congr ihd ihc
  | app fn arg ihf iha =>
      change ((fn.lift : Ty V).Scoped rigids binders ∧ (arg.lift : Ty V).Scoped rigids binders) ↔
        (fn.Scoped rigids binders ∧ arg.Scoped rigids binders)
      exact and_congr ihf iha

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

private theorem option_bind_eq_some_iff {α β : Type} {o : Option α} {f : α → Option β} {b : β} :
    (o >>= f = some b) ↔ ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none => simp
  | some a => simp

private theorem option_bind_eq_none_iff {α β : Type} {o : Option α} {f : α → Option β} :
    (o >>= f = none) ↔ o = none ∨ ∃ a, o = some a ∧ f a = none := by
  cases o with
  | none => simp
  | some a => simp

private theorem option_bind_some_eq_none {α β : Type} {o : Option α} {g : α → β} :
    (o >>= fun a => some (g a)) = none ↔ o = none := by
  cases o with
  | none => simp
  | some a => simp

private theorem ground_eq_some_aux (ty : Ty V) :
    ∀ sem : SemTy, ty.ground = some sem ↔ ty = sem.lift := by
  induction ty with
  | prim name =>
      intro sem
      constructor
      · intro h
        change some (Ty.prim name) = some sem at h
        obtain rfl := Option.some.inj h
        rfl
      · intro h; rw [h]; exact lift_ground sem
  | con id =>
      intro sem
      constructor
      · intro h
        change some (Ty.con id) = some sem at h
        obtain rfl := Option.some.inj h
        rfl
      · intro h; rw [h]; exact lift_ground sem
  | bvar index =>
      intro sem
      constructor
      · intro h
        change some (Ty.bvar index) = some sem at h
        obtain rfl := Option.some.inj h
        rfl
      · intro h; rw [h]; exact lift_ground sem
  | rigid level =>
      intro sem
      constructor
      · intro h
        change some (Ty.rigid level) = some sem at h
        obtain rfl := Option.some.inj h
        rfl
      · intro h; rw [h]; exact lift_ground sem
  | var v =>
      intro sem
      constructor
      · intro h
        change none = some sem at h
        cases h
      · intro h; rw [h]; exact lift_ground sem
  | arrow d c ihd ihc =>
      intro sem
      constructor
      · intro h
        change (d.ground >>= fun x => c.ground >>= fun y => some (Ty.arrow x y)) = some sem at h
        obtain ⟨ds, hd, h2⟩ := option_bind_eq_some_iff.mp h
        obtain ⟨cs, hc, h3⟩ := option_bind_eq_some_iff.mp h2
        obtain rfl := Option.some.inj h3
        rw [(ihd ds).mp hd, (ihc cs).mp hc]
        rfl
      · intro h; rw [h]; exact lift_ground sem
  | app fn arg ihf iha =>
      intro sem
      constructor
      · intro h
        change (fn.ground >>= fun x => arg.ground >>= fun y => some (Ty.app x y)) = some sem at h
        obtain ⟨fs, hf, h2⟩ := option_bind_eq_some_iff.mp h
        obtain ⟨as, ha, h3⟩ := option_bind_eq_some_iff.mp h2
        obtain rfl := Option.some.inj h3
        rw [(ihf fs).mp hf, (iha as).mp ha]
        rfl
      · intro h; rw [h]; exact lift_ground sem

theorem ground_eq_some {ty : Ty V} {sem : SemTy} : ty.ground = some sem ↔ ty = sem.lift :=
  ground_eq_some_aux ty sem

theorem ground_eq_none {ty : Ty V} : ty.ground = none ↔ ty.vars ≠ [] := by
  induction ty with
  | prim _ => simp [Ty.ground, Ty.vars]
  | con _ => simp [Ty.ground, Ty.vars]
  | bvar _ => simp [Ty.ground, Ty.vars]
  | rigid _ => simp [Ty.ground, Ty.vars]
  | var _ => simp [Ty.ground, Ty.vars]
  | arrow d c ihd ihc =>
      change (d.ground >>= fun x => c.ground >>= fun y => some (Ty.arrow x y)) = none ↔
        (d.vars ++ c.vars) ≠ []
      cases hd : d.ground with
      | none =>
          have hdv : d.vars ≠ [] := ihd.mp hd
          constructor
          · intro _; exact append_ne_nil_left hdv
          · intro _; rfl
      | some ds =>
          change (c.ground >>= fun y => some (Ty.arrow ds y)) = none ↔
            (d.vars ++ c.vars) ≠ []
          have hdv : d.vars = [] := by
            by_contra h
            have : d.ground = none := ihd.mpr h
            rw [this] at hd
            cases hd
          rw [option_bind_some_eq_none, ihc]
          simp [hdv]
  | app fn arg ihf iha =>
      change (fn.ground >>= fun x => arg.ground >>= fun y => some (Ty.app x y)) = none ↔
        (fn.vars ++ arg.vars) ≠ []
      cases hf : fn.ground with
      | none =>
          have hfv : fn.vars ≠ [] := ihf.mp hf
          constructor
          · intro _; exact append_ne_nil_left hfv
          · intro _; rfl
      | some fs =>
          change (arg.ground >>= fun y => some (Ty.app fs y)) = none ↔
            (fn.vars ++ arg.vars) ≠ []
          have hfv : fn.vars = [] := by
            by_contra h
            have : fn.ground = none := ihf.mpr h
            rw [this] at hf
            cases hf
          rw [option_bind_some_eq_none, iha]
          simp [hfv]

theorem instantiate_nil (ty : Ty V) : ty.instantiate [] = ty := by
  change ty.subst ⟨fun i => ([] : List (Ty V)).getD i (.bvar i), .rigid, .var⟩ = ty
  exact Ty.subst_id ty

/-- A type with no bound variables is unchanged by `instantiate`. -/
private theorem instantiate_closed {ty : Ty V} {args : List (Ty V)} {rigids : Nat}
    (h : ty.Scoped rigids 0) : ty.instantiate args = ty := by
  induction ty with
  | prim _ => rfl
  | con _ => rfl
  | bvar i => exact absurd h (Nat.not_lt_zero i)
  | rigid _ => rfl
  | var _ => rfl
  | arrow d c ihd ihc =>
      change Ty.arrow (d.instantiate args) (c.instantiate args) = Ty.arrow d c
      rw [ihd h.1, ihc h.2]
  | app fn arg ihf iha =>
      change Ty.app (fn.instantiate args) (arg.instantiate args) = Ty.app fn arg
      rw [ihf h.1, iha h.2]

private theorem getD_map_bind (args : List (Ty V)) (f : V → Ty W) (i : Nat) :
    (args.getD i (.bvar i)).bind f = (args.map (·.bind f)).getD i (.bvar i) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : args[i]? with
  | none => simp [h, Ty.bind, Ty.subst]
  | some a => simp [h]

theorem instantiate_bind (args : List (Ty V)) {ty : Ty V} {f : V → Ty W}
    (closed : ∀ v ∈ ty.vars, (f v).Scoped rigids 0) :
    (ty.instantiate args).bind f = (ty.bind f).instantiate (args.map (·.bind f)) := by
  induction ty with
  | prim _ => rfl
  | con _ => rfl
  | bvar i => exact getD_map_bind args f i
  | rigid _ => rfl
  | var v =>
      exact (instantiate_closed (args := args.map (·.bind f))
        (closed v (by simp [Ty.vars]))).symm
  | arrow d c ihd ihc =>
      have hdc : ∀ v ∈ d.vars, (f v).Scoped rigids 0 := fun v hv => closed v (by simp [Ty.vars, hv])
      have hcc : ∀ v ∈ c.vars, (f v).Scoped rigids 0 := fun v hv => closed v (by simp [Ty.vars, hv])
      change Ty.arrow ((d.instantiate args).bind f) ((c.instantiate args).bind f) =
        Ty.arrow ((d.bind f).instantiate (args.map (·.bind f)))
          ((c.bind f).instantiate (args.map (·.bind f)))
      rw [ihd hdc, ihc hcc]
  | app fn arg ihf iha =>
      have hfc : ∀ v ∈ fn.vars, (f v).Scoped rigids 0 := fun v hv => closed v (by simp [Ty.vars, hv])
      have hac : ∀ v ∈ arg.vars, (f v).Scoped rigids 0 := fun v hv => closed v (by simp [Ty.vars, hv])
      change Ty.app ((fn.instantiate args).bind f) ((arg.instantiate args).bind f) =
        Ty.app ((fn.bind f).instantiate (args.map (·.bind f)))
          ((arg.bind f).instantiate (args.map (·.bind f)))
      rw [ihf hfc, iha hac]

theorem instantiate_scoped {ty : Ty V} (inScope : ty.Scoped rigids args.length)
    (argsScoped : ∀ arg ∈ args, arg.Scoped rigids binders) :
    (ty.instantiate args).Scoped rigids binders := by
  induction ty with
  | prim _ => trivial
  | con _ => trivial
  | var _ => trivial
  | bvar i =>
      show (args.getD i (.bvar i)).Scoped rigids binders
      rw [getD_eq_getElem inScope]
      exact argsScoped _ (List.getElem_mem inScope)
  | rigid _ => exact inScope
  | arrow d c ihd ihc =>
      exact ⟨ihd inScope.1, ihc inScope.2⟩
  | app fn arg ihf iha =>
      exact ⟨ihf inScope.1, iha inScope.2⟩

theorem vars_closeRigids (k n : Nat) (ty : Ty V) : (ty.closeRigids k n).vars = ty.vars := by
  induction ty with
  | prim _ => rfl
  | con _ => rfl
  | bvar _ => rfl
  | rigid level =>
      by_cases h : k ≤ level ∧ level < k + n <;>
        simp [Ty.closeRigids, Ty.substRigids, Ty.subst, Ty.vars, h]
  | var _ => rfl
  | arrow d c ihd ihc =>
      change ((d.closeRigids k n).vars ++ (c.closeRigids k n).vars) = d.vars ++ c.vars
      rw [ihd, ihc]
  | app fn arg ihf iha =>
      change ((fn.closeRigids k n).vars ++ (arg.closeRigids k n).vars) = fn.vars ++ arg.vars
      rw [ihf, iha]

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
  induction ty with
  | prim _ => rfl
  | con _ => rfl
  | bvar _ => rfl
  | rigid level =>
      by_cases h : k ≤ level ∧ level < k + n <;>
        simp [Ty.closeRigids, Ty.substRigids, Ty.subst, Ty.bind, h]
  | var v =>
      exact (closeRigids_closed (images v (by simp [Ty.vars])) n).symm
  | arrow d c ihd ihc =>
      have hdc : ∀ v ∈ d.vars, (f v).WF k := fun v hv => images v (by simp [Ty.vars, hv])
      have hcc : ∀ v ∈ c.vars, (f v).WF k := fun v hv => images v (by simp [Ty.vars, hv])
      change Ty.arrow ((d.closeRigids k n).bind f) ((c.closeRigids k n).bind f) =
        Ty.arrow ((d.bind f).closeRigids k n) ((c.bind f).closeRigids k n)
      rw [ihd hdc, ihc hcc]
  | app fn arg ihf iha =>
      have hfc : ∀ v ∈ fn.vars, (f v).WF k := fun v hv => images v (by simp [Ty.vars, hv])
      have hac : ∀ v ∈ arg.vars, (f v).WF k := fun v hv => images v (by simp [Ty.vars, hv])
      change Ty.app ((fn.closeRigids k n).bind f) ((arg.closeRigids k n).bind f) =
        Ty.app ((fn.bind f).closeRigids k n) ((arg.bind f).closeRigids k n)
      rw [ihf hfc, iha hac]

end Ty

/-- Rigid levels below `k` are kept; level `k + i` becomes `args[i]`. -/
def blockSubst (k : Nat) (args : List (Ty V)) : Nat → Ty V :=
  fun l => if l < k then .rigid l else args.getD (l - k) (.rigid l)

private theorem rigidBlock_length (k n : Nat) : (rigidBlock k n : List (Ty V)).length = n := by
  simp [rigidBlock]

private theorem rigidBlock_getD {k n i : Nat} {d : Ty V} (h : i < n) :
    (rigidBlock k n).getD i d = .rigid (k + i) := by
  simp only [rigidBlock, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

private theorem rigidBlock_mem {k n : Nat} {ty : Ty V} :
    ty ∈ rigidBlock k n ↔ ∃ i, i < n ∧ ty = .rigid (k + i) := by
  simp only [rigidBlock, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

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
  · intro arg harg
    rw [rigidBlock_mem] at harg
    obtain ⟨i, hi, rfl⟩ := harg
    show k + i < k + scheme.arity
    omega

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
    scheme.Instance (k + scheme.arity) (scheme.skolemize k) := by
  refine ⟨rigidBlock k scheme.arity, ?_, ?_, rfl⟩
  · exact rigidBlock_length k scheme.arity
  · intro arg harg
    rw [rigidBlock_mem] at harg
    obtain ⟨i, hi, rfl⟩ := harg
    show k + i < k + scheme.arity
    omega

theorem Instance.mono {scheme : Scheme V} {ty : Ty V} (inst : scheme.Instance k ty)
    (le : k ≤ k') : scheme.Instance k' ty := by
  obtain ⟨args, length, wf, h⟩ := inst
  exact ⟨args, length, fun arg harg => Ty.Scoped.mono (wf arg harg) le (le_refl _), h⟩

/-- A monomorphic scheme's only instance is its type. -/
theorem instance_mono {ty ty' : Ty V} : (Scheme.mono ty').Instance k ty ↔ ty = ty' := by
  constructor
  · rintro ⟨args, length, _, h⟩
    cases args with
    | nil =>
        simp only [Scheme.inst, Scheme.mono] at h
        rw [Ty.instantiate_nil] at h
        exact h.symm
    | cons a as =>
        simp [Scheme.mono] at length
  · intro h
    subst h
    refine ⟨[], rfl, (by intro arg harg; simp at harg), ?_⟩
    simp only [Scheme.inst, Scheme.mono]
    rw [Ty.instantiate_nil]

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
    unfold blockSubst
    rw [if_neg (by omega : ¬ k + i < k)]
    have hki : k + i - k = i := by omega
    rw [hki]
    have hi' : i < args.length := by omega
    rw [Ty.getD_eq_getElem hi', Ty.getD_eq_getElem hi']
  · intro l hl
    show blockSubst k args l = Ty.rigid l
    unfold blockSubst
    rw [if_pos hl]
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
    rw [if_neg (by omega : ¬ k + i < k)]
    have hki : k + i - k = i := by omega
    rw [hki]
    have hi' : i < args.length := by omega
    rw [Ty.getD_eq_getElem hi', Ty.getD_eq_getElem hi']
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
    refine Ty.subst_congr wf ?_ ?_ ?_
    · intro i hi; rfl
    · intro l hl
      show f l = g l
      exact agree l hl
    · intro v hv; rfl
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
    have hc : scheme.body.subst ⟨.bvar, f, .var⟩ = scheme.body.subst Ty.Subst.id := by
      refine Ty.subst_congr wf ?_ ?_ ?_
      · intro i hi; rfl
      · intro l hl
        show f l = Ty.rigid l
        exact identity l hl
      · intro v hv; rfl
    rw [hc, Ty.subst_id]
  cases scheme with
  | mk arity body => simp only [Scheme.substRigids, h]

private theorem getD_map_substRigids (args : List (Ty V)) (f : Nat → Ty V) (i : Nat) :
    (args.getD i (.bvar i)).substRigids f =
      (args.map (·.substRigids f)).getD i (.bvar i) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : args[i]? with
  | none => simp [h, Ty.substRigids, Ty.subst]
  | some a => simp [h]

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
      by_cases hcond : k ≤ l ∧ l < k + n
      · have hlk : l - k < n := by omega
        have hk : k + (l - k) = l := by omega
        show ((if k ≤ l ∧ l < k + n then Ty.bvar (l - k) else Ty.rigid l)).subst τ = Ty.rigid l
        rw [if_pos hcond]
        show (rigidBlock k n).getD (l - k) (.bvar (l - k)) = Ty.rigid l
        rw [rigidBlock_getD (k := k) (n := n) (i := l - k) (d := .bvar (l - k)) hlk, hk]
      · show ((if k ≤ l ∧ l < k + n then Ty.bvar (l - k) else Ty.rigid l)).subst τ = Ty.rigid l
        rw [if_neg hcond]
        rfl
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
    show (if k ≤ l ∧ l < k + n then Ty.bvar (l - k) else Ty.rigid l).Scoped k n
    by_cases hcond : k ≤ l ∧ l < k + n
    · rw [if_pos hcond]
      show l - k < n
      omega
    · rw [if_neg hcond]
      show l < k
      omega
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
  cases first with
  | mk fa fb =>
    cases second with
    | mk sa sb =>
      have ha : fa = sa := arity
      have hb : fb = sb := hbody
      rw [ha, hb]

end Scheme

theorem Ctx.WF.mono {ctx : Ctx V} (wf : ctx.WF k) (le : k ≤ k') : ctx.WF k' := by
  intro scheme hmem
  exact Ty.Scoped.mono (wf scheme hmem) le (le_refl _)

namespace Expr

theorem anns_mapAnn (f : A → B) (expr : Expr A) : (expr.mapAnn f).anns = expr.anns.map f := by
  induction expr with
  | lit _ => rfl
  | primOp _ => rfl
  | const _ => rfl
  | var _ => rfl
  | lambda param body ih =>
      cases param with
      | none => simp [Expr.mapAnn, Expr.anns, ih]
      | some a => simp [Expr.mapAnn, Expr.anns, ih]
  | app fn arg ihf iha =>
      simp [Expr.mapAnn, Expr.anns, ihf, iha, List.map_append]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none => simp [Expr.mapAnn, Expr.anns, ihr, ihb, List.map_append]
      | some a => simp [Expr.mapAnn, Expr.anns, ihr, ihb, List.map_append, PolyAnn.map]
  | fix self body ih =>
      simp [Expr.mapAnn, Expr.anns, ih]

theorem mapAnn_congr {f g : A → B} {expr : Expr A} (agree : ∀ ann ∈ expr.anns, f ann = g ann) :
    expr.mapAnn f = expr.mapAnn g := by
  induction expr with
  | lit _ => rfl
  | primOp _ => rfl
  | const _ => rfl
  | var _ => rfl
  | lambda param body ih =>
      cases param with
      | none =>
          have hb : body.mapAnn f = body.mapAnn g := ih (fun ann hann => agree ann hann)
          simp [Expr.mapAnn, hb]
      | some a =>
          have hb : body.mapAnn f = body.mapAnn g :=
            ih (fun ann hann => agree ann (by simp [Expr.anns, List.mem_cons, hann]))
          have ha : f a = g a := agree a (by simp [Expr.anns])
          simp [Expr.mapAnn, ha, hb]
  | app fn arg ihf iha =>
      have hf : fn.mapAnn f = fn.mapAnn g :=
        ihf (fun ann hann => agree ann (by simp [Expr.anns, List.mem_append, hann]))
      have ha : arg.mapAnn f = arg.mapAnn g :=
        iha (fun ann hann => agree ann (by simp [Expr.anns, List.mem_append, hann]))
      simp [Expr.mapAnn, hf, ha]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          have hr : rhs.mapAnn f = rhs.mapAnn g :=
            ihr (fun ann hann => agree ann (by simp [Expr.anns, List.mem_append, hann]))
          have hb : body.mapAnn f = body.mapAnn g :=
            ihb (fun ann hann => agree ann (by simp [Expr.anns, List.mem_append, hann]))
          simp [Expr.mapAnn, hr, hb]
      | some a =>
          have hr : rhs.mapAnn f = rhs.mapAnn g :=
            ihr (fun ann hann => agree ann (by simp [Expr.anns, List.mem_cons, List.mem_append, hann]))
          have hb : body.mapAnn f = body.mapAnn g :=
            ihb (fun ann hann => agree ann (by simp [Expr.anns, List.mem_cons, List.mem_append, hann]))
          have ha : f a.body = g a.body :=
            agree a.body (by simp [Expr.anns])
          simp [Expr.mapAnn, PolyAnn.map, ha, hr, hb]
  | fix self body ih =>
      have hs : f self = g self := agree self (by simp [Expr.anns])
      have hb : body.mapAnn f = body.mapAnn g :=
        ih (fun ann hann => agree ann (by simp [Expr.anns, List.mem_cons, hann]))
      simp [Expr.mapAnn, hs, hb]

/-- If two maps of an expression agree, the functions agree on every
annotation. -/
theorem mapAnn_eq_anns {f g : A → B} {expr : Expr A} (equal : expr.mapAnn f = expr.mapAnn g) :
    ∀ ann ∈ expr.anns, f ann = g ann := by
  induction expr with
  | lit _ => intro ann h; simp [Expr.anns] at h
  | primOp _ => intro ann h; simp [Expr.anns] at h
  | const _ => intro ann h; simp [Expr.anns] at h
  | var _ => intro ann h; simp [Expr.anns] at h
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
      have hs : f self = g self := by injection equal with _ _
      have hb : body.mapAnn f = body.mapAnn g := by injection equal with _ _
      intro ann hmem
      simp only [Expr.anns, List.mem_cons] at hmem
      rcases hmem with h | h
      · subst h; exact hs
      · exact ih hb ann h

private theorem option_bind_some_eq_some {α γ : Type} {o : Option α} {g : α → γ} {c : γ} :
    (o >>= fun a => some (g a)) = some c ↔ ∃ a, o = some a ∧ g a = c := by
  cases o with
  | none => simp
  | some a => simp [eq_comm]

private theorem option_bind2_some {α β γ : Type} {o1 : Option α} {o2 : Option β}
    {g : α → β → γ} {c : γ} :
    (o1 >>= fun x => o2 >>= fun y => some (g x y)) = some c ↔
      ∃ x y, o1 = some x ∧ o2 = some y ∧ g x y = c := by
  cases o1 with
  | none => simp
  | some x =>
      cases o2 with
      | none => simp
      | some y => simp [eq_comm]

private theorem option_bind3_some {α β γ δ : Type} {o1 : Option α} {o2 : Option β} {o3 : Option γ}
    {g : α → β → γ → δ} {c : δ} :
    (o1 >>= fun x => o2 >>= fun y => o3 >>= fun z => some (g x y z)) = some c ↔
      ∃ x y z, o1 = some x ∧ o2 = some y ∧ o3 = some z ∧ g x y z = c := by
  cases o1 with
  | none => simp
  | some x =>
      cases o2 with
      | none => simp
      | some y =>
          cases o3 with
          | none => simp
          | some z => simp [eq_comm]

private theorem option_bind2_none {α β γ : Type} {o1 : Option α} {o2 : Option β}
    {g : α → β → γ} :
    (o1 >>= fun x => o2 >>= fun y => some (g x y)) = none ↔ o1 = none ∨ o2 = none := by
  cases o1 with
  | none => simp
  | some x =>
      cases o2 with
      | none => simp
      | some y => simp

private theorem option_bind3_none {α β γ δ : Type} {o1 : Option α} {o2 : Option β} {o3 : Option γ}
    {g : α → β → γ → δ} :
    (o1 >>= fun x => o2 >>= fun y => o3 >>= fun z => some (g x y z)) = none ↔
      o1 = none ∨ o2 = none ∨ o3 = none := by
  cases o1 with
  | none => simp
  | some x =>
      cases o2 with
      | none => simp
      | some y => cases o3 <;> simp

private theorem exists_mem_cons {α : Type} {a : α} {l : List α} {p : α → Prop} :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x := by
  simp only [List.mem_cons]
  constructor
  · rintro ⟨x, hx, hp⟩
    rcases hx with hx | hx
    · subst hx; exact Or.inl hp
    · exact Or.inr ⟨x, hx, hp⟩
  · rintro (hp | ⟨x, hx, hp⟩)
    · exact ⟨a, Or.inl rfl, hp⟩
    · exact ⟨x, Or.inr hx, hp⟩

private theorem traverseAnn_eq_none_iff {f : Ty V → Option SemTy} :
    ∀ (expr : Expr (Ty V)), expr.traverseAnn f = none ↔ ∃ ann ∈ expr.anns, f ann = none := by
  intro expr
  induction expr with
  | lit _ => simp [Expr.traverseAnn, Expr.anns]
  | primOp _ => simp [Expr.traverseAnn, Expr.anns]
  | const _ => simp [Expr.traverseAnn, Expr.anns]
  | var _ => simp [Expr.traverseAnn, Expr.anns]
  | lambda param body ih =>
      cases param with
      | none =>
          simp only [Expr.traverseAnn, Expr.anns]
          rw [Ty.option_bind_some_eq_none, ih]
      | some a =>
          simp only [Expr.traverseAnn, Expr.anns]
          rw [option_bind2_none, ih, exists_mem_cons]
  | app fn arg ihf iha =>
      simp only [Expr.traverseAnn, Expr.anns, option_bind2_none, ihf, iha, Ty.exists_mem_append]
  | letIn ann rhs body ihr ihb =>
      cases ann with
      | none =>
          simp only [Expr.traverseAnn, Expr.anns, option_bind2_none, ihr, ihb, Ty.exists_mem_append]
      | some a =>
          simp only [Expr.traverseAnn, Expr.anns, option_bind3_none, ihr, ihb,
            exists_mem_cons, Ty.exists_mem_append]
  | fix self body ih =>
      simp only [Expr.traverseAnn, Expr.anns, option_bind2_none, ih, exists_mem_cons]

private theorem traverseAnn_eq_some_iff {f : Ty V → Option SemTy} {r : SemTy → Ty V}
    (hf : ∀ (ty : Ty V) (sem : SemTy), f ty = some sem ↔ ty = r sem) :
    ∀ (expr : Expr (Ty V)) (el : Elab),
      expr.traverseAnn f = some el ↔ expr = el.mapAnn r := by
  intro expr
  induction expr with
  | lit l =>
      intro el; constructor
      · intro h
        rw [Expr.traverseAnn] at h
        have h' : el = Expr.lit l := (Option.some.inj h).symm
        subst h'; simp [Expr.mapAnn]
      · intro h
        cases el <;> simp [Expr.mapAnn] at h
        rw [← h]
        rfl
  | primOp p =>
      intro el; constructor
      · intro h
        rw [Expr.traverseAnn] at h
        have h' : el = Expr.primOp p := (Option.some.inj h).symm
        subst h'; simp [Expr.mapAnn]
      · intro h
        cases el <;> simp [Expr.mapAnn] at h
        rw [← h]
        rfl
  | const c =>
      intro el; constructor
      · intro h
        rw [Expr.traverseAnn] at h
        have h' : el = Expr.const c := (Option.some.inj h).symm
        subst h'; simp [Expr.mapAnn]
      · intro h
        cases el <;> simp [Expr.mapAnn] at h
        rw [← h]
        rfl
  | var i =>
      intro el; constructor
      · intro h
        rw [Expr.traverseAnn] at h
        have h' : el = Expr.var i := (Option.some.inj h).symm
        subst h'; simp [Expr.mapAnn]
      · intro h
        cases el <;> simp [Expr.mapAnn] at h
        rw [← h]
        rfl
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
                  simp only [Expr.mapAnn, Option.map_none, Expr.lambda.injEq] at h
                  obtain ⟨-, hbody⟩ := h
                  simp [Expr.traverseAnn, (ih ebody).mpr hbody]
              | some b => simp [Expr.mapAnn] at h
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
              | none => simp [Expr.mapAnn] at h
              | some b =>
                  simp only [Expr.mapAnn, Option.map_some, Expr.lambda.injEq,
                    Option.some.injEq] at h
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
                  simp only [Expr.mapAnn, Option.map_none, Expr.letIn.injEq] at h
                  obtain ⟨-, hr, hb⟩ := h
                  simp [Expr.traverseAnn, (ihr erhs).mpr hr, (ihb ebody).mpr hb]
              | some c => simp [Expr.mapAnn] at h
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
                | none => simp [Expr.mapAnn] at h
                | some an =>
                    cases an with
                    | mk anar anbody =>
                      simp only [Expr.mapAnn, Option.map_some, Expr.letIn.injEq] at h
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
      constructor
      · intro h
        rw [Expr.traverseAnn] at h
        obtain ⟨x, y, hs, hb, he⟩ := option_bind2_some.mp h
        have hself : self = r x := (hf self x).mp hs
        have hbody : body = y.mapAnn r := (ih y).mp hb
        subst he
        simp [Expr.mapAnn, hself, hbody]
      · intro h
        cases el <;> try simp [Expr.mapAnn] at h
        case fix eself ebody =>
            obtain ⟨hs, hb⟩ := h
            have hfs : f self = some eself := (hf self eself).mpr hs
            simp [Expr.traverseAnn, hfs, (ih ebody).mpr hb]

theorem traverseAnn_ground_eq_some {expr : Expr (Ty V)} {elaboration : Elab} :
    expr.traverseAnn Ty.ground = some elaboration ↔ expr = elaboration.mapAnn Ty.lift :=
  traverseAnn_eq_some_iff (f := Ty.ground) (r := Ty.lift)
    (fun _ _ => Ty.ground_eq_some) expr elaboration

theorem traverseAnn_ground_eq_none {expr : Expr (Ty V)} :
    expr.traverseAnn Ty.ground = none ↔ ∃ ann ∈ expr.anns, ann.vars ≠ [] := by
  rw [traverseAnn_eq_none_iff]
  constructor
  · rintro ⟨ann, hmem, hnone⟩
    exact ⟨ann, hmem, Ty.ground_eq_none.mp hnone⟩
  · rintro ⟨ann, hmem, hvars⟩
    exact ⟨ann, hmem, Ty.ground_eq_none.mpr hvars⟩

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

end EPL2
