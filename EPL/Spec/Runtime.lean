import EPL.Spec.Syntax
import EPL.Runtime

/-!
# Runtime metatheory

Type safety rests on four lemmas about `RuntimeTyping`:

* `mono_depth`: more rigid levels in scope — trivial thanks to the Kripke
  `letIn` rule;
* `weaken` / `subst`: the term-level lemmas for `beta`, `letValue` and
  `fixUnfold`;
* `substRigids`: the one type-substitution lemma, used only by erasure.
-/

namespace EPL

/-! ## Generic expression-spine lemmas -/

private theorem Expr.apps_append {A : Type} (head : Expr A) (first second : List (Expr A)) :
    Expr.apps head (first ++ second) = Expr.apps (Expr.apps head first) second := by
  induction first generalizing head with
  | nil => simp [Expr.apps]
  | cons a as ih =>
      simp only [List.cons_append, Expr.apps, List.foldl_cons]
      exact ih (.app head a)

private theorem Expr.spine_apps {A : Type} (head : Expr A) (args : List (Expr A)) :
    (Expr.apps head args).spine = (head.spine.1, head.spine.2 ++ args) := by
  induction args generalizing head with
  | nil => simp [Expr.apps, List.append_nil]
  | cons a as ih =>
      have step : Expr.apps head (a :: as) = Expr.apps (.app head a) as := rfl
      rw [step, ih]
      simp [Expr.spine, List.append_assoc]

private theorem Expr.apps_spine {A : Type} (expr : Expr A) :
    Expr.apps expr.spine.1 expr.spine.2 = expr := by
  induction expr with
  | app f a ihf =>
      change Expr.apps f.spine.1 (f.spine.2 ++ [a]) = Expr.app f a
      rw [Expr.apps_append, ihf]
      rfl
  | lit | primOp | const | var | lambda | letIn | fix => rfl

private theorem Expr.spine_app_spine {A : Type} {f a h : Expr A} {args : List (Expr A)}
    (hs : f.spine = (h, args)) :
    (Expr.app f a).spine = (h, args ++ [a]) := by
  simp only [Expr.spine, hs]

/-! ## Type-level list and substitution lemmas -/

private theorem Ty.instantiate_arrows {V : Type} (args : List (Ty V))
    (domains : List (Ty V)) (codomain : Ty V) :
    (Ty.arrows domains codomain).instantiate args =
      Ty.arrows (domains.map (fun d => d.instantiate args)) (codomain.instantiate args) := by
  induction domains with
  | nil => rfl
  | cons d ds ih =>
      change Ty.arrow (Ty.instantiate args d) (Ty.instantiate args (Ty.arrows ds codomain)) =
        Ty.arrow (Ty.instantiate args d)
          (Ty.arrows (ds.map (fun x => Ty.instantiate args x)) (Ty.instantiate args codomain))
      rw [ih]

private theorem Ty.instantiate_apps {V : Type} (args : List (Ty V))
    (head : Ty V) (rest : List (Ty V)) :
    (Ty.apps head rest).instantiate args =
      Ty.apps (head.instantiate args) (rest.map (fun t => t.instantiate args)) := by
  induction rest generalizing head with
  | nil => rfl
  | cons a as ih =>
      change Ty.instantiate args (Ty.apps (Ty.app head a) as) =
        Ty.apps (Ty.instantiate args (Ty.app head a))
          (as.map (fun t => Ty.instantiate args t))
      rw [ih (Ty.app head a)]

private theorem Ty.instantiate_branchTy (args : List SemTy)
    (fields : List SemTy) (result : SemTy) :
    Ty.instantiate args (branchTy fields result) =
      Ty.arrow (.prim .unit)
        (Ty.arrows (fields.map (fun ft => Ty.instantiate args ft))
          (Ty.instantiate args result)) := by
  unfold branchTy
  change Ty.arrow (Ty.instantiate args (.prim .unit))
      (Ty.instantiate args (Ty.arrows fields result)) =
    Ty.arrow (.prim .unit)
      (Ty.arrows (fields.map (fun ft => Ty.instantiate args ft)) (Ty.instantiate args result))
  rw [Ty.instantiate_arrows]
  rfl

private theorem Ty.list_reverse_induction {α : Type} {motive : List α → Prop}
    (nil : motive [])
    (step : ∀ (xs : List α) (x : α), motive xs → motive (xs ++ [x])) :
    ∀ l, motive l := by
  intro l
  suffices ∀ n (l : List α), l.length = n → motive l by exact this _ l rfl
  intro n
  induction n with
  | zero =>
      intro l hl
      cases l with
      | nil => exact nil
      | cons => simp at hl
  | succ n ih =>
      intro l hl
      cases l with
      | nil => exact nil
      | cons a l' =>
          have hne : (a :: l') ≠ [] := by simp
          have hsplit : a :: l' = (a :: l').dropLast ++ [(a :: l').getLast hne] :=
            (List.dropLast_append_getLast hne).symm
          rw [hsplit]
          apply step
          apply ih (a :: l').dropLast
          rw [hsplit] at hl
          simp only [List.length_append, List.length_singleton] at hl
          omega

private theorem Ty.apps_append_singleton {V : Type} (head : Ty V) (xs : List (Ty V)) (x : Ty V) :
    Ty.apps head (xs ++ [x]) = Ty.app (Ty.apps head xs) x := by
  induction xs generalizing head with
  | nil => rfl
  | cons a as ih =>
      change Ty.apps (Ty.app head a) (as ++ [x]) =
        Ty.app (Ty.apps (Ty.app head a) as) x
      exact ih (Ty.app head a)

private theorem Ty.apps_con_inj {V : Type} {t t' : Nat} {as bs : List (Ty V)}
    (h : Ty.apps (.con t) as = Ty.apps (.con t') bs) : t = t' ∧ as = bs := by
  have main : ∀ (as bs : List (Ty V)),
      Ty.apps (.con t) as = Ty.apps (.con t') bs → t = t' ∧ as = bs := by
    intro as
    induction as using Ty.list_reverse_induction with
    | nil =>
        intro bs h
        induction bs using Ty.list_reverse_induction with
        | nil => simpa [Ty.apps] using h
        | step ys y _ =>
            rw [Ty.apps_append_singleton] at h
            cases h
    | step xs x ih =>
        intro bs h
        induction bs using Ty.list_reverse_induction with
        | nil =>
            rw [Ty.apps_append_singleton] at h
            cases h
        | step ys y _ =>
            rw [Ty.apps_append_singleton, Ty.apps_append_singleton] at h
            injection h with hhead hlast
            obtain ⟨rfl, rfl⟩ := ih ys hhead
            subst hlast
            exact ⟨rfl, rfl⟩
  exact main as bs h

private theorem Ty.apps_con_ne_arrow {V : Type} {t : Nat} {params : List (Ty V)} {a b : Ty V} :
    Ty.apps (.con t) params ≠ .arrow a b := by
  induction params using Ty.list_reverse_induction with
  | nil => intro h; cases h
  | step xs x _ =>
      intro h
      rw [Ty.apps_append_singleton] at h
      cases h

private theorem Ty.apps_con_ne_prim {V : Type} {t : Nat} {params : List (Ty V)} {p : PrimTy} :
    Ty.apps (.con t) params ≠ .prim p := by
  induction params using Ty.list_reverse_induction with
  | nil => intro h; cases h
  | step xs x _ =>
      intro h
      rw [Ty.apps_append_singleton] at h
      cases h

private theorem Ty.arrow_ne_prim {V : Type} {a b : Ty V} {p : PrimTy} :
    Ty.arrow a b ≠ .prim p := by
  intro h; cases h

private theorem Ty.arrows_eq_arrows_append {V : Type} {as bs : List (Ty V)} {s t : Ty V}
    (h : Ty.arrows as s = Ty.arrows bs t) (hlen : as.length ≤ bs.length) :
    ∃ rest, bs = as ++ rest ∧ s = Ty.arrows rest t := by
  induction as generalizing bs with
  | nil => exact ⟨bs, by simp, h⟩
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          change Ty.arrow a (Ty.arrows as s) = Ty.arrow b (Ty.arrows bs t) at h
          injection h with hb htail
          subst hb
          have hlen' : as.length ≤ bs.length := by simpa using hlen
          obtain ⟨rest, hbs, hs⟩ := ih htail hlen'
          exact ⟨rest, by simp [hbs], hs⟩

private theorem Ty.arrows_cancel {V : Type} {as bs : List (Ty V)} {s t : Ty V}
    (h : Ty.arrows as s = Ty.arrows bs t) (hlen : as.length = bs.length) :
    as = bs ∧ s = t := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => exact ⟨rfl, h⟩
      | cons => simp at hlen
  | cons a as ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          change Ty.arrow a (Ty.arrows as s) = Ty.arrow b (Ty.arrows bs t) at h
          injection h with hb htail
          subst hb
          have hlen' : as.length = bs.length := by simpa using hlen
          obtain ⟨habs, ht⟩ := ih htail hlen'
          exact ⟨by simp [habs], ht⟩

private theorem Ty.arrows_cancel_cons {V : Type} {X r : Ty V} {bs argTys : List (Ty V)}
    {ty : Ty V} (h : Ty.arrow X (Ty.arrows bs r) = Ty.arrows argTys ty)
    (hlen : (X :: bs).length = argTys.length) :
    X :: bs = argTys ∧ r = ty := by
  have h' : Ty.arrows (X :: bs) r = Ty.arrows argTys ty := by
    simpa [Ty.arrows] using h
  exact Ty.arrows_cancel h' hlen

private theorem Ty.getD_range_eq {V : Type} {args : List (Ty V)} {n : Nat}
    (hlen : args.length = n) :
    (List.range n).map (fun i => args.getD i (.bvar i)) = args := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi _
    simp only [List.getElem_map, List.getElem_range]
    have hai : i < args.length := by simpa [hlen] using hi
    have hget : args[i]? = some args[i] := List.getElem?_eq_getElem hai
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]

private theorem DataDecl.selfTy_inst {decl : DataDecl} {type : Nat} {args : List SemTy}
    (hlen : args.length = decl.params) :
    (decl.selfTy type).instantiate args = Ty.apps (.con type) args := by
  unfold DataDecl.selfTy
  rw [Ty.instantiate_apps, List.map_map]
  congr 1
  simpa [Ty.instantiate] using (Ty.getD_range_eq (V := Empty) hlen)

private theorem Ty.apps_scoped {V : Type} {head : Ty V} {args : List (Ty V)}
    {rigids binders : Nat} (headScoped : head.Scoped rigids binders)
    (argsScoped : ∀ a ∈ args, a.Scoped rigids binders) :
    (Ty.apps head args).Scoped rigids binders := by
  induction args generalizing head with
  | nil => exact headScoped
  | cons a as ih =>
      change Ty.Scoped rigids binders (Ty.apps (Ty.app head a) as)
      exact ih ⟨headScoped, argsScoped a (by simp)⟩
        (fun x hx => argsScoped x (by simp [hx]))

private theorem Ty.arrows_scoped {V : Type} {domains : List (Ty V)} {codomain : Ty V}
    {rigids binders : Nat} (domainsScoped : ∀ d ∈ domains, d.Scoped rigids binders)
    (codomainScoped : codomain.Scoped rigids binders) :
    (Ty.arrows domains codomain).Scoped rigids binders := by
  induction domains with
  | nil => exact codomainScoped
  | cons d ds ih =>
      exact ⟨domainsScoped d (by simp),
        ih (fun x hx => domainsScoped x (by simp [hx]))⟩

/-- A declaration's self type is scoped by its own parameters. -/
private theorem DataDecl.selfTy_scoped {decl : DataDecl} (type : Nat) :
    (decl.selfTy type).Scoped rigids decl.params := by
  unfold DataDecl.selfTy
  refine Ty.apps_scoped trivial ?_
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  simp only [List.mem_range] at hi
  exact hi

theorem DataDecl.WF.ctorScheme_wf {decl : DataDecl} (wf : decl.WF) {fields : List SemTy}
    (mem : fields ∈ decl.ctors) (type : Nat) : (decl.ctorScheme type fields).WF 0 := by
  show (Ty.arrows fields (decl.selfTy type)).Scoped 0 decl.params
  refine Ty.arrows_scoped ?_ ?_
  · intro field hfield
    exact wf fields mem field hfield
  · exact Ty.Scoped.mono (DataDecl.selfTy_scoped (rigids := 0) type)
      (Nat.zero_le _) (le_refl _)

theorem DataDecl.WF.elimScheme_wf {decl : DataDecl} (wf : decl.WF) (type : Nat) :
    (decl.elimScheme type).WF 0 := by
  show (Ty.arrow (decl.selfTy type)
      (Ty.arrows (decl.ctors.map (branchTy · (.bvar decl.params))) (.bvar decl.params))).Scoped
    0 (decl.params + 1)
  refine ⟨Ty.Scoped.mono (DataDecl.selfTy_scoped (rigids := 0) type)
    (Nat.zero_le _) (Nat.le_succ _), ?_⟩
  refine Ty.arrows_scoped ?_ (Nat.lt_succ_self _)
  intro branch hbranch
  obtain ⟨fields, hfields, rfl⟩ := List.mem_map.mp hbranch
  refine ⟨trivial, ?_⟩
  refine Ty.arrows_scoped ?_ (Nat.lt_succ_self _)
  intro field hfield
  exact Ty.Scoped.mono (wf fields hfields field hfield) (Nat.zero_le _) (Nat.le_succ _)

/-! ## Signature lemmas -/

private theorem schemeOf_ctor_some {sig : Signature} {type index : Nat} {scheme : Scheme Empty}
    (found : sig.schemeOf (.ctor type index) = some scheme) :
    ∃ (decl : DataDecl) (fields : List SemTy),
      sig[type]? = some decl ∧ decl.ctors[index]? = some fields ∧
        scheme = decl.ctorScheme type fields := by
  cases hdecl : sig[type]? with
  | none => simp [Signature.schemeOf, hdecl] at found
  | some decl =>
      cases hfields : decl.ctors[index]? with
      | none => simp [Signature.schemeOf, hdecl, hfields] at found
      | some fields =>
          have hwf : decl.WF := by
            by_contra h
            simp [Signature.schemeOf, hdecl, h] at found
          refine ⟨decl, fields, rfl, hfields, ?_⟩
          have hsome : sig.schemeOf (.ctor type index) = some (decl.ctorScheme type fields) := by
            simp [Signature.schemeOf, hdecl, hfields, hwf]
          rw [hsome] at found
          exact (Option.some.inj found).symm

private theorem schemeOf_elim_some {sig : Signature} {type : Nat} {scheme : Scheme Empty}
    (found : sig.schemeOf (.elim type) = some scheme) :
    ∃ decl : DataDecl, sig[type]? = some decl ∧ scheme = decl.elimScheme type := by
  cases hdecl : sig[type]? with
  | none => simp [Signature.schemeOf, hdecl] at found
  | some decl =>
      have hwf : decl.WF := by
        by_contra h
        simp [Signature.schemeOf, hdecl, h] at found
      refine ⟨decl, rfl, ?_⟩
      have hsome : sig.schemeOf (.elim type) = some (decl.elimScheme type) := by
        simp [Signature.schemeOf, hdecl, hwf]
      rw [hsome] at found
      exact (Option.some.inj found).symm

/-- Every scheme a signature assigns is closed. -/
theorem Signature.schemeOf_wf {sig : Signature} {c : DataConst} {scheme : Scheme Empty}
    (found : sig.schemeOf c = some scheme) : scheme.WF 0 := by
  cases c with
  | ctor type index =>
      obtain ⟨decl, fields, hdecl, hfields, rfl⟩ := schemeOf_ctor_some found
      have hwf : decl.WF := by
        by_contra h
        simp [Signature.schemeOf, hdecl, h] at found
      exact DataDecl.WF.ctorScheme_wf hwf (List.mem_of_getElem? hfields) type
  | elim type =>
      obtain ⟨decl, hdecl, rfl⟩ := schemeOf_elim_some found
      have hwf : decl.WF := by
        by_contra h
        simp [Signature.schemeOf, hdecl, h] at found
      exact DataDecl.WF.elimScheme_wf hwf type

private theorem schemeOf_valueArity {sig : Signature} {c : DataConst} {scheme : Scheme Empty}
    (found : sig.schemeOf c = some scheme) : ∃ arity, sig.valueArity c = some arity := by
  cases c with
  | ctor type index =>
      obtain ⟨decl, fields, hdecl, hfields, _⟩ := schemeOf_ctor_some found
      exact ⟨fields.length, by simp [Signature.valueArity, hdecl, hfields]⟩
  | elim type =>
      obtain ⟨decl, hdecl, _⟩ := schemeOf_elim_some found
      exact ⟨decl.ctors.length, by simp [Signature.valueArity, hdecl]⟩

private theorem tyWF_mono {V : Type} {ty : Ty V} {k k' : Nat}
    (wf : ty.WF k) (le : k ≤ k') : ty.WF k' :=
  wf.mono le (le_refl _)

private theorem schemeWF_mono {V : Type} {scheme : Scheme V} {k k' : Nat}
    (wf : scheme.WF k) (le : k ≤ k') : scheme.WF k' :=
  wf.mono le (le_refl _)

private theorem Ctx.WF.getElem? {V : Type} {ctx : Ctx V} {k : Nat}
    (wf : ctx.WF k) {i : Nat} {scheme : Scheme V} (h : ctx[i]? = some scheme) :
    scheme.WF k :=
  wf scheme (List.mem_of_getElem? h)

private theorem Ctx.WF.cons {V : Type} {ctx : Ctx V} {scheme : Scheme V} {k : Nat}
    (hs : scheme.WF k) (hc : ctx.WF k) : Ctx.WF k (scheme :: ctx) := by
  intro s hmem
  rcases List.mem_cons.mp hmem with rfl | h
  · exact hs
  · exact hc s h

/-- Every instance of a scheme well-formed at `k` is well-formed at the instance
depth. -/
private theorem Scheme.Instance.wf {V : Type} {scheme : Scheme V} {ty : Ty V} {k k' : Nat}
    (hwf : scheme.WF k) (le : k ≤ k') (hinst : scheme.Instance k' ty) : ty.WF k' := by
  obtain ⟨args, hlen, hargs, heq⟩ := hinst
  rw [← heq]
  exact Scheme.inst_wf hwf le hlen hargs

/-- Every primitive operator's type is either `p → p → p` or `p → p → Bool`. -/
private theorem primOp_ty_eq {sig : Signature} {op : PrimOp} {ty : SemTy}
    (hop : op.ty sig = some ty) :
    (∃ p : PrimTy, ty = .arrow (.prim p) (.arrow (.prim p) (.prim p))) ∨
      (∃ p : PrimTy, ty = .arrow (.prim p) (.arrow (.prim p) Ty.bool)) := by
  cases op with
  | intAdd | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at hop
      subst hop
      exact .inl ⟨.int, rfl⟩
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
        subst hop
        exact .inr ⟨.int, rfl⟩
      · simp [PrimOp.ty, if_neg hb] at hop
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
        subst hop
        exact .inr ⟨.char, rfl⟩
      · simp [PrimOp.ty, if_neg hb] at hop

namespace RuntimeTyping

theorem regular (ctxWF : ctx.WF k) (typing : RuntimeTyping sig k ctx expr ty) : ty.WF k := by
  induction typing with
  | lit =>
      rename_i literal
      cases literal <;> trivial
  | primOp hop =>
      rcases primOp_ty_eq hop with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
        simp [Ty.WF, Ty.Scoped, Ty.bool]
  | const hscheme hinst =>
      exact Scheme.Instance.wf (Signature.schemeOf_wf hscheme) (Nat.zero_le _) hinst
  | var hlook hinst =>
      exact Scheme.Instance.wf (Ctx.WF.getElem? ctxWF hlook) (le_refl _) hinst
  | lambda hparam _ ih =>
      exact ⟨hparam, ih (Ctx.WF.cons hparam ctxWF)⟩
  | app _ _ ihfun _ =>
      exact (ihfun ctxWF).2
  | letIn hwf _ _ ihRhs ihBody =>
      exact ihBody (Ctx.WF.cons hwf ctxWF)
  | fix hwf _ ih =>
      exact ih (Ctx.WF.cons hwf ctxWF)

/-- Proof: induction; the `letIn` premise already quantifies over all larger
depths. -/
theorem mono_depth (typing : RuntimeTyping sig k ctx expr ty) (le : k ≤ k') :
    RuntimeTyping sig k' ctx expr ty := by
  induction typing generalizing k' with
  | lit => exact .lit
  | primOp h => exact .primOp h
  | const hsch hinst => exact .const hsch (hinst.mono le)
  | var hlook hinst => exact .var hlook (hinst.mono le)
  | lambda hwf hbody ih =>
      exact .lambda (tyWF_mono hwf le) (ih le)
  | app _ _ ihfun iharg =>
      exact .app (ihfun le) (iharg le)
  | letIn hwf hrhs hbody ihRhs ihBody =>
      exact .letIn (schemeWF_mono hwf le)
        (fun k'' hle ty hinst => hrhs k'' (le_trans le hle) ty hinst) (ihBody le)
  | fix hwf hbody ih =>
      exact .fix (tyWF_mono hwf le) (ih le)

private theorem List.getElem?_insert {α : Type} (l extra r : List α) (i : Nat) :
    (l ++ extra ++ r)[if l.length ≤ i then i + extra.length else i]? = (l ++ r)[i]? := by
  by_cases h : i < l.length
  · have h' : ¬ l.length ≤ i := Nat.not_le.mpr h
    rw [if_neg h']
    rw [List.append_assoc]
    rw [List.getElem?_append_left h, List.getElem?_append_left h]
  · have hl : l.length ≤ i := Nat.le_of_not_gt h
    rw [if_pos hl]
    rw [List.append_assoc]
    rw [List.getElem?_append_right (by omega : l.length ≤ i + extra.length)]
    have harith : i + extra.length - l.length = (i - l.length) + extra.length := by omega
    rw [harith, List.getElem?_append_right
      (by omega : extra.length ≤ (i - l.length) + extra.length)]
    rw [List.getElem?_append_right hl]
    congr 1
    omega

private theorem weaken_at {sig : Signature} {k : Nat} {env : Ctx Empty}
    {expr : RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k env expr ty) :
    ∀ (extra : Ctx Empty) (inner ctx : Ctx Empty), env = inner ++ ctx →
      RuntimeTyping sig k (inner ++ extra ++ ctx) (expr.shift inner.length extra.length) ty := by
  induction typing with
  | lit => intro extra inner ctx _; exact .lit
  | primOp h => intro extra inner ctx _; exact .primOp h
  | const hsch hinst => intro extra inner ctx _; exact .const hsch hinst
  | var hlook hinst =>
      intro extra inner ctx envEq
      rw [envEq] at hlook
      refine RuntimeTyping.var ?_ hinst
      rw [List.getElem?_insert]
      exact hlook
  | lambda hparam hbody ih =>
      expose_names
      intro extra inner ctx envEq
      refine RuntimeTyping.lambda hparam ?_
      have hb := ih extra (Scheme.mono paramTy :: inner) ctx (by simp [envEq])
      simpa [Expr.shift, List.length_cons] using hb
  | app _ _ ihfun iharg =>
      intro extra inner ctx envEq
      exact .app (ihfun extra inner ctx envEq) (iharg extra inner ctx envEq)
  | letIn hwf hrhs hbody ihRhs ihBody =>
      expose_names
      intro extra inner ctx envEq
      refine RuntimeTyping.letIn hwf ?_ ?_
      · intro k' hle ty hinst
        exact ihRhs k' hle ty hinst extra inner ctx envEq
      · have hb := ihBody extra (scheme :: inner) ctx (by simp [envEq])
        simpa [Expr.shift, List.length_cons] using hb
  | fix hwf hbody ih =>
      expose_names
      intro extra inner ctx envEq
      refine RuntimeTyping.fix hwf ?_
      have hb := ih extra (Scheme.mono selfTy :: inner) ctx (by simp [envEq])
      simpa [Expr.shift, List.length_cons] using hb

/-- Term weakening: insert `extra` below the innermost `inner.length` binders. -/
theorem weaken (typing : RuntimeTyping sig k (inner ++ ctx) expr ty) (extra : Ctx Empty) :
    RuntimeTyping sig k (inner ++ extra ++ ctx) (expr.shift inner.length extra.length) ty := by
  exact weaken_at typing extra inner ctx rfl

/-- `subst`, with the context split as an equation so that the induction goes
through. -/
private theorem subst_at {sig : Signature} {k : Nat} {env : Ctx Empty}
    {expr : RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k env expr ty) :
    ∀ (scheme : Scheme Empty) (ctx : Ctx Empty) (v : RuntimeExpr) (inner : Ctx Empty),
      env = inner ++ scheme :: ctx →
      (∀ k', k ≤ k' → ∀ ty', scheme.Instance k' ty' → RuntimeTyping sig k' ctx v ty') →
      RuntimeTyping sig k (inner ++ ctx) (expr.substAt inner.length v) ty := by
  induction typing with
  | lit => intro scheme ctx v inner _ _; exact .lit
  | primOp h => intro scheme ctx v inner _ _; exact .primOp h
  | const hsch hinst => intro scheme ctx v inner _ _; exact .const hsch hinst
  | var hlook hinst =>
      expose_names
      intro target ctx v inner envEq value
      rw [envEq] at hlook
      by_cases hlt : index < inner.length
      · rw [List.getElem?_append_left hlt] at hlook
        simp only [Expr.substAt, if_pos hlt]
        refine RuntimeTyping.var ?_ hinst
        rw [List.getElem?_append_left hlt]
        exact hlook
      · by_cases heq : index = inner.length
        · subst heq
          simp only [Expr.substAt, if_neg hlt]
          have hget : (inner ++ target :: ctx)[inner.length]? = some target := by
            rw [List.getElem?_append_right (le_refl _)]
            simp
          have hschEq : scheme = target := by
            rw [hget] at hlook
            exact (Option.some.inj hlook).symm
          subst hschEq
          exact weaken (inner := []) (ctx := ctx) (extra := inner)
            (value k_1 (le_refl k_1) ty_1 hinst)
        · simp only [Expr.substAt, if_neg hlt, if_neg heq]
          refine RuntimeTyping.var ?_ hinst
          rw [List.getElem?_append_right (by omega : inner.length ≤ index - 1)]
          rw [show index - 1 - inner.length = index - inner.length - 1 by omega]
          rw [List.getElem?_append_right (by omega : inner.length ≤ index)] at hlook
          rw [show index - inner.length = (index - inner.length - 1) + 1 by omega] at hlook
          rw [List.getElem?_cons_succ] at hlook
          exact hlook
  | lambda hparam hbody ih =>
      expose_names
      intro target ctx v inner envEq value
      refine RuntimeTyping.lambda hparam ?_
      have hb := ih target ctx v (Scheme.mono paramTy :: inner)
        (by simp [envEq]) value
      simpa [Expr.substAt, List.length_cons] using hb
  | app _ _ ihfun iharg =>
      intro target ctx v inner envEq value
      exact .app (ihfun target ctx v inner envEq value)
        (iharg target ctx v inner envEq value)
  | letIn hwf hrhs hbody ihRhs ihBody =>
      expose_names
      intro target ctx v inner envEq value
      refine RuntimeTyping.letIn hwf ?_ ?_
      · intro k' hle ty hinst
        exact ihRhs k' hle ty hinst target ctx v inner envEq
          (fun k'' hk ty'' hinst'' => value k'' (le_trans hle hk) ty'' hinst'')
      · have hb := ihBody target ctx v (scheme :: inner) (by simp [envEq]) value
        simpa [Expr.substAt, List.length_cons] using hb
  | fix hwf hbody ih =>
      expose_names
      intro target ctx v inner envEq value
      refine RuntimeTyping.fix hwf ?_
      have hb := ih target ctx v (Scheme.mono selfTy :: inner) (by simp [envEq]) value
      simpa [Expr.substAt, List.length_cons] using hb

/-- Substitute a value for the variable bound to `scheme`, given that the value
has every instance of the scheme at every larger depth (which is exactly what
the `letIn` rule provides, and what `mono_depth` provides for a monomorphic
binder). Proof: induction on `typing`, generalizing `inner` and `k`; the
variable case uses `weaken` with `inner := []`. -/
theorem subst (typing : RuntimeTyping sig k (inner ++ scheme :: ctx) expr ty)
    (value : ∀ k', k ≤ k' → ∀ ty', scheme.Instance k' ty' → RuntimeTyping sig k' ctx v ty') :
    RuntimeTyping sig k (inner ++ ctx) (expr.substAt inner.length v) ty := by
  exact subst_at typing scheme ctx v inner rfl value

private theorem mapSubstRigids_congr {ctx : Ctx Empty} {f g : Nat → SemTy} {k : Nat}
    (wf : ctx.WF k) (agree : ∀ l < k, f l = g l) :
    ctx.map (Scheme.substRigids f) = ctx.map (Scheme.substRigids g) := by
  apply List.map_congr_left
  intro s hs
  exact Scheme.substRigids_congr (wf s hs) agree

/-- Type substitution maps a scheme instance by substituting the arguments. -/
private theorem Scheme.instance_substRigids {scheme : Scheme Empty} {ty : SemTy}
    {k k' : Nat} {f : Nat → SemTy} (hinst : scheme.Instance k ty)
    (hwf : scheme.WF k) (images : ∀ l < k, (f l).WF k') :
    (scheme.substRigids f).Instance k' (ty.substRigids f) := by
  obtain ⟨args, hlen, hargs, heq⟩ := hinst
  refine ⟨args.map (fun a => a.substRigids f), ?_, ?_, ?_⟩
  · simpa using hlen
  · intro a ha
    obtain ⟨orig, horig, rfl⟩ := List.mem_map.mp ha
    exact Ty.substRigids_wf (hargs orig horig) images
  · rw [← heq]
    exact (Scheme.inst_substRigids (rigids := k') args hwf images).symm

/-- Type substitution: replace the rigid levels below `k` by types
well-formed at `k'`. Proof: induction on `typing`, generalizing `k'` and `f`.
In the `letIn` case, prove the premise at depth `k'' ≥ k'` for the instance
`(scheme.substRigids f).inst args` by applying the induction hypothesis to the
generic instance `scheme.skolemize k` (at depth `k + arity`) with the
substitution `fun l => if l < k then f l else args.getD (l - k) (.rigid l)`;
`ctxWF` makes it act on the context as `f` does. -/
theorem substRigids (ctxWF : ctx.WF k) (typing : RuntimeTyping sig k ctx expr ty)
    (f : Nat → SemTy) (images : ∀ l < k, (f l).WF k') :
    RuntimeTyping sig k' (ctx.map (Scheme.substRigids f)) expr (ty.substRigids f) := by
  induction typing generalizing k' f with
  | lit =>
      rename_i literal
      cases literal <;> exact .lit
  | primOp hop =>
      rcases primOp_ty_eq hop with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;>
        exact .primOp (by simpa [Ty.substRigids, Ty.subst] using hop)
  | const hscheme hinst =>
      have hinst' := Scheme.instance_substRigids hinst
        (schemeWF_mono (Signature.schemeOf_wf hscheme) (Nat.zero_le _)) images
      rw [Scheme.substRigids_eq_self (Signature.schemeOf_wf hscheme)
        (fun l hl => absurd hl (Nat.not_lt_zero l))] at hinst'
      exact .const hscheme hinst'
  | var hlook hinst =>
      expose_names
      refine .var (scheme := Scheme.substRigids f scheme) ?_ ?_
      · rw [List.getElem?_map, hlook]
        rfl
      · exact Scheme.instance_substRigids hinst (Ctx.WF.getElem? ctxWF hlook) images
  | lambda hparam hbody ih =>
      expose_names
      refine .lambda (Ty.substRigids_wf hparam images) ?_
      have hb := ih (Ctx.WF.cons hparam ctxWF) f images
      simpa [Scheme.substRigids, Scheme.mono] using hb
  | app _ _ ihfun iharg =>
      exact .app (ihfun ctxWF f images) (iharg ctxWF f images)
  | letIn hwf hrhs hbody ihRhs ihBody =>
      expose_names
      refine .letIn (Scheme.substRigids_wf hwf images) ?_ ?_
      · intro k'' hle ty'' hinst''
        obtain ⟨args, hlen, hargs, hinstEq⟩ := hinst''
        have hlen' : args.length = scheme.arity := by
          simpa [Scheme.substRigids] using hlen
        let g : Nat → SemTy :=
          fun l => if l < k_1 then f l else args.getD (l - k_1) (.rigid l)
        have hg : ∀ l < k_1 + scheme.arity, (g l).WF k'' := by
          intro l hl
          by_cases hlt : l < k_1
          · simp only [g, if_pos hlt]
            exact tyWF_mono (images l hlt) hle
          · have hge : k_1 ≤ l := Nat.le_of_not_gt hlt
            simp only [g, if_neg hlt]
            have hidx : l - k_1 < args.length := by
              rw [hlen']; omega
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx,
              Option.getD_some]
            exact hargs _ (List.getElem_mem hidx)
        have hgen := ihRhs (k_1 + scheme.arity) (Nat.le_add_right _ _)
          (scheme.skolemize k_1) (Scheme.skolemize_instance _ _)
          (Ctx.WF.mono ctxWF (Nat.le_add_right _ _)) g hg
        have hctx : ctx_1.map (Scheme.substRigids g) =
            ctx_1.map (Scheme.substRigids f) :=
          mapSubstRigids_congr ctxWF (fun l hl => by simp only [g, if_pos hl])
        rw [hctx] at hgen
        have hty : (scheme.skolemize k_1).substRigids g = ty'' := by
          rw [Scheme.skolemize_substRigids_inst (k := k_1) (f := f) hwf hlen' images,
            hinstEq]
        rwa [hty] at hgen
      · have hb := ihBody (Ctx.WF.cons hwf ctxWF) f images
        simpa [Scheme.substRigids] using hb
  | fix hwf hbody ih =>
      expose_names
      refine .fix (Ty.substRigids_wf hwf images) ?_
      have hb := ih (Ctx.WF.cons hwf ctxWF) f images
      simpa [Scheme.substRigids, Scheme.mono] using hb

/-! ## Primitive operators and canonical forms -/

private theorem primOp_ty_arrow {sig : Signature} {op : PrimOp} {ty : SemTy}
    (hop : op.ty sig = some ty) : ∃ a b, ty = .arrow a b := by
  rcases primOp_ty_eq hop with ⟨p, rfl⟩ | ⟨p, rfl⟩ <;> exact ⟨_, _, rfl⟩

private theorem primOp_ty_codomain_arrow {sig : Signature} {op : PrimOp} {a b : SemTy}
    (hop : op.ty sig = some (.arrow a b)) : ∃ c d, b = .arrow c d := by
  rcases primOp_ty_eq hop with ⟨p, h⟩ | ⟨p, h⟩ <;>
    (injection h with _ hb; exact ⟨_, _, hb⟩)

private theorem primOp_ty_domain {sig : Signature} {op : PrimOp} {α β ty : SemTy}
    (hop : op.ty sig = some (.arrow α (.arrow β ty))) :
    ∃ p q, α = .prim p ∧ β = .prim q := by
  rcases primOp_ty_eq hop with ⟨p, h⟩ | ⟨p, h⟩ <;>
    (injection h with hα hβ; exact ⟨p, p, hα, (Ty.arrow.inj hβ).1⟩)

private theorem primLit_int_eq {V : Type} {lit : PrimLit} (h : (lit.ty : Ty V) = .prim .int) :
    ∃ n, lit = .int n := by
  cases lit with
  | int n => exact ⟨n, rfl⟩
  | unit | char _ => simp [PrimLit.ty] at h

private theorem primLit_char_eq {V : Type} {lit : PrimLit} (h : (lit.ty : Ty V) = .prim .char) :
    ∃ c, lit = .char c := by
  cases lit with
  | char c => exact ⟨c, rfl⟩
  | unit | int _ => simp [PrimLit.ty] at h

private theorem hasBool_schemeOf_boolCtor {sig : Signature} (hsig : sig.HasBool)
    (c : Nat) (hc : c < 2) :
    sig.schemeOf (.ctor 0 c) = some (Scheme.mono Ty.bool) := by
  have h0 : sig[0]? = some boolDecl := hsig
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases hc' with rfl | rfl <;>
    simp [Signature.schemeOf, h0, boolDecl, DataDecl.ctorScheme, DataDecl.selfTy,
      Ty.apps, Ty.arrows, Scheme.mono, Ty.bool, DataDecl.WF]

private theorem hasBool_boolValue_typing {sig : Signature} (hsig : sig.HasBool) (b : Bool)
    {k : Nat} {ctx : Ctx Empty} :
    RuntimeTyping sig k ctx (Eval.boolValue b) Ty.bool := by
  exact RuntimeTyping.const (hasBool_schemeOf_boolCtor hsig (if b then 0 else 1)
    (by split <;> omega)) (Scheme.instance_mono.mpr rfl)

/-- A saturated primitive application on operands of the right kinds has a result. -/
private theorem primOp_eval_exists {sig : Signature} {op : PrimOp} {left right : PrimLit}
    {α β ty : SemTy}
    (hop : op.ty sig = some (.arrow α (.arrow β ty)))
    (hleft : left.ty = α) (hright : right.ty = β) :
    ∃ result, PrimOp.eval op left right = some result := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      obtain ⟨hα, hβ, _⟩ := hop
      obtain ⟨l, rfl⟩ := primLit_int_eq (hleft.trans hα.symm)
      obtain ⟨rr, rfl⟩ := primLit_int_eq (hright.trans hβ.symm)
      exact ⟨.lit (.int (l + rr)), by simp [PrimOp.eval]⟩
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      obtain ⟨hα, hβ, _⟩ := hop
      obtain ⟨l, rfl⟩ := primLit_int_eq (hleft.trans hα.symm)
      obtain ⟨rr, rfl⟩ := primLit_int_eq (hright.trans hβ.symm)
      exact ⟨.lit (.int (l - rr)), by simp [PrimOp.eval]⟩
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq, Ty.arrow.injEq] at hop
        obtain ⟨hα, hβ, _⟩ := hop
        obtain ⟨l, rfl⟩ := primLit_int_eq (hleft.trans hα.symm)
        obtain ⟨rr, rfl⟩ := primLit_int_eq (hright.trans hβ.symm)
        exact ⟨Eval.boolValue (decide (l < rr)), by simp [PrimOp.eval]⟩
      · simp [PrimOp.ty, if_neg hb] at hop
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq, Ty.arrow.injEq] at hop
        obtain ⟨hα, hβ, _⟩ := hop
        obtain ⟨l, rfl⟩ := primLit_char_eq (hleft.trans hα.symm)
        obtain ⟨rr, rfl⟩ := primLit_char_eq (hright.trans hβ.symm)
        exact ⟨Eval.boolValue (decide (l < rr)), by simp [PrimOp.eval]⟩
      · simp [PrimOp.ty, if_neg hb] at hop

/-- Evaluating a saturated primitive preserves the assigned type. -/
private theorem primOp_eval_typing {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {op : PrimOp} {left right : PrimLit} {result : RuntimeExpr} {α β ty : SemTy}
    (hop : op.ty sig = some (.arrow α (.arrow β ty)))
    (hleft : left.ty = α) (hright : right.ty = β)
    (heval : PrimOp.eval op left right = some result) :
    RuntimeTyping sig k ctx result ty := by
  cases op with
  | intAdd | intSub =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      obtain ⟨hα, hβ, hγ⟩ := hop
      obtain ⟨l, rfl⟩ := primLit_int_eq (hleft.trans hα.symm)
      obtain ⟨rr, rfl⟩ := primLit_int_eq (hright.trans hβ.symm)
      simp only [PrimOp.eval, Option.some.injEq] at heval
      subst heval
      rw [← hγ]
      exact .lit
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq, Ty.arrow.injEq] at hop
        obtain ⟨hα, hβ, hγ⟩ := hop
        obtain ⟨l, rfl⟩ := primLit_int_eq (hleft.trans hα.symm)
        obtain ⟨rr, rfl⟩ := primLit_int_eq (hright.trans hβ.symm)
        simp only [PrimOp.eval, Option.some.injEq] at heval
        subst heval
        rw [← hγ]
        exact hasBool_boolValue_typing hb _
      · simp [PrimOp.ty, if_neg hb] at hop
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq, Ty.arrow.injEq] at hop
        obtain ⟨hα, hβ, hγ⟩ := hop
        obtain ⟨l, rfl⟩ := primLit_char_eq (hleft.trans hα.symm)
        obtain ⟨rr, rfl⟩ := primLit_char_eq (hright.trans hβ.symm)
        simp only [PrimOp.eval, Option.some.injEq] at heval
        subst heval
        rw [← hγ]
        exact hasBool_boolValue_typing hb _
      · simp [PrimOp.ty, if_neg hb] at hop

/-! ## Application spines -/

private theorem typing_apps_intro {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {f : RuntimeExpr} {tys : List SemTy} {u : SemTy}
    (typing : RuntimeTyping sig k ctx f (Ty.arrows tys u))
    {args : List RuntimeExpr}
    (hargs : List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) args tys) :
    RuntimeTyping sig k ctx (Expr.apps f args) u := by
  induction hargs generalizing f u with
  | nil => simpa [Expr.apps] using typing
  | cons hhead htail ih =>
      exact ih (RuntimeTyping.app typing hhead)

private theorem typing_spine_inv {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {head : RuntimeExpr} {args : List RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k ctx (Expr.apps head args) ty) :
    ∃ argTys : List SemTy,
      List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) args argTys ∧
      RuntimeTyping sig k ctx head (Ty.arrows argTys ty) := by
  induction args generalizing head ty with
  | nil => exact ⟨[], .nil, by simpa [Expr.apps] using typing⟩
  | cons a as ih =>
      obtain ⟨argTys, hforall, hhead⟩ := ih typing
      cases hhead with
      | app hf ha =>
          cases argTys with
          | nil =>
              exact ⟨[_], .cons ha hforall, by simpa [Ty.arrows] using hf⟩
          | cons b bs =>
              exact ⟨_ :: b :: bs, .cons ha hforall, by simpa [Ty.arrows] using hf⟩

private theorem const_spine_inv {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {c : DataConst} {args : List RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k ctx (Expr.apps (.const c) args) ty) :
    ∃ (scheme : Scheme Empty) (argTys : List SemTy),
      sig.schemeOf c = some scheme ∧
      scheme.Instance k (Ty.arrows argTys ty) ∧
      List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) args argTys := by
  obtain ⟨argTys, hforall, hhead⟩ := typing_spine_inv typing
  cases hhead with
  | const hscheme hinst =>
      exact ⟨_, argTys, hscheme, hinst, hforall⟩

private theorem forall₂_map_inst {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {fields : List SemTy} {args : List RuntimeExpr} {f : SemTy → SemTy}
    (h : List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) args (fields.map f)) :
    List.Forall₂ (fun e ft => RuntimeTyping sig k ctx e (f ft)) args fields := by
  induction fields generalizing args with
  | nil => cases h; exact .nil
  | cons ft fts ih =>
      cases h with
      | cons hhead htail => exact .cons hhead (ih htail)

private theorem DataDecl.ctorScheme_inst {decl : DataDecl} {type : Nat} {fields : List SemTy}
    {args : List SemTy} (hlen : args.length = decl.params) :
    (decl.ctorScheme type fields).inst args =
      Ty.arrows (fields.map (fun ft => ft.instantiate args)) (Ty.apps (.con type) args) := by
  unfold DataDecl.ctorScheme Scheme.inst
  rw [Ty.instantiate_arrows, DataDecl.selfTy_inst hlen]

private theorem DataDecl.selfTy_inst_of_le {decl : DataDecl} {type : Nat} {args : List SemTy}
    (hlen : decl.params ≤ args.length) :
    (decl.selfTy type).instantiate args =
      Ty.apps (.con type) (args.take decl.params) := by
  unfold DataDecl.selfTy
  rw [Ty.instantiate_apps, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp [List.length_take, hlen]
  · intro i hi _
    simp only [List.getElem_map, List.getElem_range]
    have hi' : i < decl.params := by simpa using hi
    have hai : i < args.length := lt_of_lt_of_le hi' hlen
    have hget : args[i]? = some args[i] := List.getElem?_eq_getElem hai
    simp only [Function.comp_apply, Ty.instantiate, Ty.subst]
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_some]
    rw [List.getElem_take]

private theorem DataDecl.elimScheme_inst {decl : DataDecl} {type : Nat} {args : List SemTy}
    (hlen : decl.params < args.length) :
    (decl.elimScheme type).inst args =
      Ty.arrow (Ty.apps (.con type) (args.take decl.params))
        (Ty.arrows (decl.ctors.map (fun fields =>
            Ty.arrow (.prim .unit)
              (Ty.arrows (fields.map (fun ft => ft.instantiate args))
                (args.getD decl.params (.bvar decl.params)))))
          (args.getD decl.params (.bvar decl.params))) := by
  unfold DataDecl.elimScheme Scheme.inst
  dsimp only
  rw [show Ty.instantiate args
        (Ty.arrow (decl.selfTy type)
          (Ty.arrows (List.map (fun x => branchTy x (Ty.bvar decl.params)) decl.ctors)
            (Ty.bvar decl.params))) =
      Ty.arrow (Ty.instantiate args (decl.selfTy type))
        (Ty.instantiate args
          (Ty.arrows (List.map (fun x => branchTy x (Ty.bvar decl.params)) decl.ctors)
            (Ty.bvar decl.params))) from rfl]
  rw [DataDecl.selfTy_inst_of_le (le_of_lt hlen), Ty.instantiate_arrows]
  congr 1
  congr 1
  · rw [List.map_map]
    apply List.map_congr_left
    intro fields _
    simp only [Function.comp_apply]
    rw [Ty.instantiate_branchTy]
    rfl

private theorem Ty.arrows_scoped_inv {V : Type} {domains : List (Ty V)} {codomain : Ty V}
    {r b : Nat} (h : (Ty.arrows domains codomain).Scoped r b) :
    ∀ d ∈ domains, d.Scoped r b := by
  induction domains with
  | nil => simp
  | cons d ds ih =>
      intro x hx
      change Ty.Scoped r b (Ty.arrow d (Ty.arrows ds codomain)) at h
      rcases h with ⟨hd, hr⟩
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hd
      · exact ih hr x hmem

private theorem Ty.instantiate_eq_take {V : Type} {ty : Ty V} {n : Nat} {args : List (Ty V)}
    (wf : ty.Scoped rigids n) (hlen : n ≤ args.length) :
    ty.instantiate args = ty.instantiate (args.take n) := by
  induction ty with
  | prim | con | rigid | var => rfl
  | bvar i =>
      have hi : i < n := wf
      have hi1 : i < args.length := lt_of_lt_of_le hi hlen
      have hi2 : i < (args.take n).length := by
        simpa [List.length_take, Nat.min_eq_left hlen] using hi
      have hget1 : args[i]? = some args[i] := List.getElem?_eq_getElem hi1
      have hget2 : (args.take n)[i]? = some ((args.take n)[i]) :=
        List.getElem?_eq_getElem hi2
      simp only [Ty.instantiate, Ty.subst]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, hget1, hget2]
      simp only [Option.getD_some, List.getElem_take]
  | arrow d c ihd ihc =>
      rcases wf with ⟨hd, hc⟩
      change (Ty.instantiate args d).arrow (Ty.instantiate args c) =
        (Ty.instantiate (args.take n) d).arrow (Ty.instantiate (args.take n) c)
      rw [ihd hd, ihc hc]
  | app d c ihd ihc =>
      rcases wf with ⟨hd, hc⟩
      change (Ty.instantiate args d).app (Ty.instantiate args c) =
        (Ty.instantiate (args.take n) d).app (Ty.instantiate (args.take n) c)
      rw [ihd hd, ihc hc]

private theorem ctorScheme_fields_scoped {decl : DataDecl} {type : Nat} {fields : List SemTy}
    (h : (decl.ctorScheme type fields).WF 0) :
    ∀ ft ∈ fields, ft.Scoped 0 decl.params := by
  intro ft hft
  exact Ty.arrows_scoped_inv h ft hft

private theorem forall₂_instantiate_take {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {fields : List SemTy} {args : List RuntimeExpr} {instArgs : List SemTy} {n : Nat}
    (hfieldsWF : ∀ ft ∈ fields, ft.Scoped 0 n)
    (hlen : n ≤ instArgs.length)
    (h : List.Forall₂ (fun e ft => RuntimeTyping sig k ctx e
      (ft.instantiate (instArgs.take n))) args fields) :
    List.Forall₂ (fun e ft => RuntimeTyping sig k ctx e (ft.instantiate instArgs))
      args fields := by
  induction h with
  | nil => exact .nil
  | cons hhead htail ih =>
      exact .cons (by
        rw [Ty.instantiate_eq_take (hfieldsWF _ (by simp)) hlen]
        exact hhead)
        (ih (fun ft hft => hfieldsWF ft (by simp [hft])))

private theorem forall₂_map_of_forall₂ {fields : List SemTy} {args : List RuntimeExpr}
    {f : SemTy → SemTy} {R : RuntimeExpr → SemTy → Prop}
    (h : List.Forall₂ (fun e ft => R e (f ft)) args fields) :
    List.Forall₂ R args (fields.map f) := by
  induction fields generalizing args with
  | nil => cases h; exact .nil
  | cons ft fts ih =>
      cases h with
      | cons hhead htail => exact .cons hhead (ih htail)

private theorem valueArity_ctor {sig : Signature} {type index : Nat} {decl : DataDecl}
    {fields : List SemTy} (hdecl : sig[type]? = some decl)
    (hfields : decl.ctors[index]? = some fields) :
    sig.valueArity (.ctor type index) = some fields.length := by
  simp [Signature.valueArity, hdecl, hfields]

private theorem valueArity_elim {sig : Signature} {type : Nat} {decl : DataDecl}
    (hdecl : sig[type]? = some decl) :
    sig.valueArity (.elim type) = some decl.ctors.length := by
  simp [Signature.valueArity, hdecl]

private theorem forall₂_get? {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) :
    ∀ {i : Nat} {x : α} {y : β}, xs[i]? = some x → ys[i]? = some y → R x y := by
  induction h with
  | nil => intro i x y hx _; simp at hx
  | cons hhead htail ih =>
      intro i x y hx hy
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst hx; subst hy
          exact hhead
      | succ i =>
          simp only [List.getElem?_cons_succ] at hx hy
          exact ih hx hy

/-- Decompose the typing of an eliminator spine into its scheme instance. -/
private theorem elim_spine_decomp {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {type : Nat} {args : List RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k ctx (Expr.apps (.const (.elim type)) args) ty) :
    ∃ (decl : DataDecl) (instArgs argTys : List SemTy),
      sig[type]? = some decl ∧
      instArgs.length = decl.params + 1 ∧
      (∀ a ∈ instArgs, a.WF k) ∧
      Ty.arrow (Ty.apps (.con type) (instArgs.take decl.params))
          (Ty.arrows (decl.ctors.map (fun fields =>
              Ty.arrow (.prim .unit)
                (Ty.arrows (fields.map (fun ft => ft.instantiate instArgs))
                  (instArgs.getD decl.params (.bvar decl.params)))))
            (instArgs.getD decl.params (.bvar decl.params))) = Ty.arrows argTys ty ∧
      List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) args argTys := by
  obtain ⟨scheme, argTys, hscheme, hinst, hforall⟩ := const_spine_inv typing
  obtain ⟨decl, hdecl, hschemeEq⟩ := schemeOf_elim_some hscheme
  subst hschemeEq
  obtain ⟨instArgs, hilen, hiwf, hinstEq⟩ := hinst
  have hilen' : instArgs.length = decl.params + 1 := by simpa using hilen
  rw [DataDecl.elimScheme_inst (by omega)] at hinstEq
  exact ⟨decl, instArgs, argTys, hdecl, hilen', hiwf, hinstEq, hforall⟩

/-- A non-saturated eliminator spine has an arrow type. -/
private theorem elim_spine_ty_arrow {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {type arity : Nat} {args : List RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k ctx (Expr.apps (.const (.elim type)) args) ty)
    (harity : sig.valueArity (.elim type) = some arity) (hlen : args.length ≤ arity) :
    ∃ X Y, ty = .arrow X Y := by
  obtain ⟨decl, instArgs, argTys, hdecl, _hilen, _hiwf, hinstEq, hforall⟩ :=
    elim_spine_decomp typing
  have harityEq : decl.ctors.length = arity :=
    Option.some.inj ((valueArity_elim hdecl).symm.trans harity)
  have hargLen : argTys.length = args.length := (List.Forall₂.length_eq hforall).symm
  have hlen' : argTys.length ≤
      (Ty.apps (.con type) (instArgs.take decl.params) ::
        decl.ctors.map (fun fields =>
          Ty.arrow (.prim .unit)
            (Ty.arrows (fields.map (fun ft => ft.instantiate instArgs))
              (instArgs.getD decl.params (.bvar decl.params))))).length := by
    simp only [List.length_cons, List.length_map]
    omega
  obtain ⟨rest, hrest, hty⟩ := Ty.arrows_eq_arrows_append hinstEq.symm hlen'
  have hne : rest ≠ [] := by
    intro hnil
    have hlenEq := congrArg List.length hrest
    simp only [hnil, List.append_nil, List.length_cons, List.length_map] at hlenEq
    omega
  cases rest with
  | nil => exact absurd rfl hne
  | cons x xs =>
      exact ⟨x, Ty.arrows xs (instArgs.getD decl.params (.bvar decl.params)), hty⟩

/-- Decompose the typing of a constructor spine into its scheme instance. -/
private theorem ctor_spine_decomp {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {type ctor : Nat} {args : List RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k ctx (Expr.apps (.const (.ctor type ctor)) args) ty) :
    ∃ (decl : DataDecl) (fieldTys instArgs argTys : List SemTy),
      sig[type]? = some decl ∧
      decl.ctors[ctor]? = some fieldTys ∧
      (decl.ctorScheme type fieldTys).WF 0 ∧
      instArgs.length = decl.params ∧
      (∀ a ∈ instArgs, a.WF k) ∧
      Ty.arrows (fieldTys.map (fun ft => ft.instantiate instArgs))
          (Ty.apps (.con type) instArgs) = Ty.arrows argTys ty ∧
      List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) args argTys := by
  obtain ⟨scheme, argTys, hscheme, hinst, hforall⟩ := const_spine_inv typing
  obtain ⟨decl, fieldTys, hdecl, hctors, hschemeEq⟩ := schemeOf_ctor_some hscheme
  subst hschemeEq
  obtain ⟨instArgs, hilen, hiwf, hinstEq⟩ := hinst
  have hilen' : instArgs.length = decl.params := by simpa using hilen
  rw [DataDecl.ctorScheme_inst hilen'] at hinstEq
  exact ⟨decl, fieldTys, instArgs, argTys, hdecl, hctors, Signature.schemeOf_wf hscheme,
    hilen', hiwf, hinstEq, hforall⟩

/-- A constant spine short of saturation is not a primitive value. -/
private theorem const_spine_not_prim {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {c : DataConst} {args : List RuntimeExpr} {arity : Nat} {p : PrimTy}
    (harity : sig.valueArity c = some arity) (hlen : args.length ≤ arity)
    (typing : RuntimeTyping sig k ctx (Expr.apps (.const c) args) (.prim p)) : False := by
  cases c with
  | ctor type index =>
      obtain ⟨decl, fieldTys, instArgs, argTys, hdecl, hctors, _, _, _, hinstEq,
        hforall⟩ := ctor_spine_decomp typing
      have harityEq : fieldTys.length = arity :=
        Option.some.inj ((valueArity_ctor hdecl hctors).symm.trans harity)
      have hargLen : argTys.length = args.length := (List.Forall₂.length_eq hforall).symm
      have hlen' : argTys.length ≤
          (fieldTys.map (fun ft => ft.instantiate instArgs)).length := by
        rw [List.length_map, hargLen]
        omega
      obtain ⟨rest, hrest, hty⟩ := Ty.arrows_eq_arrows_append hinstEq.symm hlen'
      cases rest with
      | nil => exact Ty.apps_con_ne_prim hty.symm
      | cons x xs => exact Ty.arrow_ne_prim hty.symm
  | elim type =>
      obtain ⟨X, Y, hab⟩ := elim_spine_ty_arrow typing harity hlen
      exact Ty.arrow_ne_prim hab.symm

/-- A saturated constructor spine has a data type, never an arrow. -/
private theorem ctor_spine_not_arrow {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {type ctor arity : Nat} {args : List RuntimeExpr} {a b : SemTy}
    (harity : sig.valueArity (.ctor type ctor) = some arity)
    (hlen : args.length = arity)
    (typing : RuntimeTyping sig k ctx (Expr.apps (.const (.ctor type ctor)) args)
      (.arrow a b)) : False := by
  obtain ⟨decl, fieldTys, instArgs, argTys, hdecl, hctors, _, _, _, hinstEq,
    hforall⟩ := ctor_spine_decomp typing
  have harityEq : fieldTys.length = arity :=
    Option.some.inj ((valueArity_ctor hdecl hctors).symm.trans harity)
  have hargLen : argTys.length = args.length := (List.Forall₂.length_eq hforall).symm
  have hlenEq : (fieldTys.map (fun ft => ft.instantiate instArgs)).length = argTys.length := by
    rw [List.length_map, hargLen]
    omega
  obtain ⟨_, hty⟩ := Ty.arrows_cancel hinstEq hlenEq
  exact Ty.apps_con_ne_arrow hty

/-- A value typed at a primitive type is a literal of that type. -/
private theorem prim_value_canonical {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {expr : RuntimeExpr} {p : PrimTy}
    (value : Eval.Value sig expr)
    (typing : RuntimeTyping sig k ctx expr (.prim p)) :
    ∃ literal, expr = .lit literal ∧ (literal.ty : SemTy) = .prim p := by
  cases value with
  | lit =>
      rename_i literal
      cases literal <;> exact ⟨_, rfl, by cases typing; rfl⟩
  | primOp =>
      cases typing with
      | primOp hop =>
          obtain ⟨a, b, hab⟩ := primOp_ty_arrow hop
          exact False.elim (absurd hab.symm Ty.arrow_ne_prim)
  | lambda => cases typing
  | primOpPartial _ =>
      cases typing with
      | app hf _ =>
          cases hf with
          | primOp hop =>
              obtain ⟨a, b, hab⟩ := primOp_ty_codomain_arrow hop
              exact False.elim (absurd hab.symm Ty.arrow_ne_prim)
  | const hspine harity hlen hvals =>
      expose_names
      have hexpr : Expr.apps (.const c) args = expr := by
        have h := Expr.apps_spine expr
        rw [hspine] at h
        exact h
      have typing' : RuntimeTyping sig k ctx (Expr.apps (.const c) args) (.prim p) := by
        rw [hexpr]
        exact typing
      exact (const_spine_not_prim harity hlen typing').elim

/-- A value typed at a declared data type is a saturated constructor spine. -/
private theorem data_value_canonical {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {expr : RuntimeExpr} {t : Nat} {params : List SemTy}
    (value : Eval.Value sig expr)
    (typing : RuntimeTyping sig k ctx expr (Ty.apps (.con t) params)) :
    ∃ (decl : DataDecl) (ctor : Nat) (fieldTys : List SemTy) (fields : List RuntimeExpr),
      sig[t]? = some decl ∧ decl.ctors[ctor]? = some fieldTys ∧
      expr = Expr.apps (.const (.ctor t ctor)) fields ∧
      fields.length = fieldTys.length ∧
      (∀ ft ∈ fieldTys, ft.Scoped 0 decl.params) ∧
      List.Forall₂ (fun e ft => RuntimeTyping sig k ctx e (ft.instantiate params))
        fields fieldTys := by
  cases value with
  | lit =>
      rename_i literal
      generalize hty : Ty.apps (.con t) params = target at typing
      cases typing
      cases literal <;> (exfalso; exact Ty.apps_con_ne_prim hty)
  | primOp =>
      generalize hty : Ty.apps (.con t) params = target at typing
      cases typing with
      | primOp hop =>
          obtain ⟨a, b, hab⟩ := primOp_ty_arrow hop
          exact absurd (hty.trans hab) Ty.apps_con_ne_arrow
  | lambda =>
      generalize hty : Ty.apps (.con t) params = target at typing
      cases typing
      exact absurd hty Ty.apps_con_ne_arrow
  | primOpPartial _ =>
      generalize hty : Ty.apps (.con t) params = target at typing
      cases typing with
      | app hf _ =>
          cases hf with
          | primOp hop =>
              obtain ⟨a, b, hab⟩ := primOp_ty_codomain_arrow hop
              exact absurd (hty.trans hab) Ty.apps_con_ne_arrow
  | const hspine harity hlen hvals =>
      expose_names
      have hexpr : Expr.apps (.const c) args = expr := by
        have h := Expr.apps_spine expr
        rw [hspine] at h
        exact h
      have typing' : RuntimeTyping sig k ctx (Expr.apps (.const c) args)
          (Ty.apps (.con t) params) := by
        rw [hexpr]
        exact typing
      cases c with
      | ctor type ctor =>
          obtain ⟨decl, fieldTys, instArgs, argTys, hdecl, hctors, hwf0, _, _,
            hinstEq, hforall⟩ := ctor_spine_decomp typing'
          have harityEq : fieldTys.length = arity :=
            Option.some.inj ((valueArity_ctor hdecl hctors).symm.trans harity)
          have hargLen : argTys.length = args.length := (List.Forall₂.length_eq hforall).symm
          have hargLenLe : argTys.length ≤
              (fieldTys.map (fun ft => ft.instantiate instArgs)).length := by
            rw [List.length_map]
            omega
          obtain ⟨rest, hrest, htype⟩ :=
            Ty.arrows_eq_arrows_append hinstEq.symm hargLenLe
          cases rest with
          | nil =>
              have hargTys : fieldTys.map (fun ft => ft.instantiate instArgs) = argTys := by
                simpa using hrest
              have htype' : Ty.apps (.con t) params = Ty.apps (.con type) instArgs := by
                simpa using htype
              obtain ⟨htEq, hparamsEq⟩ := Ty.apps_con_inj htype'
              subst htEq
              subst hparamsEq
              refine ⟨decl, ctor, fieldTys, args, hdecl, hctors, ?_, ?_, ?_, ?_⟩
              · rw [hexpr]
              · have hlenMap := congrArg List.length hargTys
                simp only [List.length_map] at hlenMap
                omega
              · exact ctorScheme_fields_scoped hwf0
              · rw [← hargTys] at hforall
                exact forall₂_map_inst hforall
          | cons x xs => exact False.elim (Ty.apps_con_ne_arrow htype)
      | elim type =>
          obtain ⟨X, Y, hab⟩ := elim_spine_ty_arrow typing' harity hlen
          exact False.elim (Ty.apps_con_ne_arrow hab)

/-! ## Eliminator spines -/

/-- A saturated eliminator spine: the scrutinee is a constructor spine, and the
selected branch is typed at the instantiated field types. -/
private theorem elim_spine_saturated {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {type : Nat} {decl : DataDecl} {instArgs argTys : List SemTy}
    {scrutinee : RuntimeExpr} {branches : List RuntimeExpr} {ty : SemTy}
    (hdecl : sig[type]? = some decl)
    (hilen : instArgs.length = decl.params + 1)
    (hbranchLen : branches.length = decl.ctors.length)
    (hinstEq : Ty.arrow (Ty.apps (.con type) (instArgs.take decl.params))
        (Ty.arrows (decl.ctors.map (fun fields =>
            Ty.arrow (.prim .unit)
              (Ty.arrows (fields.map (fun ft => ft.instantiate instArgs))
                (instArgs.getD decl.params (.bvar decl.params)))))
          (instArgs.getD decl.params (.bvar decl.params))) = Ty.arrows argTys ty)
    (hforall : List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t)
      (scrutinee :: branches) argTys)
    (scrutineeValue : Eval.Value sig scrutinee) :
    ∃ (ctor : Nat) (fieldTys : List SemTy) (fields : List RuntimeExpr) (branch : RuntimeExpr),
      ty = instArgs.getD decl.params (.bvar decl.params) ∧
      scrutinee = Expr.apps (.const (.ctor type ctor)) fields ∧
      decl.ctors[ctor]? = some fieldTys ∧
      branches[ctor]? = some branch ∧
      fields.length = fieldTys.length ∧
      (∀ ft ∈ fieldTys, ft.Scoped 0 decl.params) ∧
      List.Forall₂ (fun e ft => RuntimeTyping sig k ctx e (ft.instantiate instArgs))
        fields fieldTys ∧
      RuntimeTyping sig k ctx branch
        (Ty.arrow (.prim .unit)
          (Ty.arrows (fieldTys.map (fun ft => ft.instantiate instArgs))
            (instArgs.getD decl.params (.bvar decl.params)))) := by
  have hargLen : argTys.length = (scrutinee :: branches).length :=
    (List.Forall₂.length_eq hforall).symm
  have hlenEq : (Ty.apps (.con type) (instArgs.take decl.params) ::
      decl.ctors.map (fun fields =>
        Ty.arrow (.prim .unit)
          (Ty.arrows (fields.map (fun ft => ft.instantiate instArgs))
            (instArgs.getD decl.params (.bvar decl.params))))).length = argTys.length := by
    simp only [List.length_cons, List.length_map]
    rw [hargLen]
    simp only [List.length_cons]
    omega
  obtain ⟨hargTys, hty⟩ := Ty.arrows_cancel_cons hinstEq hlenEq
  have hforall' : List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t)
      (scrutinee :: branches)
      (Ty.apps (.con type) (instArgs.take decl.params) ::
        decl.ctors.map (fun fields =>
          Ty.arrow (.prim .unit)
            (Ty.arrows (fields.map (fun ft => ft.instantiate instArgs))
              (instArgs.getD decl.params (.bvar decl.params))))) := by
    rw [← hargTys] at hforall
    exact hforall
  cases hforall' with
  | cons hscrut hbranchForall =>
      obtain ⟨d, ctor, fieldTys, fields, hdeclD, hctors, hexprS, hflen, hfieldWF,
        hfieldTypings⟩ := data_value_canonical scrutineeValue hscrut
      have hdEq : d = decl := Option.some.inj (hdeclD.symm.trans hdecl)
      rw [hdEq] at hctors hfieldWF
      obtain ⟨hctorLt, _⟩ := List.getElem?_eq_some_iff.mp hctors
      have hctorLtB : ctor < branches.length := by rw [hbranchLen]; exact hctorLt
      have hbranch : branches[ctor]? = some (branches[ctor]'hctorLtB) :=
        List.getElem?_eq_getElem hctorLtB
      have hdeclCtor : decl.ctors[ctor] = fieldTys :=
        Option.some.inj ((List.getElem?_eq_getElem hctorLt).symm.trans hctors)
      have hmapGet : (decl.ctors.map (fun fields =>
          Ty.arrow (.prim .unit)
            (Ty.arrows (fields.map (fun ft => ft.instantiate instArgs))
              (instArgs.getD decl.params (.bvar decl.params)))))[ctor]? =
          some (Ty.arrow (.prim .unit)
            (Ty.arrows (fieldTys.map (fun ft => ft.instantiate instArgs))
              (instArgs.getD decl.params (.bvar decl.params)))) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hctorLt, hdeclCtor]
        rfl
      have hfieldTypings' : List.Forall₂ (fun e ft => RuntimeTyping sig k ctx e
          (ft.instantiate instArgs)) fields fieldTys :=
        forall₂_instantiate_take hfieldWF (by omega) hfieldTypings
      exact ⟨ctor, fieldTys, fields, branches[ctor]'hctorLtB, hty.symm, hexprS, hctors,
        hbranch, hflen, hfieldWF, hfieldTypings',
        forall₂_get? hbranchForall hbranch hmapGet⟩

/-- Reducing a saturated eliminator spine whose scrutinee is a constructor
spine selects the matching branch. -/
private theorem reduceConst_elim {sig : Signature} {type ctor : Nat} {decl : DataDecl}
    {fields : List RuntimeExpr} {fieldTys : List SemTy} {branches : List RuntimeExpr}
    {branch scrutinee : RuntimeExpr}
    (hdecl : sig[type]? = some decl) (hbranchLen : branches.length = decl.ctors.length)
    (hctors : decl.ctors[ctor]? = some fieldTys) (hflen : fields.length = fieldTys.length)
    (hbranch : branches[ctor]? = some branch)
    (hexpr : scrutinee = Expr.apps (.const (.ctor type ctor)) fields) :
    Eval.reduceConst sig (.elim type) (scrutinee :: branches) =
      some (Expr.apps branch (.lit .unit :: fields)) := by
  rw [hexpr]
  simp [Eval.reduceConst, Expr.spine_apps, Expr.spine, hdecl, hbranchLen, hctors, hflen,
    hbranch]

/-- `progress`, with the empty context as an equation so that the induction
goes through. -/
private theorem progress_empty (typing : RuntimeTyping sig k ctx expr ty) (empty : ctx = []) :
    Eval.Value sig expr ∨ ∃ next, Eval.Step sig expr next := by
  induction typing with
  | lit => exact .inl .lit
  | primOp => exact .inl .primOp
  | var hlook => simp [empty] at hlook
  | const hscheme hinst =>
      obtain ⟨arity, harity⟩ := schemeOf_valueArity hscheme
      exact .inl (.const rfl harity (Nat.zero_le _) (by simp))
  | lambda => exact .inl .lambda
  | app functionTyping argumentTyping functionIH argumentIH =>
      rcases functionIH empty with functionValue | ⟨function', step⟩
      · rcases argumentIH empty with argumentValue | ⟨argument', step⟩
        · cases functionValue with
          | lit =>
              expose_names
              cases literal <;> cases functionTyping
          | primOp => exact .inl (.primOpPartial argumentValue)
          | lambda => exact .inr ⟨_, .beta argumentValue⟩
          | primOpPartial hleft =>
              cases functionTyping with
              | app operatorTyping leftTyping =>
                  cases operatorTyping with
                  | primOp hop =>
                      obtain ⟨p, q, hα, hβ⟩ := primOp_ty_domain hop
                      obtain ⟨l, rfl, hlty⟩ := prim_value_canonical hleft (hα ▸ leftTyping)
                      obtain ⟨r, rfl, hrty⟩ :=
                        prim_value_canonical argumentValue (hβ ▸ argumentTyping)
                      obtain ⟨result, hresult⟩ := primOp_eval_exists hop
                        (hlty.trans hα.symm) (hrty.trans hβ.symm)
                      exact .inr ⟨result, .primOp hresult⟩
          | const hspine harity hlen hvals =>
              expose_names
              have hfunction : function = Expr.apps (.const c) args := by
                have h := Expr.apps_spine function
                rw [hspine] at h
                exact h.symm
              by_cases hsmall : args.length < arity
              · refine .inl (.const (Expr.spine_app_spine hspine) harity ?_ ?_)
                · rw [List.length_append, List.length_singleton]
                  omega
                · intro arg harg
                  rcases List.mem_append.mp harg with h | h
                  · exact hvals arg h
                  · simp only [List.mem_singleton] at h
                    subst h
                    exact argumentValue
              · have hEq : args.length = arity := le_antisymm hlen (Nat.le_of_not_gt hsmall)
                cases c with
                | ctor type ctor =>
                    exfalso
                    have ftyping := functionTyping
                    rw [hfunction] at ftyping
                    exact ctor_spine_not_arrow harity hEq ftyping
                | elim type =>
                    have hwhole : Expr.apps (.const (.elim type)) (args ++ [argument]) =
                        Expr.app function argument := by
                      rw [Expr.apps_append, hfunction]
                      rfl
                    have whtyping : RuntimeTyping sig k_1 ctx_1
                        (Expr.apps (.const (.elim type)) (args ++ [argument])) resultTy := by
                      rw [hwhole]
                      exact RuntimeTyping.app functionTyping argumentTyping
                    obtain ⟨decl, _, _, hdecl, hilen, _, hinstEq, hforall⟩ :=
                      elim_spine_decomp whtyping
                    have harityEq : decl.ctors.length = arity :=
                      Option.some.inj ((valueArity_elim hdecl).symm.trans harity)
                    have hctorsLen : args.length = decl.ctors.length := by omega
                    cases args with
                    | nil =>
                        obtain ⟨ctor, _, _, _, _, _, hctors, _, _, _, _, _⟩ :=
                          elim_spine_saturated hdecl hilen hctorsLen hinstEq hforall
                            argumentValue
                        obtain ⟨hctorLt, _⟩ := List.getElem?_eq_some_iff.mp hctors
                        have hzero : decl.ctors.length = 0 := by
                          simpa using hctorsLen.symm
                        omega
                    | cons hd tl =>
                        obtain ⟨ctor, fieldTys, fields, branch, _, hexprS, hctors,
                          hbranch, hflen, _, _, _⟩ :=
                          elim_spine_saturated hdecl hilen (by simpa using hctorsLen) hinstEq
                            hforall (hvals hd (by simp))
                        have hreduce : Eval.reduceConst sig (.elim type)
                            (hd :: (tl ++ [argument])) =
                            some (Expr.apps branch (.lit .unit :: fields)) :=
                          reduceConst_elim hdecl (by simpa using hctorsLen) hctors hflen
                            hbranch hexprS
                        refine .inr ⟨Expr.apps branch (.lit .unit :: fields), ?_⟩
                        refine Eval.Step.const (c := .elim type)
                          (args := hd :: (tl ++ [argument])) ?_ ?_ ?_
                        · simpa using Expr.spine_app_spine hspine
                        · intro z hz
                          rcases List.mem_cons.mp hz with rfl | hz
                          · exact hvals z (by simp)
                          · rcases List.mem_append.mp hz with h | h
                            · exact hvals z (by simp [h])
                            · simp only [List.mem_singleton] at h
                              subst h
                              exact argumentValue
                        · simpa using hreduce
        · exact .inr ⟨_, .appArgument functionValue step⟩
      · exact .inr ⟨_, .appFunction step⟩
  | letIn hwf hrhs hbody ihRhs ihBody =>
      rcases ihRhs _ (Nat.le_add_right _ _) _ (Scheme.skolemize_instance _ _) empty with
        rhsValue | ⟨rhs', rhsStep⟩
      · exact .inr ⟨_, .letValue rhsValue⟩
      · exact .inr ⟨_, .letRhs rhsStep⟩
  | fix => exact .inr ⟨_, .fixUnfold⟩

/-- Proof: induction; canonical forms of values at arrow types (a lambda, a
primitive operator possibly applied to one literal, or a partial constant
spine) and at data types (a saturated constructor spine). -/
theorem progress (typing : RuntimeTyping sig k [] expr ty) (exhaustive : Exhaustive sig expr) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  exact progress_empty typing rfl

/-- Every instance of a monomorphic scheme is its body. -/
private theorem mono_instance_eq {V : Type} {ty : Ty V} {k : Nat} {body : Ty V}
    (hinst : (Scheme.mono body).Instance k ty) : ty = body := by
  obtain ⟨args, hlen, _, heq⟩ := hinst
  have hargsNil : args = [] := by simpa [Scheme.mono] using hlen
  subst hargsNil
  simpa [Scheme.mono, Scheme.inst, Ty.instantiate_nil] using heq.symm

/-- Proof: induction on the step. `beta`, `fixUnfold`: `subst` with
`inner := []` and `mono_depth`; `letValue`: `subst` with the `letIn` premise;
`const`: the eliminator's scheme types the chosen branch at the scrutinee's
field types (a lemma about typing `Expr.apps` spines helps). -/
theorem preservation (typing : RuntimeTyping sig k ctx expr ty)
    (step : Eval.Step expr next) :
    RuntimeTyping sig k ctx next ty := by
  induction step generalizing k ctx ty with
  | beta argumentValue =>
      cases typing with
      | app functionTyping argumentTyping =>
          cases functionTyping with
          | lambda paramWF bodyTyping =>
              exact subst (inner := []) bodyTyping (fun k' le ty' hinst => by
                rw [mono_instance_eq hinst]
                exact mono_depth argumentTyping le)
  | appFunction functionStep functionIH =>
      cases typing with
      | app functionTyping argumentTyping =>
          exact .app (functionIH functionTyping) argumentTyping
  | appArgument functionValue argumentStep argumentIH =>
      cases typing with
      | app functionTyping argumentTyping =>
          exact .app functionTyping (argumentIH argumentTyping)
  | primOp hreduce =>
      cases typing with
      | app functionTyping argumentTyping =>
          cases functionTyping with
          | app operatorTyping leftTyping =>
              cases operatorTyping with
              | primOp hop =>
                  cases leftTyping
                  cases argumentTyping
                  exact primOp_eval_typing hop rfl rfl hreduce
  | letRhs rhsStep rhsIH =>
      cases typing with
      | letIn hwf hrhs hbody =>
          exact .letIn hwf (fun k' le ty' hinst => rhsIH (hrhs k' le ty' hinst)) hbody
  | letValue rhsValue =>
      cases typing with
      | letIn hwf hrhs hbody =>
          exact subst (inner := []) hbody hrhs
  | fixUnfold =>
      cases typing with
      | fix selfWF bodyTyping =>
          exact subst (inner := []) bodyTyping (fun k' le ty' hinst => by
            rw [mono_instance_eq hinst]
            exact mono_depth (.fix selfWF bodyTyping) le)
  | const hspine hvals hreduce =>
      expose_names
      have hexpr : Expr.apps (.const c) args = Expr.app function argument := by
        have h := Expr.apps_spine (Expr.app function argument)
        rw [hspine] at h
        exact h
      have typing' : RuntimeTyping sig k ctx (Expr.apps (.const c) args) ty := by
        rw [hexpr]
        exact typing
      cases c with
      | ctor type ctor =>
          simp [Eval.reduceConst] at hreduce
      | elim type =>
          obtain ⟨decl, instArgs, _, hdecl, hilen, _, hinstEq, hforall⟩ :=
            elim_spine_decomp typing'
          cases args with
          | nil => simp [Eval.reduceConst] at hreduce
          | cons scrutinee branches =>
              have hbranchLen : branches.length = decl.ctors.length := by
                by_contra hne
                simp [Eval.reduceConst, hdecl, hne] at hreduce
              obtain ⟨ctor, fieldTys, fields, branch, hty, hexprS, hctors, hbranch,
                hflen, hfieldWF, hfieldTypings, hbranchTyping⟩ :=
                elim_spine_saturated hdecl hilen hbranchLen hinstEq hforall
                  (hvals scrutinee (by simp))
              rw [reduceConst_elim hdecl hbranchLen hctors hflen hbranch hexprS] at hreduce
              have hargsForall : List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t)
                  (.lit .unit :: fields)
                  (.prim .unit :: fieldTys.map (fun ft => ft.instantiate instArgs)) :=
                .cons .lit (forall₂_map_of_forall₂ hfieldTypings)
              have hresultTyping := typing_apps_intro hbranchTyping hargsForall
              have hres : result = Expr.apps branch (.lit .unit :: fields) := by
                simpa using hreduce.symm
              rw [hres, hty]
              exact hresultTyping

end RuntimeTyping

end EPL
