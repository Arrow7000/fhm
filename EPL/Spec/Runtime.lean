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
  | lit | primOp | ctor | var | lambda | letIn | fix | «match» => rfl

private theorem Expr.spine_app_spine {A : Type} {f a h : Expr A} {args : List (Expr A)}
    (hs : f.spine = (h, args)) :
    (Expr.app f a).spine = (h, args ++ [a]) := by
  simp only [Expr.spine, hs]

/-- If a constructor ref occurs among a branch list's patterns, `findBranch`
finds a branch. -/
private theorem Expr.findBranch_eq_some_of_mem {A : Type} {ref : CtorRef} :
    ∀ {branches : List (Pattern × Expr A)}, ref ∈ branches.map (·.1.ctor) →
      ∃ body, Expr.findBranch ref branches = some body := by
  intro branches
  induction branches with
  | nil => intro h; simp at h
  | cons branch rest ih =>
      intro h
      obtain ⟨pattern, body⟩ := branch
      by_cases hpat : pattern.ctor = ref
      · exact ⟨body, by simp [Expr.findBranch, hpat]⟩
      · have hmem : ref ∈ rest.map (·.1.ctor) := by
          simp only [List.map_cons, List.mem_cons] at h
          rcases h with h | h
          · exact absurd h.symm hpat
          · exact h
        obtain ⟨found, hfound⟩ := ih hmem
        exact ⟨found, by simpa [Expr.findBranch, hpat] using hfound⟩

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

/-- A constructor-spine type whose codomain is a data type cannot be reached by
a shorter arrow spine. -/
private theorem Ty.arrows_length_le_of_not_arrow {V : Type} {as bs : List (Ty V)} {s t : Ty V}
    (h : Ty.arrows as s = Ty.arrows bs t) (hs : ∀ u v, s ≠ .arrow u v) :
    bs.length ≤ as.length := by
  induction as generalizing bs with
  | nil =>
      cases bs with
      | nil => simp
      | cons b bs => exact absurd h (hs b _)
  | cons a as ih =>
      cases bs with
      | nil => simp
      | cons b bs =>
          change Ty.arrow a (Ty.arrows as s) = Ty.arrow b (Ty.arrows bs t) at h
          injection h with _ htail
          simpa using ih htail

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

/-- `take` of the first `n` entries of a list, written with `getD` defaults. -/
private theorem Ty.getD_range_take {V : Type} (args : List (Ty V)) {n : Nat}
    (hlen : n ≤ args.length) :
    (List.range n).map (fun i => args.getD i (.bvar i)) = args.take n := by
  apply List.ext_getElem
  · simp [hlen, List.length_take]
  · intro i hi hi'
    have he : (List.take n args).length = n := by simp [List.length_take, hlen]
    have hai : i < args.length := by omega
    have htake : (args.take n)[i] = args[i] :=
      List.getElem_take (xs := args) (j := n) (i := i) (h := by rw [he]; omega)
    simp only [List.getElem_map, List.getElem_range]
    rw [htake, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hai, Option.getD_some]

/-- A list of types recovered from `getD` at every index, with arbitrary defaults. -/
private theorem Ty.getD_range_self {V : Type} (args : List (Ty V)) (d : Nat → Ty V) :
    (List.range args.length).map (fun i => args.getD i (d i)) = args := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    simp only [List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi),
      Option.getD_some]

/-- A type-scope check passes to the arguments of a type application spine. -/
private theorem Ty.apps_scoped_inv {V : Type} {head : Ty V} {args : List (Ty V)}
    {r b : Nat} (h : (Ty.apps head args).Scoped r b) :
    head.Scoped r b ∧ ∀ a ∈ args, a.Scoped r b := by
  induction args generalizing head with
  | nil => exact ⟨h, by simp⟩
  | cons a as ih =>
      obtain ⟨⟨hhead, ha⟩, hargs⟩ := ih h
      exact ⟨hhead, fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hargs x hx⟩

/-- A rigid substitution only needs to agree below the depth of a well-formed type. -/
private theorem Ty.substRigids_congr {V : Type} {ty : Ty V} {f g : Nat → Ty V} {k : Nat}
    (wf : ty.WF k) (agree : ∀ l < k, f l = g l) :
    ty.substRigids f = ty.substRigids g :=
  Ty.subst_congr wf (fun _ _ => rfl) agree (fun _ _ => rfl)

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

/-- The codomain of a scoped arrow type is scoped. -/
private theorem Ty.arrows_scoped_codomain {V : Type} {domains : List (Ty V)} {codomain : Ty V}
    {r b : Nat} (h : (Ty.arrows domains codomain).Scoped r b) : codomain.Scoped r b := by
  induction domains with
  | nil => exact h
  | cons d ds ih =>
      change Ty.Scoped r b (Ty.arrow d (Ty.arrows ds codomain)) at h
      exact ih h.2

/-- Every domain of a scoped arrow type is scoped. -/
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

/-- A type with no rigid variables is unchanged by a rigid substitution. -/
private theorem Ty.substRigids_eq_self {V : Type} {ty : Ty V} {f : Nat → Ty V} {binders : Nat}
    (wf : ty.Scoped 0 binders) : ty.substRigids f = ty := by
  show ty.subst ⟨.bvar, f, .var⟩ = ty
  have hc : ty.subst ⟨.bvar, f, .var⟩ = ty.subst Ty.Subst.id :=
    Ty.subst_congr wf (fun _ _ => rfl) (fun l hl => absurd hl (Nat.not_lt_zero l))
      (fun _ _ => rfl)
  rw [hc, Ty.subst_id]

/-- The field types of a closed constructor scheme mention only the
declaration's parameters. -/
private theorem ctorScheme_fields_scoped {decl : DataDecl} {type : Nat} {ctor : CtorDecl}
    (h : (decl.ctorScheme type ctor).WF 0) :
    ∀ ft ∈ ctor.fields, ft.Scoped 0 (decl.params + ctor.existentials) := by
  intro ft hft
  exact Ty.arrows_scoped_inv h ft hft

/-- A declaration's self type is scoped by its own parameters. -/
private theorem DataDecl.selfTy_scoped {decl : DataDecl} (type : Nat) :
    (decl.selfTy type).Scoped rigids decl.params := by
  unfold DataDecl.selfTy
  refine Ty.apps_scoped trivial ?_
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  simp only [List.mem_range] at hi
  exact hi

theorem DataDecl.WF.ctorScheme_wf {decl : DataDecl} (wf : decl.WF) {ctor : CtorDecl}
    (mem : ctor ∈ decl.ctors) (type : Nat) : (decl.ctorScheme type ctor).WF 0 := by
  show (Ty.arrows ctor.fields (decl.selfTy type)).Scoped 0 (decl.params + ctor.existentials)
  refine Ty.arrows_scoped ?_ ?_
  · intro field hfield
    exact wf ctor mem field hfield
  · exact Ty.Scoped.mono (DataDecl.selfTy_scoped (rigids := 0) type)
      (Nat.zero_le _) (Nat.le_add_right _ _)

/-! ## Signature lemmas -/

private theorem Signature.decl?_eq_some {sig : Signature} {type : Nat} {decl : DataDecl}
    (found : sig.decl? type = some decl) : sig[type]? = some decl ∧ decl.WF := by
  cases h : sig[type]? with
  | none => simp [Signature.decl?, h] at found
  | some d =>
      by_cases hwf : d.WF
      · have hdecl : sig.decl? type = some d := by simp [Signature.decl?, h, hwf]
        rw [hdecl] at found
        have hd : d = decl := Option.some.inj found
        exact ⟨by rw [hd], hd ▸ hwf⟩
      · have hnone : sig.decl? type = none := by simp [Signature.decl?, h, hwf]
        rw [hnone] at found
        exact absurd found (by simp)

private theorem Signature.decl?_wf {sig : Signature} {type : Nat} {decl : DataDecl}
    (found : sig.decl? type = some decl) : decl.WF :=
  (Signature.decl?_eq_some found).2

private theorem Signature.decl?_some {sig : Signature} {type : Nat} {decl : DataDecl}
    (found : sig.decl? type = some decl) : sig[type]? = some decl :=
  (Signature.decl?_eq_some found).1

private theorem ctorScheme_some {sig : Signature} {ref : CtorRef} {scheme : Scheme Empty}
    (found : sig.ctorScheme ref = some scheme) :
    ∃ (decl : DataDecl) (ctor : CtorDecl),
      sig.decl? ref.type = some decl ∧ decl.ctors[ref.index]? = some ctor ∧
        scheme = decl.ctorScheme ref.type ctor := by
  cases hdecl : sig.decl? ref.type with
  | none => simp [Signature.ctorScheme, hdecl] at found
  | some decl =>
      cases hfields : decl.ctors[ref.index]? with
      | none => simp [Signature.ctorScheme, hdecl, hfields] at found
      | some fields =>
          have hsome : sig.ctorScheme ref = some (decl.ctorScheme ref.type fields) := by
            simp [Signature.ctorScheme, hdecl, hfields]
          rw [hsome] at found
          exact ⟨decl, fields, rfl, hfields, (Option.some.inj found).symm⟩

/-- Every constructor scheme a signature assigns is closed. -/
theorem Signature.ctorScheme_wf {sig : Signature} {ref : CtorRef} {scheme : Scheme Empty}
    (found : sig.ctorScheme ref = some scheme) : scheme.WF 0 := by
  obtain ⟨decl, fields, hdecl, hfields, rfl⟩ := ctorScheme_some found
  exact DataDecl.WF.ctorScheme_wf (Signature.decl?_wf hdecl) (List.mem_of_getElem? hfields)
    ref.type

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
  sorry

/-- Proof: induction; the `letIn` premise already quantifies over all larger
depths. -/
theorem mono_depth (typing : RuntimeTyping sig k ctx expr ty) (le : k ≤ k') :
    RuntimeTyping sig k' ctx expr ty := by
  sorry

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
  sorry

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
  sorry

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

/-- An `instantiate` after a rigid substitution is the rigid-substituted
`instantiate`, provided the type mentions only binders. -/
private theorem Ty.instantiate_substRigids {V : Type} {ty : Ty V} {args : List (Ty V)}
    {f : Nat → Ty V} (wf : ty.Scoped 0 args.length) :
    (ty.instantiate args).substRigids f =
      ty.instantiate (args.map (·.substRigids f)) := by
  have h := Scheme.inst_substRigids (scheme := ⟨args.length, ty⟩) args (k := 0) wf
    (f := f) (rigids := 0) (fun l hl => absurd hl (Nat.not_lt_zero l))
  simp only [Scheme.inst, Scheme.substRigids] at h
  rw [Ty.substRigids_eq_self wf] at h
  exact h

private theorem Ty.apps_substRigids {V : Type} (head : Ty V) (args : List (Ty V))
    (f : Nat → Ty V) :
    (Ty.apps head args).substRigids f =
      Ty.apps (head.substRigids f) (args.map (·.substRigids f)) := by
  induction args generalizing head with
  | nil => rfl
  | cons a as ih =>
      change (Ty.apps (Ty.app head a) as).substRigids f =
        Ty.apps ((head.substRigids f).app (a.substRigids f)) (as.map (·.substRigids f))
      rw [ih (Ty.app head a)]
      rfl

private theorem Ty.arrows_substRigids {V : Type} (domains : List (Ty V)) (codomain : Ty V)
    (f : Nat → Ty V) :
    (Ty.arrows domains codomain).substRigids f =
      Ty.arrows (domains.map (·.substRigids f)) (codomain.substRigids f) := by
  induction domains with
  | nil => rfl
  | cons d ds ih =>
      change Ty.substRigids f (Ty.arrow d (Ty.arrows ds codomain)) =
        Ty.arrow (Ty.substRigids f d)
          (Ty.arrows (ds.map (·.substRigids f)) (Ty.substRigids f codomain))
      rw [show Ty.substRigids f (Ty.arrow d (Ty.arrows ds codomain)) =
          Ty.arrow (Ty.substRigids f d) (Ty.substRigids f (Ty.arrows ds codomain)) from rfl]
      rw [ih]

/-- A member of a rigid block is well formed at the block's depth. -/
private theorem rigidBlock_mem_wf {a : SemTy} {k n : Nat} (h : a ∈ rigidBlock k n) :
    a.WF (k + n) := by
  simp only [rigidBlock, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  show k + i < k + n
  omega

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
  sorry

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

private theorem hasBool_ctorScheme {sig : Signature} (hsig : sig.HasBool)
    (c : Nat) (hc : c < 2) :
    sig.ctorScheme ⟨0, c⟩ = some (Scheme.mono Ty.bool) := by
  have h0 : sig[0]? = some boolDecl := hsig
  have hwf : boolDecl.WF := by decide
  have hdecl : sig.decl? 0 = some boolDecl := by
    simp only [Signature.decl?, h0]
    show (if boolDecl.WF then some boolDecl else none) = some boolDecl
    rw [if_pos hwf]
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases hc' with rfl | rfl
  · show (sig.decl? 0 >>= fun decl => decl.ctors[0]? >>= fun ctor =>
      some (decl.ctorScheme 0 ctor)) = some (Scheme.mono Ty.bool)
    rw [hdecl]
    rfl
  · show (sig.decl? 0 >>= fun decl => decl.ctors[1]? >>= fun ctor =>
      some (decl.ctorScheme 0 ctor)) = some (Scheme.mono Ty.bool)
    rw [hdecl]
    rfl

private theorem hasBool_boolValue_typing {sig : Signature} (hsig : sig.HasBool) (b : Bool)
    {k : Nat} {ctx : Ctx Empty} :
    RuntimeTyping sig k ctx (Eval.boolValue b) Ty.bool := by
  exact RuntimeTyping.ctor (hasBool_ctorScheme hsig (if b then 0 else 1)
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

private theorem ctor_spine_inv {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {ref : CtorRef} {args : List RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k ctx (Expr.apps (.ctor ref) args) ty) :
    ∃ (scheme : Scheme Empty) (argTys : List SemTy),
      sig.ctorScheme ref = some scheme ∧
      scheme.Instance k (Ty.arrows argTys ty) ∧
      List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) args argTys := by
  obtain ⟨argTys, hforall, hhead⟩ := typing_spine_inv typing
  cases hhead with
  | ctor hscheme hinst =>
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

/-- A constructor scheme's instance: `args` covers the data type's parameters
and then the constructor's own variables; only the former appear in the result. -/
private theorem DataDecl.ctorScheme_inst {decl : DataDecl} {type : Nat} {ctor : CtorDecl}
    {args : List SemTy} (hlen : args.length = decl.params + ctor.existentials) :
    (decl.ctorScheme type ctor).inst args =
      Ty.arrows (ctor.fields.map (fun ft => ft.instantiate args))
        (Ty.apps (.con type) (args.take decl.params)) := by
  unfold DataDecl.ctorScheme Scheme.inst
  rw [Ty.instantiate_arrows]
  congr 1
  unfold DataDecl.selfTy
  rw [Ty.instantiate_apps, List.map_map,
    ← Ty.getD_range_take args (by omega : decl.params ≤ args.length)]
  congr 1

private theorem forall₂_map_of_forall₂ {fields : List SemTy} {args : List RuntimeExpr}
    {f : SemTy → SemTy} {R : RuntimeExpr → SemTy → Prop}
    (h : List.Forall₂ (fun e ft => R e (f ft)) args fields) :
    List.Forall₂ R args (fields.map f) := by
  induction fields generalizing args with
  | nil => cases h; exact .nil
  | cons ft fts ih =>
      cases h with
      | cons hhead htail => exact .cons hhead (ih htail)

/-- Decompose the typing of a constructor spine into its scheme instance. -/
private theorem ctor_spine_decomp {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {ref : CtorRef} {args : List RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k ctx (Expr.apps (.ctor ref) args) ty) :
    ∃ (decl : DataDecl) (ctor : CtorDecl) (instArgs argTys : List SemTy),
      sig.decl? ref.type = some decl ∧
      decl.ctors[ref.index]? = some ctor ∧
      (decl.ctorScheme ref.type ctor).WF 0 ∧
      instArgs.length = decl.params + ctor.existentials ∧
      (∀ a ∈ instArgs, a.WF k) ∧
      Ty.arrows (ctor.fields.map (fun ft => ft.instantiate instArgs))
          (Ty.apps (.con ref.type) (instArgs.take decl.params)) = Ty.arrows argTys ty ∧
      List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) args argTys := by
  obtain ⟨scheme, argTys, hscheme, hinst, hforall⟩ := ctor_spine_inv typing
  obtain ⟨decl, ctor, hdecl, hctors, hschemeEq⟩ := ctorScheme_some hscheme
  subst hschemeEq
  obtain ⟨instArgs, hilen, hiwf, hinstEq⟩ := hinst
  have hilen' : instArgs.length = decl.params + ctor.existentials := by simpa using hilen
  rw [DataDecl.ctorScheme_inst hilen'] at hinstEq
  exact ⟨decl, ctor, instArgs, argTys, hdecl, hctors,
    DataDecl.WF.ctorScheme_wf (Signature.decl?_wf hdecl) (List.mem_of_getElem? hctors)
      ref.type,
    hilen', hiwf, hinstEq, hforall⟩

/-- A constructor spine's type is its data type followed by the arrows it is
still missing: `rest` is the list of field types not yet applied. -/
private theorem ctor_spine_shape {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {ref : CtorRef} {args : List RuntimeExpr} {ty : SemTy}
    (typing : RuntimeTyping sig k ctx (Expr.apps (.ctor ref) args) ty) :
    ∃ (decl : DataDecl) (ctor : CtorDecl) (instArgs rest argTys : List SemTy),
      sig.decl? ref.type = some decl ∧
      decl.ctors[ref.index]? = some ctor ∧
      instArgs.length = decl.params + ctor.existentials ∧
      (∀ a ∈ instArgs, a.WF k) ∧
      args.length + rest.length = ctor.fields.length ∧
      ty = Ty.arrows rest (Ty.apps (.con ref.type) (instArgs.take decl.params)) ∧
      ctor.fields.map (fun ft => ft.instantiate instArgs) = argTys ++ rest ∧
      List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) args argTys := by
  obtain ⟨decl, ctor, instArgs, argTys, hdecl, hctors, _hwf0, hilen, hiwf, hinstEq,
    hforall⟩ := ctor_spine_decomp typing
  have hlenLe : argTys.length ≤ (ctor.fields.map fun ft => ft.instantiate instArgs).length :=
    Ty.arrows_length_le_of_not_arrow hinstEq (fun u v => Ty.apps_con_ne_arrow)
  obtain ⟨rest, hmap, hty⟩ := Ty.arrows_eq_arrows_append hinstEq.symm hlenLe
  have hlenSum : args.length + rest.length = ctor.fields.length := by
    have hlen := congrArg List.length hmap
    simp only [List.length_map, List.length_append] at hlen
    have hargLen := (List.Forall₂.length_eq hforall).symm
    omega
  exact ⟨decl, ctor, instArgs, rest, argTys, hdecl, hctors, hilen, hiwf, hlenSum, hty,
    hmap, hforall⟩

/-- A constructor spine typed at a data type is applied to exactly its fields,
which have the field types instantiated at the type's arguments and some
well-formed `hidden` types for the constructor's own variables. -/
private theorem ctor_spine_value_decomp {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {ref : CtorRef} {fields : List RuntimeExpr} {t : Nat} {params : List SemTy}
    (typing : RuntimeTyping sig k ctx (Expr.apps (.ctor ref) fields)
      (Ty.apps (.con t) params)) :
    ∃ (decl : DataDecl) (ctor : CtorDecl) (hidden : List SemTy),
      ref.type = t ∧ sig.decl? t = some decl ∧ decl.ctors[ref.index]? = some ctor ∧
      hidden.length = ctor.existentials ∧ (∀ h ∈ hidden, h.WF k) ∧
      (∀ ft ∈ ctor.fields, ft.Scoped 0 (decl.params + ctor.existentials)) ∧
      List.Forall₂ (fun e ft => RuntimeTyping sig k ctx e (ft.instantiate (params ++ hidden)))
        fields ctor.fields := by
  obtain ⟨decl, ctor, instArgs, rest, argTys, hdecl, hctors, hilen, hiwf, _hlenSum, hty,
    hmap, hforall⟩ := ctor_spine_shape typing
  cases rest with
  | cons c cs => exact absurd hty Ty.apps_con_ne_arrow
  | nil =>
      have hty' : Ty.apps (.con t) params = Ty.apps (.con ref.type) (instArgs.take decl.params) := by
        simpa using hty
      obtain ⟨htEq, hparamsEq⟩ := Ty.apps_con_inj hty'
      have hdecl' : sig.decl? t = some decl := by
        rw [htEq]
        exact hdecl
      have hwf : decl.WF := Signature.decl?_wf hdecl'
      have hfieldWF : ∀ ft ∈ ctor.fields, ft.Scoped 0 (decl.params + ctor.existentials) :=
        ctorScheme_fields_scoped
          (DataDecl.WF.ctorScheme_wf hwf (List.mem_of_getElem? hctors) t)
      have hmapNil : ctor.fields.map (fun ft => ft.instantiate instArgs) = argTys := by
        simpa using hmap
      have hforall' : List.Forall₂ (fun e t => RuntimeTyping sig k ctx e t) fields
          (ctor.fields.map fun ft => ft.instantiate instArgs) := by
        rw [hmapNil]
        exact hforall
      have hinst := forall₂_map_inst hforall'
      have hhiddenLen : (instArgs.drop decl.params).length = ctor.existentials := by
        rw [List.length_drop, hilen]
        omega
      have hhiddenWF : ∀ h ∈ instArgs.drop decl.params, h.WF k :=
        fun h hh => hiwf h (List.mem_of_mem_drop hh)
      have hsplit : params ++ instArgs.drop decl.params = instArgs := by
        rw [hparamsEq, List.take_append_drop]
      have hfin : List.Forall₂
          (fun e ft =>
            RuntimeTyping sig k ctx e (ft.instantiate (params ++ instArgs.drop decl.params)))
          fields ctor.fields := by
        refine List.Forall₂.imp (fun e ft h => ?_) hinst
        rw [hsplit]
        exact h
      exact ⟨decl, ctor, instArgs.drop decl.params, htEq.symm, hdecl', hctors, hhiddenLen,
        hhiddenWF, hfieldWF, hfin⟩

/-- A value typed at a primitive type is a literal of that type. -/
private theorem prim_value_canonical {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {expr : RuntimeExpr} {p : PrimTy}
    (value : Eval.Value expr)
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
  | ctor hspine _ =>
      expose_names
      have hexpr : expr = Expr.apps (.ctor ref) fields := by
        have h := Expr.apps_spine expr
        rw [hspine] at h
        exact h.symm
      have typing' : RuntimeTyping sig k ctx (Expr.apps (.ctor ref) fields) (.prim p) := by
        rw [← hexpr]
        exact typing
      obtain ⟨decl, fieldTys, instArgs, rest, argTys, hdecl, hctors, hilen, _hiwf, _hlenSum,
        hty, _hmap, _hforall⟩ := ctor_spine_shape typing'
      cases rest with
      | nil => exact absurd hty.symm Ty.apps_con_ne_prim
      | cons c cs => exact absurd hty.symm Ty.arrow_ne_prim

/-- A value typed at a declared data type is a saturated constructor spine,
built with some well-formed `hidden` types for the constructor's own variables. -/
private theorem data_value_canonical {sig : Signature} {k : Nat} {ctx : Ctx Empty}
    {expr : RuntimeExpr} {t : Nat} {params : List SemTy}
    (value : Eval.Value expr)
    (typing : RuntimeTyping sig k ctx expr (Ty.apps (.con t) params)) :
    ∃ (decl : DataDecl) (ref : CtorRef) (ctor : CtorDecl) (hidden : List SemTy)
      (fields : List RuntimeExpr),
      sig.decl? t = some decl ∧ ref.type = t ∧
      decl.ctors[ref.index]? = some ctor ∧
      expr = Expr.apps (.ctor ref) fields ∧
      fields.length = ctor.fields.length ∧
      hidden.length = ctor.existentials ∧ (∀ h ∈ hidden, h.WF k) ∧
      (∀ ft ∈ ctor.fields, ft.Scoped 0 (decl.params + ctor.existentials)) ∧
      List.Forall₂ (fun e ft => RuntimeTyping sig k ctx e (ft.instantiate (params ++ hidden)))
        fields ctor.fields := by
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
  | ctor hspine _ =>
      expose_names
      have hexpr : expr = Expr.apps (.ctor ref) fields := by
        have h := Expr.apps_spine expr
        rw [hspine] at h
        exact h.symm
      have typing' : RuntimeTyping sig k ctx (Expr.apps (.ctor ref) fields)
          (Ty.apps (.con t) params) := by
        rw [← hexpr]
        exact typing
      obtain ⟨decl, ctor, hidden, hrefTy, hdecl, hctors, hhiddenLen, hhiddenWF,
        hfieldWF, hfieldTypings⟩ := ctor_spine_value_decomp typing'
      exact ⟨decl, ref, ctor, hidden, fields, hdecl, hrefTy, hctors, hexpr,
        List.Forall₂.length_eq hfieldTypings, hhiddenLen, hhiddenWF, hfieldWF,
        hfieldTypings⟩

/-- `progress`, with the empty context as an equation so that the induction
goes through. -/
private theorem progress_empty (typing : RuntimeTyping sig k ctx expr ty) (empty : ctx = [])
    (exhaustive : Exhaustive sig expr) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  sorry

/-- Proof: induction; canonical forms of values at arrow types (a lambda, a
primitive operator possibly applied to one literal, or a constructor spine
short of its fields) and at data types (a constructor spine with all its
fields, whose constructor the exhaustive match has a branch for). -/
theorem progress (typing : RuntimeTyping sig k [] expr ty) (exhaustive : Exhaustive sig expr) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  exact progress_empty typing rfl exhaustive

/-- Every instance of a monomorphic scheme is its body. -/
private theorem mono_instance_eq {V : Type} {ty : Ty V} {k : Nat} {body : Ty V}
    (hinst : (Scheme.mono body).Instance k ty) : ty = body := by
  obtain ⟨args, hlen, _, heq⟩ := hinst
  have hargsNil : args = [] := by simpa [Scheme.mono] using hlen
  subst hargsNil
  simpa [Scheme.mono, Scheme.inst, Ty.instantiate_nil] using heq.symm

/-- Proof: induction on the step. `beta`, `fixUnfold`: `subst` with
`inner := []` and `mono_depth`; `letValue`: `subst` with the `letIn` premise;
`matchCtor`: the scrutinee's constructor scheme gives its fields the types
the branch expects (a lemma about typing `Expr.apps` spines helps). -/
theorem preservation (typing : RuntimeTyping sig k ctx expr ty)
    (step : Eval.Step expr next) :
    RuntimeTyping sig k ctx next ty := by
  sorry

end RuntimeTyping

end EPL
