import EPL.Runtime

namespace EPL

namespace Expr

private theorem apps_append (head : Expr T) (first second : List (Expr T)) :
    Expr.apps head (first ++ second) = Expr.apps (Expr.apps head first) second := by
  induction first generalizing head with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, Expr.apps, List.foldl_cons]
      exact ih (.app head a)

private theorem spine_apps (head : Expr T) (args : List (Expr T)) :
    (Expr.apps head args).spine = (head.spine.1, head.spine.2 ++ args) := by
  induction args generalizing head with
  | nil =>
      change head.spine = (head.spine.1, head.spine.2 ++ [])
      cases head.spine
      simp
  | cons a as ih =>
      have step : Expr.apps head (a :: as) = Expr.apps (.app head a) as := rfl
      rw [step, ih]
      simp [Expr.spine, List.append_assoc]

private theorem apps_spine (expr : Expr T) :
    Expr.apps expr.spine.1 expr.spine.2 = expr := by
  induction expr with
  | primLit => rfl
  | primOp => rfl
  | var => rfl
  | lambda => rfl
  | app f a ihf =>
      change Expr.apps f.spine.1 (f.spine.2 ++ [a]) = Expr.app f a
      rw [Expr.apps_append, ihf]
      rfl
  | letIn => rfl
  | fix => rfl
  | const => rfl

private theorem spine_app_spine {f a : Expr T} {h : Expr T} {args : List (Expr T)}
    (hs : f.spine = (h, args)) :
    (Expr.app f a).spine = (h, args ++ [a]) := by
  simp only [Expr.spine, hs]

end Expr

namespace Ty

private theorem arrows_cons (d : Ty) (ds : List Ty) (c : Ty) :
    Ty.arrows (d :: ds) c = .arrow d (Ty.arrows ds c) := rfl

private theorem arrows_nil (c : Ty) : Ty.arrows [] c = c := rfl

private theorem apps_cons (head : Ty) (a : Ty) (as : List Ty) :
    Ty.apps head (a :: as) = Ty.apps (.app head a) as := rfl

private theorem openWith_arrows (args domains : List Ty) (codomain : Ty) :
    Ty.openWith args (Ty.arrows domains codomain) =
      Ty.arrows (domains.map (fun d => Ty.openWith args d)) (Ty.openWith args codomain) := by
  induction domains with
  | nil => rfl
  | cons d ds ih =>
      change Ty.arrow (Ty.openWith args d) (Ty.openWith args (Ty.arrows ds codomain)) =
        Ty.arrow (Ty.openWith args d)
          (Ty.arrows (ds.map (fun d => Ty.openWith args d)) (Ty.openWith args codomain))
      rw [ih]

private theorem openWith_apps (args : List Ty) (head : Ty) (rest : List Ty) :
    Ty.openWith args (Ty.apps head rest) =
      Ty.apps (Ty.openWith args head) (rest.map (fun t => Ty.openWith args t)) := by
  induction rest generalizing head with
  | nil => rfl
  | cons a as ih =>
      change Ty.openWith args (Ty.apps (.app head a) as) =
        Ty.apps (.app (Ty.openWith args head) (Ty.openWith args a))
          (as.map (fun t => Ty.openWith args t))
      rw [ih (.app head a)]
      rfl

private theorem openWith_append_of_scoped {ty : Ty} {n : Nat}
    (h : ty.Scoped 0 n) {args extra : List Ty} (hlen : args.length = n) :
    ty.openWith (args ++ extra) = ty.openWith args := by
  induction h with
  | prim => rfl
  | arrow _ _ ihd ihc => simp [Ty.openWith, ihd, ihc]
  | bvar hi =>
      simp only [Ty.openWith]
      rw [List.getElem?_append_left (by omega)]
  | rigid => rfl
  | mvar => rfl
  | con => rfl
  | app _ _ ihf iha => simp [Ty.openWith, ihf, iha]

private theorem arrows_scoped_inv {domains : List Ty} {codomain : Ty} {rc bc : Nat}
    (h : (Ty.arrows domains codomain).Scoped rc bc) :
    ∀ d ∈ domains, d.Scoped rc bc := by
  induction domains with
  | nil => simp
  | cons d ds ih =>
      intro x hx
      change Ty.Scoped rc bc (Ty.arrow d (Ty.arrows ds codomain)) at h
      cases h with
      | arrow hd hr =>
          rcases List.mem_cons.mp hx with rfl | hmem
          · exact hd
          · exact ih hr x hmem

private theorem arrows_eq_arrows_append {as bs : List Ty} {s t : Ty}
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

private theorem arrows_cancel {as bs : List Ty} {s t : Ty}
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

private theorem apps_append_singleton (head : Ty) (xs : List Ty) (x : Ty) :
    Ty.apps head (xs ++ [x]) = .app (Ty.apps head xs) x := by
  induction xs generalizing head with
  | nil => rfl
  | cons a as ih =>
      change Ty.apps (.app head a) (as ++ [x]) =
        .app (Ty.apps (.app head a) as) x
      exact ih (.app head a)

private theorem list_reverse_induction {α : Type} {motive : List α → Prop}
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

private theorem apps_con_inj {t t' : Nat} {as bs : List Ty}
    (h : Ty.apps (.con t) as = Ty.apps (.con t') bs) : t = t' ∧ as = bs := by
  have main : ∀ (as : List Ty) (bs : List Ty),
      Ty.apps (.con t) as = Ty.apps (.con t') bs → t = t' ∧ as = bs := by
    intro as
    refine Ty.list_reverse_induction (motive := fun as => ∀ bs,
      Ty.apps (.con t) as = Ty.apps (.con t') bs → t = t' ∧ as = bs) ?_ ?_ as
    · intro bs
      refine Ty.list_reverse_induction (motive := fun bs =>
        Ty.apps (.con t) [] = Ty.apps (.con t') bs → t = t' ∧ ([] : List Ty) = bs) ?_ ?_ bs
      · intro h
        simpa [Ty.apps] using h
      · intro ys y ih2 h
        rw [Ty.apps_append_singleton] at h
        cases h
    · intro xs x ih bs
      refine Ty.list_reverse_induction (motive := fun bs =>
        Ty.apps (.con t) (xs ++ [x]) = Ty.apps (.con t') bs →
          t = t' ∧ xs ++ [x] = bs) ?_ ?_ bs
      · intro h
        rw [Ty.apps_append_singleton] at h
        cases h
      · intro ys y ih2 h
        rw [Ty.apps_append_singleton, Ty.apps_append_singleton] at h
        injection h with hhead hlast
        obtain ⟨htt, hxs⟩ := ih ys hhead
        subst htt hxs hlast
        exact ⟨rfl, rfl⟩
  exact main as bs h

private theorem apps_con_ne_arrow {t : Nat} {params : List Ty} {a b : Ty} :
    Ty.apps (.con t) params ≠ .arrow a b := by
  induction params using Ty.list_reverse_induction with
  | nil => intro h; cases h
  | step xs x ih =>
      intro h
      rw [Ty.apps_append_singleton] at h
      cases h

private theorem apps_con_ne_prim {t : Nat} {params : List Ty} {p : PrimTy} :
    Ty.apps (.con t) params ≠ .prim p := by
  induction params using Ty.list_reverse_induction with
  | nil => intro h; cases h
  | step xs x ih =>
      intro h
      rw [Ty.apps_append_singleton] at h
      cases h

private theorem arrow_ne_prim {a b : Ty} {p : PrimTy} : Ty.arrow a b ≠ .prim p := by
  intro h; cases h

end Ty

private theorem bvar_openWith_append_singleton {n : Nat} {params : List Ty} {r : Ty}
    (hlen : params.length = n) :
    Ty.openWith (params ++ [r]) (Ty.bvar n) = r := by
  simp only [Ty.openWith]
  rw [List.getElem?_append_right (by omega)]
  simp [hlen]

namespace DataDecl

private theorem selfTy_openWith (decl : DataDecl) (type : Nat) (params extra : List Ty)
    (hlen : params.length = decl.paramCount) :
    Ty.openWith (params ++ extra) (decl.selfTy type) = Ty.apps (.con type) params := by
  unfold DataDecl.selfTy
  rw [Ty.openWith_apps]
  have hmap : (List.range decl.paramCount).map
      (fun i => (params ++ extra)[i]?.getD (Ty.bvar i)) = params := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_range]
      have hi' : i < params.length := by simpa [hlen] using hi
      have hget : (params ++ extra)[i]? = some params[i] := by
        rw [List.getElem?_append_left hi']
        exact List.getElem?_eq_getElem hi'
      simp [hget]
  congr 1
  simpa only [Ty.openWith, List.map_map, Function.comp_apply] using hmap

private theorem ctorScheme_openWith (decl : DataDecl) (type : Nat) (fields params : List Ty)
    (hlen : params.length = decl.paramCount) :
    (decl.ctorScheme type fields).openWith params =
      Ty.arrows (fields.map (fun ft => Ty.openWith params ft)) (Ty.apps (.con type) params) := by
  unfold DataDecl.ctorScheme
  simp only [PolyTy.openWith]
  rw [Ty.openWith_arrows]
  have hself : Ty.openWith params (decl.selfTy type) = Ty.apps (.con type) params := by
    have h := selfTy_openWith decl type params [] hlen
    simpa using h
  rw [hself]

private theorem elimScheme_openWith (decl : DataDecl) (type : Nat) {params : List Ty} {r : Ty}
    (hlen : params.length = decl.paramCount) :
    (decl.elimScheme type).openWith (params ++ [r]) =
      Ty.arrows
        ((Ty.apps (.con type) params) ::
          decl.ctors.map (fun fields =>
            .arrow (.prim .unit)
              (Ty.arrows (fields.map (fun ft => Ty.openWith (params ++ [r]) ft)) r)))
        r := by
  have hself : Ty.openWith (params ++ [r]) (decl.selfTy type) =
      Ty.apps (.con type) params := by
    have h := selfTy_openWith decl type params [r] hlen
    simpa using h
  have hbvar : Ty.openWith (params ++ [r]) (Ty.bvar decl.paramCount) = r :=
    bvar_openWith_append_singleton hlen
  unfold DataDecl.elimScheme
  simp only [PolyTy.openWith]
  change Ty.arrow (Ty.openWith (params ++ [r]) (decl.selfTy type))
      (Ty.openWith (params ++ [r])
        (Ty.arrows (decl.ctors.map (fun fields => branchTy fields (Ty.bvar decl.paramCount)))
          (Ty.bvar decl.paramCount))) =
    Ty.arrow (Ty.apps (.con type) params)
      (Ty.arrows (decl.ctors.map (fun fields =>
          Ty.arrow (.prim .unit)
            (Ty.arrows (fields.map (fun ft => Ty.openWith (params ++ [r]) ft)) r))) r)
  rw [hself, Ty.openWith_arrows, hbvar]
  congr 1
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro fields _
  change Ty.arrow (Ty.openWith (params ++ [r]) (.prim .unit))
      (Ty.openWith (params ++ [r]) (Ty.arrows fields (Ty.bvar decl.paramCount))) =
    Ty.arrow (.prim .unit) (Ty.arrows (fields.map (fun ft => Ty.openWith (params ++ [r]) ft)) r)
  rw [Ty.openWith_arrows, hbvar]
  rfl

end DataDecl

private theorem exists_append_singleton_of_length {α : Type} {n : Nat} :
    ∀ {xs : List α}, xs.length = n + 1 → ∃ ys x, xs = ys ++ [x] ∧ ys.length = n := by
  induction n with
  | zero =>
      intro xs h
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (by simpa using h)
      exact ⟨[], x, rfl, rfl⟩
  | succ n ih =>
      intro xs h
      cases xs with
      | nil => simp at h
      | cons x xs =>
          have hlen : xs.length = n + 1 := by simpa using h
          obtain ⟨ys, y, hys, hlenys⟩ := ih hlen
          exact ⟨x :: ys, y, by simp [hys], by simp [hlenys]⟩

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
          subst hx
          subst hy
          exact hhead
      | succ i =>
          simp only [List.getElem?_cons_succ] at hx hy
          exact ih hx hy

private theorem forall₂_map_of_forall₂ {fields : List Ty} {args : List RuntimeExpr}
    {f : Ty → Ty} {R : RuntimeExpr → Ty → Prop}
    (h : List.Forall₂ (fun e ft => R e (f ft)) args fields) :
    List.Forall₂ R args (fields.map f) := by
  induction fields generalizing args with
  | nil => cases h; exact .nil
  | cons ft fts ih =>
      cases h with
      | cons hhead htail => exact .cons hhead (ih htail)

namespace Signature

private theorem schemeOf_ctor_some {sig : Signature} {type ctor arity : Nat} {scheme : PolyTy}
    (h : sig.schemeOf (.ctor type ctor arity) = some scheme) :
    ∃ (decl : DataDecl) (fields : List Ty), sig[type]? = some decl ∧
      decl.ctors[ctor]? = some fields ∧ fields.length = arity ∧
      scheme = decl.ctorScheme type fields := by
  cases hdecl : sig[type]? with
  | none => simp [Signature.schemeOf, hdecl] at h
  | some decl =>
      cases hfields : decl.ctors[ctor]? with
      | none => simp [Signature.schemeOf, hdecl, hfields] at h
      | some fields =>
          by_cases hlen : fields.length = arity
          · have hsch : sig.schemeOf (.ctor type ctor arity) =
                some (decl.ctorScheme type fields) := by
              simp [Signature.schemeOf, hdecl, hfields, hlen]
            have heq : scheme = decl.ctorScheme type fields :=
              (Option.some.inj (hsch.symm.trans h)).symm
            exact ⟨decl, fields, rfl, hfields, hlen, heq⟩
          · simp [Signature.schemeOf, hdecl, hfields, hlen] at h

private theorem schemeOf_elim_some {sig : Signature} {type ctorCount : Nat} {scheme : PolyTy}
    (h : sig.schemeOf (.elim type ctorCount) = some scheme) :
    ∃ (decl : DataDecl), sig[type]? = some decl ∧ decl.ctors.length = ctorCount ∧
      scheme = decl.elimScheme type := by
  cases hdecl : sig[type]? with
  | none => simp [Signature.schemeOf, hdecl] at h
  | some decl =>
      by_cases hlen : decl.ctors.length = ctorCount
      · have hsch : sig.schemeOf (.elim type ctorCount) = some (decl.elimScheme type) := by
          simp [Signature.schemeOf, hdecl, hlen]
        have heq : scheme = decl.elimScheme type :=
          (Option.some.inj (hsch.symm.trans h)).symm
        exact ⟨decl, rfl, hlen, heq⟩
      · simp [Signature.schemeOf, hdecl, hlen] at h

end Signature

namespace RuntimeTyping

variable {sig : Signature} {r : Nat} {ctx : Ctx}

/-- A typed primitive operator has an arrow type. -/
private theorem primOp_ty_arrow {sig : Signature} {op : PrimOp} {ty : Ty}
    (hop : op.ty sig = some ty) : ∃ a b, ty = .arrow a b := by
  cases op with
  | intAdd =>
      exact ⟨_, _, by
        simp only [PrimOp.ty, Option.some.injEq] at hop
        exact hop.symm⟩
  | intSub =>
      exact ⟨_, _, by
        simp only [PrimOp.ty, Option.some.injEq] at hop
        exact hop.symm⟩
  | intLt =>
      by_cases hb : sig.HasBool
      · exact ⟨_, _, by
          simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
          exact hop.symm⟩
      · simp [PrimOp.ty, if_neg hb] at hop
  | charLt =>
      by_cases hb : sig.HasBool
      · exact ⟨_, _, by
          simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
          exact hop.symm⟩
      · simp [PrimOp.ty, if_neg hb] at hop

/-- The codomain of a typed primitive operator is itself an arrow. -/
private theorem primOp_ty_codomain_arrow {sig : Signature} {op : PrimOp} {a b : Ty}
    (hop : op.ty sig = some (.arrow a b)) : ∃ c d, b = .arrow c d := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      exact ⟨_, _, hop.2.symm⟩
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      exact ⟨_, _, hop.2.symm⟩
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq, Ty.arrow.injEq] at hop
        exact ⟨_, _, hop.2.symm⟩
      · simp [PrimOp.ty, if_neg hb] at hop
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq, Ty.arrow.injEq] at hop
        exact ⟨_, _, hop.2.symm⟩
      · simp [PrimOp.ty, if_neg hb] at hop

/-- The domain and codomain of a typed primitive operator are primitive types. -/
private theorem primOp_ty_domain {sig : Signature} {op : PrimOp} {α β ty : Ty}
    (hop : op.ty sig = some (.arrow α (.arrow β ty))) :
    ∃ p q, α = .prim p ∧ β = .prim q := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      obtain ⟨hα, hβ, _⟩ := hop
      exact ⟨.int, .int, hα.symm, hβ.symm⟩
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      obtain ⟨hα, hβ, _⟩ := hop
      exact ⟨.int, .int, hα.symm, hβ.symm⟩
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq, Ty.arrow.injEq] at hop
        obtain ⟨hα, hβ, _⟩ := hop
        exact ⟨.int, .int, hα.symm, hβ.symm⟩
      · simp [PrimOp.ty, if_neg hb] at hop
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq, Ty.arrow.injEq] at hop
        obtain ⟨hα, hβ, _⟩ := hop
        exact ⟨.char, .char, hα.symm, hβ.symm⟩
      · simp [PrimOp.ty, if_neg hb] at hop

/-- A typed primitive operator's type is well formed. -/
private theorem primOp_ty_wf {sig : Signature} {op : PrimOp} {ty : Ty} {rc : Nat}
    (hop : op.ty sig = some ty) : ty.WF rc 0 := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq] at hop
      subst hop
      exact ⟨.arrow .prim (.arrow .prim .prim),
        .arrow .prim (.arrow .prim .prim)⟩
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at hop
      subst hop
      exact ⟨.arrow .prim (.arrow .prim .prim),
        .arrow .prim (.arrow .prim .prim)⟩
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
        subst hop
        exact ⟨.arrow .prim (.arrow .prim (.con 0)),
          .arrow .prim (.arrow .prim .con)⟩
      · simp [PrimOp.ty, if_neg hb] at hop
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
        subst hop
        exact ⟨.arrow .prim (.arrow .prim (.con 0)),
          .arrow .prim (.arrow .prim .con)⟩
      · simp [PrimOp.ty, if_neg hb] at hop

private theorem primLit_int_eq {lit : PrimLit} (h : lit.ty = .prim .int) :
    ∃ n, lit = .int n := by
  cases lit with
  | int n => exact ⟨n, rfl⟩
  | unit => simp [PrimLit.ty] at h
  | nat n => simp [PrimLit.ty] at h
  | char c => simp [PrimLit.ty] at h

private theorem primLit_char_eq {lit : PrimLit} (h : lit.ty = .prim .char) :
    ∃ c, lit = .char c := by
  cases lit with
  | int n => simp [PrimLit.ty] at h
  | unit => simp [PrimLit.ty] at h
  | nat n => simp [PrimLit.ty] at h
  | char c => exact ⟨c, rfl⟩

/-- Under the `Bool` convention, declaration 0's constructors have scheme `Bool`. -/
private theorem hasBool_schemeOf_boolCtor {sig : Signature} (hsig : sig.HasBool)
    (c : Nat) (hc : c < 2) :
    sig.schemeOf (.ctor 0 c 0) = some (PolyTy.mono Ty.bool) := by
  have h0 : sig[0]? = some boolDecl := hsig
  have hc' : c = 0 ∨ c = 1 := by omega
  rcases hc' with rfl | rfl <;>
    simp [Signature.schemeOf, h0, boolDecl, DataDecl.ctorScheme, DataDecl.selfTy,
      Ty.apps, Ty.arrows, PolyTy.mono, Ty.bool]

/-- `True` and `False` are typed at `Bool` under the `Bool` convention. -/
private theorem hasBool_boolValue_typing {sig : Signature} {rc : Nat} {ctx : Ctx}
    (hsig : sig.HasBool) (b : Bool) :
    RuntimeTyping sig rc ctx (Eval.boolValue b) Ty.bool := by
  have hsch := hasBool_schemeOf_boolCtor hsig (if b then 0 else 1) (by split <;> omega)
  unfold Eval.boolValue Ty.bool
  refine RuntimeTyping.const (args := []) hsch ?_ rfl ?_
  · exact ⟨.con 0, .con⟩
  · intro arg harg
    simp at harg

/-- A saturated primitive application on operands of the right kinds has a result. -/
private theorem primOp_eval_exists {sig : Signature} {op : PrimOp} {left right : PrimLit}
    {α β ty : Ty}
    (hop : op.ty sig = some (.arrow α (.arrow β ty)))
    (hleft : left.ty = α) (hright : right.ty = β) :
    ∃ result, op.eval left right = some result := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      obtain ⟨hα, hβ, _⟩ := hop
      obtain ⟨l, rfl⟩ := primLit_int_eq (hleft.trans hα.symm)
      obtain ⟨rr, rfl⟩ := primLit_int_eq (hright.trans hβ.symm)
      exact ⟨.primLit (.int (l + rr)), by simp [PrimOp.eval]⟩
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      obtain ⟨hα, hβ, _⟩ := hop
      obtain ⟨l, rfl⟩ := primLit_int_eq (hleft.trans hα.symm)
      obtain ⟨rr, rfl⟩ := primLit_int_eq (hright.trans hβ.symm)
      exact ⟨.primLit (.int (l - rr)), by simp [PrimOp.eval]⟩
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
private theorem primOp_eval_typing {sig : Signature} {rc : Nat} {ctx : Ctx}
    {op : PrimOp} {left right : PrimLit} {result : RuntimeExpr} {α β ty : Ty}
    (hop : op.ty sig = some (.arrow α (.arrow β ty)))
    (hleft : left.ty = α) (hright : right.ty = β)
    (heval : op.eval left right = some result) :
    RuntimeTyping sig rc ctx result ty := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      obtain ⟨hα, hβ, hγ⟩ := hop
      obtain ⟨l, rfl⟩ := primLit_int_eq (hleft.trans hα.symm)
      obtain ⟨rr, rfl⟩ := primLit_int_eq (hright.trans hβ.symm)
      simp only [PrimOp.eval, Option.some.injEq] at heval
      subst heval
      rw [← hγ]
      exact .primLit
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq, Ty.arrow.injEq] at hop
      obtain ⟨hα, hβ, hγ⟩ := hop
      obtain ⟨l, rfl⟩ := primLit_int_eq (hleft.trans hα.symm)
      obtain ⟨rr, rfl⟩ := primLit_int_eq (hright.trans hβ.symm)
      simp only [PrimOp.eval, Option.some.injEq] at heval
      subst heval
      rw [← hγ]
      exact .primLit
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

private theorem typing_apps_intro {f : RuntimeExpr} {tys : List Ty} {u : Ty}
    (typing : RuntimeTyping sig r ctx f (Ty.arrows tys u))
    {args : List RuntimeExpr}
    (hargs : List.Forall₂ (fun e t => RuntimeTyping sig r ctx e t) args tys) :
    RuntimeTyping sig r ctx (Expr.apps f args) u := by
  induction hargs generalizing f u with
  | nil => simpa [Expr.apps] using typing
  | cons hhead htail ih =>
      exact ih (RuntimeTyping.app typing hhead)

private theorem typing_spine_inv {head : RuntimeExpr} {args : List RuntimeExpr} {ty : Ty}
    (typing : RuntimeTyping sig r ctx (Expr.apps head args) ty) :
    ∃ argTys : List Ty,
      List.Forall₂ (fun e t => RuntimeTyping sig r ctx e t) args argTys ∧
      RuntimeTyping sig r ctx head (Ty.arrows argTys ty) := by
  induction args generalizing head ty with
  | nil => exact ⟨[], .nil, by simpa [Expr.apps] using typing⟩
  | cons a as ih =>
      have typing' : RuntimeTyping sig r ctx (Expr.apps (.app head a) as) ty := typing
      obtain ⟨argTys, hforall, hhead⟩ := ih typing'
      cases argTys with
      | nil =>
          cases hhead with
          | app hf ha =>
              rename_i argumentTy
              exact ⟨[argumentTy], .cons ha hforall, by simpa [Ty.arrows] using hf⟩
      | cons b bs =>
          cases hhead with
          | app hf ha =>
              rename_i argumentTy
              exact ⟨argumentTy :: b :: bs, .cons ha hforall, by
                simpa [Ty.arrows] using hf⟩

private theorem const_spine_inv {c : DataConst} {args : List RuntimeExpr} {ty : Ty}
    (typing : RuntimeTyping sig r ctx (Expr.apps (.const c) args) ty) :
    ∃ (scheme : PolyTy) (instArgs argTys : List Ty),
      sig.schemeOf c = some scheme ∧ scheme.WF 0 ∧
      instArgs.length = scheme.paramCount ∧
      (∀ a ∈ instArgs, a.WF r 0) ∧
      scheme.openWith instArgs = Ty.arrows argTys ty ∧
      List.Forall₂ (fun e t => RuntimeTyping sig r ctx e t) args argTys := by
  obtain ⟨argTys, hforall, hhead⟩ := typing_spine_inv typing
  generalize hty : Ty.arrows argTys ty = target at hhead
  cases hhead with
  | const hscheme hwf hlen hargs =>
      exact ⟨_, _, argTys, hscheme, hwf, hlen, hargs, hty.symm, hforall⟩

private theorem ctorScheme_fields_scoped {decl : DataDecl} {type : Nat} {fields : List Ty}
    (h : (decl.ctorScheme type fields).WF 0) :
    ∀ ft ∈ fields, ft.Scoped 0 decl.paramCount := by
  intro ft hft
  exact Ty.arrows_scoped_inv h.1 ft hft

private theorem fields_openWith_eq {decl : DataDecl} {fields : List Ty} {params : List Ty}
    {r : Ty}
    (hfields : ∀ ft ∈ fields, ft.Scoped 0 decl.paramCount)
    (hplen : params.length = decl.paramCount) :
    fields.map (fun ft => ft.openWith (params ++ [r])) =
      fields.map (fun ft => ft.openWith params) := by
  apply List.map_congr_left
  intro ft hft
  exact Ty.openWith_append_of_scoped (hfields ft hft) hplen

private theorem forall₂_map_openWith {fields : List Ty} {args : List RuntimeExpr}
    {params : List Ty}
    (h : List.Forall₂ (fun e ty => RuntimeTyping sig r ctx e ty) args
      (fields.map (fun ft => ft.openWith params))) :
    List.Forall₂ (fun e ft => RuntimeTyping sig r ctx e (ft.openWith params)) args fields := by
  induction fields generalizing args with
  | nil => cases h; exact .nil
  | cons ft fts ih =>
      cases h with
      | cons hhead htail => exact .cons hhead (ih htail)

private theorem forall₂_openWith_append {fields : List Ty} {args : List RuntimeExpr}
    {params : List Ty} {result : Ty} {n : Nat}
    (hfields : ∀ ft ∈ fields, ft.Scoped 0 n)
    (hplen : params.length = n)
    (h : List.Forall₂ (fun e ft => RuntimeTyping sig r ctx e (ft.openWith params)) args fields) :
    List.Forall₂ (fun e ft => RuntimeTyping sig r ctx e (ft.openWith (params ++ [result]))) args fields := by
  induction fields generalizing args with
  | nil => cases h; exact .nil
  | cons ft fts ih =>
      cases h with
      | cons hhead htail =>
          exact .cons (by
            rw [Ty.openWith_append_of_scoped (hfields ft (by simp)) hplen]
            exact hhead)
            (ih (fun x hx => hfields x (by simp [hx])) htail)

/-- A value whose assigned type is a declared data type instance must be a
saturated constructor application of that declaration. -/
private theorem data_value_canonical {expr : RuntimeExpr} {t : Nat} {params : List Ty}
    (value : Eval.Value expr)
    (typing : RuntimeTyping sig r ctx expr (Ty.apps (.con t) params)) :
    ∃ (decl : DataDecl) (ctor arity : Nat) (fields : List RuntimeExpr) (fieldTys : List Ty),
      sig[t]? = some decl ∧ decl.ctors[ctor]? = some fieldTys ∧
      fieldTys.length = arity ∧
      expr = Expr.apps (.const (.ctor t ctor arity)) fields ∧
      fields.length = arity ∧
      (decl.ctorScheme t fieldTys).WF 0 ∧
      List.Forall₂ (fun e ft => RuntimeTyping sig r ctx e (ft.openWith params)) fields fieldTys := by
  cases value with
  | primLit =>
      rename_i literal
      generalize hty : Ty.apps (.con t) params = target at typing
      cases typing
      cases literal <;> (exfalso; exact Ty.apps_con_ne_prim hty)
  | primOp =>
      generalize hty : Ty.apps (.con t) params = target at typing
      cases typing with
      | primOp hop =>
          obtain ⟨a, b, hab⟩ := primOp_ty_arrow hop
          exfalso
          exact Ty.apps_con_ne_arrow (hty.trans hab)
  | lambda =>
      generalize hty : Ty.apps (.con t) params = target at typing
      cases typing
      exfalso
      exact Ty.apps_con_ne_arrow hty
  | primOpPartial _ =>
      generalize hty : Ty.apps (.con t) params = target at typing
      cases typing with
      | app hf _ =>
          cases hf with
          | primOp hop =>
              obtain ⟨a, b, hab⟩ := primOp_ty_codomain_arrow hop
              exfalso
              exact Ty.apps_con_ne_arrow (hty.trans hab)
  | const hspine hlen hvals =>
      expose_names
      have hexpr : Expr.apps (.const c) args = expr := by
        have h := Expr.apps_spine expr
        rw [hspine] at h
        exact h
      have typing' : RuntimeTyping sig r ctx (Expr.apps (.const c) args)
          (Ty.apps (.con t) params) := by
        rw [hexpr]
        exact typing
      obtain ⟨scheme, instArgs, argTys, hscheme, hwf, hilen, hiwf, hopen, hforall⟩ :=
        const_spine_inv typing'
      cases c with
      | ctor type ctor arity =>
          obtain ⟨decl, fieldTys, hdecl, hctors, hflen, hschemeEq⟩ :=
            Signature.schemeOf_ctor_some hscheme
          subst scheme
          have hilen' : instArgs.length = decl.paramCount := by simpa using hilen
          rw [DataDecl.ctorScheme_openWith decl type fieldTys instArgs hilen'] at hopen
          have hargLen : argTys.length = args.length :=
            (List.Forall₂.length_eq hforall).symm
          have hvalLen : args.length ≤ arity := by
            simpa [DataConst.valueArity] using hlen
          obtain ⟨rest, hrest, hty⟩ :=
            Ty.arrows_eq_arrows_append hopen.symm (by
              simp only [List.length_map]
              omega)
          cases rest with
          | nil =>
              have hargTys : argTys = fieldTys.map (fun ft => Ty.openWith instArgs ft) := by
                simpa using hrest.symm
              obtain ⟨htype, hparams⟩ := Ty.apps_con_inj hty
              rw [htype, hparams]
              refine ⟨decl, ctor, arity, args, fieldTys, hdecl, hctors, hflen, ?_, ?_, hwf, ?_⟩
              · rw [hexpr]
              · have hlength := List.Forall₂.length_eq hforall
                rw [hargTys] at hlength
                simpa [hflen] using hlength
              · rw [hargTys] at hforall
                exact forall₂_map_openWith hforall
          | cons x xs =>
              exfalso
              exact Ty.apps_con_ne_arrow (a := x) (b := Ty.arrows xs _) hty
      | elim type ctorCount =>
          obtain ⟨decl, hdecl, hctorsLen, hschemeEq⟩ :=
            Signature.schemeOf_elim_some hscheme
          subst scheme
          have hilen' : instArgs.length = decl.paramCount + 1 := by simpa using hilen
          obtain ⟨p, rr, hp, hplen⟩ := exists_append_singleton_of_length hilen'
          subst hp
          rw [DataDecl.elimScheme_openWith decl type hplen] at hopen
          have hargLen : argTys.length = args.length :=
            (List.Forall₂.length_eq hforall).symm
          have hvalLen : args.length ≤ ctorCount := by
            simpa [DataConst.valueArity] using hlen
          have hbranchLen : (decl.ctors.map (fun fields =>
              Ty.arrow (.prim .unit)
                (Ty.arrows (fields.map (fun ft => Ty.openWith (p ++ [rr]) ft)) rr))).length
              = ctorCount := by
            simp [hctorsLen]
          obtain ⟨rest, hrest, hty⟩ :=
            Ty.arrows_eq_arrows_append hopen.symm (by
              simp only [List.length_cons, List.length_map]
              omega)
          have hlenRest : 0 < rest.length := by
            have hcongr := congrArg List.length hrest
            simp only [List.length_append, List.length_cons, List.length_map] at hcongr
            omega
          cases rest with
          | nil => simp at hlenRest
          | cons x xs =>
              exfalso
              exact Ty.apps_con_ne_arrow (a := x) (b := Ty.arrows xs _) hty

/-- A fully applied elimininator's type is a list of all its branches at the
result type. -/
private theorem elim_spine_full {decl : DataDecl} {type : Nat}
    {instArgs argTys : List Ty} {ty : Ty}
    (hlen : instArgs.length = decl.paramCount + 1)
    (hargLen : argTys.length = decl.ctors.length + 1)
    (hopened : (decl.elimScheme type).openWith instArgs = Ty.arrows argTys ty) :
    ∃ (params : List Ty) (r : Ty),
      instArgs = params ++ [r] ∧ params.length = decl.paramCount ∧ ty = r ∧
      argTys = (Ty.apps (.con type) params) ::
        decl.ctors.map (fun fields =>
          Ty.arrow (.prim .unit)
            (Ty.arrows (fields.map (fun ft => Ty.openWith (params ++ [r]) ft)) r)) := by
  obtain ⟨params, r, rfl, hplen⟩ := exists_append_singleton_of_length hlen
  rw [DataDecl.elimScheme_openWith decl type hplen] at hopened
  have hlenEq : argTys.length =
      (Ty.apps (.con type) params :: decl.ctors.map (fun fields =>
        Ty.arrow (.prim .unit)
          (Ty.arrows (fields.map (fun ft => Ty.openWith (params ++ [r]) ft)) r))).length := by
    simp only [List.length_cons, List.length_map]
    omega
  obtain ⟨hargTys, hty⟩ := Ty.arrows_cancel hopened.symm hlenEq
  exact ⟨params, r, rfl, hplen, hty, hargTys⟩

end RuntimeTyping

private theorem erase_openRigidsFrom (expr : Source) :
    (expr.openRigidsFrom depth base count).erase = expr.erase := by
  induction expr generalizing depth with
  | primLit => rfl
  | primOp => rfl
  | var => rfl
  | lambda ann body ih =>
      simp only [Expr.openRigidsFrom, Expr.erase, ih]
  | app function argument functionIH argumentIH =>
      simp only [Expr.openRigidsFrom, Expr.erase, functionIH, argumentIH]
  | letIn ann rhs body rhsIH bodyIH =>
      simp only [Expr.openRigidsFrom, Expr.erase, rhsIH, bodyIH]
  | fix ann body ih =>
      simp only [Expr.openRigidsFrom, Expr.erase, ih]
  | const c => rfl

/-- Opening source type annotations has no runtime effect. -/
theorem erase_openRigids (expr : Source) :
    (expr.openRigids base count).erase = expr.erase := by
  exact erase_openRigidsFrom expr

namespace Typing

/-- Erasing Core-native partial annotations preserves the assigned type. -/
theorem erase (typing : Typing sig rigidCount ctx expr ty) :
    RuntimeTyping sig rigidCount ctx expr.erase ty := by
  induction typing with
  | primLit => exact .primLit
  | primOp hop => exact .primOp hop
  | var hlookup hwf hlen hargs =>
      exact .var hlookup hwf hlen hargs
  | lambda paramWF _ _ bodyErased =>
      exact .lambda paramWF bodyErased
  | app _ _ functionErased argumentErased =>
      exact .app functionErased argumentErased
  | letMono rhsWF _ _ rhsErased bodyErased =>
      exact .letMono rhsWF rhsErased bodyErased
  | letPoly _ schemeWF ctxWF _ _ _ rhsErased bodyErased =>
      apply RuntimeTyping.letPoly schemeWF ctxWF
      · simpa only [erase_openRigids] using rhsErased
      · exact bodyErased
  | fix selfWF _ _ bodyErased =>
      exact .fix selfWF bodyErased
  | const hscheme hwf hlen hargs =>
      exact .const hscheme hwf hlen hargs

end Typing
end EPL

namespace EPL
namespace RuntimeTyping

private theorem scoped_openWith
    {ty : Ty} {rigidCount binderCount : Nat} {args : List Ty}
    (hscoped : ty.Scoped rigidCount binderCount)
    (hlen : args.length = binderCount)
    (hargs : ∀ arg ∈ args, arg.Scoped rigidCount 0) :
    (ty.openWith args).Scoped rigidCount 0 := by
  induction ty generalizing binderCount with
  | prim p => exact .prim
  | arrow domain codomain ihDomain ihCodomain =>
      cases hscoped with
      | arrow domainScoped codomainScoped =>
          exact .arrow (ihDomain domainScoped hlen)
            (ihCodomain codomainScoped hlen)
  | bvar index =>
      cases hscoped with
      | bvar hindex =>
          have hindex' : index < args.length := by simpa [hlen] using hindex
          have hget : args[index]? = some args[index] :=
            List.getElem?_eq_getElem hindex'
          simp only [Ty.openWith, hget, Option.getD_some]
          exact hargs args[index] (List.getElem_mem hindex')
  | rigid level =>
      cases hscoped with
      | rigid hlevel => exact .rigid hlevel
  | mvar id => exact .mvar id
  | con id => exact .con id
  | app function argument ihFunction ihArgument =>
      cases hscoped with
      | app functionScoped argumentScoped =>
          exact .app (ihFunction functionScoped hlen)
            (ihArgument argumentScoped hlen)

private theorem metaFree_openWith
    {ty : Ty} {args : List Ty}
    (free : ty.MetaFree)
    (hargs : ∀ arg ∈ args, arg.MetaFree) :
    (ty.openWith args).MetaFree := by
  induction ty with
  | prim p => exact .prim
  | arrow domain codomain ihDomain ihCodomain =>
      cases free with
      | arrow domainFree codomainFree =>
          exact .arrow (ihDomain domainFree) (ihCodomain codomainFree)
  | bvar index =>
      simp only [Ty.openWith]
      cases hget : args[index]? with
      | none => exact .bvar
      | some arg => exact hargs arg (List.mem_of_getElem? hget)
  | rigid level => exact .rigid
  | mvar id => cases free
  | con id => exact .con
  | app function argument ihFunction ihArgument =>
      cases free with
      | app functionFree argumentFree =>
          exact .app (ihFunction functionFree) (ihArgument argumentFree)

private theorem wf_openWith
    {ty : Ty} {rigidCount binderCount : Nat} {args : List Ty}
    (wf : ty.WF rigidCount binderCount)
    (hlen : args.length = binderCount)
    (hargs : ∀ arg ∈ args, arg.WF rigidCount 0) :
    (ty.openWith args).WF rigidCount 0 := by
  exact ⟨scoped_openWith wf.1 hlen (fun arg harg => (hargs arg harg).1),
    metaFree_openWith wf.2 (fun arg harg => (hargs arg harg).2)⟩

private theorem scoped_monoRigids_zero {ty : Ty} {n : Nat}
    (h : ty.Scoped 0 n) (r : Nat) : ty.Scoped r n := by
  induction h with
  | prim => exact .prim
  | arrow _ _ ihd ihc => exact .arrow ihd ihc
  | bvar hi => exact .bvar hi
  | rigid hi => omega
  | mvar id => exact .mvar id
  | con id => exact .con id
  | app _ _ ihd ihc => exact .app ihd ihc

/-- Runtime typing also assigns only scoped, meta-free semantic types. -/
theorem regular (typing : RuntimeTyping sig rigidCount ctx expr ty) :
    ty.WF rigidCount 0 := by
  induction typing with
  | primLit => cases_type PrimLit <;> exact ⟨.prim, .prim⟩
  | primOp hop => exact primOp_ty_wf hop
  | var _ wf hlen hargs => exact wf_openWith wf hlen hargs
  | lambda paramWF _ bodyRegular =>
      exact ⟨.arrow paramWF.1 bodyRegular.1,
        .arrow paramWF.2 bodyRegular.2⟩
  | app _ _ functionRegular _ =>
      rcases functionRegular with ⟨functionScoped, functionFree⟩
      cases functionScoped with
      | arrow _ resultScoped =>
          cases functionFree with
          | arrow _ resultFree => exact ⟨resultScoped, resultFree⟩
  | letMono => assumption
  | letPoly => assumption
  | fix => assumption
  | const _ wf hlen hargs =>
      expose_names
      exact wf_openWith (binderCount := scheme.paramCount)
        ⟨scoped_monoRigids_zero wf.1 _, wf.2⟩ hlen hargs

end RuntimeTyping
end EPL

namespace EPL
namespace RuntimeTyping

private def shiftLevel (cutoff delta level : Nat) : Nat :=
  if cutoff ≤ level then level + delta else level

private def shiftTy (cutoff delta : Nat) : Ty → Ty
  | .prim p => .prim p
  | .arrow a b => .arrow (shiftTy cutoff delta a) (shiftTy cutoff delta b)
  | .bvar i => .bvar i
  | .rigid i => .rigid (shiftLevel cutoff delta i)
  | .mvar i => .mvar i
  | .con i => .con i
  | .app a b => .app (shiftTy cutoff delta a) (shiftTy cutoff delta b)

private def shiftScheme (cutoff delta : Nat) (scheme : PolyTy) : PolyTy :=
  ⟨scheme.paramCount, shiftTy cutoff delta scheme.body⟩

private def shiftCtx (cutoff delta : Nat) (ctx : Ctx) : Ctx :=
  ctx.map (shiftScheme cutoff delta)

/-- Shifting rigid levels leaves a primitive operator's type unchanged. -/
private theorem primOp_ty_shiftTy {sig : Signature} {op : PrimOp} {ty : Ty}
    (hop : op.ty sig = some ty) {cutoff delta : Nat} :
    shiftTy cutoff delta ty = ty := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq] at hop
      subst hop
      rfl
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at hop
      subst hop
      rfl
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
        subst hop
        rfl
      · simp [PrimOp.ty, if_neg hb] at hop
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
        subst hop
        rfl
      · simp [PrimOp.ty, if_neg hb] at hop

private theorem scoped_monoRigids {ty : Ty}
    (h : Ty.Scoped rigidCount binderCount ty) (hle : rigidCount ≤ larger) :
    Ty.Scoped larger binderCount ty := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar hi => exact .bvar hi
  | rigid hi => exact .rigid (Nat.lt_of_lt_of_le hi hle)
  | mvar id => exact .mvar id
  | con id => exact .con id
  | app _ _ iha ihb => exact .app iha ihb

private theorem wf_monoRigids {ty : Ty}
    (h : Ty.WF rigidCount binderCount ty) (hle : rigidCount ≤ larger) :
    Ty.WF larger binderCount ty :=
  ⟨scoped_monoRigids h.1 hle, h.2⟩

private theorem schemeWF_monoRigids {scheme : PolyTy}
    (h : PolyTy.WF rigidCount scheme) (hle : rigidCount ≤ larger) :
    PolyTy.WF larger scheme :=
  wf_monoRigids h hle

private theorem ctxWF_monoRigids {ctx : Ctx}
    (h : Ctx.WF rigidCount ctx) (hle : rigidCount ≤ larger) :
    Ctx.WF larger ctx := by
  intro scheme hs
  exact schemeWF_monoRigids (h scheme hs) hle

private theorem shiftTy_eq_self {ty : Ty} (h : Ty.Scoped cutoff binderCount ty) :
    shiftTy cutoff delta ty = ty := by
  induction h with
  | prim => rfl
  | arrow _ _ iha ihb => simp [shiftTy, iha, ihb]
  | bvar => rfl
  | rigid hi => simp [shiftTy, shiftLevel, Nat.not_le.mpr hi]
  | mvar => rfl
  | con => rfl
  | app _ _ iha ihb => simp [shiftTy, iha, ihb]

private theorem shiftScheme_eq_self {scheme : PolyTy} (h : PolyTy.WF cutoff scheme) :
    shiftScheme cutoff delta scheme = scheme := by
  cases scheme with
  | mk count body =>
      simp only [shiftScheme, Scheme.mk.injEq, true_and]
      exact shiftTy_eq_self h.1

private theorem shiftCtx_eq_self {ctx : Ctx} (h : Ctx.WF cutoff ctx) :
    shiftCtx cutoff delta ctx = ctx := by
  induction ctx with
  | nil => rfl
  | cons scheme tail ih =>
      have hs : scheme.WF cutoff := h scheme (by simp)
      have ht : Ctx.WF cutoff tail := by
        intro item hi
        exact h item (by simp [hi])
      change shiftScheme cutoff delta scheme :: shiftCtx cutoff delta tail = scheme :: tail
      rw [shiftScheme_eq_self hs, ih ht]

private theorem shiftTy_scoped {ty : Ty}
    (h : Ty.Scoped rigidCount binderCount ty) :
    Ty.Scoped (rigidCount + delta) binderCount (shiftTy cutoff delta ty) := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar hi => exact .bvar hi
  | rigid hi =>
      simp only [shiftTy]
      unfold shiftLevel
      split
      · exact .rigid (by omega)
      · exact .rigid (by omega)
  | mvar id => exact .mvar id
  | con id => exact .con id
  | app _ _ iha ihb => exact .app iha ihb

private theorem shiftTy_metaFree (h : Ty.MetaFree ty) :
    Ty.MetaFree (shiftTy cutoff delta ty) := by
  induction h with
  | prim => exact .prim
  | arrow _ _ iha ihb => exact .arrow iha ihb
  | bvar => exact .bvar
  | rigid => exact .rigid
  | con => exact .con
  | app _ _ iha ihb => exact .app iha ihb

private theorem shiftTy_wf {ty : Ty}
    (h : Ty.WF rigidCount binderCount ty) :
    Ty.WF (rigidCount + delta) binderCount (shiftTy cutoff delta ty) :=
  ⟨shiftTy_scoped h.1, shiftTy_metaFree h.2⟩

private theorem shiftScheme_wf {scheme : PolyTy}
    (h : PolyTy.WF rigidCount scheme) :
    PolyTy.WF (rigidCount + delta) (shiftScheme cutoff delta scheme) :=
  shiftTy_wf h

private theorem shiftCtx_wf {ctx : Ctx} (h : Ctx.WF rigidCount ctx) :
    Ctx.WF (rigidCount + delta) (shiftCtx cutoff delta ctx) := by
  intro scheme hmem
  rcases List.mem_map.mp hmem with ⟨original, horiginal, rfl⟩
  exact shiftScheme_wf (h original horiginal)

private theorem shiftTy_openWith (ty : Ty) (args : List Ty) :
    shiftTy cutoff delta (ty.openWith args) =
      (shiftTy cutoff delta ty).openWith (args.map (shiftTy cutoff delta)) := by
  induction ty with
  | prim => rfl
  | arrow a b iha ihb => simp [Ty.openWith, shiftTy, iha, ihb]
  | bvar index =>
      simp only [Ty.openWith, shiftTy, List.getElem?_map]
      cases args[index]? <;> simp [shiftTy]
  | rigid => rfl
  | mvar => rfl
  | con => rfl
  | app a b iha ihb => simp [Ty.openWith, shiftTy, iha, ihb]

private theorem shiftRigidBlock (hcut : cutoff ≤ base) :
    (rigidBlock base count).map (shiftTy cutoff delta) =
      rigidBlock (base + delta) count := by
  unfold rigidBlock
  rw [List.map_map]
  apply List.map_congr_left
  intro offset _
  simp only [Function.comp_apply, shiftTy]
  unfold shiftLevel
  rw [if_pos (by omega)]
  congr 1
  omega

private theorem shiftScheme_openRigids (scheme : PolyTy)
    (hcut : cutoff ≤ base) :
    shiftTy cutoff delta (scheme.openRigids base) =
      (shiftScheme cutoff delta scheme).openRigids (base + delta) := by
  simp only [PolyTy.openRigids, PolyTy.openWith, shiftScheme]
  rw [shiftTy_openWith, shiftRigidBlock hcut]

private theorem shiftTyping (typing : RuntimeTyping sig rigidCount ctx expr ty)
    (hcut : cutoff ≤ rigidCount) :
    RuntimeTyping sig (rigidCount + delta) (shiftCtx cutoff delta ctx)
      expr (shiftTy cutoff delta ty) := by
  induction typing with
  | primLit =>
      rename_i literal
      cases literal <;> exact .primLit
  | primOp hop =>
      exact .primOp (by rw [primOp_ty_shiftTy hop]; exact hop)
  | var hlookup hwf hlen hargs =>
      clear rigidCount ctx expr ty
      rename_i localCtx index scheme args localRigid
      let shiftedArgs := args.map (shiftTy cutoff delta)
      have hlookup' :
          (shiftCtx cutoff delta localCtx)[index]? =
            some (shiftScheme cutoff delta scheme) := by
        simpa [shiftCtx] using congrArg (Option.map (shiftScheme cutoff delta)) hlookup
      have hargs' : ∀ arg ∈ shiftedArgs,
          arg.WF (localRigid + delta) 0 := by
        intro arg harg
        rcases List.mem_map.mp harg with ⟨original, horiginal, rfl⟩
        exact shiftTy_wf (hargs original horiginal)
      have hopen := shiftTy_openWith (cutoff := cutoff) (delta := delta)
        scheme.body args
      simpa [shiftScheme, PolyTy.openWith, shiftedArgs, hopen] using
        (RuntimeTyping.var hlookup' (shiftScheme_wf hwf)
          (by simpa [shiftedArgs] using hlen) hargs')
  | const hscheme hwf hlen hargs =>
      clear rigidCount ctx expr ty
      expose_names
      let shiftedArgs := args.map (shiftTy cutoff delta)
      have hargs' : ∀ arg ∈ shiftedArgs,
          arg.WF (rigidCount + delta) 0 := by
        intro arg harg
        rcases List.mem_map.mp harg with ⟨original, horiginal, rfl⟩
        exact shiftTy_wf (hargs original horiginal)
      have hopen := shiftTy_openWith (cutoff := cutoff) (delta := delta)
        scheme.body args
      have hbody : shiftTy cutoff delta scheme.body = scheme.body :=
        shiftTy_eq_self (scoped_monoRigids_zero hwf.1 cutoff)
      simpa [shiftScheme, PolyTy.openWith, shiftedArgs, hopen, hbody] using
        (RuntimeTyping.const hscheme hwf
          (by simpa [shiftedArgs] using hlen) hargs')
  | lambda hwf _ ih =>
      simpa [shiftCtx, shiftScheme, PolyTy.mono, shiftTy] using
        (RuntimeTyping.lambda (shiftTy_wf hwf) (ih hcut))
  | app _ _ ihf iha =>
      simpa [shiftTy] using RuntimeTyping.app (ihf hcut) (iha hcut)
  | letMono hwf _ _ ihr ihb =>
      simpa [shiftCtx, shiftScheme, PolyTy.mono] using
        (RuntimeTyping.letMono (shiftTy_wf hwf) (ihr hcut) (ihb hcut))
  | letPoly hwf hctx _ _ ihr ihb =>
      clear rigidCount ctx expr ty
      have hRhs := ihr (by omega)
      rw [shiftScheme_openRigids _ hcut] at hRhs
      simpa [shiftCtx, shiftScheme] using
        (RuntimeTyping.letPoly (shiftScheme_wf hwf)
          (shiftCtx_wf hctx)
          (by simpa [shiftScheme, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hRhs)
          (ihb hcut))
  | fix hwf _ ih =>
      simpa [shiftCtx, shiftScheme, PolyTy.mono] using
        (RuntimeTyping.fix (shiftTy_wf hwf) (ih hcut))

private theorem rebaseExplicit
    (hctx : Ctx.WF rigidCount ctx)
    (hscheme : PolyTy.WF rigidCount scheme)
    (htyping : RuntimeTyping sig (rigidCount + scheme.paramCount) ctx rhs
      (scheme.openRigids rigidCount))
    (hle : rigidCount ≤ larger) :
    RuntimeTyping sig (larger + scheme.paramCount) ctx rhs
      (scheme.openRigids larger) := by
  let delta := larger - rigidCount
  have hshift := shiftTyping (cutoff := rigidCount) (delta := delta)
    htyping (by omega)
  have hctxId : shiftCtx rigidCount delta ctx = ctx := shiftCtx_eq_self hctx
  have hschemeId : shiftScheme rigidCount delta scheme = scheme :=
    shiftScheme_eq_self hscheme
  rw [hctxId, shiftScheme_openRigids _ (by omega), hschemeId] at hshift
  have hbase : rigidCount + delta = larger := by
    dsimp [delta]
    omega
  have hboundary : rigidCount + scheme.paramCount + delta =
      larger + scheme.paramCount := by
    dsimp [delta]
    omega
  rw [hboundary, hbase] at hshift
  exact hshift

/-- Runtime typing is stable when unrelated rigid levels are added to scope.
Explicit-polymorphic lets rebase their deterministic generic block. -/
theorem weakenRigids
    (typing : RuntimeTyping sig rigidCount ctx expr ty)
    (hscope : rigidCount ≤ larger) :
    RuntimeTyping sig larger ctx expr ty := by
  induction typing generalizing larger with
  | primLit => exact .primLit
  | primOp hop => exact .primOp hop
  | var hlookup hwf hlen hargs =>
      exact .var hlookup (schemeWF_monoRigids hwf hscope) hlen
        (fun arg harg => wf_monoRigids (hargs arg harg) hscope)
  | const hscheme hwf hlen hargs =>
      exact .const hscheme hwf hlen
        (fun arg harg => wf_monoRigids (hargs arg harg) hscope)
  | lambda hwf _ ih =>
      exact .lambda (wf_monoRigids hwf hscope) (ih hscope)
  | app _ _ ihf iha => exact .app (ihf hscope) (iha hscope)
  | letMono hwf _ _ ihr ihb =>
      exact .letMono (wf_monoRigids hwf hscope) (ihr hscope) (ihb hscope)
  | letPoly hwf hctx hrhs _ _ ihb =>
      exact .letPoly (schemeWF_monoRigids hwf hscope)
        (ctxWF_monoRigids hctx hscope)
        (rebaseExplicit hctx hwf hrhs hscope) (ihb hscope)
  | fix hwf _ ih =>
      exact .fix (wf_monoRigids hwf hscope) (ih hscope)

end RuntimeTyping
end EPL

namespace EPL
namespace RuntimeTyping

private theorem scoped_weakenRigids
    {ty : Ty}
    (hScoped : ty.Scoped rigidCount binderCount)
    (hscope : rigidCount ≤ larger) :
    ty.Scoped larger binderCount := by
  induction hScoped with
  | prim => exact .prim
  | arrow _ _ domainIH codomainIH => exact .arrow domainIH codomainIH
  | bvar hindex => exact .bvar hindex
  | rigid hlevel => exact .rigid (hlevel.trans_le hscope)
  | mvar id => exact .mvar id
  | con id => exact .con id
  | app _ _ domainIH codomainIH => exact .app domainIH codomainIH

private theorem schemeWF_weakenRigids
    {scheme : PolyTy}
    (wf : scheme.WF rigidCount)
    (hscope : rigidCount ≤ larger) :
    scheme.WF larger :=
  ⟨scoped_weakenRigids wf.1 hscope, wf.2⟩

private theorem ctxWF_insert
    {pre post : Ctx} {inserted : PolyTy}
    (wf : (pre ++ post : Ctx).WF rigidCount)
    (insertedWF : inserted.WF rigidCount) :
    (pre ++ inserted :: post : Ctx).WF rigidCount := by
  intro scheme hmem
  rcases List.mem_append.mp hmem with hpre | htail
  · exact wf scheme (List.mem_append_left post hpre)
  · rcases List.mem_cons.mp htail with rfl | hsuffix
    · exact insertedWF
    · exact wf scheme (List.mem_append_right pre hsuffix)

private theorem weakenAt
    (typing : RuntimeTyping sig rigidCount env expr ty) :
    ∀ (pre post : Ctx), env = pre ++ post →
      inserted.WF rigidCount →
      RuntimeTyping sig rigidCount (pre ++ inserted :: post)
        (expr.shiftFrom pre.length 1) ty := by
  induction typing with
  | primLit =>
      intro pre post _ _
      exact .primLit
  | primOp hop =>
      intro pre post _ _
      exact .primOp hop
  | var lookup schemeWF lengthEq argsWF =>
      expose_names
      intro pre post envEq insertedWF
      rw [envEq] at lookup
      by_cases hindex : index < pre.length
      · simp only [Expr.shiftFrom, if_neg (Nat.not_le.mpr hindex)]
        apply RuntimeTyping.var (scheme := scheme) (args := args)
        · rw [List.getElem?_append_left hindex]
          rwa [List.getElem?_append_left hindex] at lookup
        · exact schemeWF
        · exact lengthEq
        · exact argsWF
      · have hle : pre.length ≤ index := Nat.le_of_not_gt hindex
        simp only [Expr.shiftFrom, if_pos hle]
        apply RuntimeTyping.var (scheme := scheme) (args := args)
        · rw [List.getElem?_append_right hle] at lookup
          rw [List.getElem?_append_right (by omega : pre.length ≤ index + 1)]
          have hsub : index + 1 - pre.length = (index - pre.length) + 1 := by omega
          rw [hsub, List.getElem?_cons_succ]
          exact lookup
        · exact schemeWF
        · exact lengthEq
        · exact argsWF
  | lambda paramWF _ bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.lambda paramWF
      have shifted := bodyIH (PolyTy.mono paramTy :: pre) post
        (by simp [envEq]) insertedWF
      simpa only [List.cons_append, List.length_cons] using shifted
  | const hscheme hwf hlen hargs =>
      intro pre post envEq insertedWF
      simpa only [Expr.shiftFrom] using
        (RuntimeTyping.const hscheme hwf hlen hargs)
  | app _ _ functionIH argumentIH =>
      intro pre post envEq insertedWF
      exact .app (functionIH pre post envEq insertedWF)
        (argumentIH pre post envEq insertedWF)
  | letMono rhsWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.letMono rhsWF
      · exact rhsIH pre post envEq insertedWF
      · have shifted := bodyIH (PolyTy.mono rhsTy :: pre) post
          (by simp [envEq]) insertedWF
        simpa only [List.cons_append, List.length_cons] using shifted
  | letPoly schemeWF ctxWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.letPoly (scheme := scheme) schemeWF
      · rw [envEq] at ctxWF
        exact ctxWF_insert ctxWF insertedWF
      · exact rhsIH pre post envEq
          (schemeWF_weakenRigids insertedWF (Nat.le_add_right _ _))
      · have shifted := bodyIH (scheme :: pre) post
          (by simp [envEq]) insertedWF
        simpa only [List.cons_append, List.length_cons] using shifted
  | fix selfWF _ bodyIH =>
      expose_names
      intro pre post envEq insertedWF
      simp only [Expr.shiftFrom]
      apply RuntimeTyping.fix selfWF
      have shifted := bodyIH (PolyTy.mono selfTy :: pre) post
        (by simp [envEq]) insertedWF
      simpa only [List.cons_append, List.length_cons] using shifted

/-- Inserting a well-formed scheme at the head of the term context preserves
typing after shifting all free term indices by one. -/
theorem weakenHead
    (typing : RuntimeTyping sig rigidCount ctx expr ty)
    (insertedWF : inserted.WF rigidCount) :
    RuntimeTyping sig rigidCount (inserted :: ctx) (expr.shiftFrom 0 1) ty := by
  simpa using weakenAt typing [] ctx rfl insertedWF

end RuntimeTyping
end EPL

namespace EPL

private theorem openWith_nil_of_scoped_zero
    {ty : Ty} {rigidCount : Nat}
    (hscoped : ty.Scoped rigidCount 0) :
    ty.openWith [] = ty := by
  induction hscoped with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.openWith, ihDomain, ihCodomain]
  | bvar h => omega
  | rigid => rfl
  | mvar => rfl
  | con => rfl
  | app _ _ ihDomain ihCodomain =>
      simp only [Ty.openWith, ihDomain, ihCodomain]

private theorem openWith_eq_self_of_scoped_zero
    {ty : Ty} {rigidCount : Nat}
    (hscoped : ty.Scoped rigidCount 0) (replacements : List Ty) :
    ty.openWith replacements = ty := by
  induction hscoped with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.openWith, ihDomain, ihCodomain]
  | bvar h => omega
  | rigid => rfl
  | mvar => rfl
  | con => rfl
  | app _ _ ihDomain ihCodomain =>
      simp only [Ty.openWith, ihDomain, ihCodomain]

/-- A monomorphic runtime typing derivation is the unique instance of its
zero-binder scheme. -/
theorem RuntimeHasScheme.mono
    (typeWF : ty.WF rigidCount 0)
    (typing : RuntimeTyping sig rigidCount ctx expr ty) :
    RuntimeHasScheme sig rigidCount ctx expr (PolyTy.mono ty) := by
  refine ⟨typeWF, ?_⟩
  intro larger hscope args hlen _
  have : args = [] := List.length_eq_zero_iff.mp (by simpa [PolyTy.mono] using hlen)
  subst args
  simpa only [PolyTy.openWith, PolyTy.mono,
    openWith_nil_of_scoped_zero typeWF.1] using typing.weakenRigids hscope

/-- Replace one contiguous block of rigid levels, removing that block from all
higher levels. The `extra` levels used in the proofs below are the fresh blocks
introduced by nested explicit schemes. -/
private def instantiateRigids (base count : Nat) (args : List Ty) : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (instantiateRigids base count args domain)
        (instantiateRigids base count args codomain)
  | .bvar index => .bvar index
  | .rigid level =>
      if level < base then .rigid level
      else if level - base < count then
        (args[level - base]?).getD (.rigid level)
      else .rigid (level - count)
  | .mvar id => .mvar id
  | .con id => .con id
  | .app function argument =>
      .app (instantiateRigids base count args function)
        (instantiateRigids base count args argument)

private def instantiateSchemeRigids (base count : Nat) (args : List Ty)
    (scheme : PolyTy) : PolyTy :=
  ⟨scheme.paramCount, instantiateRigids base count args scheme.body⟩

private def instantiateCtxRigids (base count : Nat) (args : List Ty)
    (ctx : Ctx) : Ctx :=
  ctx.map (instantiateSchemeRigids base count args)

private theorem scoped_mono
    {ty : Ty} {rigidCount binderCount larger largerBinders : Nat}
    (hscoped : ty.Scoped rigidCount binderCount)
    (hrigid : rigidCount ≤ larger)
    (hbinders : binderCount ≤ largerBinders) :
    ty.Scoped larger largerBinders := by
  induction hscoped with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain => exact .arrow ihDomain ihCodomain
  | bvar h => exact .bvar (Nat.lt_of_lt_of_le h hbinders)
  | rigid h => exact .rigid (Nat.lt_of_lt_of_le h hrigid)
  | mvar id => exact .mvar id
  | con id => exact .con id
  | app _ _ ihDomain ihCodomain => exact .app ihDomain ihCodomain

private theorem instantiateRigids_scoped
    (hscoped : ty.Scoped (base + count + extra) binderCount)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF base 0) :
    (instantiateRigids base count args ty).Scoped (base + extra) binderCount := by
  induction ty with
  | prim => exact .prim
  | arrow domain codomain domainIH codomainIH =>
      cases hscoped with
      | arrow domainScoped codomainScoped =>
          exact .arrow (domainIH domainScoped) (codomainIH codomainScoped)
  | con id => exact .con id
  | app function argument functionIH argumentIH =>
      cases hscoped with
      | app functionScoped argumentScoped =>
          exact .app (functionIH functionScoped) (argumentIH argumentScoped)
  | bvar index =>
      cases hscoped with
      | bvar h => exact .bvar h
  | rigid level =>
      cases hscoped with
      | rigid hlevel =>
          simp only [instantiateRigids]
          split <;> rename_i hbelow
          · exact .rigid (by omega)
          · split <;> rename_i hblock
            · have hindex : level - base < args.length := by simpa [hlen] using hblock
              have hget : args[level - base]? = some args[level - base] :=
                List.getElem?_eq_getElem hindex
              simp only [hget, Option.getD_some]
              exact scoped_mono (argsWF args[level - base] (List.getElem_mem hindex)).1
                (by omega) (by omega)
            · exact .rigid (by omega)
  | mvar id => exact .mvar id

private theorem instantiateRigids_metaFree
    (free : ty.MetaFree)
    (argsFree : ∀ arg ∈ args, arg.MetaFree) :
    (instantiateRigids base count args ty).MetaFree := by
  induction ty with
  | prim => exact .prim
  | arrow domain codomain domainIH codomainIH =>
      cases free with
      | arrow domainFree codomainFree =>
          exact .arrow (domainIH domainFree) (codomainIH codomainFree)
  | con id => exact .con
  | app function argument functionIH argumentIH =>
      cases free with
      | app functionFree argumentFree =>
          exact .app (functionIH functionFree) (argumentIH argumentFree)
  | bvar => exact .bvar
  | rigid level =>
      simp only [instantiateRigids]
      split
      · exact .rigid
      · split
        · cases hget : args[level - base]? with
          | none => exact .rigid
          | some arg => exact argsFree arg (List.mem_of_getElem? hget)
        · exact .rigid
  | mvar => cases free

private theorem instantiateRigids_wf
    (wf : ty.WF (base + count + extra) binderCount)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF base 0) :
    (instantiateRigids base count args ty).WF (base + extra) binderCount :=
  ⟨instantiateRigids_scoped wf.1 hlen argsWF,
    instantiateRigids_metaFree wf.2 (fun arg harg => (argsWF arg harg).2)⟩

private theorem instantiateSchemeRigids_wf
    (wf : scheme.WF (base + count + extra))
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF base 0) :
    (instantiateSchemeRigids base count args scheme).WF (base + extra) :=
  instantiateRigids_wf wf hlen argsWF

private theorem instantiateCtxRigids_wf
    (wf : ctx.WF (base + count + extra))
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF base 0) :
    (instantiateCtxRigids base count args ctx).WF (base + extra) := by
  intro scheme hscheme
  rw [instantiateCtxRigids] at hscheme
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hscheme
  exact instantiateSchemeRigids_wf (wf original horiginal) hlen argsWF

private theorem instantiateRigids_openWith (ty : Ty)
    (argsScoped : ∀ arg ∈ args, arg.Scoped base 0) :
    instantiateRigids base count args (ty.openWith replacements) =
      (instantiateRigids base count args ty).openWith
        (replacements.map (instantiateRigids base count args)) := by
  induction ty with
  | prim => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [Ty.openWith, instantiateRigids, domainIH, codomainIH]
  | con => rfl
  | app domain codomain domainIH codomainIH =>
      simp only [Ty.openWith, instantiateRigids, domainIH, codomainIH]
  | bvar index =>
      simp only [Ty.openWith, instantiateRigids, List.getElem?_map]
      cases replacements[index]? <;> rfl
  | rigid level =>
      simp only [Ty.openWith, instantiateRigids]
      split
      · rfl
      · split
        · cases hget : args[level - base]? with
          | none => rfl
          | some arg =>
              exact (openWith_eq_self_of_scoped_zero
                (argsScoped arg (List.mem_of_getElem? hget)) _).symm
        · rfl
  | mvar id => rfl

private theorem instantiateRigids_rigidBlock :
    (rigidBlock (base + count + extra) amount).map
        (instantiateRigids base count args) =
      rigidBlock (base + extra) amount := by
  simp only [rigidBlock, List.map_map]
  apply List.map_congr_left
  intro offset hoffset
  have hoffset' : offset < amount := List.mem_range.mp hoffset
  simp only [Function.comp_apply, instantiateRigids]
  split <;> rename_i hbelow
  · omega
  · split <;> rename_i hblock
    · omega
    · congr 1
      omega

private theorem instantiateRigids_openRigids (scheme : PolyTy)
    (argsScoped : ∀ arg ∈ args, arg.Scoped base 0) :
    instantiateRigids base count args
        (scheme.openRigids (base + count + extra)) =
      (instantiateSchemeRigids base count args scheme).openRigids (base + extra) := by
  simp only [PolyTy.openRigids, PolyTy.openWith, instantiateSchemeRigids,
    instantiateRigids_openWith _ argsScoped, instantiateRigids_rigidBlock]

private theorem instantiateRigids_eq_self
    (hscoped : ty.Scoped base binderCount) :
    instantiateRigids base count args ty = ty := by
  induction hscoped with
  | prim => rfl
  | arrow _ _ domainIH codomainIH =>
      simp only [instantiateRigids, domainIH, codomainIH]
  | bvar => rfl
  | rigid hlevel => simp [instantiateRigids, hlevel]
  | mvar => rfl
  | con => rfl
  | app _ _ domainIH codomainIH =>
      simp only [instantiateRigids, domainIH, codomainIH]

private theorem instantiateSchemeRigids_eq_self
    (wf : scheme.WF base) :
    instantiateSchemeRigids base count args scheme = scheme := by
  cases scheme
  simp only [instantiateSchemeRigids]
  rw [instantiateRigids_eq_self wf.1]

private theorem instantiateCtxRigids_eq_self
    (wf : ctx.WF base) :
    instantiateCtxRigids base count args ctx = ctx := by
  induction ctx with
  | nil => rfl
  | cons scheme tail ih =>
      simp only [instantiateCtxRigids, List.map_cons, List.cons.injEq]
      constructor
      · exact instantiateSchemeRigids_eq_self (wf scheme (by simp))
      · exact ih (fun candidate hcandidate => wf candidate (by simp [hcandidate]))

private def instantiateRigidsTo (source target count : Nat) (args : List Ty) : Ty → Ty
  | .prim p => .prim p
  | .arrow domain codomain =>
      .arrow (instantiateRigidsTo source target count args domain)
        (instantiateRigidsTo source target count args codomain)
  | .bvar index => .bvar index
  | .rigid level =>
      if level < source then .rigid level
      else if level - source < count then
        (args[level - source]?).getD (.rigid level)
      else .rigid (target + (level - (source + count)))
  | .mvar id => .mvar id
  | .con id => .con id
  | .app function argument =>
      .app (instantiateRigidsTo source target count args function)
        (instantiateRigidsTo source target count args argument)

private def instantiateSchemeRigidsTo (source target count : Nat) (args : List Ty)
    (scheme : PolyTy) : PolyTy :=
  ⟨scheme.paramCount, instantiateRigidsTo source target count args scheme.body⟩

/-- Instantiating rigid levels leaves a primitive operator's type unchanged. -/
private theorem primOp_ty_instantiateRigidsTo {sig : Signature} {op : PrimOp} {ty : Ty}
    (hop : op.ty sig = some ty) {source target count : Nat} {args : List Ty} :
    instantiateRigidsTo source target count args ty = ty := by
  cases op with
  | intAdd =>
      simp only [PrimOp.ty, Option.some.injEq] at hop
      subst hop
      rfl
  | intSub =>
      simp only [PrimOp.ty, Option.some.injEq] at hop
      subst hop
      rfl
  | intLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
        subst hop
        rfl
      · simp [PrimOp.ty, if_neg hb] at hop
  | charLt =>
      by_cases hb : sig.HasBool
      · simp only [PrimOp.ty, if_pos hb, Option.some.injEq] at hop
        subst hop
        rfl
      · simp [PrimOp.ty, if_neg hb] at hop

private def instantiateCtxRigidsTo (source target count : Nat) (args : List Ty)
    (ctx : Ctx) : Ctx :=
  ctx.map (instantiateSchemeRigidsTo source target count args)

private theorem instantiateRigidsTo_scoped
    (hscoped : ty.Scoped (source + count + extra) binderCount)
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    (instantiateRigidsTo source target count args ty).Scoped
      (target + extra) binderCount := by
  induction ty with
  | prim => exact .prim
  | arrow domain codomain domainIH codomainIH =>
      cases hscoped with
      | arrow domainScoped codomainScoped =>
          exact .arrow (domainIH domainScoped) (codomainIH codomainScoped)
  | con id => exact .con id
  | app function argument functionIH argumentIH =>
      cases hscoped with
      | app functionScoped argumentScoped =>
          exact .app (functionIH functionScoped) (argumentIH argumentScoped)
  | bvar index =>
      cases hscoped with
      | bvar h => exact .bvar h
  | rigid level =>
      cases hscoped with
      | rigid hlevel =>
          simp only [instantiateRigidsTo]
          split <;> rename_i hbelow
          · exact .rigid (by omega)
          · split <;> rename_i hblock
            · have hindex : level - source < args.length := by simpa [hlen] using hblock
              have hget : args[level - source]? = some args[level - source] :=
                List.getElem?_eq_getElem hindex
              simp only [hget, Option.getD_some]
              exact scoped_mono (argsWF args[level - source] (List.getElem_mem hindex)).1
                (by omega) (by omega)
            · exact .rigid (by omega)
  | mvar id => exact .mvar id

private theorem instantiateRigidsTo_metaFree
    (free : ty.MetaFree)
    (argsFree : ∀ arg ∈ args, arg.MetaFree) :
    (instantiateRigidsTo source target count args ty).MetaFree := by
  induction ty with
  | prim => exact .prim
  | arrow domain codomain domainIH codomainIH =>
      cases free with
      | arrow domainFree codomainFree =>
          exact .arrow (domainIH domainFree) (codomainIH codomainFree)
  | con id => exact .con
  | app function argument functionIH argumentIH =>
      cases free with
      | app functionFree argumentFree =>
          exact .app (functionIH functionFree) (argumentIH argumentFree)
  | bvar => exact .bvar
  | rigid level =>
      simp only [instantiateRigidsTo]
      split
      · exact .rigid
      · split
        · cases hget : args[level - source]? with
          | none => exact .rigid
          | some arg => exact argsFree arg (List.mem_of_getElem? hget)
        · exact .rigid
  | mvar => cases free

private theorem instantiateRigidsTo_wf
    (wf : ty.WF (source + count + extra) binderCount)
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    (instantiateRigidsTo source target count args ty).WF
      (target + extra) binderCount :=
  ⟨instantiateRigidsTo_scoped wf.1 hsource hlen argsWF,
    instantiateRigidsTo_metaFree wf.2 (fun arg harg => (argsWF arg harg).2)⟩

private theorem instantiateSchemeRigidsTo_wf
    (wf : scheme.WF (source + count + extra))
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    (instantiateSchemeRigidsTo source target count args scheme).WF
      (target + extra) :=
  instantiateRigidsTo_wf wf hsource hlen argsWF

private theorem instantiateCtxRigidsTo_wf
    (wf : ctx.WF (source + count + extra))
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    (instantiateCtxRigidsTo source target count args ctx).WF (target + extra) := by
  intro scheme hscheme
  rw [instantiateCtxRigidsTo] at hscheme
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hscheme
  exact instantiateSchemeRigidsTo_wf (wf original horiginal) hsource hlen argsWF

private theorem instantiateRigidsTo_openWith (ty : Ty)
    (argsScoped : ∀ arg ∈ args, arg.Scoped target 0) :
    instantiateRigidsTo source target count args (ty.openWith replacements) =
      (instantiateRigidsTo source target count args ty).openWith
        (replacements.map (instantiateRigidsTo source target count args)) := by
  induction ty with
  | prim => rfl
  | arrow domain codomain domainIH codomainIH =>
      simp only [Ty.openWith, instantiateRigidsTo, domainIH, codomainIH]
  | con => rfl
  | app domain codomain domainIH codomainIH =>
      simp only [Ty.openWith, instantiateRigidsTo, domainIH, codomainIH]
  | bvar index =>
      simp only [Ty.openWith, instantiateRigidsTo, List.getElem?_map]
      cases replacements[index]? <;> rfl
  | rigid level =>
      simp only [Ty.openWith, instantiateRigidsTo]
      split
      · rfl
      · split
        · cases hget : args[level - source]? with
          | none => rfl
          | some arg =>
              exact (openWith_eq_self_of_scoped_zero
                (argsScoped arg (List.mem_of_getElem? hget)) _).symm
        · rfl
  | mvar => rfl

private theorem instantiateRigidsTo_nestedBlock :
    (rigidBlock (source + count + extra) amount).map
        (instantiateRigidsTo source target count args) =
      rigidBlock (target + extra) amount := by
  simp only [rigidBlock, List.map_map]
  apply List.map_congr_left
  intro offset hoffset
  have hoffset' : offset < amount := List.mem_range.mp hoffset
  simp only [Function.comp_apply, instantiateRigidsTo]
  split <;> rename_i hbelow
  · omega
  · split <;> rename_i hblock
    · omega
    · congr 1
      omega

private theorem instantiateRigidsTo_openRigids (scheme : PolyTy)
    (argsScoped : ∀ arg ∈ args, arg.Scoped target 0) :
    instantiateRigidsTo source target count args
        (scheme.openRigids (source + count + extra)) =
      (instantiateSchemeRigidsTo source target count args scheme).openRigids
        (target + extra) := by
  simp only [PolyTy.openRigids, PolyTy.openWith, instantiateSchemeRigidsTo,
    instantiateRigidsTo_openWith _ argsScoped, instantiateRigidsTo_nestedBlock]

private theorem instantiateRigidsTo_genericBlock
    (hlen : args.length = count) :
    (rigidBlock source count).map
        (instantiateRigidsTo source target count args) = args := by
  apply List.ext_getElem
  · simp [rigidBlock, hlen]
  · intro index hleft hright
    have hindex : index < count := by simpa [rigidBlock] using hleft
    simp only [rigidBlock, List.getElem_map, List.getElem_range,
      instantiateRigidsTo]
    split <;> rename_i hbelow
    · omega
    · split <;> rename_i hblock
      · have hget : args[index]? = some args[index] :=
          List.getElem?_eq_getElem (by simpa [hlen] using hindex)
        simp [hget]
      · omega

private theorem instantiateRigidsTo_generic (scheme : PolyTy)
    (hcount : scheme.paramCount = count)
    (hlen : args.length = count)
    (argsScoped : ∀ arg ∈ args, arg.Scoped target 0) :
    instantiateRigidsTo source target count args (scheme.openRigids source) =
      (instantiateSchemeRigidsTo source target count args scheme).openWith args := by
  subst count
  simp only [PolyTy.openRigids, PolyTy.openWith, instantiateSchemeRigidsTo,
    instantiateRigidsTo_openWith _ argsScoped,
    instantiateRigidsTo_genericBlock hlen]

private theorem instantiateRigidsTo_eq_self
    (hscoped : ty.Scoped source binderCount) :
    instantiateRigidsTo source target count args ty = ty := by
  induction hscoped with
  | prim => rfl
  | arrow _ _ domainIH codomainIH =>
      simp only [instantiateRigidsTo, domainIH, codomainIH]
  | bvar => rfl
  | rigid hlevel => simp [instantiateRigidsTo, hlevel]
  | mvar => rfl
  | con => rfl
  | app _ _ domainIH codomainIH =>
      simp only [instantiateRigidsTo, domainIH, codomainIH]

private theorem instantiateSchemeRigidsTo_eq_self
    (wf : scheme.WF source) :
    instantiateSchemeRigidsTo source target count args scheme = scheme := by
  cases scheme
  simp only [instantiateSchemeRigidsTo]
  rw [instantiateRigidsTo_eq_self wf.1]

private theorem instantiateCtxRigidsTo_eq_self
    (wf : ctx.WF source) :
    instantiateCtxRigidsTo source target count args ctx = ctx := by
  induction ctx with
  | nil => rfl
  | cons scheme tail ih =>
      simp only [instantiateCtxRigidsTo, List.map_cons, List.cons.injEq]
      constructor
      · exact instantiateSchemeRigidsTo_eq_self (wf scheme (by simp))
      · exact ih (fun candidate hcandidate => wf candidate (by simp [hcandidate]))

private theorem instantiateTypingTo
    (typing : RuntimeTyping sig old ctx expr ty)
    (hold : old = source + count + extra)
    (hsource : source ≤ target)
    (hlen : args.length = count)
    (argsWF : ∀ arg ∈ args, arg.WF target 0) :
    RuntimeTyping sig (target + extra)
      (instantiateCtxRigidsTo source target count args ctx) expr
      (instantiateRigidsTo source target count args ty) := by
  induction typing generalizing extra with
  | primLit =>
      cases_type PrimLit <;> exact .primLit
  | primOp hop =>
      exact .primOp (by
        rw [primOp_ty_instantiateRigidsTo hop]
        exact hop)
  | @var ctx index scheme instArgs rigidCount hlookup schemeWF instLength instWF =>
      have schemeWF' : scheme.WF (source + count + extra) := by
        simpa [hold] using schemeWF
      have hlookup' :
          (instantiateCtxRigidsTo source target count args ctx)[index]? =
            some (instantiateSchemeRigidsTo source target count args scheme) := by
        simp [instantiateCtxRigidsTo, List.getElem?_map, hlookup]
      have opened := RuntimeTyping.var (sig := sig)
        (args := instArgs.map (instantiateRigidsTo source target count args)) hlookup'
        (instantiateSchemeRigidsTo_wf schemeWF' hsource hlen argsWF)
        (by simpa using instLength)
        (fun transformed htransformed => by
          obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp htransformed
          have originalWF : original.WF (source + count + extra) 0 := by
            simpa [hold] using instWF original horiginal
          exact instantiateRigidsTo_wf originalWF hsource hlen argsWF)
      have hopen :
          instantiateRigidsTo source target count args
              (scheme.openWith instArgs) =
            (instantiateSchemeRigidsTo source target count args scheme).openWith
              (instArgs.map (instantiateRigidsTo source target count args)) := by
        exact instantiateRigidsTo_openWith
          (source := source) (target := target) (count := count) (args := args)
          scheme.body (replacements := instArgs)
          (fun arg harg => (argsWF arg harg).1)
      rw [hopen]
      exact opened
  | @const c scheme instArgs rigidCount ctx hscheme schemeWF instLength instWF =>
      let transformedArgs := instArgs.map (instantiateRigidsTo source target count args)
      have hlen' : transformedArgs.length = scheme.paramCount := by
        simpa [transformedArgs] using instLength
      have hargs' : ∀ arg ∈ transformedArgs, arg.WF (target + extra) 0 := by
        intro arg harg
        obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp harg
        have originalWF : original.WF (source + count + extra) 0 := by
          simpa [hold] using instWF original horiginal
        exact instantiateRigidsTo_wf originalWF hsource hlen argsWF
      have hopen :
          instantiateRigidsTo source target count args (scheme.openWith instArgs) =
            (instantiateRigidsTo source target count args scheme.body).openWith
              transformedArgs :=
        instantiateRigidsTo_openWith
          (source := source) (target := target) (count := count) (args := args)
          scheme.body (replacements := instArgs)
          (fun arg harg => (argsWF arg harg).1)
      have hbody : instantiateRigidsTo source target count args scheme.body = scheme.body :=
        instantiateRigidsTo_eq_self
          (scoped_mono schemeWF.1 (Nat.zero_le source) (le_refl scheme.paramCount))
      have hgoal : instantiateRigidsTo source target count args (scheme.openWith instArgs) =
          scheme.openWith transformedArgs := by
        rw [hopen, hbody]
        rfl
      rw [hgoal]
      exact RuntimeTyping.const (sig := sig) hscheme schemeWF hlen' hargs'
  | @lambda rigidCount paramTy ctx body bodyTy ann paramWF bodyTyping bodyIH =>
      have paramWF' : paramTy.WF (source + count + extra) 0 := by
        simpa [hold] using paramWF
      apply RuntimeTyping.lambda
        (instantiateRigidsTo_wf paramWF' hsource hlen argsWF)
      simpa [instantiateCtxRigidsTo, instantiateSchemeRigidsTo, PolyTy.mono] using
        bodyIH hold
  | @app rigidCount ctx function argumentTy resultTy argument
      functionTyping argumentTyping functionIH argumentIH =>
      exact RuntimeTyping.app (functionIH hold) (argumentIH hold)
  | @letMono rigidCount ctx rhs rhsTy body bodyTy ann rhsWF rhsTyping bodyTyping
      rhsIH bodyIH =>
      have rhsWF' : rhsTy.WF (source + count + extra) 0 := by
        simpa [hold] using rhsWF
      apply RuntimeTyping.letMono
        (instantiateRigidsTo_wf rhsWF' hsource hlen argsWF)
      · exact rhsIH hold
      · simpa [instantiateCtxRigidsTo, instantiateSchemeRigidsTo, PolyTy.mono] using
          bodyIH hold
  | @letPoly rigidCount ctx rhs scheme body bodyTy ann schemeWF ctxWF rhsTyping
      bodyTyping rhsIH bodyIH =>
      have schemeWF' : scheme.WF (source + count + extra) := by
        simpa [hold] using schemeWF
      have ctxWF' : ctx.WF (source + count + extra) := by
        simpa [hold] using ctxWF
      let transformed := instantiateSchemeRigidsTo source target count args scheme
      apply RuntimeTyping.letPoly
        (scheme := transformed)
        (instantiateSchemeRigidsTo_wf schemeWF' hsource hlen argsWF)
        (instantiateCtxRigidsTo_wf ctxWF' hsource hlen argsWF)
      · have rhsInstantiated := rhsIH (extra := extra + scheme.paramCount) (by omega)
        rw [hold] at rhsInstantiated
        have hopen :
            instantiateRigidsTo source target count args
                (scheme.openRigids (source + count + extra)) =
              transformed.openRigids (target + extra) := by
          exact instantiateRigidsTo_openRigids
            (source := source) (target := target) (count := count) (args := args)
            (extra := extra) scheme (fun arg harg => (argsWF arg harg).1)
        rw [hopen] at rhsInstantiated
        simpa only [Nat.add_assoc] using rhsInstantiated
      · simpa [transformed, instantiateCtxRigidsTo] using bodyIH hold
  | @fix rigidCount selfTy ctx body selfWF bodyTyping bodyIH =>
      have selfWF' : selfTy.WF (source + count + extra) 0 := by
        simpa [hold] using selfWF
      apply RuntimeTyping.fix
        (instantiateRigidsTo_wf selfWF' hsource hlen argsWF)
      simpa [instantiateCtxRigidsTo, instantiateSchemeRigidsTo, PolyTy.mono] using
        bodyIH hold

namespace RuntimeTyping

/-- Checking a runtime expression once at a fresh rigid block establishes all
well-formed semantic instances of that exact written scheme. -/
theorem genericHasScheme
    (schemeWF : scheme.WF rigidCount)
    (ctxWF : ctx.WF rigidCount)
    (generic : RuntimeTyping sig (rigidCount + scheme.paramCount) ctx expr
      (scheme.openRigids rigidCount)) :
    RuntimeHasScheme sig rigidCount ctx expr scheme := by
  refine ⟨schemeWF, ?_⟩
  intro larger hscope args hlen argsWF
  have instantiated := instantiateTypingTo
    (source := rigidCount) (target := larger) (count := scheme.paramCount)
    (args := args) (extra := 0) generic rfl hscope hlen argsWF
  have hctx :
      instantiateCtxRigidsTo rigidCount larger scheme.paramCount args ctx = ctx :=
    instantiateCtxRigidsTo_eq_self ctxWF
  have hscheme :
      instantiateSchemeRigidsTo rigidCount larger scheme.paramCount args scheme =
        scheme :=
    instantiateSchemeRigidsTo_eq_self schemeWF
  have hty :
      instantiateRigidsTo rigidCount larger scheme.paramCount args
          (scheme.openRigids rigidCount) =
        scheme.openWith args := by
    rw [instantiateRigidsTo_generic scheme rfl hlen
      (fun arg harg => (argsWF arg harg).1), hscheme]
  simpa only [Nat.add_zero, hctx, hty] using instantiated

end RuntimeTyping
end EPL

namespace EPL
namespace RuntimeTyping

private theorem scoped_monoRigids_2
    {ty : Ty} {rigidCount binderCount larger : Nat}
    (hScoped : ty.Scoped rigidCount binderCount)
    (hscope : rigidCount ≤ larger) :
    ty.Scoped larger binderCount := by
  induction hScoped with
  | prim => exact .prim
  | arrow _ _ domainIH codomainIH => exact .arrow domainIH codomainIH
  | bvar hindex => exact .bvar hindex
  | rigid hlevel => exact .rigid (hlevel.trans_le hscope)
  | mvar id => exact .mvar id
  | con id => exact .con id
  | app _ _ domainIH codomainIH => exact .app domainIH codomainIH

private theorem wf_monoRigids_2
    {ty : Ty} {rigidCount binderCount larger : Nat}
    (wf : ty.WF rigidCount binderCount)
    (hscope : rigidCount ≤ larger) :
    ty.WF larger binderCount :=
  ⟨scoped_monoRigids_2 wf.1 hscope, wf.2⟩

private theorem schemeWF_monoRigids_2
    {scheme : PolyTy} {rigidCount larger : Nat}
    (wf : scheme.WF rigidCount)
    (hscope : rigidCount ≤ larger) :
    scheme.WF larger :=
  wf_monoRigids_2 wf hscope

private theorem ctxWF_monoRigids_2
    {ctx : Ctx} {rigidCount larger : Nat}
    (wf : ctx.WF rigidCount)
    (hscope : rigidCount ≤ larger) :
    ctx.WF larger := by
  intro scheme hmem
  exact schemeWF_monoRigids_2 (wf scheme hmem) hscope

private theorem ctxWF_cons
    {head : PolyTy} {tail : Ctx} {rigidCount : Nat}
    (headWF : head.WF rigidCount)
    (tailWF : Ctx.WF rigidCount tail) :
    Ctx.WF rigidCount (head :: tail) := by
  intro scheme hmem
  rcases List.mem_cons.mp hmem with rfl | htail
  · exact headWF
  · exact tailWF scheme htail

private theorem ctxWF_remove_middle
    {pre post : Ctx} {removed : PolyTy} {rigidCount : Nat}
    (wf : (pre ++ [removed] ++ post : Ctx).WF rigidCount) :
    (pre ++ post : Ctx).WF rigidCount := by
  intro scheme hmem
  apply wf scheme
  simp only [List.mem_append, List.mem_singleton] at hmem ⊢
  tauto

private theorem shiftFrom_zero (expr : Expr T) :
    expr.shiftFrom threshold 0 = expr := by
  induction expr generalizing threshold with
  | primLit => rfl
  | primOp => rfl
  | var index => simp [Expr.shiftFrom]
  | lambda ann body ih => simp [Expr.shiftFrom, ih]
  | app function argument ihFunction ihArgument =>
      simp [Expr.shiftFrom, ihFunction, ihArgument]
  | letIn ann rhs body ihRhs ihBody =>
      simp [Expr.shiftFrom, ihRhs, ihBody]
  | fix ann body ih => simp [Expr.shiftFrom, ih]
  | const c => rfl

private theorem shiftFrom_add_zero (expr : Expr T) :
    (expr.shiftFrom threshold first).shiftFrom threshold second =
      expr.shiftFrom threshold (first + second) := by
  induction expr generalizing threshold with
  | primLit => rfl
  | primOp => rfl
  | var index =>
      by_cases h : threshold ≤ index
      · simp [Expr.shiftFrom, h, h.trans (Nat.le_add_right _ _), Nat.add_assoc]
      · simp [Expr.shiftFrom, h]
  | lambda ann body ih => simp [Expr.shiftFrom, ih]
  | app function argument ihFunction ihArgument =>
      simp [Expr.shiftFrom, ihFunction, ihArgument]
  | letIn ann rhs body ihRhs ihBody =>
      simp [Expr.shiftFrom, ihRhs, ihBody]
  | fix ann body ih => simp [Expr.shiftFrom, ih]
  | const c => rfl

private theorem hasScheme_weakenPrefix
    {rigidCount : Nat} {ctx pre : Ctx} {replacement : RuntimeExpr}
    {scheme : PolyTy}
    (typing : RuntimeHasScheme sig rigidCount ctx replacement scheme)
    (preWF : pre.WF rigidCount) :
    RuntimeHasScheme sig rigidCount (pre ++ ctx)
      (replacement.shiftFrom 0 pre.length) scheme := by
  refine ⟨typing.schemeWF, ?_⟩
  intro larger hscope args hlen hargs
  have baseTyping := typing.typed larger hscope args hlen hargs
  induction pre with
  | nil =>
      simpa only [List.nil_append, List.length_nil,
        shiftFrom_zero] using baseTyping
  | cons head tail tailIH =>
      have headWF : head.WF rigidCount := preWF head (by simp)
      have tailWF : Ctx.WF rigidCount tail := by
        intro item hitem
        exact preWF item (by simp [hitem])
      have weakenedTail := tailIH tailWF
      have weakened := RuntimeTyping.weakenHead weakenedTail
        (schemeWF_monoRigids_2 headWF hscope)
      simpa only [List.cons_append, List.length_cons,
        shiftFrom_add_zero, Nat.add_comm] using weakened

private theorem substAt
    (bodyTyping : RuntimeTyping sig rigidCount env body ty) :
    ∀ (pre ctx : Ctx) (target : PolyTy) (replacement : RuntimeExpr),
      env = pre ++ [target] ++ ctx →
      pre.WF rigidCount →
      RuntimeHasScheme sig rigidCount ctx replacement target →
      RuntimeTyping sig rigidCount (pre ++ ctx)
        (body.substN pre.length [replacement]) ty := by
  induction bodyTyping with
  | primLit =>
      intro pre ctx target replacement _ _ _
      exact .primLit
  | primOp hop =>
      intro pre ctx target replacement _ _ _
      exact .primOp hop
  | var lookup schemeWF lengthEq argsWF =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      rw [envEq, List.append_assoc] at lookup
      simp only [Expr.substN]
      by_cases hlt : index < pre.length
      · rw [if_pos hlt]
        apply RuntimeTyping.var (scheme := scheme) (args := args)
        · rw [List.getElem?_append_left hlt]
          rwa [List.getElem?_append_left hlt] at lookup
        · exact schemeWF
        · exact lengthEq
        · exact argsWF
      · rw [if_neg hlt]
        by_cases hselected : index - pre.length < [replacement].length
        · rw [dif_pos hselected]
          simp only [List.length_cons, List.length_nil, Nat.zero_add] at hselected
          have hzero : index - pre.length = 0 := by omega
          have lookup' := lookup
          rw [List.getElem?_append_right (by omega)] at lookup'
          simp only [hzero] at lookup'
          have schemeEq : scheme = target := (Option.some.inj lookup').symm
          subst scheme
          have replacementAtPrefix := hasScheme_weakenPrefix replacementTyping preWF
          have typed : RuntimeTyping sig rigidCount_1 (pre ++ ctx)
              (replacement.shiftFrom 0 pre.length) (target.openWith args) :=
            replacementAtPrefix.typed rigidCount_1 (le_refl rigidCount_1)
              args lengthEq argsWF
          simpa using typed
        · rw [dif_neg hselected]
          have hpre : pre.length ≤ index := Nat.le_of_not_gt hlt
          have hone : [target].length ≤ index - pre.length := by
            simpa using (Nat.le_of_not_gt hselected)
          have hindices :
              index - [replacement].length - pre.length =
                index - pre.length - [target].length := by
            simp only [List.length_cons, List.length_nil, Nat.zero_add]
            omega
          apply RuntimeTyping.var (scheme := scheme) (args := args)
          · rw [List.getElem?_append_right
              (by omega : pre.length ≤ index - [replacement].length)]
            rw [List.getElem?_append_right hpre,
              List.getElem?_append_right hone] at lookup
            rw [hindices]
            exact lookup
          · exact schemeWF
          · exact lengthEq
          · exact argsWF
  | lambda paramWF _ bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      apply RuntimeTyping.lambda paramWF
      have substituted := bodyIH (PolyTy.mono paramTy :: pre) ctx target replacement
        (by simp [envEq, List.append_assoc])
        (ctxWF_cons ⟨paramWF.1, paramWF.2⟩ preWF) replacementTyping
      simpa only [List.cons_append, List.length_cons] using substituted
  | app _ _ functionIH argumentIH =>
      intro pre ctx target replacement envEq preWF replacementTyping
      exact .app (functionIH pre ctx target replacement envEq preWF replacementTyping)
        (argumentIH pre ctx target replacement envEq preWF replacementTyping)
  | const hscheme hwf hlen hargs =>
      intro pre ctx target replacement _ _ _
      simpa only [Expr.substN] using
        (RuntimeTyping.const hscheme hwf hlen hargs)
  | letMono rhsWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      apply RuntimeTyping.letMono rhsWF
      · exact rhsIH pre ctx target replacement envEq preWF replacementTyping
      · have substituted := bodyIH (PolyTy.mono rhsTy :: pre) ctx target replacement
          (by simp [envEq, List.append_assoc])
          (ctxWF_cons ⟨rhsWF.1, rhsWF.2⟩ preWF) replacementTyping
        simpa only [List.cons_append, List.length_cons] using substituted
  | letPoly schemeWF localCtxWF _ _ rhsIH bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      rw [envEq] at localCtxWF
      apply RuntimeTyping.letPoly (scheme := scheme) schemeWF
      · exact ctxWF_remove_middle localCtxWF
      · exact rhsIH pre ctx target replacement envEq
          (ctxWF_monoRigids_2 preWF (Nat.le_add_right _ _))
          ⟨schemeWF_monoRigids_2 replacementTyping.schemeWF (Nat.le_add_right _ _),
            fun larger hscope => replacementTyping.typed larger
              ((Nat.le_add_right _ _).trans hscope)⟩
      · have substituted := bodyIH (scheme :: pre) ctx target replacement
          (by simp [envEq, List.append_assoc])
          (ctxWF_cons schemeWF preWF) replacementTyping
        simpa only [List.cons_append, List.length_cons] using substituted
  | fix selfWF _ bodyIH =>
      expose_names
      intro pre ctx target replacement envEq preWF replacementTyping
      simp only [Expr.substN]
      apply RuntimeTyping.fix selfWF
      have substituted := bodyIH (PolyTy.mono selfTy :: pre) ctx target replacement
        (by simp [envEq, List.append_assoc])
        (ctxWF_cons ⟨selfWF.1, selfWF.2⟩ preWF) replacementTyping
      simpa only [List.cons_append, List.length_cons] using substituted

/-- Replacing the head variable by an expression inhabiting its whole scheme
preserves runtime typing. This is the common substitution principle for beta,
monomorphic lets, explicit-polymorphic lets, and fixed-point unfolding. -/
theorem substScheme
    (replacementTyping : RuntimeHasScheme sig rigidCount ctx replacement scheme)
    (bodyTyping : RuntimeTyping sig rigidCount (scheme :: ctx) body ty) :
    RuntimeTyping sig rigidCount ctx (body.subst1 replacement) ty := by
  simpa [Expr.subst1] using
    substAt bodyTyping [] ctx scheme replacement (by simp) (by simp [Ctx.WF])
      replacementTyping

end RuntimeTyping
end EPL

namespace EPL
namespace RuntimeTyping

private theorem value_const_not_prim {c : DataConst} {args : List RuntimeExpr} {p : PrimTy}
    (hlen : args.length ≤ c.valueArity)
    (typing : RuntimeTyping sig r ctx (Expr.apps (.const c) args) (.prim p)) : False := by
  obtain ⟨scheme, instArgs, argTys, hscheme, hwf, hilen, hiwf, hopen, hforall⟩ :=
    const_spine_inv typing
  cases c with
  | ctor type ctor arity =>
      obtain ⟨decl, fieldTys, hdecl, hctors, hflen, hschemeEq⟩ :=
        Signature.schemeOf_ctor_some hscheme
      subst scheme
      have hilen' : instArgs.length = decl.paramCount := by simpa using hilen
      rw [DataDecl.ctorScheme_openWith decl type fieldTys instArgs hilen'] at hopen
      have hargLen : argTys.length = args.length :=
        (List.Forall₂.length_eq hforall).symm
      have hvalLen : args.length ≤ arity := by
        simpa [DataConst.valueArity] using hlen
      obtain ⟨rest, hrest, hty⟩ :=
        Ty.arrows_eq_arrows_append hopen.symm (by
          simp only [List.length_map]
          omega)
      cases rest with
      | nil => exact Ty.apps_con_ne_prim hty.symm
      | cons x xs => exact Ty.arrow_ne_prim hty.symm
  | elim type ctorCount =>
      obtain ⟨decl, hdecl, hctorsLen, hschemeEq⟩ :=
        Signature.schemeOf_elim_some hscheme
      subst scheme
      have hilen' : instArgs.length = decl.paramCount + 1 := by simpa using hilen
      obtain ⟨p', rr, hp, hplen⟩ := exists_append_singleton_of_length hilen'
      subst hp
      rw [DataDecl.elimScheme_openWith decl type hplen] at hopen
      have hargLen : argTys.length = args.length :=
        (List.Forall₂.length_eq hforall).symm
      have hvalLen : args.length ≤ ctorCount := by
        simpa [DataConst.valueArity] using hlen
      obtain ⟨rest, hrest, hty⟩ :=
        Ty.arrows_eq_arrows_append hopen.symm (by
          simp only [List.length_cons, List.length_map]
          omega)
      have hlenRest : 0 < rest.length := by
        have hcongr := congrArg List.length hrest
        simp only [List.length_append, List.length_cons, List.length_map] at hcongr
        omega
      cases rest with
      | nil => simp at hlenRest
      | cons x xs => exact Ty.arrow_ne_prim hty.symm

private theorem prim_value_canonical {expr : RuntimeExpr} {p : PrimTy}
    (value : Eval.Value expr)
    (typing : RuntimeTyping sig rigidCount ctx expr (.prim p)) :
    ∃ literal, expr = .primLit literal := by
  cases value with
  | primLit => exact ⟨_, rfl⟩
  | primOp =>
      cases typing with
      | primOp hop =>
          obtain ⟨a, b, hab⟩ := primOp_ty_arrow hop
          exact absurd hab.symm Ty.arrow_ne_prim
  | lambda => cases typing
  | primOpPartial _ =>
      cases typing with
      | app hf _ =>
          cases hf with
          | primOp hop =>
              obtain ⟨a, b, hab⟩ := primOp_ty_codomain_arrow hop
              exact absurd hab.symm Ty.arrow_ne_prim
  | const hspine hlen hvals =>
      exfalso
      expose_names
      have hexpr : Expr.apps (.const c) args = expr := by
        have h := Expr.apps_spine expr
        rw [hspine] at h
        exact h
      have typing' : RuntimeTyping sig rigidCount ctx (Expr.apps (.const c) args)
          (.prim p) := by
        rw [hexpr]
        exact typing
      exact value_const_not_prim hlen typing'

private theorem progress_empty (typing : RuntimeTyping sig rigidCount ctx expr ty)
    (empty : ctx = []) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  induction typing with
  | primLit => exact .inl .primLit
  | primOp => exact .inl .primOp
  | var hlookup => simp [empty] at hlookup
  | lambda => exact .inl .lambda
  | app functionTyping argumentTyping functionIH argumentIH =>
      rcases functionIH empty with functionValue | ⟨function', functionStep⟩
      · rcases argumentIH empty with argumentValue | ⟨argument', argumentStep⟩
        · cases functionValue with
          | primLit =>
              cases_type PrimLit <;> cases functionTyping
          | primOp =>
              exact .inl (.primOpPartial argumentValue)
          | lambda =>
              exact .inr ⟨_, .beta argumentValue⟩
          | primOpPartial hleft =>
              cases functionTyping with
              | app operatorTyping leftTyping =>
                  cases operatorTyping with
                  | primOp hop =>
                      obtain ⟨p, q, hα, hβ⟩ := primOp_ty_domain hop
                      obtain ⟨l, rfl⟩ := prim_value_canonical hleft (hα ▸ leftTyping)
                      cases leftTyping
                      obtain ⟨r, rfl⟩ := prim_value_canonical argumentValue (hβ ▸ argumentTyping)
                      cases argumentTyping
                      obtain ⟨result, hresult⟩ := primOp_eval_exists hop rfl rfl
                      exact .inr ⟨result, .primOp hresult⟩
          | const hspine hlen hvals =>
              expose_names
              by_cases hsmall : args.length < c.valueArity
              · refine .inl (Eval.Value.const (Expr.spine_app_spine hspine) ?_ ?_)
                · simpa [List.length_append, List.length_cons] using Nat.succ_le_of_lt hsmall
                · intro arg harg
                  rcases List.mem_append.mp harg with h | h
                  · exact hvals arg h
                  · simp only [List.mem_singleton] at h
                    subst h
                    exact argumentValue
              · have heq : args.length = c.valueArity :=
                  le_antisymm hlen (Nat.le_of_not_gt hsmall)
                cases c with
                | ctor type ctor arity =>
                    exfalso
                    have hfunction : function =
                        Expr.apps (.const (.ctor type ctor arity)) args := by
                      have h := Expr.apps_spine function
                      rw [hspine] at h
                      exact h.symm
                    have ftyping := functionTyping
                    rw [hfunction] at ftyping
                    obtain ⟨scheme, instArgs, argTys, hscheme, hwf, hilen, hiwf, hopen, hforall⟩ :=
                      const_spine_inv ftyping
                    obtain ⟨decl, fieldTys, hdecl, hctors, hflen, hschemeEq⟩ :=
                      Signature.schemeOf_ctor_some hscheme
                    subst scheme
                    have hilen' : instArgs.length = decl.paramCount := by simpa using hilen
                    rw [DataDecl.ctorScheme_openWith decl type fieldTys instArgs hilen'] at hopen
                    have hargLen : argTys.length = args.length :=
                      (List.Forall₂.length_eq hforall).symm
                    have hvalLen : args.length ≤ arity := by
                      simpa [DataConst.valueArity] using hlen
                    have hargsArity : args.length = arity := by
                      simpa [DataConst.valueArity] using heq
                    have hlenEq : (fieldTys.map (fun ft => Ty.openWith instArgs ft)).length
                        = argTys.length := by
                      rw [List.length_map, hflen, hargLen, hargsArity]
                    obtain ⟨_, hty⟩ := Ty.arrows_cancel hopen hlenEq
                    exact Ty.apps_con_ne_arrow hty
                | elim type ctorCount =>
                    have hfunction : function =
                        Expr.apps (.const (.elim type ctorCount)) args := by
                      have h := Expr.apps_spine function
                      rw [hspine] at h
                      exact h.symm
                    have hwhole :
                        Expr.apps (.const (.elim type ctorCount)) (args ++ [argument]) =
                          Expr.app function argument := by
                      rw [Expr.apps_append, hfunction]
                      rfl
                    have whtyping := RuntimeTyping.app functionTyping argumentTyping
                    rw [← hwhole] at whtyping
                    obtain ⟨scheme, instArgs, argTys, hscheme, hwf, hilen, hiwf, hopen, hforall⟩ :=
                      const_spine_inv whtyping
                    obtain ⟨decl, hdecl, hctorsLen, hschemeEq⟩ :=
                      Signature.schemeOf_elim_some hscheme
                    subst scheme
                    have hargsCtor : args.length = ctorCount := by
                      simpa [DataConst.valueArity] using heq
                    have hilen' : instArgs.length = decl.paramCount + 1 := by simpa using hilen
                    have hargLen : argTys.length = decl.ctors.length + 1 := by
                      have hlength := List.Forall₂.length_eq hforall
                      simp only [List.length_append, List.length_cons, List.length_nil] at hlength
                      omega
                    obtain ⟨params, r, hparams, hplen, hty, hargTys⟩ :=
                      elim_spine_full hilen' hargLen hopen
                    rw [hargTys] at hforall
                    cases args with
                    | nil =>
                        exfalso
                        simp only [List.length_nil] at hargsCtor
                        simp only [List.nil_append] at hforall
                        cases hforall with
                        | cons hscrut _ =>
                            obtain ⟨d, ctor, arity, fields, fieldTys, hd, hctors, hflen,
                              hargsEq, hfieldsLen, hctorWF, hfieldTypings⟩ :=
                              data_value_canonical argumentValue hscrut
                            have hdEq : d = decl := Option.some.inj (hd.symm.trans hdecl)
                            rw [hdEq] at hctors
                            obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hctors
                            omega
                    | cons s rest =>
                        simp only [List.length_cons] at hargsCtor
                        simp only [List.cons_append] at hforall
                        cases hforall with
                        | cons hscrut _ =>
                            obtain ⟨d, ctor, arity, fields, fieldTys, hd, hctors, hflen,
                              hargsEq, hfieldsLen, hctorWF, hfieldTypings⟩ :=
                              data_value_canonical (hvals s (by simp)) hscrut
                            have hdEq : d = decl := Option.some.inj (hd.symm.trans hdecl)
                            rw [hdEq] at hctors hctorWF
                            have hbranchLen : (rest ++ [argument]).length = ctorCount := by
                              simp only [List.length_append, List.length_cons, List.length_nil]
                              omega
                            have hctorLt : ctor < ctorCount := by
                              obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hctors
                              omega
                            have hspineScrut : s.spine =
                                (.const (.ctor type ctor arity), fields) := by
                              rw [hargsEq]
                              exact Expr.spine_apps _ _
                            have hget : (rest ++ [argument])[ctor]? =
                                some ((rest ++ [argument])[ctor]'(by omega)) :=
                              List.getElem?_eq_getElem (by omega)
                            have hreduce : Eval.reduceConst (.elim type ctorCount)
                                (s :: (rest ++ [argument])) =
                                some (Expr.apps ((rest ++ [argument])[ctor]'(by omega))
                                  (Expr.primLit .unit :: fields)) := by
                              simp only [Eval.reduceConst, hbranchLen, hspineScrut,
                                hfieldsLen, hget, Option.map_some, if_true]
                            refine .inr ⟨Expr.apps ((rest ++ [argument])[ctor]'(by omega))
                                (Expr.primLit .unit :: fields), ?_⟩
                            refine Eval.Step.const (Expr.spine_app_spine hspine) ?_ ?_
                            · intro arg harg
                              rcases List.mem_append.mp harg with h | h
                              · exact hvals arg h
                              · simp only [List.mem_singleton] at h
                                subst h
                                exact argumentValue
                            · simpa only [List.cons_append] using hreduce
        · exact .inr ⟨_, .appArgument functionValue argumentStep⟩
      · exact .inr ⟨_, .appFunction functionStep⟩
  | letMono _ _ _ rhsIH _ =>
      rcases rhsIH empty with rhsValue | ⟨rhs', rhsStep⟩
      · exact .inr ⟨_, .letValue rhsValue⟩
      · exact .inr ⟨_, .letRhs rhsStep⟩
  | letPoly _ _ _ _ rhsIH _ =>
      rcases rhsIH empty with rhsValue | ⟨rhs', rhsStep⟩
      · exact .inr ⟨_, .letValue rhsValue⟩
      · exact .inr ⟨_, .letRhs rhsStep⟩
  | fix => exact .inr ⟨_, .fixUnfold⟩
  | const hscheme hwf hlen hargs =>
      exact .inl (Eval.Value.const rfl (Nat.zero_le _) (by simp))

/-- Closed, well-typed runtime terms are values or can take a step. -/
theorem progress (typing : RuntimeTyping sig 0 [] expr ty) :
    Eval.Value expr ∨ ∃ next, Eval.Step expr next := by
  exact progress_empty typing rfl

/-- A runtime step preserves the exact assigned type. -/
theorem preservation
    (typing : RuntimeTyping sig rigidCount ctx expr ty)
    (step : Eval.Step expr next) :
    RuntimeTyping sig rigidCount ctx next ty := by
  induction step generalizing rigidCount ctx ty with
  | beta argumentValue =>
      cases typing with
      | app functionTyping argumentTyping =>
          cases functionTyping with
          | lambda paramWF bodyTyping =>
              exact substScheme (RuntimeHasScheme.mono paramWF argumentTyping)
                bodyTyping
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
      | letMono rhsWF rhsTyping bodyTyping =>
          exact .letMono rhsWF (rhsIH rhsTyping) bodyTyping
      | letPoly schemeWF ctxWF rhsTyping bodyTyping =>
          exact .letPoly schemeWF ctxWF (rhsIH rhsTyping) bodyTyping
  | letValue rhsValue =>
      cases typing with
      | letMono rhsWF rhsTyping bodyTyping =>
          exact substScheme (RuntimeHasScheme.mono rhsWF rhsTyping) bodyTyping
      | letPoly schemeWF ctxWF rhsTyping bodyTyping =>
          exact substScheme (genericHasScheme schemeWF ctxWF rhsTyping) bodyTyping
  | fixUnfold =>
      cases typing with
      | fix selfWF bodyTyping =>
          expose_names
          have fixed := RuntimeTyping.fix selfWF bodyTyping
          exact substScheme (RuntimeHasScheme.mono selfWF fixed) bodyTyping
  | const hspine hvals hreduce =>
      expose_names
      have hexpr : Expr.apps (.const c) args = Expr.app function argument := by
        have h := Expr.apps_spine (Expr.app function argument)
        rw [hspine] at h
        exact h
      have typing' : RuntimeTyping sig rigidCount ctx (Expr.apps (.const c) args) ty := by
        rw [hexpr]
        exact typing
      obtain ⟨scheme, instArgs, argTys, hscheme, hwf, hilen, hiwf, hopen, hforall⟩ :=
        const_spine_inv typing'
      cases c with
      | ctor type ctor arity =>
          simp [Eval.reduceConst] at hreduce
      | elim type ctorCount =>
          cases args with
          | nil => simp [Eval.reduceConst] at hreduce
          | cons scrutinee branches =>
              simp only [Eval.reduceConst] at hreduce
              by_cases hbranchLen : branches.length = ctorCount
              · rw [if_pos hbranchLen] at hreduce
                cases hsp : scrutinee.spine with
                | mk head fields =>
                    rw [hsp] at hreduce
                    cases head with
                    | const dc =>
                        cases dc with
                        | ctor type' ctor arity =>
                            by_cases hfieldsLen : fields.length = arity
                            · simp only [hfieldsLen, if_true] at hreduce
                              cases hbranch : branches[ctor]? with
                              | none => simp [hbranch] at hreduce
                              | some branch =>
                                  simp only [hbranch, Option.map_some, Option.some.injEq] at hreduce
                                  obtain ⟨decl, hdecl, hctorsLen, hschemeEq⟩ :=
                                    Signature.schemeOf_elim_some hscheme
                                  subst scheme
                                  have hilen' : instArgs.length = decl.paramCount + 1 := by
                                    simpa using hilen
                                  have hargLen : argTys.length = decl.ctors.length + 1 := by
                                    have hlength := List.Forall₂.length_eq hforall
                                    simp only [List.length_cons] at hlength
                                    omega
                                  obtain ⟨params, r, hparams, hplen, hty, hargTys⟩ :=
                                    elim_spine_full hilen' hargLen hopen
                                  rw [hargTys] at hforall
                                  cases hforall with
                                  | cons hscrut htail =>
                                      obtain ⟨d, ctor', arity', fields', fieldTys', hd, hctors',
                                        hflen', hargsEq, hfieldsLen', hctorWF, hfieldTypings⟩ :=
                                        data_value_canonical (hvals scrutinee (by simp)) hscrut
                                      have hdEq : d = decl :=
                                        Option.some.inj (hd.symm.trans hdecl)
                                      rw [hdEq] at hctors' hctorWF
                                      have hspineCanon : scrutinee.spine =
                                          (.const (.ctor type ctor' arity'), fields') := by
                                        rw [hargsEq]
                                        exact Expr.spine_apps _ _
                                      have hspineEq := hsp.symm.trans hspineCanon
                                      injection hspineEq with hhead hfieldsEq
                                      injection hhead with hcEq
                                      injection hcEq with htypeEq hctorEq harityEq
                                      subst htypeEq
                                      subst hctorEq
                                      subst harityEq
                                      subst hfieldsEq
                                      have hctorLt : ctor < decl.ctors.length := by
                                        obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hctors'
                                        exact hlt
                                      have hdeclCtor : decl.ctors[ctor] = fieldTys' := by
                                        have hsome := List.getElem?_eq_getElem hctorLt
                                        exact Option.some.inj (hsome.symm.trans hctors')
                                      let branchTy : List Ty → Ty := fun fs =>
                                        Ty.arrow (.prim .unit)
                                          (Ty.arrows (fs.map (fun ft =>
                                            Ty.openWith (params ++ [r]) ft)) r)
                                      have hmapGet : ((decl.ctors.map branchTy)[ctor]?) =
                                          some (branchTy (decl.ctors[ctor]'(by omega))) := by
                                        rw [List.getElem?_map, List.getElem?_eq_getElem hctorLt]
                                        rfl
                                      have hbranchTyping :
                                          RuntimeTyping sig rigidCount ctx branch
                                            (Ty.arrow (.prim .unit)
                                              (Ty.arrows (fieldTys'.map
                                                (fun ft => Ty.openWith (params ++ [r]) ft)) r)) := by
                                        have hb := forall₂_get? htail hbranch hmapGet
                                        rw [hdeclCtor] at hb
                                        exact hb
                                      have hfieldScoped : ∀ ft ∈ fieldTys',
                                          ft.Scoped 0 decl.paramCount :=
                                        ctorScheme_fields_scoped hctorWF
                                      have hfieldTypings' : List.Forall₂ (fun e ft =>
                                          RuntimeTyping sig rigidCount ctx e
                                            (ft.openWith (params ++ [r]))) fields fieldTys' :=
                                        forall₂_openWith_append hfieldScoped hplen hfieldTypings
                                      have hargsForall : List.Forall₂ (fun e t =>
                                          RuntimeTyping sig rigidCount ctx e t)
                                          (Expr.primLit .unit :: fields)
                                          (.prim .unit :: fieldTys'.map
                                            (fun ft => Ty.openWith (params ++ [r]) ft)) :=
                                        .cons .primLit (forall₂_map_of_forall₂ hfieldTypings')
                                      have hresultTyping : RuntimeTyping sig rigidCount ctx
                                          (Expr.apps branch (Expr.primLit .unit :: fields)) r :=
                                        typing_apps_intro hbranchTyping hargsForall
                                      rw [← hreduce, hty]
                                      exact hresultTyping
                            · simp [hfieldsLen] at hreduce
                        | elim type' ctorCount' => simp at hreduce
                    | primLit => simp at hreduce
                    | primOp => simp at hreduce
                    | var index => simp at hreduce
                    | lambda ann body => simp at hreduce
                    | app f a => simp at hreduce
                    | letIn ann rhs body => simp at hreduce
                    | fix ann body => simp at hreduce
              · rw [if_neg hbranchLen] at hreduce
                simp at hreduce

end RuntimeTyping
end EPL

/-!
# The executable evaluator computes `Eval.Step`

`step?` is sound and complete for the step relation, so the relation is
deterministic and `step? = none` characterises normal forms. `run` follows
the relation, and it is complete: any execution that reaches a value is found
by `run` given enough fuel.
-/

namespace EPL
namespace Eval

private theorem reduceConst_eq_none_of_length_le {c : DataConst} {args : List RuntimeExpr}
    (hlen : args.length ≤ c.valueArity) : reduceConst c args = none := by
  cases c with
  | ctor type ctor arity => rfl
  | elim type ctorCount =>
      cases args with
      | nil => rfl
      | cons scrutinee branches =>
          have hbranch : ¬ branches.length = ctorCount := by
            simp [DataConst.valueArity] at hlen
            omega
          simp only [reduceConst, if_neg hbranch]



private theorem value_app_spine_all_values {f a : RuntimeExpr} {c : DataConst}
    {args : List RuntimeExpr}
    (vf : Value f) (va : Value a)
    (hsp : (Expr.app f a).spine = (.const c, args)) :
    ∀ x ∈ args, Value x := by
  cases vf with
  | const hfspine hflen hfvals =>
      have hsp' : (Expr.app f a).spine = (f.spine.1, f.spine.2 ++ [a]) := rfl
      rw [hsp'] at hsp
      rw [hfspine] at hsp
      injection hsp with _ hargs
      intro x hx
      rw [← hargs] at hx
      rcases List.mem_append.mp hx with h | h
      · exact hfvals x h
      · simp only [List.mem_singleton] at h
        subst h
        exact va
  | primLit => simp only [Expr.spine] at hsp; cases hsp
  | primOp => simp only [Expr.spine] at hsp; cases hsp
  | lambda => simp only [Expr.spine] at hsp; cases hsp
  | primOpPartial => simp only [Expr.spine] at hsp; cases hsp

private theorem value_app_parts {f a : RuntimeExpr} {c : DataConst} {args : List RuntimeExpr}
    (hsp : (Expr.app f a).spine = (.const c, args))
    (hlen : args.length ≤ c.valueArity)
    (hvals : ∀ x ∈ args, Value x) : Value f ∧ Value a := by
  have hsp' : (Expr.app f a).spine = (f.spine.1, f.spine.2 ++ [a]) := rfl
  rw [hsp'] at hsp
  cases hfs : f.spine with
  | mk head fs =>
      rw [hfs] at hsp
      injection hsp with hhead hargs
      subst hhead
      have hargsEq : args = fs ++ [a] := hargs.symm
      have hlenF : fs.length ≤ c.valueArity := by
        have hlen' := congrArg List.length hargsEq
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
        omega
      have hvalsF : ∀ x ∈ fs, Value x := by
        intro x hx
        exact hvals x (by rw [hargsEq]; exact List.mem_append_left _ hx)
      exact ⟨Value.const hfs hlenF hvalsF,
        hvals a (by rw [hargsEq]; simp)⟩

theorem isValue_iff {expr : RuntimeExpr} :
    isValue expr = true ↔ Value expr := by
  constructor
  · intro h
    induction expr with
    | primLit literal => exact .primLit
    | primOp op => exact .primOp
    | var index => simp [isValue] at h
    | lambda ann body => exact .lambda
    | letIn ann rhs body => simp [isValue] at h
    | fix ann body => simp [isValue] at h
    | const c => exact .const rfl (Nat.zero_le _) (by simp)
    | app f a ihf iha =>
        cases f with
        | primOp op =>
            exact .primOpPartial (iha (by simpa [isValue] using h))
        | primLit literal => simp [isValue, Expr.spine] at h
        | var index => simp [isValue, Expr.spine] at h
        | lambda ann body => simp [isValue, Expr.spine] at h
        | letIn ann rhs body => simp [isValue, Expr.spine] at h
        | fix ann body => simp [isValue, Expr.spine] at h
        | const c =>
            simp only [isValue, Expr.spine, Bool.and_eq_true, Bool.true_and,
              decide_eq_true_eq] at h
            obtain ⟨hia, hlen'⟩ := h
            refine .const (c := c) (args := [a]) rfl ?_ ?_
            · simpa using hlen'
            · intro x hx
              simp only [List.mem_singleton] at hx
              subst hx
              exact iha hia
        | app f' a' =>
            simp only [isValue, Bool.and_eq_true] at h
            obtain ⟨⟨hif, hia⟩, hmatch⟩ := h
            cases hsp : (Expr.app (.app f' a') a).spine with
            | mk head args =>
                simp only [hsp] at hmatch
                cases head with
                | const c =>
                    simp only [decide_eq_true_eq] at hmatch
                    exact .const hsp hmatch
                      (value_app_spine_all_values (ihf hif) (iha hia) hsp)
                | primLit => simp at hmatch
                | primOp => simp at hmatch
                | var => simp at hmatch
                | lambda => simp at hmatch
                | app => simp at hmatch
                | letIn => simp at hmatch
                | fix => simp at hmatch
  · intro value
    induction expr with
    | primLit literal => rfl
    | primOp op => rfl
    | var index =>
        cases value with
        | const hsp _ _ => simp [Expr.spine] at hsp
    | lambda ann body => rfl
    | letIn ann rhs body =>
        cases value with
        | const hsp _ _ => simp [Expr.spine] at hsp
    | fix ann body =>
        cases value with
        | const hsp _ _ => simp [Expr.spine] at hsp
    | const c => rfl
    | app f a ihf iha =>
        cases f with
        | primOp op =>
            cases value with
            | primOpPartial h => exact iha h
            | const hsp _ _ => simp [Expr.spine] at hsp
        | primLit literal =>
            cases value with
            | const hsp _ _ => simp [Expr.spine] at hsp
        | var index =>
            cases value with
            | const hsp _ _ => simp [Expr.spine] at hsp
        | lambda ann body =>
            cases value with
            | const hsp _ _ => simp [Expr.spine] at hsp
        | letIn ann rhs body =>
            cases value with
            | const hsp _ _ => simp [Expr.spine] at hsp
        | fix ann body =>
            cases value with
            | const hsp _ _ => simp [Expr.spine] at hsp
        | const c0 =>
            cases value with
            | const hsp hlen hvals =>
                obtain ⟨hvalF, hvalA⟩ := value_app_parts hsp hlen hvals
                have hif := ihf hvalF
                have hia := iha hvalA
                have hstep : isValue (.app (.const c0) a) =
                    (isValue (.const c0) && isValue a &&
                      (match (Expr.app (.const c0) a).spine with
                        | (.const c, args) => decide (args.length ≤ c.valueArity)
                        | _ => false)) := rfl
                rw [hstep]
                simp only [isValue, hia, Bool.true_and, hsp, decide_eq_true_eq]
                exact hlen
        | app f' a' =>
            cases value with
            | const hsp hlen hvals =>
                obtain ⟨hvalF, hvalA⟩ := value_app_parts hsp hlen hvals
                have hif := ihf hvalF
                have hia := iha hvalA
                have hstep : isValue (.app (.app f' a') a) =
                    (isValue (.app f' a') && isValue a &&
                      (match (Expr.app (.app f' a') a).spine with
                        | (.const c, args) => decide (args.length ≤ c.valueArity)
                        | _ => false)) := rfl
                rw [hstep]
                simp only [hif, hia, Bool.true_and, hsp, decide_eq_true_eq]
                exact hlen




private theorem reduceConst_some_length {c : DataConst} {args : List RuntimeExpr}
    {result : RuntimeExpr} (h : reduceConst c args = some result) :
    args.length ≤ c.valueArity + 1 := by
  cases c with
  | ctor type ctor arity => simp [reduceConst] at h
  | elim type ctorCount =>
      cases args with
      | nil => simp [reduceConst] at h
      | cons scrutinee branches =>
          by_cases hb : branches.length = ctorCount
          · simp [DataConst.valueArity, List.length_cons]
            omega
          · simp [reduceConst, hb] at h

private theorem reduceApp_eq_reduceConst {f a : RuntimeExpr} {c : DataConst}
    {args : List RuntimeExpr} (hsp : (Expr.app f a).spine = (.const c, args)) :
    reduceApp f a = reduceConst c args := by
  cases f with
  | lambda ann body => simp [Expr.spine] at hsp
  | primOp op =>
      have hsp' : (Expr.app (.primOp op) a).spine = (.primOp op, [a]) := rfl
      rw [hsp'] at hsp
      simp at hsp
  | primLit literal => simp [Expr.spine] at hsp
  | var index => simp [Expr.spine] at hsp
  | letIn ann rhs body => simp [Expr.spine] at hsp
  | fix ann body => simp [Expr.spine] at hsp
  | const c0 => simp [reduceApp, hsp]
  | app f' a' =>
      cases f' with
      | primOp op =>
          have hsp' : (Expr.app (.app (.primOp op) a') a).spine =
              (.primOp op, [a', a]) := rfl
          rw [hsp'] at hsp
          simp at hsp
      | primLit literal => simp [reduceApp, hsp]
      | var index => simp [reduceApp, hsp]
      | lambda ann body => simp [reduceApp, hsp]
      | letIn ann rhs body => simp [reduceApp, hsp]
      | fix ann body => simp [reduceApp, hsp]
      | const c0 => simp [reduceApp, hsp]
      | app g b => simp [reduceApp, hsp]

private theorem isValue_lambda (ann : Option Unit) (body : RuntimeExpr) :
    isValue (.lambda ann body) = true := rfl

private theorem step?_of_value {expr : RuntimeExpr} (value : Value expr) :
    step? expr = none := by
  induction expr with
  | primLit literal => rfl
  | primOp op => rfl
  | lambda ann body => rfl
  | const c => rfl
  | var index =>
      cases value with
      | const hsp _ _ => simp [Expr.spine] at hsp
  | letIn ann rhs body =>
      cases value with
      | const hsp _ _ => simp [Expr.spine] at hsp
  | fix ann body =>
      cases value with
      | const hsp _ _ => simp [Expr.spine] at hsp
  | app f a ihf iha =>
      cases value with
      | primOpPartial harg =>
          have ha := iha harg
          have hia : isValue a = true := isValue_iff.mpr harg
          simp [step?, reduceApp, Expr.spine, ha, hia]
      | const hsp hlen hvals =>
          obtain ⟨hvalF, hvalA⟩ := value_app_parts hsp hlen hvals
          have hf := ihf hvalF
          have ha := iha hvalA
          have hif : isValue f = true := isValue_iff.mpr hvalF
          have hia : isValue a = true := isValue_iff.mpr hvalA
          have hredNone : reduceApp f a = none := by
            rw [reduceApp_eq_reduceConst hsp]
            exact reduceConst_eq_none_of_length_le hlen
          simp [step?, hf, hif, ha, hia, hredNone]

theorem Value.irreducible {expr next : RuntimeExpr}
    (value : Value expr) : ¬ Step expr next := by
  revert value
  induction expr generalizing next with
  | primLit literal =>
      intro value step
      cases value with
      | primLit => cases step
      | const hsp _ _ => simp [Expr.spine] at hsp
  | primOp op =>
      intro value step
      cases value with
      | primOp => cases step
      | const hsp _ _ => simp [Expr.spine] at hsp
  | lambda ann body =>
      intro value step
      cases value with
      | lambda => cases step
      | const hsp _ _ => simp [Expr.spine] at hsp
  | var index =>
      intro value step
      cases value with
      | const hsp _ _ => simp [Expr.spine] at hsp
  | letIn ann rhs body =>
      intro value step
      cases value with
      | const hsp _ _ => simp [Expr.spine] at hsp
  | fix ann body =>
      intro value step
      cases value with
      | const hsp _ _ => simp [Expr.spine] at hsp
  | const c =>
      intro value step
      cases value with
      | const hsp hlen hvals => cases step
  | app f a ihf iha =>
      intro value step
      cases value with
      | primOpPartial harg =>
          cases step with
          | appFunction h => exact ihf Value.primOp h
          | appArgument _ h => exact iha harg h
          | const hspStep _ _ => simp [Expr.spine] at hspStep
      | const hsp hlen hvals =>
          obtain ⟨hvalF, hvalA⟩ := value_app_parts hsp hlen hvals
          cases step with
          | beta _ => simp [Expr.spine] at hsp
          | primOp _ => simp [Expr.spine] at hsp
          | appFunction h => exact ihf hvalF h
          | appArgument _ h => exact iha hvalA h
          | const hspStep _ hred =>
              have hEq := hsp.symm.trans hspStep
              cases hEq
              rw [reduceConst_eq_none_of_length_le hlen] at hred
              cases hred

theorem step?_sound {expr next : RuntimeExpr}
    (h : step? expr = some next) : Step expr next := by
  induction expr generalizing next with
  | primLit literal => simp [step?] at h
  | primOp op => simp [step?] at h
  | var index => simp [step?] at h
  | lambda ann body => simp [step?] at h
  | const c => simp [step?] at h
  | fix ann body =>
      cases ann
      simp only [step?] at h
      cases h
      exact Step.fixUnfold
  | letIn ann rhs body ihRhs ihBody =>
      simp only [step?] at h
      cases hr : step? rhs with
      | some rhs' =>
          rw [hr] at h
          simp only [Option.some.injEq] at h
          cases h
          exact Step.letRhs (ihRhs hr)
      | none =>
          rw [hr] at h
          by_cases hval : isValue rhs = true
          · simp only [hval, if_true] at h
            cases h
            exact Step.letValue (isValue_iff.mp hval)
          · simp only [hval] at h
            simp at h
  | app function argument ihFunction ihArgument =>
      simp only [step?] at h
      cases hf : step? function with
      | some function' =>
          rw [hf] at h
          simp only [Option.some.injEq] at h
          cases h
          exact Step.appFunction (ihFunction hf)
      | none =>
          rw [hf] at h
          by_cases hval : isValue function = true
          · simp only [hval, if_true] at h
            cases ha : step? argument with
            | some argument' =>
                rw [ha] at h
                simp only [Option.some.injEq] at h
                cases h
                exact Step.appArgument (isValue_iff.mp hval) (ihArgument ha)
            | none =>
                rw [ha] at h
                by_cases harg : isValue argument = true
                · simp only [harg, if_true] at h
                  have vf := isValue_iff.mp hval
                  have va := isValue_iff.mp harg
                  unfold reduceApp at h
                  split at h
                  · rename_i ann body _heq
                    simp only [Option.some.injEq] at h
                    cases h
                    exact Step.beta va
                  · exact Step.primOp h
                  · cases hsp : (Expr.app function argument).spine with
                    | mk head args =>
                        simp only [hsp] at h
                        cases head with
                        | const c =>
                            change reduceConst c args = some next at h
                            exact Step.const hsp
                              (value_app_spine_all_values vf va hsp) h
                        | primLit => simp at h
                        | primOp => simp at h
                        | var => simp at h
                        | lambda => simp at h
                        | app => simp at h
                        | letIn => simp at h
                        | fix => simp at h
                · simp only [harg] at h
                  simp at h
          · simp only [hval] at h
            simp at h


theorem step?_complete {expr next : RuntimeExpr}
    (step : Step expr next) : step? expr = some next := by
  induction step with
  | beta value =>
      simp [step?, reduceApp, step?_of_value value, isValue_iff.mpr value, isValue_lambda]
  | appFunction h ih =>
      simp [step?, ih]
  | appArgument value h ih =>
      simp [step?, step?_of_value value, isValue_iff.mpr value, ih]
  | primOp h =>
      simp [step?, reduceApp, isValue, Expr.spine, h]
  | letRhs h ih =>
      simp [step?, ih]
  | letValue value =>
      simp [step?, step?_of_value value, isValue_iff.mpr value]
  | fixUnfold =>
      simp [step?]
  | const hsp hvals hreduce =>
      expose_names
      have hlenTotal := reduceConst_some_length hreduce
      have hspSpine : (Expr.app function argument).spine =
          (function.spine.1, function.spine.2 ++ [argument]) := rfl
      rw [hspSpine] at hsp
      cases hfs : function.spine with
      | mk head fs =>
          rw [hfs] at hsp
          injection hsp with hhead hargs
          subst hhead
          have hargsEq : args = fs ++ [argument] := hargs.symm
          have hspine : (Expr.app function argument).spine = (.const c, args) := by
            rw [hspSpine, hfs, ← hargsEq]
          have hlenFs : fs.length ≤ c.valueArity := by
            have := hlenTotal
            rw [hargsEq] at this
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            omega
          have hvalsFs : ∀ x ∈ fs, Value x := by
            intro x hx
            exact hvals x (by rw [hargsEq]; exact List.mem_append_left _ hx)
          have hvalArg : Value argument := hvals argument (by rw [hargsEq]; simp)
          have hvalFunc : Value (Expr.apps (.const c) fs) :=
            Value.const (by simpa using Expr.spine_apps (.const c) fs) hlenFs hvalsFs
          have hfuncVal : function = Expr.apps (.const c) fs := by
            have := Expr.apps_spine function
            rw [hfs] at this
            exact this.symm
          have hstepFunc : step? function = none := by
            rw [hfuncVal]
            exact step?_of_value hvalFunc
          have hif : isValue function = true := by
            rw [hfuncVal]
            exact isValue_iff.mpr hvalFunc
          have hstepArg : step? argument = none := step?_of_value hvalArg
          have hia : isValue argument = true := isValue_iff.mpr hvalArg
          have hreduceApp : reduceApp function argument = some result := by
            rw [reduceApp_eq_reduceConst hspine]
            exact hreduce
          have hstepEq : step? (Expr.app function argument) = some result := by
            simp [step?, hstepFunc, hif, hstepArg, hia, hreduceApp]
          rw [hstepEq]


theorem Step.deterministic {expr first second : RuntimeExpr}
    (stepFirst : Step expr first) (stepSecond : Step expr second) :
    first = second := by
  have hFirst := step?_complete stepFirst
  have hSecond := step?_complete stepSecond
  rw [hFirst] at hSecond
  exact Option.some.inj hSecond

/-- `step?` returns `none` exactly on normal forms of `Step`. -/
theorem step?_eq_none_iff {expr : RuntimeExpr} :
    step? expr = none ↔ ∀ next, ¬ Step expr next := by
  constructor
  · intro h next step
    have hsome := step?_complete step
    rw [h] at hsome
    exact nomatch hsome
  · intro h
    cases hstep : step? expr with
    | none => rfl
    | some next => exact absurd (step?_sound hstep) (h next)

/-- `run` is stationary when `step?` has no successor. -/
private theorem run_none {expr : RuntimeExpr} (h : step? expr = none) (fuel : Nat) :
    run fuel expr = expr := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [run, h]

private theorem run_add (first second : Nat) (expr : RuntimeExpr) :
    run (first + second) expr = run second (run first expr) := by
  induction first generalizing expr with
  | zero => simp [run]
  | succ first ih =>
      rw [Nat.succ_add]
      cases h : step? expr with
      | none =>
          rw [run_none h (first + second + 1)]
          rw [run_none h (first + 1)]
          rw [run_none h second]
      | some next =>
          have hlhs : run (first + second + 1) expr = run (first + second) next := by
            simp [run, h]
          have hrhs : run (first + 1) expr = run first next := by
            simp [run, h]
          rw [hlhs, hrhs]
          exact ih next

/-- The evaluator only ever follows the step relation. -/
theorem run_steps (fuel : Nat) (expr : RuntimeExpr) :
    Steps expr (run fuel expr) := by
  induction fuel generalizing expr with
  | zero => exact Relation.ReflTransGen.refl
  | succ fuel ih =>
      simp only [run]
      cases h : step? expr with
      | none =>
          exact Relation.ReflTransGen.refl
      | some next =>
          exact Relation.ReflTransGen.head (step?_sound h) (ih next)

/-- The evaluator leaves values unchanged. -/
theorem run_value {fuel : Nat} {expr : RuntimeExpr}
    (value : Value expr) : run fuel expr = expr := by
  exact run_none (step?_of_value value) fuel

/-- Any finite execution is realised by `run` at exactly the corresponding
fuel. -/
private theorem run_reaches {expr result : RuntimeExpr} (steps : Steps expr result) :
    ∃ fuel, run fuel expr = result := by
  induction steps with
  | refl => exact ⟨0, rfl⟩
  | tail hsteps hstep ih =>
      obtain ⟨fuel, hfuel⟩ := ih
      refine ⟨fuel + 1, ?_⟩
      rw [run_add fuel 1 expr, hfuel]
      simp [run, step?_complete hstep]

/-- Evaluator completeness: an execution reaching a value is found by `run`
with enough fuel (and with any larger fuel). -/
theorem run_complete {expr result : RuntimeExpr}
    (steps : Steps expr result) (value : Value result) :
    ∃ fuel, ∀ extra, run (fuel + extra) expr = result := by
  obtain ⟨fuel, hfuel⟩ := run_reaches steps
  refine ⟨fuel, fun extra => ?_⟩
  rw [run_add fuel extra expr, hfuel]
  exact run_value (fuel := extra) value

end Eval
end EPL
