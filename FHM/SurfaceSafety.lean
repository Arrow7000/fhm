import FHM.SurfaceBridge
import FHM.InferW

/-! Coverage transfers directly from surface syntax to canonical source erasure.
Inference then supplies runtime typing, so exhaustive accepted surface programs
are safe for every finite execution. No completed annotated expression is used. -/

open SmallStep PatComp

namespace SurfaceBridge

private theorem emitCases_eq_map' (env : List Occ) (bodies : Nat → Expr) (occ : Occ) :
    ∀ (cases : List (CtorName × Nat × DTree)),
      emitCases env bodies occ cases
        = cases.map (fun x => (MatchPattern.named x.1 x.2.1,
            emit (subOccs occ x.2.1 ++ env) bodies x.2.2))
  | [] => rfl
  | (_c, _a, _t) :: rest => by
    change (MatchPattern.named _c _a, emit (subOccs occ _a ++ env) bodies _t)
      :: emitCases env bodies occ rest = _
    rw [emitCases_eq_map' env bodies occ rest, List.map_cons]

private theorem mem_emitCases_of_mem_cases (env : List Occ) (bodies : Nat → Expr)
    (occ : Occ) {cases : List (CtorName × Nat × DTree)} {c : CtorName} {a : Nat}
    {t : DTree} (h : (c, a, t) ∈ cases) :
    (MatchPattern.named c a, emit (subOccs occ a ++ env) bodies t) ∈
      emitCases env bodies occ cases := by
  rw [emitCases_eq_map']
  exact List.mem_map.mpr ⟨(c, a, t), h, rfl⟩

/-- Inverse membership: a named branch in `emitCases` comes from a case. -/
private theorem mem_cases_of_mem_emitCases (env : List Occ) (bodies : Nat → Expr)
    (occ : Occ) {cases : List (CtorName × Nat × DTree)} {c : CtorName} {n : Nat}
    {body : Expr}
    (h : (MatchPattern.named c n, body) ∈ emitCases env bodies occ cases) :
    ∃ t, (c, n, t) ∈ cases ∧ body = emit (subOccs occ n ++ env) bodies t := by
  rw [emitCases_eq_map'] at h
  obtain ⟨⟨c', a', t'⟩, hx, heq⟩ := List.mem_map.mp h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := (Prod.mk.injEq _ _ _ _).mp heq
  exact ⟨t', hx, rfl⟩

theorem emitLets_AllMatchesExhaustive {ctors : CtorEnv} (env binds : List Occ)
    {body : Expr} (h : AllMatchesExhaustive ctors body) :
    AllMatchesExhaustive ctors (emitLets env binds body) := by
  unfold emitLets
  have go_exh : ∀ (bs : List Occ) (depth : Nat),
      AllMatchesExhaustive ctors (emitLets.go env binds body bs depth) := by
    intro bs depth
    induction bs generalizing depth with
    | nil => exact AllMatchesExhaustive.shiftFrom h _ _
    | cons _b rest ih => exact .letIn .var (ih (depth + 1))
  exact go_exh binds.reverse 0

/-- Branch bodies of `emitCases` are exhaustive when each case subtree is. -/
private theorem emitCases_AllBranchBodiesExhaustive {ctors : CtorEnv}
    (bodies : Nat → Expr) (env : List Occ) (occ : Occ)
    (cases : List (CtorName × Nat × DTree))
    (h : ∀ c a t, (c, a, t) ∈ cases →
      AllMatchesExhaustive ctors (emit (subOccs occ a ++ env) bodies t)) :
    AllBranchBodiesExhaustive ctors (emitCases env bodies occ cases) := by
  induction cases with
  | nil => exact .nil
  | cons hd tl ih =>
    obtain ⟨c, a, t⟩ := hd
    rw [emitCases, emitCasesWith]
    exact .cons (h c a t List.mem_cons_self)
      (ih fun c' a' t' hm => h c' a' t' (List.mem_cons_of_mem _ hm))

/-- Append a single exhaustive branch onto an exhaustive branch list. -/
private theorem AllBranchBodiesExhaustive.append_singleton {ctors : CtorEnv}
    {brs : List (MatchPattern × Expr)} {pat : MatchPattern} {body : Expr}
    (hbrs : AllBranchBodiesExhaustive ctors brs)
    (hbody : AllMatchesExhaustive ctors body) :
    AllBranchBodiesExhaustive ctors (brs ++ [(pat, body)]) := by
  induction brs with
  | nil => exact .cons hbody .nil
  | cons hd tl ih =>
    cases hbrs with
    | cons hb0 hrest => exact .cons hb0 (ih hrest)

/-- **(A-core) Emitting a tree-exhaustive decision tree yields an
    `AllMatchesExhaustive` Core term** — given the leaf bodies are exhaustive.
    Structural induction on the `DTreeExhaustive` derivation: `switchFail` uses
    the coverage clause (every ctor of `T` tested) for `AllMatchesExhaustive`'s
    cover obligation with no wildcard; `switchDefault`'s emitted wildcard covers
    the rest; the per-case ctor typing gives the "pinned" (named ctors ∈ `T`)
    obligation; `leaf` via `emitLets_AllMatchesExhaustive`. `env` is generalized
    (it only drives `resolveOcc`/leaf-lets, irrelevant to coverage). -/
theorem emit_DTreeExhaustive {ctors : CtorEnv} (bodies : Nat → Expr)
    (hbodies : ∀ i, AllMatchesExhaustive ctors (bodies i)) :
    ∀ {octx : OccCtx} {t : DTree}, DTreeExhaustive ctors octx t →
      ∀ (env : List Occ), AllMatchesExhaustive ctors (emit env bodies t) := by
  intro octx t hexh
  induction hexh with
  | leaf =>
    intro env
    simp only [emit, emitWith]
    exact emitLets_AllMatchesExhaustive env _ (hbodies _)
  | @switchFail octx occ cases T tyArgs hlook htyped hsub hcover ih =>
    intro env
    change AllMatchesExhaustive ctors
      (.match_ (resolveOcc env occ) (emitCases env bodies occ cases ++ []))
    rw [List.append_nil]
    refine AllMatchesExhaustive.match_ (tyName := T) .var
      (emitCases_AllBranchBodiesExhaustive bodies env occ cases
        (fun c a t hm => ih c a t hm (subOccs occ a ++ env))) ?_ ?_
    · intro c n body hmem
      obtain ⟨t, ht, rfl⟩ := mem_cases_of_mem_emitCases env bodies occ hmem
      obtain ⟨ctor, hctor, hty, _⟩ := htyped c n t ht
      exact ⟨ctor, hctor, hty⟩
    · intro ctorName ctor hctor hty
      obtain ⟨a, t, ht⟩ := hcover ctorName ctor hctor hty
      obtain ⟨ctor', hctor', _, ha⟩ := htyped ctorName a t ht
      have hlen : a = ctor.contents.length := by
        have : ctor' = ctor := Option.some.inj (hctor'.symm.trans hctor)
        exact this ▸ ha
      refine ⟨.named ctorName a, emit (subOccs occ a ++ env) bodies t,
        mem_emitCases_of_mem_cases env bodies occ ht, ?_⟩
      simp only [MatchPattern.matchesCtor, Bool.and_eq_true, beq_iff_eq, true_and, hlen]
  | @switchDefault octx occ cases dflt T tyArgs hdne hlook htyped hsub hexh_dflt ih ihd =>
    intro env
    have hemit :
        emit env bodies (.switch occ cases dflt) =
          .match_ (resolveOcc env occ)
            (emitCases env bodies occ cases ++
              [(.wildcard, emit env bodies dflt)]) := by
      cases dflt with
      | fail => exact (hdne rfl).elim
      | leaf | switch => rfl
    rw [hemit]
    refine AllMatchesExhaustive.match_ (tyName := T) .var
      (AllBranchBodiesExhaustive.append_singleton
        (emitCases_AllBranchBodiesExhaustive bodies env occ cases
          (fun c a t hm => ih c a t hm (subOccs occ a ++ env)))
        (ihd env)) ?_ ?_
    · intro c n body hmem
      simp only [List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | hmem
      · obtain ⟨t, ht, rfl⟩ := mem_cases_of_mem_emitCases env bodies occ hmem
        obtain ⟨ctor, hctor, hty, _⟩ := htyped c n t ht
        exact ⟨ctor, hctor, hty⟩
      · nomatch hmem
    · intro ctorName ctor hctor hty
      exact ⟨.wildcard, emit env bodies dflt,
        by simp only [List.mem_append, List.mem_singleton, or_true], rfl⟩

/-- Corollary at a compiled match tree: `MatchExhaustive` (tree coverage) plus
    exhaustive branch bodies ⇒ the emitted match is `AllMatchesExhaustive`. -/
theorem emit_compile_AllMatchesExhaustive {ctors : CtorEnv} {T : TyName}
    {tyArgs : List Ty} (bodies : Nat → Expr) (ps : List Surface.Pattern)
    (hbodies : ∀ i, AllMatchesExhaustive ctors (bodies i))
    (hexh : MatchExhaustive ctors T tyArgs ps) :
    AllMatchesExhaustive ctors (emit [[]] bodies (compile [[]] (initMatrix ps))) := by
  unfold MatchExhaustive at hexh
  exact emit_DTreeExhaustive bodies hbodies hexh [[]]

private theorem match_exhaustive {ctors : CtorEnv} {scrut : InferInput}
    {pats : List Surface.Pattern} {bodies : List InferInput} {T : TyName} {args : List Ty}
    (hs : AllMatchesExhaustive ctors scrut.erase)
    (hb : ∀ body ∈ bodies, AllMatchesExhaustive ctors body.erase)
    (hc : MatchExhaustive ctors T args pats) :
    AllMatchesExhaustive ctors (inputLoweringOps.match_ scrut pats bodies).erase := by
  change AllMatchesExhaustive ctors
    (lowerInputMatch scrut pats (fun i => bodies.getD i (.ctor cNil))).erase
  rw [erase_lowerInputMatch]
  refine .letIn hs (emit_compile_AllMatchesExhaustive _ _ ?_ hc)
  intro i
  rw [List.getD]
  cases hi : bodies[i]? with
  | none => simpa only [Option.getD, Expr.erase] using (AllMatchesExhaustive.ctor (ctors := ctors) (name := cNil))
  | some body => exact hb body (List.mem_of_getElem? hi)

private theorem list_exhaustive {ctors : CtorEnv} (items : List InferInput)
    (h : ∀ item ∈ items, AllMatchesExhaustive ctors item.erase) :
    AllMatchesExhaustive ctors (inputLoweringOps.mkList items).erase := by
  induction items with
  | nil => simp only [LoweringOps.mkList, inputLoweringOps, inputEmissionOps, Expr.erase]; exact .ctor
  | cons item rest ih =>
    simp only [LoweringOps.mkList, inputLoweringOps, inputEmissionOps, Expr.erase]
    exact .app (.app .ctor (h item List.mem_cons_self))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

private theorem wrap_exhaustive {ctors : CtorEnv} {ke : KindEnv} {tvs : List ValName}
    {params : List (ValName × Option Surface.Ty)} {body wrapped : InferInput}
    (hw : wrapInputParams ke tvs params body = some wrapped)
    (hb : AllMatchesExhaustive ctors body.erase) :
    AllMatchesExhaustive ctors wrapped.erase := by
  induction params generalizing wrapped with
  | nil => cases hw; exact hb
  | cons param rest ih =>
    rw [wrapInputParams, LoweringOps.wrapParams_eq] at hw
    simp only [bind, pure,
      Option.bind_eq_some_iff, Option.some.injEq] at hw
    obtain ⟨ann, _, inner, hi, rfl⟩ := hw
    simp only [inputLoweringOps, Expr.erase]
    exact .lambda (ih hi)

mutual
/-- Structural lowering preserves coverage directly in source erasure. -/
theorem lowerExpr_exhaustive {ctors ke tvs vs source input}
    (hl : LowersExpr ctors ke tvs vs source input)
    (hc : SurfaceCovers ctors source) : AllMatchesExhaustive ctors input.erase := by
  cases hl with
  | primLitUnit | primLitInt | primLitNat | primLitChar =>
      simp only [inputLoweringOps, Expr.erase]; exact .primLit
  | primLitBool => simp only [inputLoweringOps, inputEmissionOps, Expr.erase]; exact .ctor
  | primBinOp => simp only [inputLoweringOps, Expr.erase]; exact .primBinOp
  | var => simp only [inputLoweringOps, inputEmissionOps, Expr.erase]; exact .var
  | ctor => simp only [inputLoweringOps, inputEmissionOps, Expr.erase]; exact .ctor
  | pair ha hb =>
      simp only [inputLoweringOps, inputEmissionOps, Expr.erase]
      cases hc with
      | pair hca hcb => exact .app (.app .ctor (lowerExpr_exhaustive ha hca)) (lowerExpr_exhaustive hb hcb)
  | cons ha hb =>
      simp only [inputLoweringOps, inputEmissionOps, Expr.erase]
      cases hc with
      | cons hca hcb => exact .app (.app .ctor (lowerExpr_exhaustive ha hca)) (lowerExpr_exhaustive hb hcb)
  | list hs =>
      cases hc with
      | list hcs => exact list_exhaustive _ (lowerList_exhaustive hs hcs)
  | lambda_name _ hb | lambda_wild _ hb =>
      simp only [inputLoweringOps, inputEmissionOps, Expr.erase]
      cases hc with
      | lambda hcb _ => exact .lambda (lowerExpr_exhaustive hb hcb)
  | lambda_pattern _ _ hb =>
      simp only [LoweringOps.patternLambda, inputLoweringOps, Expr.erase]
      cases hc with
      | lambda hcb hp =>
          obtain ⟨T, args, hp⟩ := hp
          exact .lambda (match_exhaustive (by simp only [inputEmissionOps, Expr.erase]; exact .var)
            (by intro b h; simp only [List.mem_singleton] at h; subst b
                exact lowerExpr_exhaustive hb hcb) hp)
  | app hf hx =>
      simp only [inputLoweringOps, inputEmissionOps, Expr.erase]
      cases hc with
      | app hcf hcx => exact .app (lowerExpr_exhaustive hf hcf) (lowerExpr_exhaustive hx hcx)
  | letIn _ hr hw hb =>
      simp only [inputLoweringOps, inputEmissionOps, Expr.erase]
      cases hc with
      | letIn hcr hcb =>
          exact .letIn (wrap_exhaustive hw (lowerExpr_exhaustive hr hcr))
            (lowerExpr_exhaustive hb hcb)
  | letRecIn hbs hb =>
      simp only [inputLoweringOps, inputEmissionOps, Expr.erase]
      cases hc with
      | letRecIn hcbs hcb =>
          refine .letRec ?_ (lowerExpr_exhaustive hb hcb)
          intro binding hm
          change binding ∈ List.map _ _ at hm
          obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hm
          exact lowerBindings_exhaustive hbs hcbs original ho
  | ife hcond ht hf =>
      cases hc with
      | ife hcc hct hcf hexh =>
          exact match_exhaustive (lowerExpr_exhaustive hcond hcc)
            (by intro b hm; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
                rcases hm with rfl | rfl
                · exact lowerExpr_exhaustive ht hct
                · exact lowerExpr_exhaustive hf hcf) hexh
  | match_ hs hbs =>
      cases hc with
      | match_ hcs hcbs hexh =>
          exact match_exhaustive (lowerExpr_exhaustive hs hcs)
            (lowerBranches_exhaustive hbs hcbs) hexh

private theorem lowerList_exhaustive {ctors ke tvs vs sources inputs}
    (hl : LowersExprList ctors ke tvs vs sources inputs)
    (hc : ∀ source ∈ sources, SurfaceCovers ctors source) :
    ∀ input ∈ inputs, AllMatchesExhaustive ctors input.erase := by
  cases hl with
  | nil => simp
  | cons hx hxs =>
      intro input hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact lowerExpr_exhaustive hx (hc _ List.mem_cons_self)
      · exact lowerList_exhaustive hxs (fun s hs => hc s (List.mem_cons_of_mem _ hs)) input hm

private theorem lowerBindings_exhaustive {ctors ke tvs vs sources inputs}
    (hl : LowersRecBinds ctors ke tvs vs sources inputs)
    (hc : ∀ source ∈ sources, SurfaceCovers ctors source.rhs) :
    ∀ input ∈ inputs, AllMatchesExhaustive ctors input.rhs.erase := by
  cases hl with
  | nil => simp
  | cons _ hr hw hrest =>
      intro input hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact wrap_exhaustive hw (lowerExpr_exhaustive hr (hc _ List.mem_cons_self))
      · exact lowerBindings_exhaustive hrest (fun s hs => hc s (List.mem_cons_of_mem _ hs)) input hm

private theorem lowerBranches_exhaustive {ctors ke tvs vs sources inputs}
    (hl : LowersBranches ctors ke tvs vs sources inputs)
    (hc : ∀ p b, (p,b) ∈ sources → SurfaceCovers ctors b) :
    ∀ input ∈ inputs, AllMatchesExhaustive ctors input.erase := by
  cases hl with
  | nil => simp
  | cons hb hrest =>
      intro input hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact lowerExpr_exhaustive hb (hc _ _ List.mem_cons_self)
      · exact lowerBranches_exhaustive hrest
          (fun p b hb => hc p b (List.mem_cons_of_mem _ hb)) input hm
end

/-- Successful canonical lowering transfers surface coverage to the runtime term. -/
theorem lower_exhaustive {ctors : CtorEnv} {source : Surface.Expr} {input : InferInput}
    (hl : lower ctors source = some input) (hc : SurfaceCovers ctors source) :
    AllMatchesExhaustive ctors input.erase := lowerExpr_exhaustive (lower_sound hl) hc

theorem lowerProgram_exhaustive {p : Surface.Program} {ctors : CtorEnv} {input : InferInput}
    (hl : lowerProgram p = some (ctors, input)) (hc : SurfaceCovers ctors p.term) :
    AllMatchesExhaustive ctors input.erase := by
  cases lowerProgram_sound hl with
  | mk _ _ hinput => exact lowerExpr_exhaustive hinput hc

/-- The exact inferred type survives every finite execution of the original
partial source's erasure, which is always a value or can step further. -/
theorem program_type_safe {p : Surface.Program} {ctors : CtorEnv} {input : InferInput}
    {result : InferenceResult} (hl : lowerProgram p = some (ctors, input))
    (hi : inferWithTypes ctors input = some result) (hc : SurfaceCovers ctors p.term) :
    ∀ e', Relation.ReflTransGen Step input.erase e' →
      RuntimeTyping.RunWT ⟨[], ctors⟩ e' result.ty ∧
        (IsValue e' ∨ ∃ e'', Step e' e'') :=
  RuntimeTyping.RunWT.type_safety_star (inferWithTypes_runtime_sound hi)
    (Expr.erase_idem input) (lowerProgram_exhaustive hl hc)

end SurfaceBridge
