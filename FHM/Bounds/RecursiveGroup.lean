import FHM.Bounds.RecursiveRHS

/-! # Checked introduction of simultaneous recursive contract groups

All members are checked under the same declared assumptions, and their universal
certificates discharge the group rule before its body result is accepted. The
initial body keeps fixed HM monotypes: HM generalization at group exit and nested
groups remain separate work. This optional checker does not change CLI/LSP launch.
-/

namespace FHM.Bounds.RecursiveGroup

open RecursiveContract RecursiveTyping CountSubstitution ScopedScheme

/-- Length- and order-indexed certificates prevent skipping, swapping or
    certifying a different member. RHS indices retain the actual found trees. -/
inductive Members (env : List Binding) : List Declared → List Expr → List (Option PolyTy) → Type where
  | nil : Members env [] [] []
  | cons {c cs rhs rhss ann anns} :
      RecursiveRHS.Certified c env rhs.stripFound ann →
      Members env cs rhss anns → Members env (c :: cs) (rhs :: rhss) (ann :: anns)

namespace Members

def actuals {env cs rhss anns} (ms : Members env cs rhss anns) (i : Nat)
    (args : List Count) : BoundsTy :=
  match ms, i with
  | .nil, _ => .prim .int
  | .cons (c := c) cert _, 0 => bounds (c.counts.quantified.zip args) cert.actual
  | .cons _ tail, i + 1 => tail.actuals i args

theorem lengths {env cs rhss anns} (ms : Members env cs rhss anns) :
    anns.length = cs.length ∧ rhss.length = cs.length := by
  induction ms with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ ih => simpa using ih

theorem obligations {env cs rhss anns} (ms : Members env cs rhss anns)
    (i : Nat) (c : Declared) (rhs : Expr) (ann : Option PolyTy)
    (hc : cs[i]? = some c) (hr : rhss[i]? = some rhs) (ha : anns[i]? = some ann)
    (args caller) (inst : Instance c.counts args caller) :
    Derives (c.counts.quantified ++ c.counts.captures) (c.counts.quantified.zip args)
      inst.premises env rhs.stripFound (ms.actuals i args) ∧
    InterpretedAnnotation.BindingOK (c.counts.quantified ++ c.counts.captures)
      (c.counts.quantified.zip args) inst.premises ann (ms.actuals i args) ∧
    SemanticSub inst.premises (ms.actuals i args) inst.bounds := by
  induction ms generalizing i with
  | nil => simp at hc
  | cons cert tail ih =>
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hr ha
          subst c; subst rhs; subst ann
          exact ⟨(RecursiveRHS.use cert inst).typing, (RecursiveRHS.use cert inst).annotation,
            (RecursiveRHS.use cert inst).inclusion⟩
      | succ i => exact ih i hc hr ha

end Members

structure Certified (ids : List Nat) (rows : Bindings) (Δ : List Constraint)
    (env : List Binding) (anns : List (Option PolyTy)) (rhss : List Expr) (body : Expr) where
  contracts : List Declared
  independent : Independent contracts
  captureScope : ∀ c ∈ contracts, ∀ b ∈ env, BindingScoped c.counts.captures b
  members : Members (contracts.map Binding.recursive ++ env) contracts rhss anns
  result : BoundsTy
  bodyTyping : Derives ids rows Δ (contracts.map Binding.recursive ++ env) body.stripFound result

/-- Assumption-based RHS certificates alone are insufficient. This theorem
    introduces a group only after every universal obligation and the body have
    been supplied in their exact order. -/
theorem Certified.typing {ids rows Δ env anns rhss body}
    (cert : Certified ids rows Δ env anns rhss body) :
    Derives ids rows Δ env (.letRec anns (rhss.map Expr.stripFound) body.stripFound) cert.result := by
  apply Derives.letRec (actuals := cert.members.actuals) cert.members.lengths.1
    (by simpa using cert.members.lengths.2) cert.independent cert.captureScope
  · intro i c rhs ann hc hr ha args caller inst
    rw [List.getElem?_map] at hr
    obtain ⟨found, hf, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact (cert.members.obligations i c found ann hc hf ha args caller inst).1
  · intro i c rhs ann hc hr ha args caller inst
    rw [List.getElem?_map] at hr
    obtain ⟨found, hf, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact (cert.members.obligations i c found ann hc hf ha args caller inst).2.1
  · intro i c rhs ann hc hr ha args caller inst
    rw [List.getElem?_map] at hr
    obtain ⟨found, hf, rfl⟩ := Option.map_eq_some_iff.mp hr
    exact (cert.members.obligations i c found ann hc hf ha args caller inst).2.2
  · exact cert.bodyTyping

private def captureOK (env : List Binding) (c : Declared) : Bool :=
  env.all fun
    | .mono β => boundsScopedBool c.counts.captures β
    | .recursive d => d.counts.captures.all (c.counts.captures.contains ·)

private theorem captureOK_sound {env c} (h : captureOK env c = true) :
    ∀ b ∈ env, BindingScoped c.counts.captures b := by
  intro b hb
  have h := List.all_eq_true.mp h b hb
  cases b with
  | mono β => exact boundsScopedBool_sound h
  | recursive d =>
      intro i hi
      simpa [List.contains_iff_mem] using List.all_eq_true.mp h i hi

private def checkMembers (schemes : BinderSchemeMap) (metadata : Scope.Metadata)
    (path : CorePath) (env : List Binding) (index : Nat)
    (cs : List Declared) (rhss : List Expr) (anns : List (Option PolyTy)) :
    Except String (Members env cs rhss anns × List Typed.NodeResult) := do
  match cs, rhss, anns with
  | [], [], [] => pure ⟨.nil, []⟩
  | c :: cs, rhs :: rhss, ann :: anns =>
      let q ← ScopedDeclaration.telescope metadata (.letRec path index)
      let checked ← RecursiveRHS.checkLocated schemes q ⟨ann, rhs, path ++ [.letRecRhs index]⟩ c env
      let tail ← checkMembers schemes metadata path env (index + 1) cs rhss anns
      pure ⟨.cons checked.certificate tail.1, checked.typed.nodes ++ tail.2⟩
  | _, _, _ => throw "bounds: recursive contract/annotation/RHS arity mismatch"

private def decodeMembers (metadata : Scope.Metadata) (path : CorePath) (captures : List Nat)
    (index : Nat) (rhss : List Expr) (anns : List (Option PolyTy)) : Except String (List Declared) := do
  match rhss, anns with
  | [], [] => pure []
  | rhs :: rhss, some ann :: anns =>
      let hm ← match Typed.rootHM? rhs with
        | some hm => pure hm | none => throw "bounds: recursive member lacks found payload"
      let q ← ScopedDeclaration.telescope metadata (.letRec path index)
      let c ← RecursiveContract.decode ann hm q captures
      pure (c :: (← decodeMembers metadata path captures (index + 1) rhss anns))
  | _ :: _, none :: _ => throw "bounds: recursive group requires declared bounds contracts"
  | _, _ => throw "bounds: recursive annotation/RHS arity mismatch"

structure Result (ids : List Nat) (rows : Bindings) (caller : List Nat)
    (Δ : List Constraint) (env : List Binding) (e : Expr) where
  hm : Ty
  bounds : BoundsTy
  root : Typed.rootHM? e = some hm
  shape : Synth.BoundsTy.toTy bounds = hm
  derivation : Derives ids rows Δ env e.stripFound bounds
  countScope : BoundsScoped caller bounds
  nodes : List Typed.NodeResult

/-- Check a found recursive group at its logical Core path. Missing contracts,
    invalid members or an invalid body reject the whole group; no partial result
    is exported and no legacy fallback is used. -/
def check (ids : List Nat) (rows : Bindings) (caller : List Nat) (Δ : List Constraint)
    (env : List Binding) (path : CorePath) (e : Expr) (schemes : BinderSchemeMap)
    (metadata : Scope.Metadata) : Except String (Result ids rows caller Δ env e) := do
  unless metadata.problems.isEmpty do throw "bounds: unresolved recursive group count scope"
  match e with
  | .found hm (.letRec anns rhss body) =>
      unless anns.length = rhss.length do throw "bounds: recursive annotation/RHS arity mismatch"
      let cs ← decodeMembers metadata path caller 0 rhss anns
      if hi : independentBool cs = true then
        if hc : cs.all (captureOK env) = true then
          let members ← checkMembers schemes metadata path (cs.map Binding.recursive ++ env) 0 cs rhss anns
          let result ← RecursiveWalk.walk ids rows caller Δ (cs.map Binding.recursive ++ env)
            (path ++ [.letRecBody]) body schemes
          let shape ← match BinderBridge.equalTy result.hm hm.eraseBounds with
            | some h => pure h | none => throw "bounds: recursive group body disagrees with root found payload"
          let cert : Certified ids rows Δ env anns rhss body :=
            ⟨cs, independentBool_sound hi,
              fun c h => captureOK_sound (List.all_eq_true.mp hc c h), members.1,
              result.bounds, result.derivation⟩
          pure ⟨hm.eraseBounds, result.bounds, rfl, result.shape.trans shape.down,
            by simpa only [Expr.stripFound] using cert.typing,
            result.countScope, ⟨path, hm.eraseBounds, some result.bounds⟩ :: members.2 ++ result.nodes⟩
        else throw "bounds: recursive group environment escapes declared captures"
      else throw "bounds: recursive group count telescopes overlap or capture quantified counts"
  | _ => throw "bounds: requested expression is not a found recursive group"

#print axioms Certified.typing
#print axioms check

end FHM.Bounds.RecursiveGroup
