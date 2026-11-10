import EPL.Properties.InferenceState

namespace EPL

/-- Opening one authored binder block into the next rigid-level block preserves
algorithmic type scope. -/
theorem Ty.openRigidsFrom_scoped
    {ty : Ty} {rigidCount depth count : Nat}
    (typeScoped : ty.Scoped rigidCount (depth + count)) :
    (ty.openRigidsFrom depth rigidCount count).Scoped
      (rigidCount + count) depth := by
  induction typeScoped with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain
  | bvar hlt =>
      simp only [Ty.openRigidsFrom]
      split
      next hInner => exact .bvar hInner
      next hOuter =>
        split
        next hBlock => exact .rigid (by omega)
        next hBeyond => omega
  | rigid hlt =>
      exact .rigid (by omega)
  | mvar id => exact .mvar id

theorem Ty.openRigidsFrom_metaFree
    {ty : Ty} {depth base count : Nat}
    (metaFree : ty.MetaFree) :
    (ty.openRigidsFrom depth base count).MetaFree := by
  induction metaFree with
  | prim => exact .prim
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain
  | bvar =>
      simp only [Ty.openRigidsFrom]
      split
      · exact .bvar
      · split
        · exact .rigid
        · exact .bvar
  | rigid => exact .rigid

/-- Opening preserves declarative type well-formedness while replacing the
selected bound block by fresh rigid levels. -/
theorem Ty.openRigidsFrom_wf
    {ty : Ty} {rigidCount depth count : Nat}
    (typeWF : ty.WF rigidCount (depth + count)) :
    (ty.openRigidsFrom depth rigidCount count).WF
      (rigidCount + count) depth := by
  exact ⟨Ty.openRigidsFrom_scoped typeWF.1,
    Ty.openRigidsFrom_metaFree typeWF.2⟩

theorem Template.openRigidsFrom_scoped
    {template : Template} {rigidCount depth count : Nat}
    (templateScoped : template.Scoped rigidCount (depth + count)) :
    (template.openRigidsFrom depth rigidCount count).Scoped
      (rigidCount + count) depth := by
  induction templateScoped with
  | fixed typeWF => exact .fixed (Ty.openRigidsFrom_wf typeWF)
  | hole => exact .hole
  | named => exact .named
  | arrow _ _ ihDomain ihCodomain =>
      exact .arrow ihDomain ihCodomain

/-- Source opening respects nested written schemes: their own binders remain
protected while the selected enclosing block becomes fresh rigid levels. -/
theorem Expr.openRigidsFrom_typeScoped
    {input : Source} {rigidCount depth count : Nat}
    (inputScoped : input.TypeScoped rigidCount (depth + count)) :
    (input.openRigidsFrom depth rigidCount count).TypeScoped
      (rigidCount + count) depth := by
  induction input generalizing depth with
  | primLit literal => exact .primLit
  | primOp op => exact .primOp
  | var index => exact .var
  | lambda ann body ihBody =>
      cases inputScoped with
      | lambda annotationScoped bodyScoped =>
          apply Expr.TypeScoped.lambda
          · intro openedTemplate heq
            cases ann with
            | none => simp at heq
            | some template =>
                simp only [Option.map_some, Option.some.injEq] at heq
                subst openedTemplate
                exact Template.openRigidsFrom_scoped
                  (annotationScoped template rfl)
          · exact ihBody bodyScoped
  | app function argument ihFunction ihArgument =>
      cases inputScoped with
      | app functionScoped argumentScoped =>
          exact .app (ihFunction functionScoped) (ihArgument argumentScoped)
  | letIn ann rhs body ihRhs ihBody =>
      cases ann with
      | none =>
          cases inputScoped with
          | letMono rhsScoped bodyScoped =>
              exact .letMono (ihRhs rhsScoped) (ihBody bodyScoped)
      | some written =>
          cases inputScoped with
          | letPoly writtenScoped rhsScoped bodyScoped =>
              have writtenScoped' :
                  written.body.Scoped rigidCount
                    ((depth + written.paramCount) + count) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  writtenScoped
              have rhsScoped' :
                  rhs.TypeScoped rigidCount
                    ((depth + written.paramCount) + count) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                  rhsScoped
              exact .letPoly
                (Template.openRigidsFrom_scoped writtenScoped')
                (ihRhs rhsScoped')
                (ihBody bodyScoped)
  | fix ann body ihBody =>
      cases inputScoped with
      | fix annotationScoped bodyScoped =>
          exact .fix
            (Template.openRigidsFrom_scoped annotationScoped)
            (ihBody bodyScoped)

end EPL
