import EPL.RuntimeTyping

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

private theorem wf_openWith
    {ty : Ty} {rigidCount binderCount : Nat} {args : List Ty}
    (wf : ty.WF rigidCount binderCount)
    (hlen : args.length = binderCount)
    (hargs : ∀ arg ∈ args, arg.WF rigidCount 0) :
    (ty.openWith args).WF rigidCount 0 := by
  exact ⟨scoped_openWith wf.1 hlen (fun arg harg => (hargs arg harg).1),
    metaFree_openWith wf.2 (fun arg harg => (hargs arg harg).2)⟩

/-- Runtime typing also assigns only scoped, meta-free semantic types. -/
theorem regular (typing : RuntimeTyping rigidCount ctx expr ty) :
    ty.WF rigidCount 0 := by
  induction typing with
  | primLit => cases_type PrimLit <;> exact ⟨.prim, .prim⟩
  | primOp =>
      cases_type PrimOp
      exact ⟨.arrow .prim (.arrow .prim .prim),
        .arrow .prim (.arrow .prim .prim)⟩
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

end RuntimeTyping
end EPL
