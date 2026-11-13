import EPL.Typing

namespace EPL.Examples

open EPL

def intTy : Ty := .prim .int

/-- `data Bool = True | False`, as type `con 0`. -/
def boolSig : Signature := [⟨0, [[], []]⟩]
def boolTy : Ty := .con 0
def trueExpr : Expr T := .const (.ctor 0 0 0)
def falseExpr : Expr T := .const (.ctor 0 1 0)

def polyIdentityScheme : PolyTy :=
  ⟨1, .arrow (.bvar 0) (.bvar 0)⟩

def polyIdentityAnnotation : Scheme Template :=
  ⟨1, .arrow (.fixed (.bvar 0)) (.fixed (.bvar 0))⟩

def identityRhs : Source :=
  .lambda none (.var 0)

private theorem prim_wf (p : PrimTy) : (Ty.prim p).WF rigidCount 0 :=
  ⟨.prim, .prim⟩

private theorem con_wf (id : Nat) : (Ty.con id).WF rigidCount 0 :=
  ⟨.con id, .con⟩

private theorem rigid_wf (h : level < rigidCount) :
    (Ty.rigid level).WF rigidCount 0 :=
  ⟨.rigid h, .rigid⟩

private theorem arrow_wf (ha : a.WF rigidCount 0) (hb : b.WF rigidCount 0) :
    (Ty.arrow a b).WF rigidCount 0 :=
  ⟨.arrow ha.1 hb.1, .arrow ha.2 hb.2⟩

private theorem fixed_matches (ty : Ty) :
    Template.Matches (.fixed ty) ty :=
  ⟨[], by simp [HoleAssignment.Unique], .fixed⟩

private theorem absent_matches (ty : Ty) : ParamAnn.Matches none ty := by
  intro template h
  cases h

private theorem openWith_nil_of_scoped_zero {ty : Ty} (h : ty.Scoped rigidCount 0) :
    ty.openWith [] = ty := by
  induction h with
  | prim => rfl
  | arrow _ _ ihDomain ihCodomain =>
      simp only [Ty.openWith, ihDomain, ihCodomain]
  | bvar hlt => omega
  | rigid => rfl
  | mvar => rfl
  | con => rfl
  | app _ _ ihDomain ihCodomain =>
      simp only [Ty.openWith, ihDomain, ihCodomain]

private theorem mono_var_inv
    (lookup : ctx[index]? = some (PolyTy.mono expected))
    (typing : Typing sig rigidCount ctx (.var index) actual) :
    actual = expected := by
  cases typing with
  | var =>
      rename_i scheme args lengthEq inferredWF _ inferredLookup
      have schemeEq : scheme = PolyTy.mono expected :=
        Option.some.inj (inferredLookup.symm.trans lookup)
      subst scheme
      have argsNil : args = [] := List.eq_nil_of_length_eq_zero (by
        simpa [PolyTy.mono] using lengthEq)
      subst args
      simpa [PolyTy.openWith, PolyTy.mono] using
        openWith_nil_of_scoped_zero inferredWF.1

private theorem identity_type
    (typing : Typing sig rigidCount ctx identityRhs ty) :
    ∃ param, ty = .arrow param param := by
  cases typing with
  | lambda =>
      rename_i paramTy bodyTy _ _ bodyTyping
      have bodyEq : bodyTy = paramTy := mono_var_inv (by simp [PolyTy.mono]) bodyTyping
      subst bodyTy
      exact ⟨paramTy, rfl⟩

private theorem int_literal_type
    (typing : Typing sig rigidCount ctx (.primLit (.int value)) ty) :
    ty = intTy := by
  cases typing
  rfl

/-- Opening a `con`-headed type application can never produce a primitive
type. -/
private theorem apps_openWith_not_prim (head : Ty) (args : List Ty) (p : PrimTy)
    (hhead : ∀ targs, head.openWith targs ≠ .prim p) (targs : List Ty) :
    (Ty.apps head args).openWith targs ≠ .prim p := by
  induction args generalizing head with
  | nil => simpa [Ty.apps] using hhead targs
  | cons a t ih =>
      apply ih (.app head a)
      intro targs' h
      simp only [Ty.openWith] at h
      cases h

private theorem selfTy_openWith_not_prim (decl : DataDecl) (type : Nat)
    (args : List Ty) (p : PrimTy) :
    (decl.selfTy type).openWith args ≠ .prim p := by
  unfold DataDecl.selfTy
  apply apps_openWith_not_prim
  intro targs h
  simp only [Ty.openWith] at h
  cases h

private theorem arrows_openWith_not_prim (fields : List Ty) (result : Ty)
    (args : List Ty) (p : PrimTy) (hresult : result.openWith args ≠ .prim p) :
    (Ty.arrows fields result).openWith args ≠ .prim p := by
  induction fields with
  | nil => simpa [Ty.arrows] using hresult
  | cons a t _ =>
      simp only [Ty.arrows, List.foldr_cons, Ty.openWith]
      intro h
      cases h

private theorem ctor_scheme_eq {sig : Signature} {type ctor arity : Nat}
    {scheme : PolyTy}
    (h : sig.schemeOf (.ctor type ctor arity) = some scheme) :
    ∃ (decl : DataDecl) (fields : List Ty),
      fields.length = arity ∧ scheme = decl.ctorScheme type fields := by
  unfold Signature.schemeOf at h
  cases hdecl : sig[type]? with
  | none => simp [hdecl] at h
  | some decl =>
      cases hfields : decl.ctors[ctor]? with
      | none => simp [hdecl, hfields] at h
      | some fields =>
          by_cases hlen : fields.length = arity
          · simp [hdecl, hfields, hlen] at h
            exact ⟨decl, fields, hlen, h.symm⟩
          · simp [hdecl, hfields, hlen] at h

private theorem ctor_const_type_head {sig : Signature} {rigidCount : Nat}
    {ctx : Ctx} {type ctor arity : Nat} {ty : Ty}
    (typing : Typing sig rigidCount ctx (.const (.ctor type ctor arity)) ty) :
    ∃ scheme args, sig.schemeOf (.ctor type ctor arity) = some scheme ∧
      ty = scheme.openWith args := by
  cases typing with
  | const hscheme _ _ _ => exact ⟨_, _, hscheme, rfl⟩

/-- No constructor constant can have a primitive type, since its scheme is
headed by a declared type. -/
private theorem ctor_const_not_prim {sig : Signature} {rigidCount : Nat}
    {ctx : Ctx} {type ctor arity : Nat} {p : PrimTy}
    (typing : Typing sig rigidCount ctx (.const (.ctor type ctor arity)) (.prim p)) :
    False := by
  obtain ⟨scheme, args, hscheme, hty⟩ := ctor_const_type_head typing
  obtain ⟨decl, fields, _, hsch⟩ := ctor_scheme_eq hscheme
  subst scheme
  have hty' : (Ty.arrows fields (decl.selfTy type)).openWith args = .prim p := by
    simpa [DataDecl.ctorScheme, PolyTy.openWith] using hty.symm
  exact arrows_openWith_not_prim fields (decl.selfTy type) args p
    (selfTy_openWith_not_prim decl type args p) hty'

/-- The outer identity is explicitly polymorphic. The nested monomorphic let
uses it at `Int`, then the continuation uses it independently at `Bool`. -/
def explicitPolyProgram : Source :=
  .letIn (some polyIdentityAnnotation) identityRhs
    (.letIn none
      (.app (.var 0) (.primLit (.int 5)))
      (.app (.var 1) trueExpr))

theorem explicitPolyProgram_typed :
    Typing boolSig 0 [] explicitPolyProgram boolTy := by
  apply Typing.letPoly (scheme := polyIdentityScheme)
  · exact ⟨rfl, ⟨[], by simp [HoleAssignment.Unique], .arrow .fixed .fixed⟩⟩
  · exact ⟨.arrow (.bvar (by decide)) (.bvar (by decide)), .arrow .bvar .bvar⟩
  · simp [Ctx.WF]
  · exact .lambda (by intro template h; cases h) .var
  · simpa [identityRhs, Expr.openRigids, Expr.openRigidsFrom,
      polyIdentityScheme, PolyTy.openRigids, PolyTy.openWith, rigidBlock,
      Ty.openWith] using
      (Typing.lambda (ctx := []) (ann := none) (body := .var 0)
        (bodyTy := .rigid 0) (paramTy := .rigid 0)
        (rigid_wf (rigidCount := 1) (by decide)) (absent_matches (.rigid 0))
        (Typing.var (scheme := PolyTy.mono (.rigid 0)) (args := [])
          (by simp [PolyTy.mono])
          ⟨.rigid (by decide), .rigid⟩ rfl (by simp)))
  · apply Typing.letMono (rhsTy := intTy) (prim_wf .int)
    · apply Typing.app (argumentTy := intTy)
      · exact Typing.var (scheme := polyIdentityScheme) (args := [intTy])
          (by simp [polyIdentityScheme])
          ⟨.arrow (.bvar (by decide)) (.bvar (by decide)), .arrow .bvar .bvar⟩
          rfl (by
            intro arg h
            simp only [List.mem_singleton] at h
            subst arg
            exact prim_wf .int)
      · exact .primLit
    · apply Typing.app (argumentTy := boolTy)
      · exact Typing.var (scheme := polyIdentityScheme) (args := [boolTy])
          (by simp [PolyTy.mono, polyIdentityScheme])
          ⟨.arrow (.bvar (by decide)) (.bvar (by decide)), .arrow .bvar .bvar⟩
          rfl (by
            intro arg h
            simp only [List.mem_singleton] at h
            subst arg
            exact con_wf 0)
      · exact Typing.const (c := .ctor 0 0 0) (scheme := PolyTy.mono boolTy)
          (args := []) (by decide) (con_wf 0) rfl (by simp)

/-- Without the written `forall`, the same identity has one monotype and
cannot be used at both `Int` and `Bool`. -/
def implicitPolyProgram : Source :=
  .letIn none identityRhs
    (.letIn none
      (.app (.var 0) (.primLit (.int 5)))
      (.app (.var 1) trueExpr))

theorem implicitPolyProgram_untypable :
    ¬ ∃ ty, Typing sig 0 [] implicitPolyProgram ty := by
  rintro ⟨ty, typing⟩
  cases typing with
  | letMono =>
      rename_i rhsTy rhsWF rhsTyping bodyTyping
      obtain ⟨param, rhsTyEq⟩ := identity_type rhsTyping
      subst rhsTy
      cases bodyTyping with
      | letMono =>
          rename_i nestedTy nestedWF nestedRhsTyping nestedBodyTyping
          cases nestedRhsTyping with
          | app =>
              rename_i argumentTy functionTyping argumentTyping
              have functionEq :
                  Ty.arrow argumentTy nestedTy = Ty.arrow param param :=
                mono_var_inv (by simp [PolyTy.mono]) argumentTyping
              have argumentEq : argumentTy = intTy := int_literal_type functionTyping
              have paramEq : param = intTy := by
                injection functionEq with domainEq _
                exact domainEq.symm.trans argumentEq
              have nestedEq : nestedTy = param := by
                exact (Ty.arrow.inj functionEq).2
              subst param
              subst nestedTy
              cases nestedBodyTyping with
              | app =>
                  rename_i finalArgumentTy finalFunctionTyping finalArgumentTyping
                  have finalFunctionEq :
                      Ty.arrow finalArgumentTy ty = Ty.arrow intTy intTy :=
                    mono_var_inv
                      (ctx := [PolyTy.mono intTy, PolyTy.mono (.arrow intTy intTy)])
                      (index := 1) (expected := .arrow intTy intTy)
                      (by simp [PolyTy.mono]) finalArgumentTyping
                  have finalArgumentEq : finalArgumentTy = intTy :=
                    (Ty.arrow.inj finalFunctionEq).1
                  subst finalArgumentTy
                  exact ctor_const_not_prim finalFunctionTyping

/-- An omitted lambda annotation is constrained by how its parameter is used
inside the body. -/
def inferredIntLambda : Source :=
  .lambda none
    (.app (.app (.primOp .intAdd) (.var 0)) (.primLit (.int 1)))

theorem inferredIntLambda_typed :
    Typing sig 0 [] inferredIntLambda (.arrow intTy intTy) := by
  apply Typing.lambda (paramTy := intTy) (prim_wf .int) (absent_matches intTy)
  apply Typing.app (argumentTy := intTy)
  · apply Typing.app (argumentTy := intTy)
    · exact .primOp rfl
    · exact Typing.var (scheme := PolyTy.mono intTy) (args := [])
        (by simp [PolyTy.mono]) (prim_wf .int) rfl (by simp)
  · exact .primLit

/-- General recursion is monomorphic and has no recursive binding group. This
loop is intentionally divergent but has the ordinary function type. -/
def integerLoop : Source :=
  .fix (.fixed (.arrow intTy intTy))
    (.lambda (some (.fixed intTy))
      (.app (.var 1) (.var 0)))

theorem integerLoop_typed :
    Typing sig 0 [] integerLoop (.arrow intTy intTy) := by
  apply Typing.fix (selfTy := .arrow intTy intTy)
  · exact arrow_wf (prim_wf .int) (prim_wf .int)
  · exact fixed_matches (.arrow intTy intTy)
  · apply Typing.lambda (paramTy := intTy) (prim_wf .int)
      (by
        intro template h
        cases h
        exact fixed_matches intTy)
    apply Typing.app (argumentTy := intTy)
    · exact Typing.var (scheme := PolyTy.mono (.arrow intTy intTy)) (args := [])
        (by simp [PolyTy.mono])
        (arrow_wf (prim_wf .int) (prim_wf .int)) rfl (by simp)
    · exact Typing.var (scheme := PolyTy.mono intTy) (args := [])
        (by simp [PolyTy.mono]) (prim_wf .int) rfl (by simp)

end EPL.Examples
