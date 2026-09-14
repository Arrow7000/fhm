import FHM.Bounds.RecursiveVariable
import FHM.Bounds.ScopedDeclaration
import FHM.Bounds.Found

namespace FHM.Bounds.RecursiveContractTests

open RecursiveContract RecursiveTyping CountSubstitution SurfaceBridge.Provenance

private def ctors : CtorEnv := (elabDecls preludeDecls).getD []
private def span : Surface.Span.Span := ⟨1, 1, 1, 80⟩
private def leaf : Surface.Span.SpannedExpr := .leaf span
private def n : ValName := ⟨"n"⟩
private def xs : ValName := ⟨"xs"⟩
private def f : ValName := ⟨"f"⟩
private def exact : Surface.Ty := .bl (.solid (.var n)) (.solid (.var n)) (.prim .int)
private def unspecialized : Surface.Binding :=
  { name := f, natBinders := [n], ann := some ⟨[], .arrow exact exact⟩
    rhs := .lambda (.name xs) (some exact) (.app (.var f) (.var xs)) }
private def recursiveBinding (name callee : ValName) : Surface.Binding :=
  { unspecialized with
    name := name
    rhs := .lambda (.name xs) (some exact)
      (.app (.lambda (.name ⟨"ignored"⟩) (some exact) (.var xs))
        (.app (.var callee) (.var xs))) }
private def source : Surface.Binding := recursiveBinding f f
private def rhsSpan : Surface.Span.SpannedExpr :=
  .lambda span (.app span (.lambda span leaf) (.app span leaf leaf))

private def artifactFor (b : Surface.Binding) (rhsSpan : Surface.Span.SpannedExpr) : Option TypedLowered := do
  let lowered ← lowerWithProvenance ctors (.letRecIn [b] (.primLit (.int 1)))
    (.letRecIn span [rhsSpan] leaf)
  inferWithProvenance ctors lowered
private def artifact : Option TypedLowered :=
  artifactFor source rhsSpan

-- A real recursive HM artifact supplies the carried signature, fixed found
-- monotype and exact count telescope. This decodes an ASSUMPTION, not its proof.
private def declared (guarded : Bool := false) (captures : List Nat := []) : Except String Declared := do
  let a ← match artifact with | some a => pure a | none => throw "test: recursive HM artifact failed"
  let rhs ← ScopedDeclaration.locate a.inference.output (.letRec [] 0)
  let ann ← match rhs.annotation with | some a => pure a | none => throw "test: missing recursive signature"
  let hm ← match Typed.rootHM? rhs.expr with | some h => pure h | none => throw "test: missing recursive found type"
  let quantified ← ScopedDeclaration.telescope a.lowering.counts (.letRec [] 0)
  let premises := if guarded then quantified.map (fun id => (⟨.var ⟨.rigid, id⟩, .lit 0⟩ : Constraint)) else []
  RecursiveContract.decode ann hm quantified captures premises

private def specializationDeferred : Bool :=
  match artifactFor unspecialized (.lambda span (.app span leaf leaf)) with
  | none => false
  | some a => match ScopedDeclaration.locate a.inference.output (.letRec [] 0),
      ScopedDeclaration.telescope a.lowering.counts (.letRec [] 0) with
    | .ok rhs, .ok q => match rhs.annotation, Typed.rootHM? rhs.expr with
      | some ann, some hm => match RecursiveContract.decode ann hm q [] with
        | .error e => (e.splitOn "needs specialization").length > 1
        | _ => false
      | _, _ => false
    | _, _ => false

private def mutualDeclared : Except String (List Declared) := do
  let g : ValName := ⟨"g"⟩
  let lowered ← match lowerWithProvenance ctors
      (.letRecIn [recursiveBinding f g, recursiveBinding g f] (.primLit (.int 1)))
      (.letRecIn span [rhsSpan, rhsSpan] leaf) with
    | some a => pure a | none => throw "test: mutual lowering failed"
  let a ← match inferWithProvenance ctors lowered with
    | some a => pure a | none => throw "test: mutual HM artifact failed"
  (List.range 2).mapM fun member => do
    let rhs ← ScopedDeclaration.locate a.inference.output (.letRec [] member)
    let ann ← match rhs.annotation with | some a => pure a | none => throw "test: missing mutual signature"
    let hm ← match Typed.rootHM? rhs.expr with | some h => pure h | none => throw "test: missing mutual found type"
    let q ← ScopedDeclaration.telescope a.lowering.counts (.letRec [] member)
    RecursiveContract.decode ann hm q []

private def intList : Ty := listTy (.prim .int)
private def intHM : Ty := .arrow intList intList
private def charHM : Ty := .arrow (listTy (.prim .char)) (listTy (.prim .char))
private def zero : BoundsTy := .list (.lit 0) (.lit 0) (.prim .int)
private def nil : Expr := .ctor nilCtorName
private def one : Expr := .app (.app (.ctor consCtorName) (.primLit (.int 1))) nil
private def oneBounds : BoundsTy := .list (.add (.lit 0) (.lit 1)) (.add (.lit 0) (.lit 1)) (.prim .int)
private def cm : Count := .var ⟨.rigid, 99⟩
private def succeeds (r : Except String α) : Bool := match r with | .ok _ => true | _ => false
private def fails (r : Except String α) (needle : String) : Bool :=
  match r with | .error m => (m.splitOn needle).length > 1 | _ => false

private def use (args : List Count) (hm : Ty := intHM) (caller : List Nat := [])
    (Δ : List Constraint := []) (guarded : Bool := false) (captures : List Nat := []) := do
  let c ← declared guarded captures
  let r ← RecursiveVariable.check [] [] Δ [.recursive c] 0 hm args caller
  pure r.bounds

private def call (arg : Expr) (actual : BoundsTy)
    (typing : ∀ c, Derives [] [] Δ [.recursive c] arg actual)
    (args : Option (List Count) := none) (hm : Ty := intHM) (resultHM : Ty := intList)
    (guarded : Bool := false) : Except String BoundsTy := do
  let c ← declared guarded
  let r ← match args with
    | none => RecursiveVariable.inferApplication [] [] Δ [.recursive c] 0 arg actual (typing c) hm resultHM []
    | some args => RecursiveVariable.application [] [] Δ [.recursive c] 0 arg actual (typing c) hm resultHM args []
  pure r.bounds

private def mutualCalls : Bool :=
  match mutualDeclared with
  | .error _ => false
  | .ok cs =>
      let env := cs.map Binding.recursive
      succeeds (RecursiveVariable.inferApplication [] [] [] env 0 nil zero .nil intHM intList []) &&
        succeeds (RecursiveVariable.inferApplication [] [] [] env 1 one oneBounds
          (.cons .literal .nil (SemanticSub.refl [] (.prim .int))) intHM intList [])

private def freeAnnotation : PolyTy :=
  let ty : Ty := .bl (.solid cm) (.solid cm) (.fvar 7)
  ⟨0, .arrow ty ty⟩
private def freeHM : Ty := .arrow (listTy (.fvar 7)) (listTy (.fvar 7))
private def freeUse (hm : Ty) : Except String BoundsTy := do
  let c ← RecursiveContract.decode freeAnnotation freeHM [99] []
  let used ← RecursiveContract.check c [] hm [.lit 2] []
  pure used.bounds

private def formalN : Count := .var ⟨.rigid, 7⟩
private def formalList : BoundsTy := .list formalN formalN (.prim .int)
private def formalContract : Declared :=
  { hm := intHM, counts := ⟨[7], [], [], .arrow formalList formalList⟩
    wf := ScopedScheme.Scheme.wfBool_sound (by decide)
    shape := by simp [intHM, intList, formalList, Synth.BoundsTy.toTy, listTy,
      FHM.Bounds.listTyName]
    lc := (Ty.bvarsBelow_iff intHM).mp (by decide) }

private def otherContract : Declared :=
  let k : Count := .var ⟨.rigid, 8⟩
  let ty : BoundsTy := .list k k (.prim .int)
  { formalContract with
    counts := ⟨[8], [], [], .arrow ty ty⟩
    wf := ScopedScheme.Scheme.wfBool_sound (by decide)
    shape := by simp [ty, formalContract, intHM, intList, Synth.BoundsTy.toTy, listTy,
      FHM.Bounds.listTyName] }
private def capturedContract : Declared :=
  { formalContract with
    counts := ⟨[7], [8], [], .arrow formalList formalList⟩
    wf := ScopedScheme.Scheme.wfBool_sound (by decide) }

private def loop : Expr := .lambda none (.app (.var 1) (.var 0))
private def formalTy : Ty := .bl (.solid formalN) (.solid formalN) (.prim .int)
private def formalSignature : PolyTy := ⟨0, .arrow formalTy formalTy⟩
private def decodedList : ScopedAnnotation.Decoded [7] formalTy :=
  ⟨formalList, by simp [formalList, ScopedScheme.BoundsScoped, Scope.CountScoped, formalN],
    by simp [formalList, formalTy, Synth.BoundsTy.toTy, Ty.eraseBounds, listTy,
      bareListTy, FHM.Bounds.listTyName, _root_.listTyName]⟩
private def decodedArrow : ScopedAnnotation.Decoded [7] formalSignature.body :=
  ⟨.arrow formalList formalList, ⟨decodedList.inScope, decodedList.inScope⟩,
    by simpa [formalSignature, Synth.BoundsTy.toTy, Ty.eraseBounds] using
      congrArg₂ Ty.arrow decodedList.shape decodedList.shape⟩
private theorem decodedList_eq : ScopedAnnotation.decode [7] formalTy = .ok decodedList := by
  simp [formalTy, ScopedAnnotation.decode, ScopedScheme.countScopedBool, formalN, decodedList, formalList]
  rfl
private theorem decodedArrow_eq : ScopedAnnotation.decode [7] formalSignature.body = .ok decodedArrow := by
  simp [formalSignature, ScopedAnnotation.decode, decodedList_eq, decodedList, decodedArrow]
  rfl

/-- A solver-free simultaneous group derivation. The self-recursive call works
    at EVERY scoped finite count use, not just one sample. It may diverge; this
    is static bounds typing, not a claim of termination or runtime soundness. -/
private theorem formalGroup :
    Derives [] [] [] [] (.letRec [none] [loop] (.primLit (.int 1))) (.prim .int) := by
  apply Derives.letRec (contracts := [formalContract])
    (actuals := fun _ args => bounds ([7].zip args) (.arrow formalList formalList))
  · rfl
  · rfl
  · exact ⟨by decide, by simp [formalContract]⟩
  · simp
  · intro i c rhs ann hc hr ha args caller inst
    cases i with
    | succ i => simp at hc
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hr ha
        subst c; subst rhs; subst ann
        apply Derives.lambda (ann := none) True.intro
        apply Derives.app
        · exact .varRecursive rfl inst (by intro σ h goal hg; exact h goal hg)
        · exact .varMono rfl
        · exact SemanticSub.refl _ _
  · intro i c rhs ann hc hr ha args caller inst
    cases i with
    | succ i => simp at hc
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hr ha
        subst ann
        trivial
  · intro i c rhs ann hc hr ha args caller inst
    cases i with
    | succ i => simp at hc
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hr ha
        subst c
        exact SemanticSub.refl _ _
  · exact .literal

/-- Universal checking also retains the original symbolic lambda and binding
    annotations; neither is discarded to obtain the group premise. -/
private theorem formalAnnotatedGroup : Derives [] [] [] []
    (.letRec [some formalSignature] [.lambda (some formalTy) (.var 0)] (.primLit (.int 1))) (.prim .int) := by
  apply Derives.letRec (contracts := [formalContract])
    (actuals := fun _ args => bounds ([7].zip args) (.arrow formalList formalList))
  · rfl
  · rfl
  · exact ⟨by decide, by simp [formalContract]⟩
  · simp
  · intro i c rhs ann hc hr ha args caller inst
    cases i with
    | succ i => simp at hc
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hr ha
        subst c; subst rhs; subst ann
        exact .lambda ⟨decodedList, decodedList_eq, SemanticSub.refl _ _⟩ (.varMono rfl)
  · intro i c rhs ann hc hr ha args caller inst
    cases i with
    | succ i => simp at hc
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hr ha
        subst c; subst ann
        exact ⟨rfl, decodedArrow, decodedArrow_eq, SemanticSub.refl _ _⟩
  · intro i c rhs ann hc hr ha args caller inst
    cases i with
    | succ i => simp at hc
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hc hr ha
        subst c
        exact SemanticSub.refl _ _
  · exact .literal

example {c Δ found caller} (u : RecursiveContract.Use c Δ found caller) :
    Synth.BoundsTy.toTy u.bounds = found.eraseBounds := u.shape

example {ids rows Δ env i arg actual functionHM resultHM caller}
    (r : RecursiveVariable.Application ids rows Δ env i arg actual functionHM resultHM caller) :
    Derives ids rows Δ env (.app (.var i) arg) r.bounds ∧ SemanticSub Δ actual r.domain :=
  ⟨r.derivation, r.inclusion⟩

private def cases : List (String × Bool) := [
  ("recursive assumption decoded from actual self-recursive HM artifact", succeeds (declared false)),
  ("recursive variable supports independent count instantiations", succeeds (use [.lit 0]) && succeeds (use [.lit 4])),
  ("recursive variable rejects changing Int to Char", fails (use [.lit 0] charHM) "fixed HM monotype"),
  ("free recursive HM identity remains fixed", succeeds (freeUse freeHM)),
  ("free recursive HM identity cannot specialize to Int", fails (freeUse intHM) "fixed HM monotype"),
  ("recursive Nat arguments reject infinity", fails (use [.inf]) "finite"),
  ("recursive count arity checked", fails (use []) "arity"),
  ("recursive count caller scope checked", fails (use [cm]) "outside caller scope"),
  ("scoped symbolic recursive count accepted", succeeds (use [cm] intHM [99])),
  ("recursive premises require independent caller evidence", fails (use [.lit 1] intHM [] [] true) "not established"),
  ("true recursive premises independently discharged", succeeds (use [.lit 0] intHM [] [] true)),
  ("recursive captured coordinates require caller scope", fails (use [.lit 0] intHM [] [] false [99]) "capture"),
  ("recursive captures preserved when in caller scope", succeeds (use [.lit 0] intHM [99] [] false [99])),
  ("implicit recursive Nil call infers zero", succeeds (call nil zero (Δ := []) (fun _ => .nil))),
  ("implicit recursive Cons call infers one", succeeds
    (call one oneBounds (Δ := []) (fun _ => .cons .literal .nil (SemanticSub.refl [] (.prim .int))))),
  ("explicit recursive call rejects wrong list length", fails
    (call nil zero (Δ := []) (fun _ => .nil) (some [.lit 1])) "interval inclusion"),
  ("recursive application rejects HM polymorphic use", fails
    (call nil zero (Δ := []) (fun _ => .nil) none charHM (listTy (.prim .char))) "fixed HM monotype"),
  ("recursive result found payload checked separately", fails
    (call nil zero (Δ := []) (fun _ => .nil) none intHM (listTy (.prim .char))) "result disagrees"),
  ("implicit recursive call does not assert failed premises", fails
    (call one oneBounds (Δ := []) (fun _ => .cons .literal .nil (SemanticSub.refl [] (.prim .int)))
      none intHM intList true) "not established"),
  ("decoder rejects independent polymorphic annotation opening", fails
    (RecursiveContract.decode ⟨1, .arrow (.bvar 0) (.bvar 0)⟩ (.arrow (.fvar 7) (.fvar 7)) [] []) "fixed opening"),
  ("decoder rejects mismatching fixed HM signature", fails
    (RecursiveContract.decode freeAnnotation intHM [99] []) "fixed HM monotype"),
  ("decoder rejects unscoped declaration counts", fails
    (RecursiveContract.decode freeAnnotation freeHM [] []) "lexical scope"),
  ("decoder rejects enclosing HM slots", fails
    (RecursiveContract.decode ⟨0, .arrow (.bvar 0) (.bvar 0)⟩ (.arrow (.bvar 0) (.bvar 0)) [] []) "enclosing bound slot"),
  ("monomorphic assumption has no count telescope", fails
    (RecursiveVariable.check [] [] [] [.mono zero] 0 intList [.lit 0] []) "no count telescope"),
  ("recursive variable outside environment rejected", fails
    (RecursiveVariable.check [] [] [] [] 0 intHM [] []) "outside assumption environment"),
  ("valid HM self-loop needing RHS specialization explicitly deferred", specializationDeferred),
  ("group rejects duplicate quantified count interfaces", !independentBool [formalContract, formalContract]),
  ("single recursive count interface is independent", independentBool [formalContract]),
  ("actual mutually recursive HM artifact has independent count telescopes", match mutualDeclared with
    | .ok cs => cs.length == 2 && independentBool cs
    | _ => false),
  ("two mutual assumptions permit different count calls at fixed HM types", mutualCalls),
  ("group member cannot capture another member's quantified coordinate",
    !independentBool [capturedContract, otherContract])]

def main : IO Unit := do
  for (name, ok) in cases do
    IO.println s!"{if ok then "PASS" else "FAIL"}: {name}"
    unless ok do throw (IO.userError s!"recursive contract regression: {name}")

#eval main
#print axioms formalGroup
#print axioms formalAnnotatedGroup

end FHM.Bounds.RecursiveContractTests
