import FHM.Unverified.RecoveryArtifacts

/-! Recovery of source subexpressions in actual lexical inference contexts.
Native success is the only source of fragment types and binding schemes.
Failed source expressions always return no type. Their independent children can
still contribute checked artifacts and successful contextual constraints. -/
namespace FHM.Unverified.ExpressionRecovery
open SurfaceBridge SurfaceBridge.Provenance Surface.Span RecoveryDependencies RecoveryArtifacts

structure State where
  context : Context
  checked : List CheckedSlice := []
  unavailable : List UnavailableSlice := []
  diagnostics : List HoverDiag := []
  subst : Subst := []

structure Fact where
  ty : Ty
  after : Nat
  annotation : Bool := false

def Fact.current (fact : Fact) (state : State) : Ty := Subst.onTy (state.subst.drop fact.after) fact.ty

private def applySubst (state : State) (subst : Subst) (frontier : Nat) : State :=
  { state with
    context := { state.context.onSubst subst with frontier := max frontier state.context.frontier }
    checked := state.checked.map (fun slice => { slice with typed := slice.typed.onSubst subst })
    subst := state.subst ++ subst }

private def accept (state : State) (slice : CheckedSlice) (emit : Bool := true) : State :=
  let state := applySubst state slice.typed.inference.subst slice.typed.inference.frontier
  if emit then { state with checked := state.checked ++ [slice] } else state

private def restore (state : State) (outer : Context) (start : Nat) : State :=
  { state with context := { outer.onSubst (state.subst.drop start) with frontier := state.context.frontier } }

private def causes (source : Source) (context : Context) (expr : Surface.Expr) : List Cause :=
  (context.causesFor (Surface.freeNames [] expr) ++
    DeclarationRecovery.causesFor source.declarations (expression expr)).eraseDups

private def addError (state : State) (error : HoverDiag) : State :=
  if state.diagnostics.any (fun existing => existing.code? == error.code? && existing.line == error.line && existing.col == error.col) then
    { state with diagnostics := state.diagnostics.map (fun existing =>
      if existing.code? == error.code? && existing.line == error.line && existing.col == error.col &&
          (error.endLine < existing.endLine || (error.endLine == existing.endLine && error.endCol ≤ existing.endCol))
        then error else existing) }
  else { state with diagnostics := state.diagnostics ++ [error] }

private def diagnosticSpan (diagnostic : HoverDiag) : Span :=
  ⟨diagnostic.line, diagnostic.col, diagnostic.endLine, diagnostic.endCol⟩

/-- Retain native root failures, including recursive-call constraints that
cannot be reconstructed without provisional member types. Replace only a broad
ancestor or recursive result-shape cascade with a more precise source failure. -/
def withNativeFailure (before : Nat) (diagnostic : HoverDiag) (state : State) : State :=
  let children := state.diagnostics.drop before
  let same := children.any (fun child => child.code? == diagnostic.code? &&
    child.line == diagnostic.line && child.col == diagnostic.col)
  let represented := diagnostic.code? == some "type.mismatch" && children.any fun child =>
    child.code? == diagnostic.code? && match diagnostic.constraint?, child.constraint? with
      | some (a, b), some (c, d) => decide ((a = c ∧ b = d) ∨ (a = d ∧ b = c))
      | _, _ => false
  let ancestor := !same && diagnostic.code?.any (·.startsWith "type.") &&
    children.any (fun child => HMArtifacts.inside (diagnosticSpan child) (diagnosticSpan diagnostic) &&
      diagnosticSpan child != diagnosticSpan diagnostic)
  let dependent := diagnostic.code? == some "type.mismatch" &&
    children.any (·.code? == some "type.annotationMismatch") && state.unavailable.any (fun slice =>
      match slice.program.term with
      | .var _ => !slice.causes.isEmpty && slice.tree.span.contains diagnostic.line diagnostic.col
      | _ => false)
  if diagnostic.code? != some "type.infiniteType" && (represented || ancestor || dependent) then state
  else addError state diagnostic

private def markUnavailable (state : State) (source : Source) (roots : List Cause) : State :=
  match RecoveryArtifacts.unavailable source roots with
  | .error error => addError state error
  | .ok slice => { state with unavailable := state.unavailable ++ [slice] }

private def stripGenerated : SpannedExpr → SpannedExpr
  | .generated tree | .generatedRoot tree => stripGenerated tree
  | tree => tree

private def rootCause (name : ValName) (span : Span) : List Cause := [.localBinding name span]

/-- Administrative lets keep every pattern capture in the native compilation
trace. Their generated Unit termination is never exposed as a source result. -/
private def captureBody (names : List ValName) (span : Span) : Surface.Expr × SpannedExpr :=
  names.zipIdx.foldr (fun (name, index) (body, tree) =>
    (.letIn ⟨s!"$recover/capture/{index}"⟩ [] [] none (.var name) body,
      .generated (.letIn span (.generated (.leaf span)) tree)))
    (.primLit .unit, .generated (.leaf span))

private def captureTypes (pat : Surface.Pattern) (typed : TypedLowered) : Option (List PolyTy) :=
  match pat with
  | .name _ => do
      let .arrow domain _ := typed.inference.ty | none
      pure [PolyTy.mkTrivial domain]
  | .wildcard => some []
  | _ => (Surface.patVars pat).zipIdx.mapM fun (_, capture) => do
      let (_, facts) ← typed.patternBinderTypes.find? fun (site, _) => match site with
        | .patCapture _ 0 index => index == capture
        | _ => false
      let (_, ty) ← facts.head?
      pure (PolyTy.mkTrivial ty)

private def lexical (source : Source) (expr : Surface.Expr) (tree : SpannedExpr)
    (names : List ValName) (scope : Span) : List HMArtifacts.BinderLocation :=
  let locations := HMArtifacts.collect source.binders expr (identify tree)
  locations.binders.filterMap fun binder =>
    if names.contains (.mk binder.name) && HMArtifacts.before binder.span scope then
      some { binder with scope }
    else none

private def require (value : Option α) (error : HoverDiag) : Except HoverDiag α :=
  match value with | some value => .ok value | none => .error error

private def patternHeader (source : Source) (state : State) (pat : Surface.Pattern)
    (ann : Option Surface.Ty) (owner body : Span) : Except HoverDiag (CheckedSlice × List PolyTy) := do
  let (expr, tree) := captureBody (Surface.patVars pat) body
  let header := source.expression (.lambda pat ann expr) (.generatedRoot (.lambda owner tree))
  let slice ← RecoveryArtifacts.check state.context header source.declarations.ctors
  let types ← require (captureTypes pat slice.typed)
    { diagAtSpan "internal recovered pattern capture missing" (some owner) with code? := some "internal.recoveryArtifact" }
  pure (slice, types)

private def compareTypes (source : Source) (state : State) (actual expected : Ty) (span : Span) (annotation : Bool := false) : State :=
  match unifyResultK state.context.protectedVars actual expected with
  | .ok result =>
      let escaped := state.context.escaping result.val
      if escaped.isEmpty then applySubst state result.val state.context.frontier else
        addError state (Diagnostics.inferenceDiag (InferError.root (.escapingVariables escaped))
          (authoredRoot ⟨0, span, true⟩ (.primLit .unit)) source.program source.spanned source.binders (.leaf span))
  | .error error =>
      let reason : InferErrorReason := if annotation then .annotation (.unification error) else .unification error
      let diagnostic := Diagnostics.inferenceDiag (InferError.root reason)
        (authoredRoot ⟨0, span, true⟩ (.primLit .unit)) source.program source.spanned source.binders (.leaf span)
      addError state diagnostic

private def enterPattern (source : Source) (state : State) (expr : Surface.Expr) (tree : SpannedExpr)
    (pat : Surface.Pattern) (types : List PolyTy) (body : Span) : State :=
  let names := Surface.patVars pat
  { state with context := { state.context.withBindings names types with
    lexical := lexical source expr tree names body ++ state.context.lexical } }

private def enterUnknown (state : State) (names : List ValName) (roots : List Cause) : State :=
  { state with context := state.context.withUnavailable names roots }

private def bindingHeader (source : Source) (binding : Surface.Binding) (rhs : SpannedExpr)
    (scope : Span) : Source :=
  let grouped := source.group [binding] [rhs] scope
  { grouped with
    program := { grouped.program with groups := [], body := .letIn binding.name binding.tyParams binding.params binding.ann binding.rhs (.primLit .unit) }
    spanned := { grouped.spanned with groups := [], body := .generatedRoot (.letIn scope rhs (.generated (.leaf scope))) } }

private def recHeader (source : Source) (bindings : List Surface.Binding) (rhss : List SpannedExpr)
    (scope : Span) : Source :=
  let grouped := source.group bindings rhss scope
  { grouped with
    program := { grouped.program with groups := [], body := .letRecIn bindings (.primLit .unit) }
    spanned := { grouped.spanned with groups := [], body := .generatedRoot (.letRecIn scope rhss (.generated (.leaf scope))) } }

private def wrapParameters (source : Source) (binding : Surface.Binding) (tree : SpannedExpr)
    (scope : Span) : Surface.Expr × SpannedExpr :=
  let name := match binding.name with | .mk name => name
  let owner := (source.binders.filter fun binder => binder.name == name && binder.kind == .val &&
    HMArtifacts.inside binder.span scope && HMArtifacts.before binder.span tree.span).getLast?
  let header := { scope with
    startLine := (owner.map (·.span.startLine)).getD scope.startLine
    startCol := (owner.map (·.span.startCol)).getD scope.startCol }
  let parameters := (source.binders.filter fun binder => binder.kind == .param && source.valueBinderSpans.contains binder.span &&
    HMArtifacts.inside binder.span header && HMArtifacts.before binder.span tree.span).mergeSort fun a b =>
      a.span.startLine < b.span.startLine || (a.span.startLine == b.span.startLine && a.span.startCol ≤ b.span.startCol)
  let starts := binding.params.zipIdx.map fun ((name, _), index) =>
    let candidate := parameters[index]?
    match candidate with
    | some binder => if name == ValName.mk binder.name then binder.span else tree.span
    | none => tree.span
  (binding.params.zip starts).foldr (fun ((name, ann), start) (body, child) =>
    let span := { tree.span with startLine := start.startLine, startCol := start.startCol }
    (.lambda (.name name) ann body, .generatedRoot (.lambda span child))) (binding.rhs, tree)

private def rhsContext (state : State) (binding : Surface.Binding) : Context :=
  let typePrefix := letAnnTyPrefix binding.tyParams (finalizeInputAnn binding.tyParams binding.params binding.ann)
  let written := freshVars state.context.frontier typePrefix.length
  { state.context with
    tvs := typePrefix ++ state.context.tvs
    written := written ++ state.context.written
    protectedVars := state.context.protectedVars ++ written
    frontier := state.context.frontier + typePrefix.length
    boundaries := if written.isEmpty then state.context.boundaries else
      (written, state.context.schemes) :: state.context.boundaries }

private def rhsExpected (source : Source) (state : State) (outer : Context)
    (binding : Surface.Binding) : State × Option Fact := Id.run do
  let ann := lowerInputLetAnnResult (kindEnvOfCtors source.declarations.ctors) outer.tvs
    (finalizeInputAnn binding.tyParams binding.params binding.ann)
  match ann with
  | .error _ => return (state, none)
  | .ok ann =>
    let input : InferInput := .letIn ann (.primLit .unit) (.primLit .unit)
    let .letIn ann _ _ := input.openSourceTyVars outer.written | return (state, none)
    let written := state.context.written.take (state.context.written.length - outer.written.length)
    match ann.annotationView with
    | .complete scheme => return (state, some ⟨scheme.openVars written, state.subst.length, true⟩)
    | .template template | .partialForall _ template =>
        match seedResult state.context.protectedVars state.context.frontier
            (some (template.openTyVarsFrom 0 written)) with
        | .error _ => return (state, none)
        | .ok seeded => return ({ state with context := { state.context with frontier := seeded.val.1 } },
            some ⟨seeded.val.2, state.subst.length, true⟩)
    | .absent => return (state, none)

private def validateAnnotation (source : Source) (state : State) (binding : Surface.Binding)
    (tree : SpannedExpr) (scope : Span) : State :=
  let finalized := finalizeInputAnn binding.tyParams binding.params binding.ann
  let uses : Uses := ⟨(finalized.map (fun ann => typeNames ann.body)).getD [], []⟩
  if !(DeclarationRecovery.causesFor source.declarations uses).isEmpty then state else
  match lowerInputLetAnnResult (kindEnvOfCtors source.declarations.ctors) state.context.tvs finalized with
  | .ok _ => state
  | .error error =>
      let error := (error.atSite .bindingAnnotation).inBinding binding.name
      let header := bindingHeader source binding tree scope
      addError state (Diagnostics.loweringDiag error header.program header.spanned header.binders scope)

private def inspectRhs (recurse : State → Surface.Expr → SpannedExpr → Option Fact → State × Option Fact)
    (source : Source) (state : State) (binding : Surface.Binding) (tree : SpannedExpr) (scope : Span) : State :=
  let state := validateAnnotation source state binding tree scope
  let (expr, tree) := wrapParameters source binding tree scope
  let context := rhsContext state binding
  -- Every accepted substitution has passed the saved forall escape boundary.
  -- Keep safe constraints on captured monotypes even when this RHS fails;
  -- restore removes only the lexical/type-variable scope, never those facts.
  let start := state.subst.length
  let (inside, expected) := rhsExpected source { state with context } state.context binding
  let (inside, _) := recurse inside expr tree expected
  restore inside state.context start

private def recoverLet (recurse : State → Surface.Expr → SpannedExpr → Option Fact → State × Option Fact)
    (source : Source) (state : State) (binding : Surface.Binding) (rhs body : SpannedExpr)
    (continuation : Surface.Expr) (scope : Span) (expected : Option Fact) : State := Id.run do
  let outer := state.context
  let start := state.subst.length
  let header := bindingHeader source binding rhs scope
  let dependencies := causes source state.context (.letIn binding.name binding.tyParams binding.params binding.ann binding.rhs (.primLit .unit))
  let mut state := state
  let mut exported : Option PolyTy := none
  let mut failure : Option HoverDiag := none
  let mut roots := dependencies
  if dependencies.isEmpty then
    match RecoveryArtifacts.check state.context header source.declarations.ctors with
    | .ok slice =>
        exported := (groupSchemes [binding] slice.typed).bind (·.head?)
        state := accept state slice
    | .error error =>
        failure := some error
        roots := rootCause binding.name scope
  if exported.isNone then
    if roots.isEmpty then roots := rootCause binding.name scope
    state := markUnavailable state header roots
    let before := state.diagnostics.length
    state := inspectRhs recurse source state binding rhs scope
    if let some error := failure then state := withNativeFailure before error state
    state := enterUnknown state [binding.name] roots
  else
    state := { state with context := state.context.withBindings [binding.name] exported.toList }
  let expression := Surface.Expr.letIn binding.name binding.tyParams binding.params binding.ann binding.rhs continuation
  let tree := SpannedExpr.letIn scope rhs body
  state := { state with context := { state.context with
    lexical := lexical source expression tree [binding.name] body.span ++ state.context.lexical } }
  let (next, _) := recurse state continuation body expected
  return restore next outer start

private def recoverRec (recurse : State → Surface.Expr → SpannedExpr → Option Fact → State × Option Fact)
    (source : Source) (state : State) (bindings : List Surface.Binding) (rhss : List SpannedExpr × SpannedExpr)
    (continuation : Surface.Expr) (scope : Span) (expected : Option Fact) : State := Id.run do
  let outer := state.context
  let start := state.subst.length
  let names := bindings.map (·.name)
  let header := recHeader source bindings rhss.1 scope
  let dependencies := causes source state.context (.letRecIn bindings (.primLit .unit))
  let mut state := state
  let mut exported : Option (List PolyTy) := none
  let mut failure : Option HoverDiag := none
  let mut roots := dependencies
  if dependencies.isEmpty then
    match RecoveryArtifacts.check state.context header source.declarations.ctors with
    | .ok slice =>
        exported := groupSchemes bindings slice.typed
        state := accept state slice
    | .error error =>
        failure := some error
        roots := bindings.map (fun binding => Cause.localBinding binding.name scope)
  if exported.isNone then
    if roots.isEmpty then roots := bindings.map (fun binding => Cause.localBinding binding.name scope)
    state := markUnavailable state header roots
    state := enterUnknown state names roots
    let before := state.diagnostics.length
    for (binding, rhs) in bindings.zip rhss.1 do
      state := inspectRhs recurse source state binding rhs scope
    if let some error := failure then state := withNativeFailure before error state
  else
    state := { state with context := state.context.withBindings names (exported.getD []) }
  let expression := Surface.Expr.letRecIn bindings continuation
  let tree := SpannedExpr.letRecIn scope rhss.1 rhss.2
  state := { state with context := { state.context with
    lexical := lexical source expression tree names rhss.2.span ++ state.context.lexical } }
  let (next, _) := recurse state continuation rhss.2 expected
  return restore next outer start

private def matchHeader (source : Source) (state : State) (pat : Surface.Pattern) (scrutTy : Ty)
    (owner scrut body : Span) : Except HoverDiag (CheckedSlice × List PolyTy) := do
  let dummy := ValName.mk "$recover/scrutinee"
  let (expr, tree) := captureBody (Surface.patVars pat) body
  let header := source.expression (.match_ (.var dummy) [(pat, expr)])
    (.generatedRoot (.match_ owner (.generated (.leaf scrut)) [tree]))
  let context := state.context.withBindings [dummy] [PolyTy.mkTrivial scrutTy]
  let slice ← RecoveryArtifacts.check context header source.declarations.ctors
  let types ← require ((Surface.patVars pat).zipIdx.mapM fun (_, capture) => (do
    let (_, facts) ← slice.typed.patternBinderTypes.find? fun (site, _) => match site with
      | .patCapture _ 0 index => index == capture
      | _ => false
    let (_, ty) ← facts.head?
    pure (PolyTy.mkTrivial ty) : Option PolyTy))
      { diagAtSpan "internal recovered match capture missing" (some owner) with code? := some "internal.recoveryArtifact" }
  pure (slice, types)

/-- Recovery is fuelled by source size. Each recursive source descent consumes
fuel, including generated head-parameter lambdas; no failed subtree yields a type. -/
def walk : Nat → Source → State → Surface.Expr → SpannedExpr → Option Fact → State × Option Fact
  | 0, _, state, _, tree, _ =>
      (addError state { diagAtSpan "internal recovery traversal exhausted" (some tree.span) with
        code? := some "internal.recoveryArtifact" }, none)
  | fuel + 1, source, initial, expr, tree, expectedType => Id.run do
      let roots := causes source initial.context expr
      let checked := if roots.isEmpty then
        RecoveryArtifacts.check initial.context (source.expression expr tree) source.declarations.ctors
        else .error (diagAtSpan "unavailable dependency" (some tree.span))
      match checked with
      | .ok slice =>
          let state := accept initial slice
          let fact : Fact := ⟨slice.typed.inference.ty, state.subst.length, false⟩
          let state := match expectedType with
            | some expected => compareTypes source state fact.ty (expected.current state) tree.span expected.annotation
            | none => state
          return (state, some fact)
      | .error original =>
        let mut state := initial
        let diagnosticCount := state.diagnostics.length
        let recurse := walk fuel source
        match expr, stripGenerated tree with
        | .pair a b, .pair _ sa sb =>
            let left := expectedType.bind fun expected => match expected.current state with
              | .customTy ⟨"Pair"⟩ [left, _] => some ⟨left, state.subst.length, expected.annotation⟩
              | _ => none
            let (next, _) := recurse state a sa left
            state := next
            let right := expectedType.bind fun expected => match expected.current state with
              | .customTy ⟨"Pair"⟩ [_, right] => some ⟨right, state.subst.length, expected.annotation⟩
              | _ => none
            let (next, _) := recurse state b sb right
            state := next
        | .cons a b, .cons _ sa sb =>
            let (next, _) := recurse state a sa none
            let (next, _) := recurse next b sb none
            state := next
        | .app fn arg, .app _ sf sa =>
            let (next, fnType) := recurse state fn sf none
            let (next, _) := recurse next arg sa none
            state := next
            if let some fact := fnType then
              match fact.current state with
              | .arrow _ _ | .fvar _ => pure ()
              | actual =>
                  -- A concrete non-function is invalid even when the argument
                  -- is unavailable. No argument or result type is invented.
                  let reason := TypeDiagnostics.Reason.notFunction actual
                  state := addError state { diagAtSpan reason.message (some sf.span) with code? := some reason.code }
        | .list items, .list _ trees =>
            let mut expected : Option Fact := none
            for (item, child) in items.zip trees do
              let (next, fact) := recurse state item child (expectedType.bind fun expected =>
                match expected.current state with
                | .customTy ⟨"List"⟩ [item] => some ⟨item, state.subst.length, expected.annotation⟩
                | _ => none)
              state := next
              match expected, fact with
              | some prior, some actual =>
                  state := compareTypes source state (actual.current state) (prior.current state) child.span
              | none, some actual => expected := some actual
              | _, _ => pure ()
        | .lambda pat ann body, .lambda owner sbody =>
            let outer := state.context
            let start := state.subst.length
            let mut failures := roots
            let headerUses := (patternUses pat).append ⟨(ann.map typeNames).getD [], []⟩
            let headerCauses := DeclarationRecovery.causesFor source.declarations headerUses
            let headerCheck := if headerCauses.isEmpty then patternHeader source state pat ann owner sbody.span
              else .error (diagAtSpan "unavailable pattern header" (some owner))
            match headerCheck with
            | .ok (header, types) =>
                state := accept state header
                let before := state.subst.length
                if let some expected := expectedType then
                  if let .arrow domain _ := expected.current state then
                    if let .arrow actual _ := header.typed.inference.ty then
                      state := compareTypes source state actual domain owner expected.annotation
                let types := types.map (Subst.onPolyTy (state.subst.drop before))
                state := enterPattern source state expr tree pat types sbody.span
            | .error error =>
                if headerCauses.isEmpty then state := addError state error
                if !headerCauses.isEmpty then failures := headerCauses
                if failures.isEmpty then failures := [.expression owner]
                state := enterUnknown state (Surface.patVars pat) failures
                state := { state with context := { state.context with
                  lexical := lexical source expr tree (Surface.patVars pat) sbody.span ++ state.context.lexical } }
            let bodyExpected := expectedType.bind fun expected =>
              match expected.current state with
              | .arrow _ result => some ⟨result, state.subst.length, expected.annotation⟩
              | _ => none
            let (next, _) := recurse state body sbody bodyExpected
            state := restore next outer start
        | .letIn name tyParams params ann rhs body, .letIn owner srhs sbody =>
            state := recoverLet recurse source state ⟨name, tyParams, params, ann, rhs⟩ srhs sbody body owner expectedType
        | .letRecIn bindings body, .letRecIn owner rhss sbody =>
            state := recoverRec recurse source state bindings (rhss, sbody) body owner expectedType
        | .ife condition yes no, .ife _ sc sy sn =>
            let (next, conditionTy) := recurse state condition sc none
            state := next
            if let some conditionTy := conditionTy then
              state := compareTypes source state (conditionTy.current state) (Ty.customTy ⟨"Bool"⟩ []) sc.span
            let (next, yesTy) := recurse state yes sy expectedType
            let (next, noTy) := recurse next no sn expectedType
            state := next
            if let some yesTy := yesTy then
              if let some noTy := noTy then
                state := compareTypes source state (noTy.current state) (yesTy.current state) sn.span
        | .match_ scrut branches, .match_ owner sscrut arms =>
            let (next, scrutTy) := recurse state scrut sscrut none
            state := next
            let mut expected : Option Fact := none
            for ((pat, body), arm) in branches.zip arms do
              let outer := state.context
              let start := state.subst.length
              let headerCauses := DeclarationRecovery.causesFor source.declarations (patternUses pat)
              if !headerCauses.isEmpty then
                state := enterUnknown state (Surface.patVars pat) headerCauses
              else
                match scrutTy with
                | some scrutTy =>
                    match matchHeader source state pat (scrutTy.current state) owner sscrut.span arm.span with
                    | .ok (header, types) =>
                        state := accept state { header with checkCoverage := false }
                        let synthetic := Surface.Expr.lambda pat none body
                        let mirror := SpannedExpr.lambda owner arm
                        state := enterPattern source state synthetic mirror pat types arm.span
                    | .error error =>
                        state := addError state error
                        state := enterUnknown state (Surface.patVars pat) (if roots.isEmpty then [.expression owner] else roots)
                | none =>
                    match patternHeader source state pat none owner arm.span with
                    | .error error => state := addError state error
                    | .ok _ => pure ()
                    state := enterUnknown state (Surface.patVars pat) (if roots.isEmpty then [.expression sscrut.span] else roots)
              let (next, fact) := recurse state body arm expectedType
              state := restore next outer start
              match expected, fact with
              | some prior, some actual =>
                  state := compareTypes source state (actual.current state) (prior.current state) arm.span
              | none, some actual => expected := some actual
              | _, _ => pure ()
        | _, _ => pure ()
        if roots.isEmpty then state := withNativeFailure diagnosticCount original state
        let failures := if roots.isEmpty then [.expression tree.span] else roots
        state := markUnavailable state (source.expression expr tree) failures
        return (state, none)

mutual
private def fuelSize : Surface.Expr → Nat
  | .primLit _ | .primBinOp _ | .var _ | .ctor _ => 1
  | .pair a b | .cons a b | .app a b => 1 + fuelSize a + fuelSize b
  | .list items => 1 + fuelList items
  | .lambda _ _ body => 1 + fuelSize body
  | .letIn _ _ params _ rhs body => 1 + params.length + fuelSize rhs + fuelSize body
  | .letRecIn binds body => 1 + fuelBindings binds + fuelSize body
  | .ife c t f => 1 + fuelSize c + fuelSize t + fuelSize f
  | .match_ scrut arms => 1 + fuelSize scrut + fuelBranches arms
private def fuelList : List Surface.Expr → Nat
  | [] => 0
  | expr :: rest => fuelSize expr + fuelList rest
private def fuelBindings : List Surface.Binding → Nat
  | [] => 0
  | binding :: rest => 1 + binding.params.length + fuelSize binding.rhs + fuelBindings rest
private def fuelBranches : List (Surface.Pattern × Surface.Expr) → Nat
  | [] => 0
  | (_, body) :: rest => fuelSize body + fuelBranches rest
end

/-- Inspect a rejected top-level group without exporting any of its members.
Actual group checking and all successful top-level exports stay in EditorRecovery. -/
def group (source : Source) (context : Context) (bindings : List Surface.Binding) (rhss : List SpannedExpr)
    (roots : List Cause) : State := Id.run do
  let context := context.withUnavailable (bindings.map (·.name)) roots
  let mut state : State := { context }
  for (binding, rhs) in bindings.zip rhss do
    state := inspectRhs (walk (fuelSize binding.rhs + binding.params.length + 32) source) source state binding rhs source.scope
  return state

def expression (source : Source) (context : Context) (expr : Surface.Expr) (tree : SpannedExpr) : State :=
  (walk (fuelSize expr + 32) source { context } expr tree none).1

end FHM.Unverified.ExpressionRecovery
