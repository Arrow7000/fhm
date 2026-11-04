import FHM.Unverified.EditorSupport

/-! Failed declaration components contribute no kinds or constructor schemes.
Independent declaration/value checks survive, and dependent errors are suppressed. -/
namespace FHM.Unverified.DeclarationRecoveryTests
open Surface.Parse Surface.Span RecoveryDependencies

private def declarations (source : String) : Option DeclarationRecovery.Result := do
  let (program, binders, spanned) ← (parseProgramWithSpans source).toOption
  (DeclarationRecovery.check program spanned binders (programWideScope binders spanned)).toOption
private def hover (source : String) : Option HoverReport := do
  let (program, binders, spanned) ← (parseProgramWithSpans source).toOption
  pure (collectHover source program binders spanned)
private def value (report : HoverReport) (name : String) : Option String :=
  (report.symbols.find? (fun symbol => symbol.name == name && symbol.kind == "val" && symbol.isDef)).map (·.type_)

private def independent : String :=
  "type BadHole = Hole _\ntype BadName = Name Missing\ntype Good a = Good a\n" ++
  "let broken : Int = True\nlet healthy = Good 3\nhealthy\n"
#guard match declarations independent with
  | some result => result.diagnostics.length == 2 && result.declarations.length == 1 &&
      result.declarations.any (·.name == TyName.mk "Good") &&
      (LookupList.get? result.ctors ⟨"Hole"⟩).isNone && (LookupList.get? result.ctors ⟨"Name"⟩).isNone &&
      (LookupList.get? result.ctors ⟨"Good"⟩).isSome
  | none => false
#guard match hover independent with
  | some report => report.diagnostics.length == 3 && value report "healthy" == some "Good Int" &&
      report.programTy == "Good Int" && report.diagnostics.any (·.code? == some "type.annotationMismatch")
  | none => false

private def chain : String :=
  "type A = MkA Missing\ntype B = MkB A\ntype C = MkC B\n" ++
  "let blocked = MkC (MkB (MkA 1))\nlet annotation (x : C) = x\nlet healthy = 7\nhealthy\n"
#guard match declarations chain with
  | some result => result.diagnostics.length == 1 && result.declarations.isEmpty &&
      result.unavailableTypes.all (fun pair => pair.2 == [.declaration ⟨"A"⟩]) &&
      (LookupList.get? result.ctors ⟨"MkB"⟩).isNone && (LookupList.get? result.ctors ⟨"MkC"⟩).isNone
  | none => false
#guard match hover chain with
  | some report => report.diagnostics.length == 1 && value report "healthy" == some "Int" &&
      value report "blocked" == some "type unknown (error in type `A`)" &&
      value report "annotation" == some "type unknown (error in type `A`)"
  | none => false

-- All conflicting definitions are withheld, instead of picking one by order.
#guard match declarations "type X = First\ntype X = Second\ntype Good = Good Int\n" with
  | some result => result.diagnostics.length == 1 && result.declarations.length == 1 &&
      result.diagnostics.all (·.code? == some "decl.duplicateType") &&
      (LookupList.get? result.ctors ⟨"First"⟩).isNone && (LookupList.get? result.ctors ⟨"Second"⟩).isNone &&
      (LookupList.get? result.ctors ⟨"Good"⟩).isSome
  | none => false
#guard match declarations "type A = C Int\ntype B = C Bool\ntype Good = Good Int\n" with
  | some result => result.diagnostics.length == 1 && result.declarations.length == 1 &&
      result.diagnostics.all (·.code? == some "decl.duplicateConstructor") &&
      (LookupList.get? result.ctors ⟨"C"⟩).isNone
  | none => false

-- Accepted mutually recursive kinds are checked together against native rules.
private def mutualDeclarations : String :=
  "type Broken = Broken _\n" ++
  "type Tree a = Node a (Forest a)\ntype Forest a = FNil | FCons (Tree a) (Forest a)\n" ++
  "let tree = Node 1 FNil\ntree\n"
#guard match hover mutualDeclarations with
  | some report => report.diagnostics.length == 1 && value report "tree" == some "Tree Int" &&
      report.programTy == "Tree Int"
  | none => false
#guard match declarations "type A = MkA B\ntype B = MkB (A _)\ntype Good = Good Int\n" with
  | some result => result.diagnostics.length == 1 && result.declarations.length == 1 &&
      (LookupList.get? result.ctors ⟨"MkA"⟩).isNone && (LookupList.get? result.ctors ⟨"MkB"⟩).isNone &&
      (LookupList.get? result.ctors ⟨"Good"⟩).isSome
  | none => false

-- A collision with the prelude cannot replace an existing constructor scheme.
#guard match declarations "type Bad = Cons Int\ntype Good = Good Int\n" with
  | some result => result.diagnostics.length == 1 && result.declarations.length == 1 &&
      result.diagnostics.all (·.code? == some "decl.duplicateConstructor") &&
      ((LookupList.get? result.ctors ⟨"Cons"⟩).map (·.tyName)) == some ⟨"List"⟩
  | none => false

-- Dependencies include constructor patterns and annotation types, not just terms.
#guard match hover ("type Bad = MkBad _\nlet blocked x = match x with | MkBad y -> y\n" ++
    "let good x = x\ngood 3\n") with
  | some report => report.diagnostics.length == 1 && value report "good" == some "∀ a. a → a" &&
      value report "blocked" == some "type unknown (error in type `Bad`)"
  | none => false

end FHM.Unverified.DeclarationRecoveryTests
