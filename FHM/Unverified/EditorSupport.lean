import FHM.Unverified.HMDisplay
import FHM.Unverified.Diagnostics
import FHM.Unverified.EditorRecovery
import FHM.Unverified.CoverageDiagnostics
import FHM.Unverified.Surface.Parse

/-!
# Editor support helpers

`fhm diagnose` consumes path-keyed HM inference metadata and separate provenance.
Binding definitions use inferred schemes or validated declarations. Source
locations, name recovery, and JSON presentation remain unverified.
-/

open Surface.Parse
open Surface.Span
open Surface.Lex (BinOpToken Punct Token)
open SurfaceBridge

def prettyTyName : TyName → String
  | .mk s => s

def prettyCtorName : CtorName → String
  | .mk s => s

/-- A type declaration laid out one constructor per line, each under its doc
    comment (as `---` lines):

    ```
    type Maybe a =
      --- No value.
      | Nothing
      | Just a
    ```
-/
def layoutDataDecl (header : String) (ctors : List (String × Option String)) : String :=
  let ctorLines := fun (ctor, doc?) =>
    let docLines := (doc?.map fun doc => (doc.splitOn "\n").map fun l =>
      if l.isEmpty then "  ---" else s!"  --- {l}").getD []
    docLines ++ [s!"  | {ctor}"]
  String.intercalate "\n" ((header ++ " =") :: ctors.flatMap ctorLines)

def prettySurfaceDataDecl (d : Surface.DataDecl)
    (ctorDoc : CtorName → Option String := fun _ => none) : String :=
  let params := String.intercalate " " (d.params.map prettyValName)
  let header :=
    if d.params.isEmpty then s!"type {prettyTyName d.name}"
    else s!"type {prettyTyName d.name} {params}"
  let ctorStr (c : CtorName × List Surface.Ty) : String :=
    let ⟨cname, fields⟩ := c
    if fields.isEmpty then prettyCtorName cname
    else prettyCtorName cname ++ " " ++
      String.intercalate " " (fields.map (Surface.Ty.prettyAux 2))
  layoutDataDecl header (d.ctors.map fun c => (ctorStr c, ctorDoc c.1))

/-- Spanned hover symbol (v3): `span` plus lexical `scope`. `isDef` marks a
    definition site (a binder, type, constructor or type variable binder), as
    opposed to an occurrence; editors use it for go to definition. -/
structure RangedSymbol where
  name : String
  kind : String
  type_ : String
  span : Span
  scope : Span
  isDef : Bool := false
  /-- Doc comment of the definition (also on its occurrences). -/
  doc : Option String := none
  /-- A constructor's enclosing data declaration, separate from its use-site type. -/
  declaration : Option String := none
  deriving Repr, BEq

def RangedSymbol.toJson (s : RangedSymbol) : Lean.Json :=
  Lean.Json.mkObj <| [
    ("name", Lean.Json.str s.name),
    ("kind", Lean.Json.str s.kind),
    ("type", Lean.Json.str s.type_),
    ("startLine", Lean.Json.num s.span.startLine),
    ("startCol", Lean.Json.num s.span.startCol),
    ("endLine", Lean.Json.num s.span.endLine),
    ("endCol", Lean.Json.num s.span.endCol),
    ("scopeStartLine", Lean.Json.num s.scope.startLine),
    ("scopeStartCol", Lean.Json.num s.scope.startCol),
    ("scopeEndLine", Lean.Json.num s.scope.endLine),
    ("scopeEndCol", Lean.Json.num s.scope.endCol),
    ("def", Lean.Json.bool s.isDef)
  ] ++ (s.doc.map fun d => ("doc", Lean.Json.str d)).toList ++
    (s.declaration.map fun d => ("declaration", Lean.Json.str d)).toList

def mkSym (name kind type_ : String) (span scope : Span) : RangedSymbol :=
  { name, kind, type_, span, scope }

def symbolAt (syms : List RangedSymbol) (line col : Nat) : Option RangedSymbol :=
  let hits := syms.filter (fun s => s.span.contains line col)
  match hits with
  | [] => none
  | h :: rest =>
    some <| rest.foldl (fun best s =>
      let aBest := best.span.area
      let aS := s.span.area
      if aS < aBest then s else if aS == aBest then s else best) h

def symbolAtUseSite (syms : List RangedSymbol) (line col : Nat) (name : String) :
    Option RangedSymbol :=
  let hits := syms.filter fun s =>
    s.name == name && !s.type_.isEmpty && s.scope.contains line col
  match hits with
  | [] => none
  | h :: rest =>
    some <| rest.foldl (fun best s =>
      let aBest := best.scope.area
      let aS := s.scope.area
      if aS < aBest then s else if aS == aBest then s else best) h

def programWideScope (binders : List BinderSpan) (sp : SpannedProgram) : Span :=
  let spans :=
    binders.map (·.span) ++ sp.groups.flatMap (·.map SpannedExpr.span) ++ [sp.body.span]
  (Span.hull spans).getD sp.body.span

def prettyCoreDataDecl (d : DataDecl) : String :=
  let params := String.intercalate " " ((List.range d.paramCount).map prettyTyVarName)
  let header :=
    if d.paramCount == 0 then s!"type {prettyTyName d.name}"
    else s!"type {prettyTyName d.name} {params}"
  let ctorStr (c : CtorName × List Ty) : String :=
    let ⟨cname, fields⟩ := c
    if fields.isEmpty then prettyCtorName cname
    else prettyCtorName cname ++ " " ++
      String.intercalate " " (fields.map (fun τ => Ty.prettyAux 2 τ))
  layoutDataDecl header (d.ctors.map fun c => (ctorStr c, none))

def preludeTypeCtorSymbols (ctors : CtorEnv) (scope : Span) : List RangedSymbol :=
  preludeDecls.flatMap fun d =>
    let typeSym : RangedSymbol := {
      name := prettyTyName d.name
      kind := "type"
      type_ := prettyCoreDataDecl d
      span := Span.empty
      scope := scope
      isDef := true
    }
    let ctorSyms := d.ctors.map fun ⟨cname, _⟩ =>
      let tyStr :=
        match LookupList.get? ctors cname with
        | some ctor => ctor.toTy.pretty
        | none => prettyCtorName cname
      ({ name := prettyCtorName cname, kind := "ctor", type_ := tyStr,
         span := Span.empty, scope := scope, isDef := true,
         declaration := some (prettyCoreDataDecl d) } : RangedSymbol)
    typeSym :: ctorSyms

/-- Built-in primitive types (`Bool` is a prelude data type instead). Like the
    prelude, they have no source location. -/
def primTypeSymbols (scope : Span) : List RangedSymbol :=
  ["Int", "Char", "Unit"].map fun name =>
    { name, kind := "type", type_ := s!"type {name}  -- built in", span := Span.empty,
      scope, isDef := true }

def binOpPrimTy (ctors : CtorEnv) : BinOpToken → Option (String × String)
  | .plus => (PrimBinOp.ty ctors .intAdd).map fun τ => ("+", τ.pretty)
  | .minus => (PrimBinOp.ty ctors .intSub).map fun τ => ("-", τ.pretty)
  | .lt => (PrimBinOp.ty ctors .intLt).map fun τ => ("<", τ.pretty)
  | .cons =>
      match LookupList.get? ctors cCons with
      | some ctor => some ("::", ctor.toTy.pretty)
      | none => none

def collectLitOpSymbols (src : String) (ctors : CtorEnv) : List RangedSymbol :=
  match Surface.Lex.lex src with
  | .error _ => []
  | .ok toks =>
    Id.run do
      let mut out : List RangedSymbol := []
      let mut i : Nat := 0
      while h : i < toks.size do
        let t := toks[i]
        match t.token with
        | .punct .lparen =>
          if h2 : i + 1 < toks.size then
            let t2 := toks[i + 1]
            if t2.token == .punct .rparen then
              let sp := Span.union (Span.ofTok t) (Span.ofTok t2)
              out := out ++ [mkSym "()" "lit" (PrimLitExpr.ty .unit).pretty sp sp]
              i := i + 2
            else i := i + 1
          else i := i + 1
        | .intLit n =>
          let sp := Span.ofTok t
          out := out ++ [mkSym (toString n) "lit" (PrimLitExpr.ty (.int n)).pretty sp sp]
          i := i + 1
        | .charLit c =>
          let sp := Span.ofTok t
          out := out ++ [mkSym (prettyPrimLit (.char c)) "lit"
            (PrimLitExpr.ty (.char c)).pretty sp sp]
          i := i + 1
        | .boolLit b =>
          let sp := Span.ofTok t
          out := out ++ [mkSym (if b then "True" else "False") "lit"
            (Ty.customTy nBool []).pretty sp sp]
          i := i + 1
        | .op o =>
          let sp := Span.ofTok t
          match binOpPrimTy ctors o with
          | some (nm, tyStr) => out := out ++ [mkSym nm "op" tyStr sp sp]
          | none => pure ()
          i := i + 1
        | _ => i := i + 1
      return out

structure HoverReport where
  symbols : List RangedSymbol
  programTy : String
  diagnostics : List HoverDiag := []
  deriving Repr

def bodyDiagSpan (body : SpannedExpr) : Span :=
  match body with
  | .match_ s _ _ => s
  | _ => body.span

def exhaustivenessDiag (typed : SurfaceBridge.Provenance.TypedLowered)
    (term : Surface.Expr) (tree : SurfaceBridge.Provenance.IdentifiedExpr)
    (fallback : Span) : HoverDiag :=
  let failure := FHM.Unverified.CoverageDiagnostics.firstFailure typed term tree
  let patterns := (failure.map fun f => f.missing.patterns.map
    (Surface.Pattern.pretty 0)).getD []
  let more := (failure.map fun f => f.missing.more).getD false
  let message := if patterns.isEmpty then "match not exhaustive" else
    "match not exhaustive (missing: " ++ String.intercalate ", " patterns ++
      (if more then "; and more" else "") ++ ")"
  { diagAtSpan message (some ((failure.map (·.span)).getD fallback)) with
    code? := some "match.notExhaustive"
    missingPatterns := patterns
    moreMissing := more }

/-- Render one checked source slice using its native inference artifacts. -/
def collectTypedHover (src : String) (p : Surface.Program) (binders : List BinderSpan)
    (sp : SpannedProgram) (tree : SpannedExpr)
    (typed : SurfaceBridge.Provenance.TypedLowered) : HoverReport :=
  let ctors := typed.ctors
  let lowered := typed.lowering
  let scope := programWideScope binders sp
  let fail (d : HoverDiag) : HoverReport :=
    { symbols := [], programTy := "", diagnostics := [d] }
  if !(typed.lowering.mapExpr Expr.erase).provenanceTotal ||
      !typed.nodeTypesTotal || !typed.sourceTypesTotal ||
      !typed.patternBinderTypesTotal then
    fail (diagAtSpan "internal inferred provenance coverage failure" (some scope))
  else
    let identified := SurfaceBridge.Provenance.identify tree
    let collected := FHM.Unverified.HMArtifacts.collect binders p.term identified
    let wrapperIds := FHM.Unverified.HMArtifacts.programWrapperIds p.groups identified
    let authoredOccurrences := collected.occurrences.filter fun occ =>
      !(wrapperIds.contains occ.id)
    let locations := { collected with occurrences := authoredOccurrences }
    let displayScopes := FHM.Unverified.HMDisplay.scopes typed locations
    let docAt (span : Span) : Option String :=
      (binders.find? (·.span == span)).bind (·.doc?)
    let ctorDecl (name : String) : Option String :=
      ((p.decls.find? fun d => d.ctors.any fun c => prettyCtorName c.1 == name).map
        fun d => prettySurfaceDataDecl d) <|>
      ((preludeDecls.find? fun d => d.ctors.any fun c => prettyCtorName c.1 == name).map
        prettyCoreDataDecl)
    let values := locations.binders.filterMap fun b =>
      (FHM.Unverified.HMDisplay.binderType typed displayScopes locations b.site).map
        fun ty => { mkSym b.name b.kind.toString ty b.span b.scope with
          isDef := true, doc := docAt b.span }
    let occurrences := locations.occurrences.filterMap fun occ => do
      let source ← lowered.sourceNodes.find? (fun n => n.id == occ.id)
      let ty ← FHM.Unverified.HMDisplay.sourceType typed displayScopes occ.id
      let name := if occ.kind == "lit" || occ.kind == "op" then
        FHM.Unverified.HMArtifacts.spanText src source.span else occ.name
      -- A value occurrence refers to the innermost binder of its name.
      let binder := if occ.kind == "val" then
        ((locations.binders.filter fun b => b.name == occ.name &&
          b.scope.contains source.span.startLine source.span.startCol).mergeSort
          (fun a b => a.scope.area ≤ b.scope.area)).head?
        else none
      let kind := if occ.kind == "val" then
        (binder.map (·.kind.toString)).getD "val" else occ.kind
      let doc := match binder with
        | some b => docAt b.span
        | none => if occ.kind == "ctor" then
            (binders.find? fun b => b.kind == .ctor && b.name == occ.name).bind (·.doc?)
          else none
      pure { mkSym name kind ty source.span source.span with
        doc := doc
        declaration := if occ.kind == "ctor" then ctorDecl name else none }
    let syntaxSyms := (binders.filterMap fun b =>
      if locations.binders.any (fun s => s.span == b.span) then none
      else if b.kind == .type then
        (p.decls.find? (fun d => prettyTyName d.name == b.name)).map fun d =>
          let ctorDoc := fun (c : CtorName) => (binders.find? fun b =>
            b.kind == .ctor && b.name == prettyCtorName c).bind (·.doc?)
          mkSym b.name "type" (prettySurfaceDataDecl d ctorDoc) b.span scope
      else if b.kind == .ctor then
        (LookupList.get? ctors (.mk b.name)).map fun c =>
          let names := ((p.decls.find? fun d =>
            d.ctors.any (fun (name, _) => prettyCtorName name == b.name)).map
              (fun d => d.params.map prettyValName)).getD []
          mkSym b.name "ctor" (FHM.Unverified.HMDisplay.scheme {} names c.toTy)
            b.span scope
      else if b.kind == .param then
        let decl := (p.decls.zip sp.declSpans).find? fun (_, s) =>
          FHM.Unverified.HMArtifacts.inside b.span s
        let label := match decl with
          | some (d, _) => s!"type variable (of {prettyTyName d.name})"
          | none => "type variable (scheme binder)"
        let sc := match decl with
          | some (_, s) => s
          | none => b.scope?.getD scope
        some (mkSym b.name "param" label b.span sc)
      else none).map fun s => { s with
        isDef := true
        doc := docAt s.span
        declaration := if s.kind == "ctor" then ctorDecl s.name else none }
    let prelude := (preludeTypeCtorSymbols ctors scope ++ primTypeSymbols scope).filter fun s =>
      !(syntaxSyms.any fun b => b.name == s.name && b.kind == s.kind)
    let references := sp.references.filterMap fun ref => do
      let kind ← match ref.kind with
        | .type => some "type"
        | .typeVar => some "param"
        | .ctor => some "ctor"
        | .typeHole => none
      let candidates := (prelude ++ syntaxSyms).filter fun s =>
        s.kind == kind
      let target ← symbolAtUseSite candidates ref.span.startLine ref.span.startCol ref.name
      pure { target with span := ref.span, scope := ref.span, isDef := false }
    let holeSymbols :=
      (FHM.Unverified.HMDisplay.holeDisplays typed displayScopes binders sp.references
        (FHM.Unverified.HMArtifacts.programBindingHeaders sp p.groups identified) p.term identified).filterMap
        fun hole => if hole.types.isEmpty then none else
          some (mkSym hole.name "typeHole" (String.intercalate " | " hole.types) hole.span
            (if hole.name == "_" then hole.span else hole.annotation?.getD hole.span))
    let sugarOps := (collectLitOpSymbols src ctors).filter fun s => s.name == "::"
    -- Typing succeeded, so hovers stay available alongside this error.
    let exhaustiveness :=
      if checkExhaustive ctors p.term then []
      else [exhaustivenessDiag typed p.term identified (bodyDiagSpan sp.body)]
    { symbols := prelude ++ syntaxSyms ++ values ++ sugarOps ++ occurrences ++ references ++ holeSymbols
      programTy := FHM.Unverified.HMDisplay.scheme {} []
        (genScheme [] [] typed.inference.ty)
      diagnostics := exhaustiveness }

def collectHoverStrict (src : String) (p : Surface.Program) (binders : List BinderSpan)
    (sp : SpannedProgram) : HoverReport :=
  let fail (d : HoverDiag) : HoverReport :=
    { symbols := [], programTy := "", diagnostics := [d] }
  match lowerDataDeclsInResult preludeKindEnv p.decls with
  | .error error => fail (FHM.Unverified.Diagnostics.loweringDiag error p sp binders sp.body.span)
  | .ok userCore =>
    match elabDeclsResult (preludeDecls ++ userCore) with
    | .error error => fail (FHM.Unverified.Diagnostics.declarationDiag error p sp binders)
    | .ok ctors =>
      let scope := programWideScope binders sp
      match FHM.Unverified.HMArtifacts.programSpannedResult p sp scope with
      | .error error => fail (FHM.Unverified.Diagnostics.provenanceDiag error p sp binders scope)
      | .ok tree =>
        match SurfaceBridge.Provenance.lowerWithProvenanceResult ctors p.term tree with
        | .error error => fail (FHM.Unverified.Diagnostics.provenanceDiag error p sp binders scope)
        | .ok lowered =>
          match SurfaceBridge.Provenance.inferWithProvenanceResult ctors lowered with
          | .error error =>
            fail (FHM.Unverified.Diagnostics.inferenceDiag error lowered p sp binders tree)
          | .ok typed =>
            collectTypedHover src p binders sp tree typed

/-- Fully checked programs retain the original whole-program artifact path.
After a source rejection, the editor checks independent top-level groups and
keeps only their validated hovers. The runner never uses recovery. -/
def collectHover (src : String) (p : Surface.Program) (binders : List BinderSpan)
    (sp : SpannedProgram) : HoverReport :=
  let strict := collectHoverStrict src p binders sp
  if !strict.symbols.isEmpty || strict.diagnostics.isEmpty then strict
  else
    match FHM.Unverified.EditorRecovery.check p sp binders (programWideScope binders sp) with
    | .error diagnostic => { symbols := [], programTy := "", diagnostics := [diagnostic] }
    | .ok recovered =>
      let reports := recovered.checked.map fun slice =>
        collectTypedHover src slice.program slice.binders slice.spanned slice.tree slice.typed
      let body := recovered.checked.find? (·.isBody)
      { symbols := (reports.flatMap (·.symbols)).eraseDups
        programTy := (body.map fun slice => FHM.Unverified.HMDisplay.scheme {} []
          (genScheme [] [] slice.typed.inference.ty)).getD ""
        diagnostics := (recovered.diagnostics ++ reports.flatMap (·.diagnostics)).mergeSort
          (fun a b => a.line < b.line || (a.line == b.line && a.col ≤ b.col)) }

def parseDiagJson (e : ParseError) : Lean.Json :=
  Lean.Json.mkObj [
    ("severity", Lean.Json.str "error"),
    ("message", Lean.Json.str e.msg),
    ("line", Lean.Json.num e.line),
    ("col", Lean.Json.num e.col),
    ("endLine", Lean.Json.num e.endLine),
    ("endCol", Lean.Json.num e.endCol)
  ]

/-- Token class reported to editors, which use token boundaries to decide what
    a hover position is on (whitespace and comments get no hover). -/
def tokenClass : Surface.Lex.Token → String
  | .lineComment _ | .blockComment _ | .docComment _ => "comment"
  | .ident _ _ => "ident"
  | .namedHole _ => "ident"
  | .keyword _ => "keyword"
  | .intLit _ | .charLit _ | .stringLit _ | .boolLit _ => "lit"
  | .op _ => "op"
  | .punct _ => "punct"

/-- Every token as a compact `[startLine, startCol, endLine, endCol, class]`
    (1-based, half-open, in source order). Empty if the source doesn't lex. -/
def tokensJson (src : String) : Lean.Json :=
  match Surface.Lex.lex src with
  | .error _ => Lean.Json.arr #[]
  | .ok toks => Lean.Json.arr <| toks.map fun t =>
      Lean.Json.arr #[Lean.Json.num t.startLine, Lean.Json.num t.startCol,
        Lean.Json.num t.endLine, Lean.Json.num t.endCol, Lean.Json.str (tokenClass t.token)]

def diagnosePayload (src : String) : Lean.Json :=
  match parseProgramWithSpans src with
  | .error e => Lean.Json.mkObj [
      ("version", Lean.Json.num 3),
      ("diagnostics", Lean.Json.arr #[parseDiagJson e]),
      ("symbols", Lean.Json.arr #[]),
      ("tokens", tokensJson src)
    ]
  | .ok (p, binders, sp) =>
    let r := collectHover src p binders sp
    Lean.Json.mkObj [
      ("version", Lean.Json.num 3),
      ("diagnostics", Lean.Json.arr (r.diagnostics.map HoverDiag.toJson).toArray),
      ("symbols", Lean.Json.arr (r.symbols.map RangedSymbol.toJson).toArray),
      ("tokens", tokensJson src),
      ("programTy", Lean.Json.str r.programTy)
    ]

def binderNames (bs : List BinderSpan) : List String :=
  bs.map (·.name)
