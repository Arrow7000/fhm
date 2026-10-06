import FHM.Unverified.HMDisplay
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
  ] ++ (s.doc.map fun d => ("doc", Lean.Json.str d)).toList

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
         span := Span.empty, scope := scope, isDef := true } : RangedSymbol)
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

structure HoverDiag where
  message : String
  line : Nat := 1
  col : Nat := 1
  endLine : Nat := 1
  endCol : Nat := 2
  deriving Repr

def HoverDiag.toJson (d : HoverDiag) : Lean.Json :=
  Lean.Json.mkObj [
    ("severity", Lean.Json.str "error"),
    ("message", Lean.Json.str d.message),
    ("line", Lean.Json.num d.line),
    ("col", Lean.Json.num d.col),
    ("endLine", Lean.Json.num d.endLine),
    ("endCol", Lean.Json.num d.endCol)
  ]

structure HoverReport where
  symbols : List RangedSymbol
  programTy : String
  diagnostics : List HoverDiag := []
  deriving Repr

def bodyDiagSpan (body : SpannedExpr) : Span :=
  match body with
  | .match_ s _ _ => s
  | _ => body.span

def topRhsSpan (p : Surface.Program) (sp : SpannedProgram) (n : ValName) : Option SpannedExpr :=
  let flatB := p.groups.flatMap id
  let flatS := sp.groups.flatMap id
  (flatB.zip flatS).find? (fun pair => pair.1.name == n) |>.map (·.2)

def valBinderSpan (binders : List BinderSpan) (n : String) : Option Span :=
  (binders.find? fun b => b.kind == .val && b.name == n).map (·.span)

def bindingExtentSpan (binders : List BinderSpan) (p : Surface.Program)
    (sp : SpannedProgram) (n : String) : Option Span :=
  match (topRhsSpan p sp (.mk n)).map (·.span) with
  | some s => some s
  | none => valBinderSpan binders n

def firstIdentSpan (src : String) (name : String) : Option Span :=
  match Surface.Lex.lex src with
  | .error _ => none
  | .ok toks =>
    Id.run do
      for t in toks do
        match t.token with
        | .ident raw _ => if raw == name then return some (Span.ofTok t)
        | _ => pure ()
      return none

def diagAtSpan (msg : String) (s? : Option Span) : HoverDiag :=
  match s? with
  | some s => {
      message := msg
      line := s.startLine
      col := s.startCol
      endLine := s.endLine
      endCol := s.endCol
    }
  | none => { message := msg }

def hmInfer (ctors : CtorEnv) (term : Surface.Expr) : Option (Expr × Ty) :=
  match lower ctors term with
  | none => none
  | some c =>
    match infer c.freshFloor ⟨[], ctors⟩ c with
    | some (_, _, τ) => some (c, τ)
    | none => none

def hmSucceeds (ctors : CtorEnv) (term : Surface.Expr) : Bool :=
  (hmInfer ctors term).isSome

def prettySurfaceName : ValName → String
  | .mk s => s

def stripBindingAnn (b : Surface.Binding) : Surface.Binding :=
  { b with ann := none }

def explainTypeMismatch (ctors : CtorEnv) (ke : KindEnv)
    (acc : List (List Surface.Binding)) (g : List Surface.Binding)
    (b : Surface.Binding) : String :=
  let nm := prettySurfaceName b.name
  match b.ann with
  | none => s!"typechecking failed in `{nm}`"
  | some σs =>
      let σs := (finalizeAnn b.tyParams b.params (some σs)).getD σs
      let wantStr :=
        match lowerPoly ke σs with
        | some σ => FHM.Unverified.HMDisplay.scheme {} (σs.foralls.map prettyValName) σ
        | none => Surface.PolyTy.pretty σs
      let g' := g.map fun b' => if b'.name == b.name then stripBindingAnn b' else b'
      let probe := Surface.desugarGroups (acc ++ [g']) (.var b.name)
      match hmInfer ctors probe with
      | none => s!"typechecking failed in `{nm}` (ascribed {wantStr}; RHS also fails without ascription)"
      | some (_, ty) =>
          let got := genScheme [] [] ty
          s!"type mismatch in `{nm}`: expected {wantStr}, got {FHM.Unverified.HMDisplay.scheme {} [] got}"

def locateTypecheckFail (ctors : CtorEnv) (ke : KindEnv) (p : Surface.Program)
    (binders : List BinderSpan) (sp : SpannedProgram) : HoverDiag :=
  let rec go (acc : List (List Surface.Binding))
      (rest : List (List Surface.Binding)) : HoverDiag :=
    match rest with
    | [] => diagAtSpan "typechecking failed" (some (bodyDiagSpan sp.body))
    | g :: gs =>
      match g with
      | [] => go (acc ++ [g]) gs
      | b :: _ =>
        let acc' := acc ++ [g]
        let probe := Surface.desugarGroups acc' (.var b.name)
        if hmSucceeds ctors probe then go acc' gs
        else
          let nm := prettySurfaceName b.name
          let msg := explainTypeMismatch ctors ke acc g b
          match bindingExtentSpan binders p sp nm with
          | some s => diagAtSpan msg (some s)
          | none => diagAtSpan msg (some (bodyDiagSpan sp.body))
  go [] p.groups

def locateLowerFail (src : String) (p : Surface.Program) (sp : SpannedProgram) : HoverDiag :=
  match freeNamesD [] p.term with
  | n :: _ =>
      let nm := prettySurfaceName n
      let msg := s!"unbound name `{nm}`"
      match firstIdentSpan src nm with
      | some s => diagAtSpan msg (some s)
      | none => diagAtSpan msg (some (bodyDiagSpan sp.body))
  | [] => diagAtSpan
      "expression lowering failed (rejected sugar, bad annotation, or pattern λ)"
      (some (bodyDiagSpan sp.body))

/-- The first `match` (outermost first, in source order) that isn't
    exhaustive, found by walking the program alongside its span tree. Each
    match is judged by `checkExhaustive` on the match alone, with its scrutinee
    and arm bodies replaced by `()`. -/
partial def firstNonExhaustive (ctors : CtorEnv) : Surface.Expr → SpannedExpr → Option Span
  | .pair a b, .pair _ sa sb | .cons a b, .cons _ sa sb | .app a b, .app _ sa sb =>
      firstNonExhaustive ctors a sa <|> firstNonExhaustive ctors b sb
  | .list es, .list _ ses => firstIn (es.zip ses)
  | .lambda _ _ body, .lambda _ sbody => firstNonExhaustive ctors body sbody
  | .letIn _ _ _ _ rhs body, .letIn _ srhs sbody =>
      firstNonExhaustive ctors rhs srhs <|> firstNonExhaustive ctors body sbody
  | .letRecIn binds body, .letRecIn _ rhss sbody =>
      firstIn ((binds.map (·.rhs)).zip rhss) <|> firstNonExhaustive ctors body sbody
  | .ife c t f, .ife _ sc st sf =>
      firstIn [(c, sc), (t, st), (f, sf)]
  | .match_ scrut arms, .match_ span sscrut sarms =>
      let alone := Surface.Expr.match_ (.primLit .unit) (arms.map fun (p, _) => (p, .primLit .unit))
      firstNonExhaustive ctors scrut sscrut <|>
        (if checkExhaustive ctors alone then none else some span) <|>
        firstIn ((arms.map (·.2)).zip sarms)
  | _, _ => none
where
  firstIn : List (Surface.Expr × SpannedExpr) → Option Span
    | [] => none
    | (e, se) :: rest => firstNonExhaustive ctors e se <|> firstIn rest

def locateDeclFail (sp : SpannedProgram) (msg : String) : HoverDiag :=
  match sp.declSpans with
  | s :: _ => diagAtSpan msg (some s)
  | [] => diagAtSpan msg none

def collectHover (src : String) (p : Surface.Program) (binders : List BinderSpan)
    (sp : SpannedProgram) : HoverReport :=
  let fail (d : HoverDiag) : HoverReport :=
    { symbols := [], programTy := "", diagnostics := [d] }
  match lowerDataDeclsIn preludeKindEnv p.decls with
  | none => fail (locateDeclFail sp
      "declaration lowering failed (duplicate type/ctor, bad field, or unknown type)")
  | some userCore =>
    match elabDecls (preludeDecls ++ userCore) with
    | none => fail (locateDeclFail sp "declaration elaboration failed (ill-formed data decls)")
    | some ctors =>
      let ke := DataDecls.kindEnv (preludeDecls ++ userCore)
      let scope := programWideScope binders sp
      match FHM.Unverified.HMArtifacts.programSpanned p sp scope with
      | none => fail (diagAtSpan "internal parser provenance shape mismatch" (some scope))
      | some tree =>
        match SurfaceBridge.Provenance.lowerWithProvenance ctors p.term tree with
        | none => fail (locateLowerFail src p sp)
        | some lowered =>
          match SurfaceBridge.Provenance.inferWithProvenance ctors lowered with
          | none => fail (locateTypecheckFail ctors ke p binders sp)
          | some typed =>
            if !lowered.provenanceTotal || !typed.nodeTypesTotal || !typed.sourceTypesTotal ||
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
                pure { mkSym name kind ty source.span source.span with doc }
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
                else none).map fun s => { s with isDef := true, doc := docAt s.span }
              let prelude := (preludeTypeCtorSymbols ctors scope ++ primTypeSymbols scope).filter fun s =>
                !(syntaxSyms.any fun b => b.name == s.name && b.kind == s.kind)
              let sugarOps := (collectLitOpSymbols src ctors).filter fun s => s.name == "::"
              -- Typing succeeded, so hovers stay available alongside this error.
              let exhaustiveness :=
                if checkExhaustive ctors p.term then []
                else [diagAtSpan "match not exhaustive"
                  ((firstNonExhaustive ctors p.term tree).orElse fun _ => some (bodyDiagSpan sp.body))]
              { symbols := prelude ++ syntaxSyms ++ values ++ sugarOps ++ occurrences
                programTy := FHM.Unverified.HMDisplay.scheme {} []
                  (genScheme [] [] typed.inference.ty)
                diagnostics := exhaustiveness }

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
