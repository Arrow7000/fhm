import FHM.Unverified.Surface.Parse
import FHM.Unverified.RecoveryDependencies
import FHM.Unverified.LexRecovery

/-! Editor-only top-level parser resynchronisation. Native parsing remains
strict. Recovery removes rejected token regions, retaining original token spans,
and withholds names established by their authored headers. Recovered fragments
are parsed again by the canonical grammar; no executable program is certified. -/
namespace FHM.Unverified.ParserRecovery
open Surface Surface.Parse Surface.Span RecoveryDependencies
open Surface.Lex (Token)

structure Unparsed where
  error : ParseError
  span : Span
  tokens : Array Tok
  binders : List BinderSpan := []

structure Result where
  program : Surface.Program
  binders : List BinderSpan
  spanned : SpannedProgram
  errors : List ParseError := []
  unavailable : List Unparsed := []
  seed : Seed := {}

private structure Item where
  first : Nat
  last : Nat
  parsed : Sum (Surface.DataDecl × Span) ParsedLetBinding × List ParsedNameSpan

private structure Scan where
  items : List Item := []
  failure : Option (Nat × ParseError) := none
  body : Option Nat := none

private def isHeader (token : Token) : Bool :=
  match token with | .keyword .«let» | .keyword .«type» => true | _ => false

private def codeAt (tokens : Array Tok) (index : Nat) : Nat :=
  index + ((tokens.toList.drop index).takeWhile (fun token => isComment token.token)).length

private def beforeComments (tokens : Array Tok) (index : Nat) : Nat :=
  index - ((List.range index).reverse.takeWhile fun i =>
    (tokens[i]?.map fun token => isComment token.token).getD false).length

private def regionSpan (tokens : Array Tok) (first last : Nat) : Span :=
  (Span.hull ((tokens.extract first last).toList.map Span.ofTok)).getD Span.empty

/-- Scan only through grammar-accepted items; errors preserve the native site.
The finite fuel also protects the editor if a future parser fails to advance. -/
private def scan (tokens : Array Tok) (offset : Nat := 0) : Scan :=
  let rec go : Nat → Nat → List Item → Scan
    | 0, index, items => ⟨items, none, some index⟩
    | fuel + 1, index, items =>
      let first := codeAt tokens index
      match tokens[first]? with
      | none => ⟨items, none, none⟩
      | some token =>
        if !isHeader token.token then ⟨items, none, some first⟩ else
          match Parser.run programItem (tokens.toSubarray first) with
          | .error _ error => ⟨items, some (first, simpleErrToParse tokens error), none⟩
          | .ok remaining parsed =>
            if remaining.start ≤ first then ⟨items, none, some first⟩ else
              go fuel remaining.start (items ++ [⟨beforeComments tokens first, beforeComments tokens remaining.start, parsed⟩])
  go (tokens.size + 1) offset []

private def nextHeader (tokens : Array Tok) (first : Nat) : Nat :=
  match tokens[first]? with
  | none => tokens.size
  | some owner =>
      let next := (List.range tokens.size).find? fun index => index > first &&
        ((tokens[index]?.map fun token => isHeader token.token &&
          token.startLine > owner.startLine && token.startCol ≤ owner.startCol).getD false)
      (next.map (beforeComments tokens)).getD tokens.size

private structure Removal where
  first : Nat
  last : Nat
  body : Bool := false

private def itemNames (item : Item) : List ValName :=
  match item.parsed.1 with
  | .inl _ => []
  | .inr binding => binding.entries.map (·.1.name)

private def covers (span : Span) (error : ParseError) : Bool :=
  span.contains error.line error.col ||
    (span.endLine == error.line && span.endCol == error.col)

/-- Global grammar checks (duplicates, pattern cycles, documentation) happen
after item parsing. Keep their rejection unit rather than silently keeping one
of several conflicting definitions. -/
private def removals (tokens : Array Tok) (error : ParseError) : List Removal := Id.run do
  if error.msg.startsWith "a doc comment must" then
    let index := (List.range tokens.size).find? fun i =>
      (tokens[i]?.map fun token => covers (Span.ofTok token) error).getD false
    return index.toList.map fun i => ⟨i, i + 1, false⟩
  let scanned := scan tokens
  match scanned.failure with
  | some (first, _) =>
      return [⟨beforeComments tokens first, nextHeader tokens first, false⟩]
  | none =>
    let names := scanned.items.flatMap itemNames
    let duplicates := (names.filter (fun name => 1 < names.count name)).eraseDups
    if !duplicates.isEmpty then
      return (scanned.items.filter fun item => (itemNames item).any duplicates.contains).map
        fun item => ⟨item.first, item.last, false⟩
    let pattern := scanned.items.find? fun item =>
      match item.parsed.1 with
      | .inr binding => (binding.patternToken?.map fun token => covers (Span.ofTok token) error).getD false
      | _ => false
    match pattern with
    | some item => return [⟨item.first, item.last, false⟩]
    | none =>
      match scanned.body with
      | some first =>
          match scanned.items.getLast?, tokens[first]? with
          | some previous, some bodyToken =>
              let headerIndex := codeAt tokens previous.first
              let headerCol := ((tokens[headerIndex]?).map (·.startCol)).getD 1
              let previousSpan := regionSpan tokens previous.first previous.last
              if bodyToken.startLine == previousSpan.endLine || bodyToken.startCol > headerCol then
                return [⟨previous.first, nextHeader tokens headerIndex, false⟩]
              else return [⟨first, nextHeader tokens first, true⟩]
          | _, _ => return [⟨first, nextHeader tokens first, true⟩]
      | none =>
          return ((scanned.items.find? fun item => covers (regionSpan tokens item.first item.last) error).toList).map
            fun item => ⟨item.first, item.last, false⟩

/-- Parse the already established part of a malformed header with the native
pattern/name grammar. A missing name is not guessed from the failed RHS. -/
private def headerBinders (tokens : Array Tok) : List BinderSpan := Id.run do
  let first := codeAt tokens 0
  match tokens[first]? with
  | none => return []
  | some token =>
    match token.token with
    | .keyword .«let» =>
        match Parser.run (keyword .«let» *> skipComments *> pattern) (tokens.toSubarray first) with
        | .error .. => return []
        | .ok _ (_, names) => return names.filterMap fun name =>
            if name.isDef then some { name.toBinderSpan with kind := .val } else none
    | .keyword .«type» =>
        let prefixParser := do
          let _ ← keyword .«type»
          skipComments
          upperIdentTok
        match Parser.run prefixParser (tokens.toSubarray first) with
        | .error .. => return []
        | .ok _ (nameToken, name) =>
            let code := tokens.toList.filter (fun tok => !isComment tok.token)
            let constructors : List BinderSpan := code.zip code.tail |>.filterMap fun (previous, current) =>
              if previous.token == .punct .eq || previous.token == .punct .pipe then
                match current.token with
                | .ident name true => some { name := name, kind := .ctor, span := Span.ofTok current }
                | _ => none
              else none
            return { name, kind := .type, span := Span.ofTok nameToken } :: constructors
    | _ => return []

private def mergeNames [BEq α] (existing additions : List (α × List Cause)) : List (α × List Cause) :=
  additions.foldl (fun current (name, causes) =>
    if current.any (·.1 == name) then current.map (fun (prior, old) =>
      if prior == name then (prior, (old ++ causes).eraseDups) else (prior, old))
    else current ++ [(name, causes)]) existing

private def addSeed (seed : Seed) (binders : List BinderSpan) (cause : Cause)
    (body : Bool) : Seed :=
  { values := mergeNames seed.values (binders.filterMap (fun binder =>
      if binder.kind == .val then some (.mk binder.name, [cause]) else none))
    types := mergeNames seed.types (binders.filterMap (fun binder =>
      if binder.kind == .type then some (.mk binder.name, [cause]) else none))
    constructors := mergeNames seed.constructors (binders.filterMap (fun binder =>
      if binder.kind == .ctor then some (.mk binder.name, [cause]) else none))
    body := if body then (seed.body ++ [cause]).eraseDups else seed.body }

private def positionLE (a b : Span) : Bool :=
  a.startLine < b.startLine || (a.startLine == b.startLine && a.startCol ≤ b.startCol)

private def inInterval (tokens : Array Tok) (gap : Span) (first last : Nat) : Bool :=
  let start := (tokens[first]?.map Span.ofTok).getD Span.empty
  let stop := tokens[last]?.map Span.ofTok
  positionLE start gap && (stop.map (fun stop => !positionLE stop gap)).getD true

private def bodyOwner (tokens : Array Tok) (scanned : Scan) (first : Nat) : Nat :=
  match scanned.items.getLast?, tokens[first]? with
  | some previous, some bodyToken =>
      let headerIndex := codeAt tokens previous.first
      let headerCol := ((tokens[headerIndex]?).map (·.startCol)).getD 1
      let previousSpan := regionSpan tokens previous.first previous.last
      if bodyToken.startLine == previousSpan.endLine || bodyToken.startCol > headerCol then headerIndex else first
  | _, _ => first

private def scanAround (tokens : Array Tok) (gap : Span) : Scan :=
  let rec go : Nat → Nat → Scan
    | 0, offset => scan tokens offset
    | fuel + 1, offset =>
        let scanned := scan tokens offset
        let failed := (scanned.failure.map (·.1)).orElse
          (fun _ => scanned.body.map (bodyOwner tokens scanned))
        match failed with
        | none => scanned
        | some first =>
            let next := nextHeader tokens first
            match tokens[next]? with
            | some header => if next > offset && header.startLine ≤ gap.startLine then go fuel next else scanned
            | none => scanned
  go (tokens.size + 1) 0

/-- A lexical gap can make the remaining tokens look valid. Quarantine its
owning item/body before any recovered source is checked, instead of accepting a
program obtained by deleting a malformed literal or layout character. -/
private def gapRemoval (tokens : Array Tok) (gap : Span) : Option Removal := Id.run do
  let scanned := scanAround tokens gap
  let exact := scanned.items.find? fun item =>
    covers (regionSpan tokens item.first item.last) { msg := "", line := gap.startLine, col := gap.startCol }
  let before := (scanned.items.filter fun item =>
    let span := regionSpan tokens item.first item.last
    gap.startLine == span.endLine && gap.startCol ≥ span.endCol).getLast?
  let after := scanned.items.find? fun item =>
    let span := regionSpan tokens item.first item.last
    gap.startLine == span.startLine && gap.startCol ≤ span.startCol
  let owner := exact.orElse (fun _ => before) |>.orElse (fun _ => after)
  match owner with
  | some item => return some ⟨item.first, item.last, false⟩
  | none =>
    match scanned.failure with
    | some (first, _) =>
        let last := nextHeader tokens first
        if inInterval tokens gap first last ||
            ((tokens[first]?.map (·.startLine)).getD 0 == gap.startLine) then
          return some ⟨beforeComments tokens first, last, false⟩
    | none => pure ()
    match scanned.body with
    | some bodyFirst =>
        let first := bodyOwner tokens scanned bodyFirst
        let last := nextHeader tokens first
        if inInterval tokens gap first last then return some ⟨beforeComments tokens first, last, first == bodyFirst⟩
    | none => pure ()
    let laterHeader := tokens.toList.any fun token => isHeader token.token && positionLE gap (Span.ofTok token)
    if !laterHeader then
      match scanned.body with
      | some first => return some ⟨first, tokens.size, true⟩
      | none => return none
    else return none

/-- Recover top-level source from native tokens and rejected lexical regions.
Opaque gap markers are excluded from parsing and inference. -/
def check (source : String) : Except ParseError Result := do
  let lexed := LexRecovery.check source
  let original := lexed.tokens
  let mut lexicalUnavailable : List Unparsed := []
  let mut lexicalSeed : Seed := {}
  let mut lexicalRemovals : List Removal := []
  for gap in lexed.gaps do
    let error := lexToParse gap.error
    let cause := Cause.syntax ⟨error.line, error.col, error.endLine, error.endCol⟩
    if gap.commentOnly then
      lexicalUnavailable := lexicalUnavailable ++ [⟨error, gap.span, #[], []⟩]
    else
      match gapRemoval original gap.span with
      | some removal =>
          let removed := original.extract removal.first removal.last
          let binders := headerBinders removed
          let span := (Span.hull [regionSpan original removal.first removal.last, gap.span]).getD gap.span
          if !lexicalUnavailable.any (·.span == span) then
            lexicalUnavailable := lexicalUnavailable ++ [⟨error, span, removed, binders⟩]
          lexicalRemovals := lexicalRemovals ++ [removal]
          lexicalSeed := addSeed lexicalSeed binders cause (removal.last == original.size)
      | none =>
          lexicalUnavailable := lexicalUnavailable ++ [⟨error, gap.span, #[], []⟩]
          let laterHeader := original.toList.any fun token => isHeader token.token && positionLE gap.span (Span.ofTok token)
          if !laterHeader then lexicalSeed := { lexicalSeed with body := (lexicalSeed.body ++ [cause]).eraseDups }
  let surviving := original.zipIdx.filterMap fun (token, index) =>
    if lexicalRemovals.any (fun removal => removal.first ≤ index && index < removal.last) then none else some token
  let rec go (fuel : Nat) (tokens : Array Tok) (errors : List ParseError)
      (unavailable : List Unparsed) (seed : Seed) : Except ParseError Result := do
    match parseProgramTokensWithSpans tokens with
    | .ok (program, binders, spanned) => pure ⟨program, binders, spanned, errors, unavailable, seed⟩
    | .error error =>
      match fuel with
      | 0 => .error error
      | fuel + 1 =>
        let rejected := removals tokens error
        if rejected.isEmpty then .error error else do
          let spans := rejected.map (fun removal => regionSpan tokens removal.first removal.last)
          let diagnostic := if spans.any (covers · error) then error else
            let last := rejected.getLast?.getD ⟨0, 0, false⟩
            let span := if error.msg == "duplicate binding names" then
              ((headerBinders (tokens.extract last.first last.last)).find? (·.kind == .val)).map (·.span)
                |>.getD ((spans.getLast?).getD Span.empty)
              else (spans.head?).getD Span.empty
            if error.msg == "duplicate binding names" then
              { error with
                line := span.startLine
                col := span.startCol
                endLine := span.endLine
                endCol := span.endCol }
            else
              { error with
                line := span.endLine
                col := span.endCol
                endLine := span.endLine
                endCol := span.endCol + 1 }
          let mut exclusions := unavailable
          let mut nextSeed := seed
          for removal in rejected do
            let removed := tokens.extract removal.first removal.last
            let binders := headerBinders removed
            let span := regionSpan tokens removal.first removal.last
            let cause := Cause.syntax ⟨diagnostic.line, diagnostic.col, diagnostic.endLine, diagnostic.endCol⟩
            exclusions := exclusions ++ [⟨diagnostic, span, removed, binders⟩]
            -- A rejected trailing item may contain an unparsed final expression.
            nextSeed := addSeed nextSeed binders cause (removal.last == tokens.size && !error.msg.startsWith "a doc comment must")
          let remaining := tokens.zipIdx.filterMap fun (token, index) =>
            if rejected.any (fun removal => removal.first ≤ index && index < removal.last) then none else some token
          if remaining.size ≥ tokens.size then .error error else
            go fuel remaining (errors ++ [diagnostic]) exclusions nextSeed
  go (original.size + 1) surviving (lexed.gaps.map (fun gap => lexToParse gap.error)) lexicalUnavailable lexicalSeed

end FHM.Unverified.ParserRecovery
