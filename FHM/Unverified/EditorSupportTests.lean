import FHM.Unverified.EditorSupport

/-!
# Editor hover canaries (span + scope / use-site)

`lake build FHMEditorTests` evaluates these `#guard`s.
-/

open Surface.Parse
open Surface.Span

/-- Substring check (`String.contains` is Char-only). -/
def hasSub (s needle : String) : Bool :=
  (s.splitOn needle).length > 1

/-- Helper: parse + collect hover symbols. -/
def hoverSyms (src : String) : Option (List RangedSymbol) :=
  match parseProgramWithSpans src with
  | .error _ => none
  | .ok (p, bs, sp) => some (collectHover src p bs sp).symbols

-- Span.contains / symbolAt edge cases
#guard (Span.contains ⟨1, 5, 1, 7⟩ 1 5) = true
#guard (Span.contains ⟨1, 5, 1, 7⟩ 1 7) = false

def toySyms : List RangedSymbol := [
  { name := "xs", kind := "param", type_ := "a",
    span := ⟨1, 10, 1, 12⟩, scope := ⟨1, 10, 1, 20⟩ },
  { name := "xs", kind := "val", type_ := "Int",
    span := ⟨2, 5, 2, 7⟩, scope := ⟨2, 5, 3, 5⟩ }
]

#guard (match symbolAt toySyms 1 11 with
  | some s => s.kind == "param" && s.type_ == "a"
  | none => false)
#guard (match symbolAt toySyms 2 6 with
  | some s => s.kind == "val" && s.type_ == "Int"
  | none => false)
-- Cursor on whitespace between binders → none
#guard (symbolAt toySyms 1 1).isNone
#guard (symbolAt toySyms 1 20).isNone

-- 1. Shadowed `xs`
def shadowedXs : String :=
  "let f = \\xs -> xs\nlet xs = 1\nf xs\n"

#guard (match hoverSyms shadowedXs with
  | none => false
  | some syms =>
    match symbolAt syms 1 10, symbolAt syms 2 5 with
    | some p, some v =>
        p.name == "xs" && v.name == "xs" &&
        p.kind == "param" && v.kind == "val" &&
        p.type_ != v.type_ &&
        hasSub v.type_ "Int"
    | _, _ => false)

-- 2. Annotation ceilings need not constrain an unused RHS parameter. Its
-- actual inferred monotype remains more general than the declared domain.
def mapLike : String :=
  "let map : {a} (a -> a) -> List a -> List a =\n  \\f xs -> xs\n"

#guard (match hoverSyms mapLike with
  | none => false
  | some syms =>
    match symbolAt syms 2 4, symbolAt syms 2 6 with
    | some f, some xs =>
        f.name == "f" && xs.name == "xs" &&
        f.kind == "param" && xs.kind == "param" &&
        !f.type_.isEmpty && !xs.type_.isEmpty &&
        !hasSub f.type_ "type variable" && !hasSub xs.type_ "type variable"
    | _, _ => false)

-- 3. Type / ctor spans + tyvar label (D)
def maybeSrc : String :=
  "type Maybe a = Just a | Nothing\n"

#guard (match hoverSyms maybeSrc with
  | none => false
  | some syms =>
    match symbolAt syms 1 6, symbolAt syms 1 16 with
    | some t, some c =>
        t.name == "Maybe" && t.kind == "type" &&
        c.name == "Just" && c.kind == "ctor"
    | _, _ => false)

#guard (match hoverSyms maybeSrc with
  | none => false
  | some syms =>
    match symbolAt syms 1 12 with
    | some a =>
        a.name == "a" && a.kind == "param" &&
        hasSub a.type_ "type variable" && hasSub a.type_ "Maybe"
    | none => false)

-- A type and its constructor occupy separate namespaces at use sites,
-- including nested annotations, wildcard parameters and constructor fields.
def sameNameSrc : String :=
  "type Box a = Box a\n" ++
  "type Wrap a = Wrap (Box a)\n" ++
  "let unbox : {a} Box a -> a = \\b -> match b with | Box x -> x\n" ++
  "let ignore = \\(_ : Box Int) -> 0\n" ++
  "unbox (Box 3)\n"

#guard (match hoverSyms sameNameSrc with
  | none => false
  | some syms =>
    match symbolAt syms 2 21, symbolAt syms 3 17,
        symbolAt syms 3 51, symbolAt syms 4 20, symbolAt syms 5 8 with
    | some field, some ann, some pat, some wildcardAnn, some value =>
        field.kind == "type" && ann.kind == "type" &&
        wildcardAnn.kind == "type" && hasSub ann.type_ "type Box a" &&
        pat.kind == "ctor" && value.kind == "ctor"
    | _, _, _, _, _ => false)

-- 4. Binder span count / name order canary
def binderCanarySrc : String :=
  "type Maybe a = Just a | Nothing\nlet id = \\x -> x\n"

#guard (match parseProgramWithBinders binderCanarySrc with
  | .error _ => false
  | .ok (_, bs) =>
      binderNames bs == ["Maybe", "a", "Just", "Nothing", "id", "x"])

-- 5. Nested let shadows
def nestedShadow : String :=
  "let x = 1\nlet y = let x = True in x\ny\n"

#guard (match hoverSyms nestedShadow with
  | none => false
  | some syms =>
    match symbolAt syms 1 5, symbolAt syms 2 13 with
    | some outer, some inner =>
        outer.name == "x" && inner.name == "x" &&
        outer.kind == "val" && inner.kind == "val" &&
        hasSub outer.type_ "Int" &&
        (hasSub inner.type_ "Bool" || inner.type_ == "Bool")
    | _, _ => false)

-- 5b. Local acyclic forward references are SCC-ordered for lowering while
-- binder and use-site locations remain attached to their source tokens.
def localForwardRef : String :=
  "let result =\n" ++
  "  let x = y\n" ++
  "      y = 1\n" ++
  "  in x\n" ++
  "result\n"

#guard (match hoverSyms localForwardRef with
  | none => false
  | some syms =>
    match symbolAt syms 2 7, symbolAt syms 3 7,
        symbolAt syms 2 11, symbolAt syms 4 6 with
    | some xBinder, some yBinder, some yUse, some xUse =>
        xBinder.name == "x" && yBinder.name == "y" &&
        yUse.name == "y" && xUse.name == "x" &&
        xBinder.kind == "val" && yBinder.kind == "val" &&
        hasSub xBinder.type_ "Int" && hasSub yBinder.type_ "Int" &&
        hasSub yUse.type_ "Int" && hasSub xUse.type_ "Int"
    | _, _, _, _ => false)

-- 6. Pattern binds (`h` / `t`) from scrutinee + patBindTys
def patBindSrc : String :=
  "let xs : List Int = [1]\n" ++
  "let f = \\ys -> match ys with | h :: t -> h | [] -> 0\n" ++
  "f xs\n"

#guard (match hoverSyms patBindSrc with
  | none => false
  | some syms =>
    let h? := syms.find? (fun s => s.name == "h" && s.kind == "pat")
    let t? := syms.find? (fun s => s.name == "t" && s.kind == "pat")
    match h?, t? with
    | some h, some t =>
        !h.type_.isEmpty && !t.type_.isEmpty &&
        (hasSub h.type_ "Int" || h.type_ == "Int") &&
        hasSub t.type_ "List"
    | _, _ => false)

-- 7. λ-as-arg: domain peel through `.app` (filter (\n -> …))
def filterLamSrc : String :=
  "let filter : {a} (a -> Bool) -> List a -> List a = \\p xs -> xs\n" ++
  "filter (\\n -> True) []\n"

#guard (match hoverSyms filterLamSrc with
  | none => false
  | some syms =>
    match symbolAt syms 2 10 with
    | some n =>
        n.name == "n" && n.kind == "param" && !n.type_.isEmpty
    | none => false)

-- 8. Shadowed xs still distinct (span-only; empty must not steal)
#guard (match hoverSyms shadowedXs with
  | none => false
  | some syms =>
    match symbolAt syms 1 10, symbolAt syms 2 5 with
    | some p, some v =>
        p.name == "xs" && v.name == "xs" && p.span != v.span
    | _, _ => false)

-- A1. Use of `xs` in body resolves via scope
#guard (match hoverSyms mapLike with
  | none => false
  | some syms =>
    -- `\f xs -> xs` — use of xs at end of line 2
    match symbolAtUseSite syms 2 12 "xs" with
    | some s =>
        s.name == "xs" && s.kind == "param" && !s.type_.isEmpty
    | none => false)

-- A2. Shadowed use: `f xs` on line 3 resolves to val xs, not param
#guard (match hoverSyms shadowedXs with
  | none => false
  | some syms =>
    match symbolAtUseSite syms 3 3 "xs" with
    | some s => s.kind == "val" && hasSub s.type_ "Int"
    | none => false)

-- A3. Nested let use of inner x
#guard (match hoverSyms nestedShadow with
  | none => false
  | some syms =>
    -- `let x = True in x` — use of x (col of the final `x`)
    match symbolAtUseSite syms 2 25 "x" with
    | some s => s.kind == "val" && (hasSub s.type_ "Bool" || s.type_ == "Bool")
    | none => false)

-- B/C1. let in match arm — def + use of y
def letInMatchSrc : String :=
  "let f = \\b -> match b with | True -> let y = 1 in y | False -> 0\n" ++
  "f True\n"

#guard (match hoverSyms letInMatchSrc with
  | none => false
  | some syms =>
    let yDef := syms.find? (fun s => s.name == "y" && s.kind == "val")
    match yDef with
    | some y =>
        !y.type_.isEmpty && hasSub y.type_ "Int" &&
        -- use site of y in `in y` (col of the use)
        match symbolAtUseSite syms 1 51 "y" with
        | some u => u.name == "y" && !u.type_.isEmpty
        | none => false
    | none => false)

-- B/C2. pat x from `Just 1` scrutinee when synth works
def justPatSrc : String :=
  "type Maybe a = Just a | Nothing\n" ++
  "let v = match (Just 1) with | Just x -> x | Nothing -> 0\n" ++
  "v\n"

#guard (match hoverSyms justPatSrc with
  | none => false
  | some syms =>
    match syms.find? (fun s => s.name == "x" && s.kind == "pat") with
    | some x => !x.type_.isEmpty && (hasSub x.type_ "Int" || x.type_ == "Int")
    | none => false)

-- D1. Lit / op tokens from Core types
#guard (match hoverSyms "1 + 2\n" with
  | none => false
  | some syms =>
    match symbolAt syms 1 3 with
    | some s =>
        s.kind == "op" && s.name == "+" &&
        hasSub s.type_ "Int" && (hasSub s.type_ "→" || hasSub s.type_ "->")
    | none => false)

#guard (match hoverSyms "42\n" with
  | none => false
  | some syms =>
    match symbolAt syms 1 1 with
    | some s => s.kind == "lit" && hasSub s.type_ "Int"
    | none => false)

#guard (match hoverSyms "True\n" with
  | none => false
  | some syms =>
    match symbolAt syms 1 1 with
    | some s => s.kind == "lit" && (hasSub s.type_ "Bool" || s.type_ == "Bool")
    | none => false)

#guard (match hoverSyms "1 :: []\n" with
  | none => false
  | some syms =>
    match symbolAt syms 1 3 with
    | some s =>
        s.kind == "op" && s.name == "::" &&
        hasSub s.type_ "∀" && hasSub s.type_ "List"
    | none => false)

-- D2. Type / ctor use-site via program-wide scope
def maybeUseSrc : String :=
  "type Maybe a = Just a | Nothing\n" ++
  "let v : Maybe Int = Just 1\n" ++
  "v\n"

#guard (match hoverSyms maybeUseSrc with
  | none => false
  | some syms =>
    -- `Maybe` in `Maybe Int` annotation (line 2, after `: `)
    match symbolAtUseSite syms 2 9 "Maybe" with
    | some s => s.kind == "type" && hasSub s.type_ "Maybe"
    | none => false)

#guard (match hoverSyms maybeUseSrc with
  | none => false
  | some syms =>
    -- `Just` in `Just 1`
    match symbolAtUseSite syms 2 21 "Just" with
    | some s => s.kind == "ctor" && !s.type_.isEmpty
    | none => false)

-- D3. Prelude `List` / `Bool` use-site (no source def span)
#guard (match hoverSyms "let xs : List Int = []\nxs\n" with
  | none => false
  | some syms =>
    match symbolAtUseSite syms 1 10 "List" with
    | some s => s.kind == "type" && hasSub s.type_ "List"
    | none => false)

#guard (match hoverSyms "let b : Bool = True\nb\n" with
  | none => false
  | some syms =>
    match symbolAtUseSite syms 1 9 "Bool" with
    | some s => s.kind == "type" && hasSub s.type_ "Bool"
    | none => false)

-- E1. Tyvar use-site inside data decl field (`Just a`)
#guard (match hoverSyms maybeSrc with
  | none => false
  | some syms =>
    -- `a` in `Just a` (col 21 of `type Maybe a = Just a | Nothing`)
    match symbolAtUseSite syms 1 21 "a" with
    | some s =>
        s.name == "a" && s.kind == "param" &&
        hasSub s.type_ "type variable" && hasSub s.type_ "Maybe"
    | none => false)

-- E2. Unit lit `()` (two punct tokens → one lit span)
#guard (match hoverSyms "()\n" with
  | none => false
  | some syms =>
    match symbolAt syms 1 1 with
    | some s =>
        s.kind == "lit" && s.name == "()" &&
        (hasSub s.type_ "Unit" || s.type_ == "Unit")
    | none => false)

-- E3. Scheme-ann tyvar use inside annotation (`List a`)
#guard (match hoverSyms mapLike with
  | none => false
  | some syms =>
    -- `a` in `List a` on line 1 (col 32 of mapLike)
    match symbolAtUseSite syms 1 32 "a" with
    | some s =>
        s.name == "a" && s.kind == "param" &&
        hasSub s.type_ "type variable" && hasSub s.type_ "scheme"
    | none => false)

-- E4. Several annotated lets: later λ params must not get empty/stolen types
-- (regression: takeFirstKind .val reshuffled earlier λ/pats ahead of scheme binders)
def multiLetParams : String :=
  "let first : {a} (a -> a) -> List a -> List a =\n" ++
  "  \\f xs -> xs\n" ++
  "let second : {a} (a -> a) -> List a -> List a =\n" ++
  "  \\f ys -> ys\n" ++
  "let colorOf = \\n -> n\n" ++
  "colorOf 1\n"

#guard (match hoverSyms multiLetParams with
  | none => false
  | some syms =>
    match symbolAt syms 2 4, symbolAt syms 2 6,
          symbolAt syms 4 4, symbolAt syms 4 6,
          symbolAt syms 5 16 with
    | some f1, some xs, some f2, some ys, some n =>
        f1.name == "f" && !f1.type_.isEmpty && !hasSub f1.type_ "type variable" &&
        xs.name == "xs" && !xs.type_.isEmpty &&
        f2.name == "f" && !f2.type_.isEmpty &&
        ys.name == "ys" && !ys.type_.isEmpty &&
        n.name == "n" && !n.type_.isEmpty
    | _, _, _, _, _ => false)

-- E5. SCC topo order ≠ source order must not steal types (live.fhm class bug).
-- Independent tops elaborate callees-outer (often reverse source); hover walks
-- source order and looks up schemes by name.
def sccOrderSrc : String :=
  "type Maybe a = Just a | Nothing\n" ++
  "type Tree a = Leaf | Node a (Tree a) (Tree a)\n" ++
  "let mapMaybe : {a b} (a -> b) -> Maybe a -> Maybe b =\n" ++
  "  \\f m -> match m with | Nothing -> Nothing | Just x -> Just (f x)\n" ++
  "let treeMap : {a b} (a -> b) -> Tree a -> Tree b =\n" ++
  "  \\f t -> match t with | Leaf -> Leaf | Node x l r -> Node (f x) (treeMap f l) (treeMap f r)\n" ++
  "let addInts : Int -> Int -> Int = \\a b -> a + b\n" ++
  "addInts 1 2\n"

#guard (match hoverSyms sccOrderSrc with
  | none => false
  | some syms =>
    let mm := syms.find? (fun s => s.name == "mapMaybe" && s.kind == "val")
    let tm := syms.find? (fun s => s.name == "treeMap" && s.kind == "val")
    let ai := syms.find? (fun s => s.name == "addInts" && s.kind == "val")
    let mParam := syms.find? (fun s =>
      s.name == "m" && s.kind == "param" && hasSub s.type_ "Maybe")
    let tParam := syms.find? (fun s =>
      s.name == "t" && s.kind == "param" && hasSub s.type_ "Tree")
    match mm, tm, ai, mParam, tParam with
    | some mm, some tm, some ai, some m, some t =>
        hasSub mm.type_ "Maybe" && hasSub tm.type_ "Tree" &&
        hasSub ai.type_ "Int" &&
        !(hasSub mm.type_ "Int → Int") &&  -- not stolen from addInts
        !m.type_.isEmpty && !t.type_.isEmpty &&
        -- use-site: `m` in `match m` on line 4 (`  \f m -> match m with…`, col 17)
        match symbolAtUseSite syms 4 17 "m" with
        | some u => u.kind == "param" && hasSub u.type_ "Maybe"
        | none => false
    | _, _, _, _, _ => false)

/-- Helper: parse + full HM hover report. -/
def hoverReport (src : String) : Option HoverReport :=
  match parseProgramWithSpans src with
  | .error _ => none
  | .ok (p, bs, sp) => some (collectHover src p bs sp)

-- Removed bounds syntax is rejected before the HM editor pipeline runs.
#guard !(parseProgramWithSpans "let xs : BL 1 1 Int = [1]\nxs\n").isOk
#guard !(parseProgramWithSpans "let id : {n : Nat, a} a -> a = \\x -> x\nid\n").isOk

/-! ## HM / lower diagnostics (must not collapse to file-top (1,1)) -/

-- E7. Unbound name: point at the free use site, message names it.
def unboundSrc : String :=
  "let x = y\nx\n"

#guard (match hoverReport unboundSrc with
  | none => false
  | some r =>
      match r.diagnostics with
      | [d] =>
          hasSub d.message "unbound" &&
          hasSub d.message "y" &&
          d.line == 1 &&
          d.col == 9  -- `y` in `let x = y`
      | _ => false)

-- E8. Type error on second binding: progressive probe points at `bad`, not (1,1).
-- Prefer expected/got when ascription is the problem.
def typeSecondSrc : String :=
  "let ok = 1\nlet bad : Int = True\nbad\n"

#guard (match hoverReport typeSecondSrc with
  | none => false
  | some r =>
      match r.diagnostics with
      | [d] =>
          hasSub d.message "bad" &&
          (hasSub d.message "type mismatch" || hasSub d.message "typechecking failed") &&
          (hasSub d.message "Int" || hasSub d.message "Bool" || hasSub d.message "True") &&
          d.line == 2 &&
          -- RHS `True`, not binder `bad`
          d.col ≥ 17 &&
          d.endCol > d.col
      | _ => false)

-- E8b. map vs list→list ascription: show expected vs got (not bare "typechecking failed").
def typeMapMismatchSrc : String :=
  "let map : {a b} (a -> b) -> List a -> List b =\n" ++
  "  \\f xs -> match xs with | [] -> [] | h :: t -> f h :: map f t\n" ++
  "let asdfs : List Int -> List Int = map\n" ++
  "asdfs\n"

#guard (match hoverReport typeMapMismatchSrc with
  | none => false
  | some r =>
      match r.diagnostics with
      | [d] =>
          hasSub d.message "asdfs" &&
          hasSub d.message "expected" &&
          hasSub d.message "got" &&
          hasSub d.message "List Int"
      | _ => false)

-- E9. An argument mismatch identifies the argument inside the body.
def typeBodySrc : String :=
  "let a = 1\na + True\n"

#guard (match hoverReport typeBodySrc with
  | none => false
  | some r =>
      match r.diagnostics with
      | [d] =>
          d.message == "type mismatch: expected Int, got Bool" &&
          d.code? == some "type.argumentMismatch" &&
          d.line == 2 &&  -- body line, not file top
          d.col == 5 && d.endCol == 9  -- `True`
      | _ => false)

-- E11. Unbound multi-char name underlines the whole identifier.
def unboundLongSrc : String :=
  "let x = missingName\nx\n"

#guard (match hoverReport unboundLongSrc with
  | none => false
  | some r =>
      match r.diagnostics with
      | [d] =>
          hasSub d.message "missingName" &&
          d.line == 1 &&
          d.col == 9 &&
          d.endCol == 20  -- full `missingName`
      | _ => false)

-- E10. Parse error has a real end span covering the unexpected token when present.
#guard (match parseProgramWithSpans "let x = \n" with
  | .error e =>
      e.line ≥ 1 && e.col ≥ 1 &&
      (e.endLine > e.line || e.endCol > e.col)
  | .ok _ => false)

/-! ## Rich-output HM regressions (executable tests, not coherence proofs). -/

def instantiatedIdSrc : String :=
  "let id = \\x -> x\nlet number = id 1\nlet truth = id True\n(number, truth)\n"

#guard (match hoverReport instantiatedIdSrc with
  | some r => r.diagnostics.isEmpty &&
    (match symbolAt r.symbols 1 5, symbolAt r.symbols 2 14, symbolAt r.symbols 3 13 with
      | some definition, some numberUse, some truthUse =>
          hasSub definition.type_ "∀" &&
          numberUse.type_ == "Int → Int" && truthUse.type_ == "Bool → Bool"
      | _, _, _ => false)
  | none => false)

-- Later unification refines the lambda binder's payload.
#guard (match hoverReport "let inc = \\x -> x + 1\ninc 2\n" with
  | some r => r.diagnostics.isEmpty &&
      (match symbolAt r.symbols 1 12 with
       | some x => x.kind == "param" && x.type_ == "Int"
       | none => false)
  | none => false)

-- Authored expressions have hovers too, not just names.
#guard (match hoverReport "[1, 2]\n" with
  | some r => r.diagnostics.isEmpty &&
      (match symbolAt r.symbols 1 1 with
       | some xs => xs.kind == "expr" && xs.type_ == "List Int"
       | none => false)
  | none => false)

def afterSccSrc : String :=
  "let f = \\x -> g x\nlet g = \\x -> f x\n(f 1, g True)\n"

#guard (match hoverReport afterSccSrc with
  | some r => r.diagnostics.isEmpty &&
      (r.symbols.any fun s => s.name == "f" && s.span.startLine == 1 && hasSub s.type_ "∀") &&
      (r.symbols.any fun s => s.name == "g" && s.span.startLine == 2 && hasSub s.type_ "∀")
  | none => false)

#guard (match hoverReport "let f : {a} a = 1\nf\n" with
  | some r => !r.diagnostics.isEmpty &&
      (r.diagnostics.all fun d => d.endLine > d.line || d.endCol > d.col)
  | none => false)

-- Complete annotations permit polymorphic calls within their SCC.
#guard (match hoverReport "let f : {a} a -> Int = \\x -> g True + g 1\nlet g : {a} a -> Int = \\x -> f x\nf\n" with
  | some r => r.diagnostics.isEmpty
  | none => false)

-- Non-BMP characters consume two UTF-16 columns before later tokens.
#guard (match hoverReport "let value = 1\n('😀', value)\n" with
  | some r => r.diagnostics.isEmpty &&
      (match symbolAt r.symbols 2 8 with
       | some value => value.name == "value" && value.type_ == "Int" && value.span.startCol == 8
       | none => false)
  | none => false)

-- Keep the existing scoped-head-sugar limitation visible.
#guard (hoverReport "let id {a} (x : a) : a = x\nid\n").isNone

-- Named annotation binders survive presentation, both for a recursive
-- binding's synthesized variables and for genuine nested-let skolems.
def namedSignatureSrc : String :=
  "let keep : {element} element -> element = \\x -> x\nkeep\n"

#guard (match hoverReport namedSignatureSrc with
  | some r => r.diagnostics.isEmpty &&
      (r.symbols.any fun s => s.name == "keep" && s.type_ == "∀ element. element → element") &&
      (r.symbols.any fun s => s.name == "x" && s.kind == "param" && s.type_ == "element") &&
      (r.symbols.all fun s => !hasSub s.type_ "?")
  | none => false)

#guard (match hoverReport "let demo = let keep : {item} item -> item = \\x -> x in keep 1\ndemo\n" with
  | some r => r.diagnostics.isEmpty &&
      (r.symbols.any fun s => s.name == "x" && s.kind == "param" && s.type_ == "item")
  | none => false)

#guard (match hoverReport "let map : {input output} (input -> output) -> List input -> List output =\n  \\f xs -> match xs with | [] -> [] | h :: t -> f h :: map f t\nmap\n" with
  | some r => r.diagnostics.isEmpty &&
      (r.symbols.any fun s => s.name == "f" && s.kind == "param" && s.type_ == "input → output") &&
      (r.symbols.any fun s => s.name == "xs" && s.kind == "param" && s.type_ == "List input")
  | none => false)

-- An ordinary annotated `let` checks its RHS at the declared scheme, so both
-- lambda parameters reflect the authored `item` type. (The former distinction
-- was an artifact of routing every top-level singleton through `letRec`.)
#guard (match hoverReport "let f : {item} item -> item -> item = \\x y -> y\nf\n" with
  | some r => r.diagnostics.isEmpty &&
      (match r.symbols.find? (fun s => s.name == "x" && s.kind == "param"),
             r.symbols.find? (fun s => s.name == "y" && s.kind == "param") with
       | some x, some y => x.type_ == "item" && y.type_ == "item"
       | _, _ => false)
  | none => false)

-- Fresh inferred quantifier names must not capture a named outer type variable.
#guard FHM.Unverified.HMDisplay.scheme
  { aliases := [(0, "a")], freeIds := [0] } []
  ⟨1, .arrow (.bvar 0) (.fvar 0)⟩ == "∀ b. b → a"

-- Definition sites (binders, types, constructors, type variable binders) are
-- flagged `isDef`; occurrences are not. Go to definition relies on this.
def userDefSites (src : String) : List (String × Nat × Nat) :=
  ((hoverSyms src).getD []).filterMap fun s =>
    if s.isDef && s.span != Span.empty then some (s.name, s.span.startLine, s.span.startCol)
    else none

#guard userDefSites "type Box a = Box a\nlet f : {b} b -> b = \\x -> x\nf (Box 1)\n" =
  [("Box", 1, 6), ("a", 1, 10), ("Box", 1, 14), ("b", 2, 10), ("f", 2, 5), ("x", 2, 23)]

-- Editors get every token's span and class, comments included.
#guard (tokensJson "f /- c -/ (1)").compress =
  "[[1,1,1,2,\"ident\"],[1,3,1,10,\"comment\"],[1,11,1,12,\"punct\"],[1,12,1,13,\"lit\"],[1,13,1,14,\"punct\"]]"

-- Doc comments reach the definition's symbol and its occurrences: values via
-- their innermost binder, constructors by name.
def docSites (src : String) : List (String × Nat × Nat × String) :=
  ((hoverSyms src).getD []).filterMap fun s =>
    s.doc.map fun d => (s.name, s.span.startLine, s.span.startCol, d)

#guard docSites "type Box a =\n  --- Holds one value.\n  | Box a\n/-- Opens a box. -/\nlet unbox = \\b -> match b with | Box x -> x\nunbox (Box 1)\n" =
  [("Box", 3, 5, "Holds one value."), ("unbox", 5, 5, "Opens a box."),
   ("unbox", 6, 1, "Opens a box."), ("Box", 6, 8, "Holds one value."),
   ("Box", 5, 34, "Holds one value.")]

-- A type's hover lists its constructors one per line, under their docs.
def typeHover (src : String) (name : String) : Option String :=
  (((hoverSyms src).getD []).find? fun s => s.kind == "type" && s.name == name).map (·.type_)

#guard typeHover "type Maybe a =\n  /-- No value.\n      Really none. -/\n  | Nothing\n  | Just a\n1\n" "Maybe" =
  some "type Maybe a =\n  --- No value.\n  --- Really none.\n  | Nothing\n  | Just a"

-- A non-exhaustive match is reported where it is (here the inner one), and
-- hovers stay available since typing succeeded.
def diagSites (src : String) : Option (List (String × Nat × Nat)) :=
  (hoverReport src).map (·.diagnostics.map fun d => (d.message, d.line, d.col))

def innerNonExhaustive : String :=
  "type Maybe a = Just a | Nothing\nlet g = \\m ->\n  match m with\n  | Nothing -> 0\n  | Just xs ->\n    match xs with\n    | [] -> 0\ng (Just [1])\n"

#guard diagSites innerNonExhaustive = some [("match not exhaustive (missing: _ :: _)", 6, 5)]
#guard ((hoverReport innerNonExhaustive).map (·.symbols.isEmpty)) = some false

-- Structured witnesses use the inferred scrutinee type and remain available
-- alongside hovers even when the failure is in a nested recursive definition.
#guard ((hoverReport innerNonExhaustive).map fun r =>
  r.diagnostics.map fun d => (d.code?, d.missingPatterns, d.moreMissing)) =
  some [(some "match.notExhaustive", ["_ :: _"], false)]

-- Constructor declaration context belongs to definitions, pattern references
-- and value occurrences, while the occurrence type remains specialised.
#guard (match hoverSyms sameNameSrc with
  | none => false
  | some syms =>
    match symbolAt syms 1 14, symbolAt syms 3 51, symbolAt syms 5 8 with
    | some defn, some pat, some value =>
        defn.declaration == some "type Box a =\n  | Box a" &&
        pat.declaration == defn.declaration && value.declaration == defn.declaration &&
        value.type_ == "Int → Box Int"
    | _, _, _ => false)


-- Compound lambda parameters use the same capture provenance as match arms.
#guard (match hoverReport "let swap = \\((a, b) : (Int, Bool)) -> (b, a)\nswap (3, True)\n" with
  | some r => r.diagnostics.isEmpty &&
      (r.symbols.any fun s => s.name == "a" && s.kind == "pat" && s.type_ == "Int") &&
      (r.symbols.any fun s => s.name == "b" && s.kind == "pat" && s.type_ == "Bool")
  | none => false)

#guard (match hoverReport "type Maybe a = Just a | Nothing\nlet get = \\(Just x) -> x\nget (Just 3)\n" with
  | some r => (r.diagnostics.any fun d => d.code? == some "match.notExhaustive" &&
      d.missingPatterns == ["Nothing"]) && !r.symbols.isEmpty
  | none => false)


-- Pattern-let captures are ordinary generalised values, with authored token spans.
def patternLetSrc : String :=
  "let (identity, number) = (\\x -> x, 7)\nlet integer = identity number\nlet truth = identity True\n(integer, truth)\n"
#guard (match hoverReport patternLetSrc with
  | some r => r.diagnostics.isEmpty &&
      (match symbolAt r.symbols 1 6, symbolAt r.symbols 1 16,
          symbolAt r.symbols 2 15, symbolAt r.symbols 3 13 with
        | some f, some n, some intUse, some boolUse =>
            f.kind == "val" && hasSub f.type_ "∀" && n.type_ == "Int" &&
            intUse.type_ == "Int → Int" && boolUse.type_ == "Bool → Bool"
        | _, _, _, _ => false) &&
      !(r.symbols.any fun s => s.name.startsWith "$pattern/")
  | none => false)

#guard (match hoverReport "let (True, _) = (True, 3)\n0\n" with
  | some r => r.diagnostics.any fun d => d.code? == some "match.notExhaustive" &&
      d.missingPatterns == ["(False, _)"]
  | none => false)

-- Anonymous annotation holes use the production lowering/inference path.
private def holeTypes (src : String) : Option (List String) := do
  let r ← hoverReport src
  if !r.diagnostics.isEmpty then none else
    some ((r.symbols.filter fun s => s.kind == "typeHole").map (·.type_))

private def holeIdSrc := "let id = \\(x : _) -> x\n(id 1, id True)\n"
#guard holeTypes holeIdSrc == some ["a"]
#guard ((hoverReport holeIdSrc).map (·.programTy)) == some "(Int, Bool)"
#guard holeTypes "let f : _ -> _ = \\x -> 1\nf True\n" == some ["a", "Int"]
#guard holeTypes "(\\(x : _) (y : _) -> (x,y)) 1 True\n" == some ["Int", "Bool"]
#guard holeTypes "(\\(f : Int -> _) -> f 1) (\\x -> True)\n" == some ["Bool"]
#guard holeTypes "(\\(x : List _) -> x) [1,2]\n" == some ["Int"]
#guard holeTypes "(\\(x : (_, _)) -> x) (1, True)\n" == some ["Int", "Bool"]
#guard (match hoverReport "let f = \\(x : _) -> x x\nf\n" with
  | some r => r.diagnostics.any fun d => d.code? == some "type.infiniteType"
  | none => false)
#guard (match hoverReport "let f : Int -> _ = \\x -> x\nf True\n" with
  | some r => !r.diagnostics.isEmpty
  | none => false)

-- Pattern underscores remain wildcards, with no inferred-hole symbol.
#guard holeTypes "let f = \\_ -> 1\nf True\n" == some []

private def copiedHoleFallback :=
  "let f = \\p -> match p with | (True, True) -> 1 | _ -> let id = \\(x : _) -> x in id 2\n" ++
  "(f (True, False), f (False, True))\n"

-- This checks the real parser/compiler path independently of inference: one
-- authored annotation survives at three compiler-produced expression paths.
#guard (match parseProgramWithSpans copiedHoleFallback with
  | .error _ => false
  | .ok (p, bs, sp) =>
      let result := do
        let ctors ← elabDecls preludeDecls
        let tree ← FHM.Unverified.HMArtifacts.programSpanned p sp (programWideScope bs sp)
        SurfaceBridge.Provenance.lowerWithProvenance ctors p.term tree
      match result with
      | none => false
      | some lowered =>
          (sp.references.filter fun r => r.kind == .typeHole).length == 1 &&
          (lowered.mapExpr Elaboration.Input.erase).provenanceTotal &&
          lowered.sourceTargets.any fun (_, target) => match target with
            | .absent _ => false
            | .present paths => paths.length == 3 && paths.all fun path =>
                match SurfaceBridge.Provenance.inputAtCorePath lowered.expr path with
                | some (.lambda (some .hole) _) => true
                | _ => false)

-- Every copied signature contributes its own display scope. The source binder
-- remains one authored token; its three generated RHS paths all retain `item`.
#guard (match parseProgramWithSpans
    "let f = \\p -> match p with | (True, True) -> 1 | _ -> let id : {item} item -> item = \\x -> x in id 2\nf (False, True)\n" with
  | .error _ => false
  | .ok (p, bs, sp) =>
      let result := do
        let ctors ← elabDecls preludeDecls
        let tree ← FHM.Unverified.HMArtifacts.programSpanned p sp (programWideScope bs sp)
        let lowered ← SurfaceBridge.Provenance.lowerWithProvenance ctors p.term tree
        let typed ← SurfaceBridge.Provenance.inferWithProvenance ctors lowered
        let locations := FHM.Unverified.HMArtifacts.collect bs p.term
          (SurfaceBridge.Provenance.identify tree)
        pure (FHM.Unverified.HMDisplay.scopes typed locations)
      match result with
      | none => false
      | some scopes => (scopes.filter fun scope => scope.names == ["item"]).length == 3)

-- Completion retains authored forall order and vacuous slots; extra hole
-- variables get fresh names without taking over an authored `a` or `b`.
#guard FHM.Unverified.HMDisplay.annotationNames
  (.partialForall 2 (.arrow (.fixed (.bvar 1)) .hole)) ["b", "a"]
  ⟨3, .arrow (.bvar 1) (.bvar 2)⟩ == ["b", "a", "c"]
#guard FHM.Unverified.HMDisplay.annotationNames
  (.partialForall 1 .hole) ["unused"] ⟨2, .bvar 1⟩ == ["unused", "a"]
#guard FHM.Unverified.HMDisplay.extendNames ["element"] 2 == ["element", "a"]
#guard FHM.Unverified.HMDisplay.extendNames ["item"] 2 ["a"] == ["item", "b"]

-- Partial holes survive the actual match compiler and canonical match worker.
#guard holeTypes
  "let f = \\p -> match p with | (True, True) -> 1 | _ -> let id = \\(x : _) -> x in id 2\n(f (True, False), f (False, True))\n" == some ["a"]
#guard ((hoverReport "match (\\(x : _) -> x) True with | True -> 1 | False -> 2\n").map (·.programTy)) == some "Int"
#guard holeTypes "(\\((a,b) : (_, _)) -> (b,a)) (1, True)\n" == some ["Int", "Bool"]

-- Metadata retains only the explicit binder; completed annotation syntax also
-- counts the synthetic hole binder before reaching the next outer scope.
private def twoDepthScopes : List FHM.Unverified.HMDisplay.Scope := [
  ⟨[.letRhs], ["outer"], [], [], ["outer", "a"]⟩,
  ⟨[.letRhs, .letRhs], ["middle"], [], [], ["middle", "b"]⟩ ]
#guard FHM.Unverified.HMDisplay.pretty
  (FHM.Unverified.HMDisplay.context twoDepthScopes [.letRhs, .letRhs] (.bvar 1))
  (.bvar 1) == "outer"
#guard FHM.Unverified.HMDisplay.pretty
  (FHM.Unverified.HMDisplay.context twoDepthScopes [.letRhs, .letRhs] (.bvar 2) true)
  (.bvar 2) == "outer"

-- Pattern-let desugaring keeps the annotation token order and nested lambda
-- owner, while a non-BMP character before a hole preserves UTF-16 columns.
#guard holeTypes "let (x,y) : (_,_) = (1,True)\n(x,y)\n" == some ["Int", "Bool"]
#guard holeTypes "let (id,n) : (_,_) = (\\(x : _) -> x,1)\n(id True,n)\n" == some ["a → a", "Int", "a"]
#guard holeTypes "('😀', (\\(x : _) -> x) True)\n" == some ["Bool"]

-- Signed completions use the canonical worker, including binder-definition
-- hovers, vacuous explicit slots, and copied RHS annotation scopes.
private def signedKeep :=
  "let keep : {element} element -> _ -> element = \\(x : element) (y : _) -> x\n" ++
  "(keep 1 True, keep False 2)\n"
#guard holeTypes signedKeep == some ["a", "a"]
#guard (match hoverReport signedKeep with
  | some r => r.programTy == "(Int, Bool)" &&
      (match symbolAt r.symbols 1 5 with
        | some s => s.type_ == "∀ element a. element → a → element"
        | none => false)
  | none => false)

private def signedUnused := "let id : {unused} _ -> _ = \\x -> x\n(id 1, id True)\n"
#guard holeTypes signedUnused == some ["a", "a"]
#guard (match hoverReport signedUnused with
  | some r => (symbolAt r.symbols 1 5).map (·.type_) == some "∀ unused a. a → a"
  | none => false)
#guard holeTypes
  "let id : {element} element -> element = \\(x : _) -> x\n(id 1, id True)\n" == some ["element"]
#guard holeTypes
  "let f = \\p -> match p with | (True, True) -> 1 | _ -> let id : {item} item -> item = \\(x : _) -> x in id 2\n(f (True, False), f (False, True))\n" == some ["item"]

private def signedNested :=
  "let outer : {element} element -> _ = \\(x : element) -> " ++
  "let inner : {item} item -> _ = \\(y : item) -> (x, y) in inner True\nouter 1\n"
#guard holeTypes signedNested == some ["(element, Bool)", "(element, item)"]
#guard (match hoverReport signedNested with
  | some r => r.symbols.any fun s => s.name == "inner" &&
      s.kind == "val" && s.type_ == "∀ item. item → (element, item)"
  | none => false)

-- A completed outer scheme includes synthetic binders that are absent from
-- metadata's authored-name scopes. Both depths must reach the same `outer`.
#guard holeTypes
  ("let outer : {outer} outer -> _ = \\(x : outer) -> " ++
   "let middle : {middle} middle -> _ -> _ = \\(y : middle) z -> " ++
   "let inner : {inner} inner -> _ = \\(w : inner) -> x in (inner y, z) " ++
   "in middle True\nouter 1 False\n") == some ["a → (outer, a)", "b", "(outer, b)", "outer"]

-- Recursive worker targets below deliberately check lowering only until its
-- proof-backed implementation lands. Runtime expectations live in the smoke
-- suite as independent positive/negative groups; rejection alone proves little.
private def lowersWith (src : String) (check : Elaboration.Input → Bool) : Bool :=
  match parseProgramWithSpans src with
  | .error _ => false
  | .ok (p, bs, sp) =>
      let result := do
        let ctors ← elabDecls preludeDecls
        let tree ← FHM.Unverified.HMArtifacts.programSpanned p sp (programWideScope bs sp)
        SurfaceBridge.Provenance.lowerWithProvenance ctors p.term tree
      match result with
      | none => false
      | some lowered => (lowered.mapExpr Elaboration.Input.erase).provenanceTotal && check lowered.expr

private def nestedRecCapture :=
  "let f : {a} _ = \\x -> let g : {b} b -> _ = \\(y : a) -> " ++
  "if True then y else g y in if True then x else f x\nf 1\n"
private def nestedRecIndependent :=
  "let f : {a} _ = \\x -> let g : {b} b -> _ = \\(y : b) -> " ++
  "if True then y else g y in if True then x else f x\nf 1\n"

-- Both groups really are recursive. At the inner RHS, outer `a` has index1
-- and the independently declared `b` has index0. Outer `a` is absent from f's
-- template, so only the provisional-forall frame can prevent its capture.
#guard lowersWith nestedRecCapture fun
  | .letRec [.partialForall 1 .hole]
      [.lambda none (.letRec [.partialForall 1 _] [.lambda (some (.fixed (.bvar 1))) _] _)] _ => true
  | _ => false
#guard lowersWith nestedRecIndependent fun
  | .letRec [.partialForall 1 .hole]
      [.lambda none (.letRec [.partialForall 1 _] [.lambda (some (.fixed (.bvar 0))) _] _)] _ => true
  | _ => false

private def recCompleteLambda :=
  "let f : {a} a -> _ = \\(x : a) -> if True then x else f x\n(f 1, f True)\n"
private def recCompleteLambdaSpecialized :=
  "let f : {a} a -> _ = \\(x : Int) -> if True then x else f x\n(f 1, f True)\n"
private def recCompleteNested :=
  "let f : {a} a -> _ = \\x -> let id : a -> a = \\y -> y " ++
  "in if True then id x else f x\n(f 1, f True)\n"
private def recCompleteNestedSpecialized :=
  "let f : {a} a -> _ = \\x -> let id : Int -> Int = \\y -> y " ++
  "in if True then id x else f x\n(f 1, f True)\n"

-- A complete subtree can still mention an outer provisional variable. Its
-- successful toCore conversion must not force an ineligible backend dispatch.
#guard lowersWith recCompleteLambda fun
  | .letRec [.partialForall 1 _] [rhs@(.lambda (some (.fixed (.bvar 0))) _)] _ =>
      rhs.toCore.isSome && (rhs.openTyVars [1000]).rigidVars.contains 1000
  | _ => false
#guard lowersWith recCompleteNested fun
  | .letRec [.partialForall 1 _] [rhs@(.lambda none (.letIn (.complete scheme) _ _))] _ =>
      scheme.paramCount == 0 && rhs.toCore.isSome && (rhs.openTyVars [1000]).rigidVars.contains 1000
  | _ => false
#guard lowersWith recCompleteLambdaSpecialized (fun _ => true)
#guard lowersWith recCompleteNestedSpecialized (fun _ => true)

-- An ordinary nested let must protect provisional F during generalization,
-- independently of the signed-pop escape checks above.
private def ordinaryRecCapture :=
  "let f : {a} _ = \\x -> let id = \\(y : a) -> y " ++
  "in if True then (id 1, id True) else f x\nf 0\n"
private def ordinaryRecProtected :=
  "let f : {a} a -> _ = \\x -> let id = \\(y : a) -> y " ++
  "in if True then id x else f x\n(f 1, f True)\n"
#guard lowersWith ordinaryRecCapture fun
  | .letRec [.partialForall 1 .hole]
      [.lambda none (.letIn .absent (.lambda (some (.fixed (.bvar 0))) _) _)] _ => true
  | _ => false
#guard lowersWith ordinaryRecProtected fun
  | .letRec [.partialForall 1 _]
      [.lambda none (.letIn .absent (.lambda (some (.fixed (.bvar 0))) _) _)] _ => true
  | _ => false
