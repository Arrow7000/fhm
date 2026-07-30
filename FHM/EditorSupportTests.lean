import FHM.EditorSupport
import FHM.Surface.Parse
import FHM.Surface.Span

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
  | .ok (p, bs, sp) => (collectHover src p bs sp).map (·.symbols)

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

-- 2. Lambda params under annotated map-like let (body must inhabit the scheme)
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
        (hasSub f.type_ "→" || hasSub f.type_ "->") &&
        hasSub xs.type_ "List"
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
    | some s => s.name == "xs" && s.kind == "param" && hasSub s.type_ "List"
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

-- E3b. `{n : Nat, a}` — `n` is count, not the next type forall
def natSchemeHover : String :=
  "let id : {n : Nat, a} BL n n a -> BL n n a =\n" ++
  "  \\xs -> xs\nid\n"

#guard (match hoverSyms natSchemeHover with
  | none => false
  | some syms =>
    match symbolAtUseSite syms 1 11 "n",
          symbolAtUseSite syms 1 20 "a" with
    | some n, some a =>
        n.name == "n" && n.kind == "count" && hasSub n.type_ "count" &&
        a.name == "a" && a.kind == "param" && hasSub a.type_ "type variable"
    | _, _ => false)

-- E3b2. Val hover type is ProgramReport pretty (BL scheme), not HM List.
#guard (match hoverSyms natSchemeHover with
  | none => false
  | some syms =>
    match syms.find? (fun s => s.name == "id" && s.kind == "val") with
    | some id =>
        hasSub id.type_ "BL" && hasSub id.type_ "Nat" && !hasSub id.type_ "List"
    | none => false)

-- E3c. Multiple tops with `{n : Nat, …}`: erase must not zero `natBinders` for
-- the hover walk (regression: unconsumed `.count` at head blocks later `.val`).
def natMultiTop : String :=
  "let id : {n : Nat, a} BL n n a -> BL n n a =\n" ++
  "  \\xs -> xs\n" ++
  "let id2 : {m : Nat, b} BL m m b -> BL m m b =\n" ++
  "  \\ys -> ys\n" ++
  "id\n"

#guard (match hoverSyms natMultiTop with
  | none => false
  | some syms =>
    let id2Vals := syms.filter fun s => s.name == "id2" && s.kind == "val"
    match symbolAt syms 3 5, symbolAt syms 3 12, id2Vals.length with
    | some id2, some m, 1 =>
        id2.kind == "val" && m.kind == "count" && hasSub m.type_ "count" &&
        -- proper def (not leftover): val scope extends past the name line
        id2.scope.endLine > id2.span.startLine
    | _, _, _ => false)

-- E3d. `{n : Nat, …}` after header tyParams / value-params (parse order).
def natAfterHeaderParams : String :=
  "let f {a} (x : a) : {n : Nat, b} BL n n b -> BL n n b =\n" ++
  "  \\y -> y\n" ++
  "f\n"

#guard (match hoverSyms natAfterHeaderParams with
  | none => false
  | some syms =>
    let a? := syms.find? (fun s => s.name == "a" && s.kind == "param" && s.span.startLine == 1)
    let x? := syms.find? (fun s => s.name == "x" && s.kind == "param" && s.span.startLine == 1)
    let n? := syms.find? (fun s => s.name == "n" && s.kind == "count")
    match a?, x?, n? with
    | some a, some x, some n =>
        hasSub a.type_ "type variable" &&
        !x.type_.isEmpty &&
        hasSub n.type_ "count" &&
        -- count binders must follow header tyParams / value-params in the walk
        a.span.startCol < x.span.startCol && x.span.startCol < n.span.startCol
    | _, _, _ => false)

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
        f1.name == "f" && !f1.type_.isEmpty && hasSub f1.type_ "→" &&
        xs.name == "xs" && hasSub xs.type_ "List" &&
        f2.name == "f" && !f2.type_.isEmpty &&
        ys.name == "ys" && hasSub ys.type_ "List" &&
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
  "let treeMap {a b} (f : a -> b) : Tree a -> Tree b =\n" ++
  "  \\t -> match t with | Leaf -> Leaf | Node x l r -> Node (f x) (treeMap f l) (treeMap f r)\n" ++
  "let addInts (a : Int) : Int -> Int = \\b -> a + b\n" ++
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

/-! ## Bounds diagnostics (must not be swallowed — diagnose ≡ Live `--bl`) -/

/-- Helper: parse + full hover report (symbols + bounds diags). -/
def hoverReport (src : String) : Option HoverReport :=
  match parseProgramWithSpans src with
  | .error _ => none
  | .ok (p, bs, sp) => collectHover src p bs sp

-- E6. Ascription fail: diagnostic present, pointed at binder `xs`, symbols kept.
def holeFailSrc : String :=
  "let xs : BL _ 0 Int = [1, 2]\nxs\n"

#guard (match hoverReport holeFailSrc with
  | none => false
  | some r =>
      match r.diagnostics with
      | [d] =>
          hasSub d.message "ascription" &&
          d.line == 1 &&
          d.col == 5 &&  -- `xs` def site
          (r.symbols.any fun s => s.name == "xs" && s.kind == "val")
      | _ => false)

-- E6b. Happy-path BL: no diagnostics.
def holeOkSrc : String :=
  "let xs : BL _ 5 Int = [1, 2]\nxs\n"

#guard (match hoverReport holeOkSrc with
  | none => false
  | some r => r.diagnostics.isEmpty &&
      (r.symbols.any fun s => s.name == "xs" && s.kind == "val"))

-- E6c. BoundCovers / Nil-only fail surfaces as a diagnostic (not silent).
def nilOnlyFailSrc : String :=
  "let xs : BL 2 2 Int = [1, 2]\n" ++
  "match xs with\n" ++
  "| [] -> 0\n"

#guard (match hoverReport nilOnlyFailSrc with
  | none => false
  | some r =>
      match r.diagnostics with
      | [d] =>
          hasSub d.message "Nil-only" ||
          hasSub d.message "cover" ||
          hasSub d.message "empty"
      | _ => false)

-- E6d. Solid demand fail.
def synthFailSrc : String :=
  "let xs : BL 0 0 Int = [1, 2]\nxs\n"

#guard (match hoverReport synthFailSrc with
  | none => false
  | some r =>
      match r.diagnostics with
      | [d] =>
          hasSub d.message "bounds" &&
          hasSub d.message "ascription" &&
          d.line == 1 &&
          d.col == 5
      | _ => false)
