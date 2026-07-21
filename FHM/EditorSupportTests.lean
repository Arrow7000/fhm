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
  | .ok (p, bs, sp) => (collectHover src p bs sp).map (·.1)

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
