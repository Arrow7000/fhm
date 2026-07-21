import FHM.EditorSupport
import FHM.Surface.Parse
import FHM.Surface.Span

/-!
# Editor hover canaries (span-based symbols)

`lake build FHMEditorTests` evaluates these `#guard`s.
-/

open Surface.Parse
open Surface.Span

/-- Substring check (`String.contains` is Char-only). -/
def hasSub (s needle : String) : Bool :=
  (s.splitOn needle).length > 1

/-- Helper: parse + collect hover symbols. -/
def hoverSyms (src : String) : Option (List RangedSymbol) :=
  match parseProgramWithBinders src with
  | .error _ => none
  | .ok (p, bs) => (collectHover p bs).map (·.1)

-- Span.contains / symbolAt edge cases
#guard (Span.contains ⟨1, 5, 1, 7⟩ 1 5) = true
#guard (Span.contains ⟨1, 5, 1, 7⟩ 1 7) = false

def toySyms : List RangedSymbol := [
  { name := "xs", kind := "param", type_ := "a",
    span := ⟨1, 10, 1, 12⟩ },
  { name := "xs", kind := "val", type_ := "Int",
    span := ⟨2, 5, 2, 7⟩ }
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

-- 3. Type / ctor spans
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
    -- `h :: t` arm: find pats named h and t with non-empty types
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
