import FHM.Surface.Parse
import FHM.SurfaceBridge
import FHM.InferW
import FHM.Pretty
import FHM.Decls
import Lean.Data.Json

/-!
# Editor support helpers

Shared collection of hover symbols (bindings + type/ctor decls) for
`fhm_diagnose`. Duplicates the small `collectTopSchemes` / `zipBindingTypes`
helpers from `Live` rather than importing the live exe module.

Name clashes: later entries overwrite earlier (v1 — nested/`let` shadows win).
-/

open Surface.Parse
open SurfaceBridge

/-- Collect schemes from the outer `letIn (some σ)` spine produced by
    `letRecElab` (stops at the first non-annotated-let). -/
partial def collectTopSchemes : Expr → List PolyTy
  | .letIn (some σ) _ body => σ :: collectTopSchemes body
  | _ => []

/-- Drop `n` outer annotated `letIn`s (inverse of taking the first `n` from
    `collectTopSchemes`). -/
def dropAnnotatedLets : Nat → Expr → Expr
  | 0, e => e
  | n + 1, .letIn (some _) _ body => dropAnnotatedLets n body
  | _, e => e

/-- `letRecElab` wraps group members outermost-last, so each group's chunk of
    schemes from `collectTopSchemes` is reversed relative to binding order.
    Undo that per SCC group and zip with surface names. -/
def zipBindingTypes (groups : List (List Surface.Binding)) (schemes : List PolyTy) :
    List (ValName × PolyTy) :=
  let rec go (gs : List (List Surface.Binding)) (ss : List PolyTy)
      (acc : List (ValName × PolyTy)) : List (ValName × PolyTy) :=
    match gs with
    | [] => acc
    | g :: gs' =>
      let n := g.length
      let chunk := (ss.take n).reverse
      let pairs := g.map (·.name) |>.zip chunk
      go gs' (ss.drop n) (acc ++ pairs)
  go groups schemes []

/-- Zip a surface list spine against Core `Cons`/`Nil` after infer. -/
partial def zipExprListBindingTypes (zip : Surface.Expr → Expr → List (ValName × PolyTy)) :
    List Surface.Expr → Expr → List (ValName × PolyTy)
  | [], _ => []
  | x :: xs, .app (.app (.ctor ⟨"Cons"⟩) eh) et =>
      zip x eh ++ zipExprListBindingTypes zip xs et
  | _, _ => []

/-- Zip a surface expression against its Core elaboration-after-infer, collecting
    nested `let` / `let rec` binding schemes. Stops at `match_` / `ife` so we do
    not walk into compiler-generated match lets. For `letRecIn`, only the body is
    walked further (RHS Core shape is `letRecElab` wrappers, not the surface RHS). -/
partial def zipExprBindingTypes : Surface.Expr → Expr → List (ValName × PolyTy)
  | .letIn name _ sRhs sBody, .letIn (some σ) eRhs eBody =>
      (name, σ) :: zipExprBindingTypes sRhs eRhs ++ zipExprBindingTypes sBody eBody
  | .letRecIn binds sBody, e =>
      let n := binds.length
      let schemes := (collectTopSchemes e).take n
      let chunk := schemes.reverse
      let pairs := binds.map (·.1) |>.zip chunk
      let eBody := dropAnnotatedLets n e
      pairs ++ zipExprBindingTypes sBody eBody
  | .lambda _ _ sBody, .lambda _ eBody =>
      zipExprBindingTypes sBody eBody
  | .app sf sx, .app ef ex =>
      zipExprBindingTypes sf ef ++ zipExprBindingTypes sx ex
  | .pair sa sb, .app (.app (.ctor ⟨"Pair"⟩) ea) eb =>
      zipExprBindingTypes sa ea ++ zipExprBindingTypes sb eb
  | .cons sh st, .app (.app (.ctor ⟨"Cons"⟩) eh) et =>
      zipExprBindingTypes sh eh ++ zipExprBindingTypes st et
  | .list items, e =>
      zipExprListBindingTypes zipExprBindingTypes items e
  | .match_ _ _, _ => []
  | .ife _ _ _, _ => []
  | _, _ => []

def prettyTyName : TyName → String
  | .mk s => s

def prettyCtorName : CtorName → String
  | .mk s => s

/-- Surface `type T a = C … | D …` rendering for hover. -/
def prettySurfaceDataDecl (d : Surface.DataDecl) : String :=
  let params := String.intercalate " " (d.params.map prettyValName)
  let header :=
    if d.params.isEmpty then s!"type {prettyTyName d.name}"
    else s!"type {prettyTyName d.name} {params}"
  let ctorStr (c : CtorName × List Surface.Ty) : String :=
    let ⟨cname, fields⟩ := c
    if fields.isEmpty then prettyCtorName cname
    else prettyCtorName cname ++ " " ++
      String.intercalate " " (fields.map (Surface.Ty.prettyAux 2))
  header ++ " = " ++ String.intercalate " | " (d.ctors.map ctorStr)

/-- Core prelude `DataDecl` as `type T a = …` (params named `a, b, …`). -/
def prettyCoreDataDecl (d : DataDecl) : String :=
  let params := String.intercalate " " ((List.range d.paramCount).map prettyTyVarName)
  let header :=
    if d.paramCount = 0 then s!"type {prettyTyName d.name}"
    else s!"type {prettyTyName d.name} {params}"
  let ctorStr (c : CtorName × List Ty) : String :=
    let ⟨cname, fields⟩ := c
    if fields.isEmpty then prettyCtorName cname
    else prettyCtorName cname ++ " " ++
      String.intercalate " " (fields.map (Ty.prettyAux 2))
  header ++ " = " ++ String.intercalate " | " (d.ctors.map ctorStr)

/-- Insert/overwrite an assoc entry (later write wins). -/
def assocUpsert (k : String) (v : Lean.Json) (xs : List (String × Lean.Json)) :
    List (String × Lean.Json) :=
  (k, v) :: xs.filter (fun ⟨k', _⟩ => k' ≠ k)

def symbolJson (type_ kind : String) : Lean.Json :=
  Lean.Json.mkObj [("type", Lean.Json.str type_), ("kind", Lean.Json.str kind)]

/-- Decl + ctor hover entries from prelude Core decls and surface user decls.
    Ctor types come from the elaborated `CtorEnv` (`Ctor.toTy.pretty`). -/
def declSymbols (user : List Surface.DataDecl) (ctors : CtorEnv) :
    List (String × Lean.Json) :=
  let preludeTypes : List (String × Lean.Json) :=
    preludeDecls.map fun d =>
      (prettyTyName d.name, symbolJson (prettyCoreDataDecl d) "type")
  let userTypes : List (String × Lean.Json) :=
    user.map fun d =>
      (prettyTyName d.name, symbolJson (prettySurfaceDataDecl d) "type")
  let ctorEntries : List (String × Lean.Json) :=
    ctors.map fun ⟨cname, ctor⟩ =>
      (prettyCtorName cname, symbolJson ctor.toTy.pretty "ctor")
  (preludeTypes ++ userTypes ++ ctorEntries).foldl
    (fun acc ⟨k, v⟩ => assocUpsert k v acc) []

/-- Binding hover entries (top-level groups + nested lets on the program body). -/
def bindingSymbols (p : Surface.Program) (eOut : Expr) : List (String × Lean.Json) :=
  let topCount := (p.groups.map (·.length)).sum
  let topBinds := zipBindingTypes p.groups (collectTopSchemes eOut)
  let bodyCore := dropAnnotatedLets topCount eOut
  let nested := zipExprBindingTypes p.body bodyCore
  (topBinds ++ nested).foldl
    (fun acc ⟨n, σ⟩ => assocUpsert (prettyValName n) (symbolJson σ.pretty "val") acc) []

/-- Full hover report for a parsed program. `none` if lower or infer fails.
    On success: symbols (decls + bindings) and `programTy`. -/
def collectHover (p : Surface.Program) : Option (List (String × Lean.Json) × String) := do
  let userCore ← lowerDataDeclsIn preludeKindEnv p.decls
  let ctors ← elabDecls (preludeDecls ++ userCore)
  let c ← lower ctors p.term
  let (_, _, eOut, τ) ← infer c.freshFloor ⟨[], ctors⟩ c
  let decls := declSymbols p.decls ctors
  let binds := bindingSymbols p eOut
  -- Later entries overwrite earlier (bindings shadow decl names on clash).
  let syms := (decls ++ binds).foldl
    (fun acc ⟨k, v⟩ => assocUpsert k v acc) []
  pure (syms, (genScheme [] [] τ).pretty)

/-- Parse-error diagnostic JSON object. -/
def parseDiagJson (e : ParseError) : Lean.Json :=
  Lean.Json.mkObj [
    ("severity", Lean.Json.str "error"),
    ("message", Lean.Json.str e.msg),
    ("line", Lean.Json.num e.line),
    ("col", Lean.Json.num e.col)
  ]

/-- Diagnose payload: versioned object with diagnostics, symbols, optional programTy. -/
def diagnosePayload (src : String) : Lean.Json :=
  match parseProgram src with
  | .error e =>
    Lean.Json.mkObj [
      ("version", Lean.Json.num 1),
      ("diagnostics", Lean.Json.arr #[parseDiagJson e]),
      ("symbols", Lean.Json.mkObj [])
    ]
  | .ok p =>
    match collectHover p with
    | none =>
      Lean.Json.mkObj [
        ("version", Lean.Json.num 1),
        ("diagnostics", Lean.Json.arr #[Lean.Json.mkObj [
          ("severity", Lean.Json.str "error"),
          ("message", Lean.Json.str "lowering or typechecking failed"),
          ("line", Lean.Json.num 1),
          ("col", Lean.Json.num 1)
        ]]),
        ("symbols", Lean.Json.mkObj [])
      ]
    | some (syms, programTy) =>
      Lean.Json.mkObj [
        ("version", Lean.Json.num 1),
        ("diagnostics", Lean.Json.arr #[]),
        ("symbols", Lean.Json.mkObj syms),
        ("programTy", Lean.Json.str programTy)
      ]
