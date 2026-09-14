import FHM.Core

/-! # Logical paths through Core expressions

Paths describe the ordinary Core skeleton. Inference metadata (`Expr.found`) is
transparent: adding or removing found wrappers never changes a path.
-/

/-- One edge from a Core expression to an immediate logical child. -/
inductive CoreStep where
  /-- Body of a `lambda`. -/
  | lambdaBody
  /-- Function of an `app`. -/
  | appFun
  /-- Argument of an `app`. -/
  | appArg
  /-- Bound RHS of a `letIn`. -/
  | letRhs
  /-- Body of a `letIn`. -/
  | letBody
  /-- Scrutinee of a `match_`. -/
  | matchScrut
  /-- Body of the `index`-th match branch. -/
  | matchBranch (index : Nat)
  /-- RHS of the `member`-th `letRec` binding. -/
  | letRecRhs (member : Nat)
  /-- Body of a `letRec`. -/
  | letRecBody
  deriving Repr, DecidableEq, BEq

/-- A root-relative path in the `.found`-transparent Core skeleton. -/
abbrev CorePath := List CoreStep

namespace CorePath

/-- Put every path below the same immediate Core edge. -/
def below (step : CoreStep) (paths : List CorePath) : List CorePath :=
  paths.map (step :: ·)

end CorePath

/-- Look up a logical Core node. A nonempty path passes transparently through
    any `.found` wrapper; an empty path returns the node including its wrapper,
    when present, so callers can inspect the discovered type. -/
def Expr.atCorePath : Expr → CorePath → Option Expr
  | e, [] => some e
  | .found _ inner, path => inner.atCorePath path
  | .lambda _ body, .lambdaBody :: rest => body.atCorePath rest
  | .app f _, .appFun :: rest => f.atCorePath rest
  | .app _ input, .appArg :: rest => input.atCorePath rest
  | .letIn _ rhs _, .letRhs :: rest => rhs.atCorePath rest
  | .letIn _ _ body, .letBody :: rest => body.atCorePath rest
  | .match_ scrut _, .matchScrut :: rest => scrut.atCorePath rest
  | .match_ _ branches, .matchBranch index :: rest =>
      match _h : branches[index]? with
      | some (_, body) => body.atCorePath rest
      | none => none
  | .letRec _ bindings _, .letRecRhs member :: rest =>
      match _h : bindings[member]? with
      | some rhs => rhs.atCorePath rest
      | none => none
  | .letRec _ _ body, .letRecBody :: rest => body.atCorePath rest
  | _, _ => none
termination_by e path => sizeOf e + sizeOf path
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have hsz := List.sizeOf_lt_of_mem (List.mem_of_getElem? _h); omega)
    | (have hsz := List.sizeOf_lt_of_mem (List.mem_of_getElem? _h)
       simp only [Prod.mk.sizeOf_spec] at hsz
       omega)

/-- Source-relative descent composes with an already located logical node.
    Empty paths retain `.found` payloads; nonempty descent remains transparent.
    This lets runtime member proofs identify an actual original group RHS. -/
theorem Expr.atCorePath_append (e : Expr) : ∀ basePath suffix,
    e.atCorePath (basePath ++ suffix) = (e.atCorePath basePath).bind (fun node => node.atCorePath suffix) := by
  induction e using Expr.rec_strong with
  | primLit | primBinOp | var | ctor =>
      intro basePath suffix
      cases basePath with
      | nil => simp only [List.nil_append, Expr.atCorePath, Option.bind_some]
      | cons step rest => cases step <;> simp [Expr.atCorePath]
  | lambda ann body ih =>
      intro basePath suffix
      cases basePath with
      | nil => simp only [List.nil_append, Expr.atCorePath, Option.bind_some]
      | cons step rest => cases step <;> simp [Expr.atCorePath, ih]
  | app fn arg ihf iha =>
      intro basePath suffix
      cases basePath with
      | nil => simp only [List.nil_append, Expr.atCorePath, Option.bind_some]
      | cons step rest => cases step <;> simp [Expr.atCorePath, ihf, iha]
  | letIn ann rhs body ihr ihb =>
      intro basePath suffix
      cases basePath with
      | nil => simp only [List.nil_append, Expr.atCorePath, Option.bind_some]
      | cons step rest => cases step <;> simp [Expr.atCorePath, ihr, ihb]
  | found ty inner ih =>
      intro basePath suffix
      cases basePath with
      | nil => simp only [List.nil_append, Expr.atCorePath, Option.bind_some]
      | cons step rest => simpa only [List.cons_append, Expr.atCorePath] using ih (step :: rest) suffix
  | match_ scrut branches ihs ihb =>
      intro basePath suffix
      cases basePath with
      | nil => simp only [List.nil_append, Expr.atCorePath, Option.bind_some]
      | cons step rest =>
          cases step <;> try simp [Expr.atCorePath, ihs]
          rename_i index
          cases atIndex : branches[index]? with
          | none => simp [Expr.atCorePath, atIndex]
          | some br =>
              simpa [Expr.atCorePath, atIndex] using
                ihb br.1 br.2 (List.mem_of_getElem? atIndex) rest suffix
  | letRec ann rhss body ihr ihb =>
      intro basePath suffix
      cases basePath with
      | nil => simp only [List.nil_append, Expr.atCorePath, Option.bind_some]
      | cons step rest =>
          cases step <;> try simp [Expr.atCorePath, ihb]
          rename_i index
          cases atIndex : rhss[index]? with
          | none => simp [Expr.atCorePath, atIndex]
          | some rhs =>
              simpa [Expr.atCorePath, atIndex] using
                ihr rhs (List.mem_of_getElem? atIndex) rest suffix

#print axioms Expr.atCorePath_append

/-- A binder-producing position in Core. Several source binders can point into
    one node (a recursive group), and pattern compilation can duplicate a
    capture site. -/
inductive CoreBinderSite where
  | lambda (path : CorePath)
  | letIn (path : CorePath)
  | letRec (path : CorePath) (member : Nat)
  | patCapture (paths : List CorePath) (capture : Nat)
  deriving Repr, DecidableEq, BEq

namespace CoreBinderSite

def paths : CoreBinderSite → List CorePath
  | .lambda path | .letIn path | .letRec path _ => [path]
  | .patCapture paths _ => paths

/-- Rebase a binder site below one logical Core edge. Pattern captures may have
    several equivalent Core targets, so every target path is rebased. -/
def below (step : CoreStep) : CoreBinderSite → CoreBinderSite
  | .lambda path => .lambda (step :: path)
  | .letIn path => .letIn (step :: path)
  | .letRec path member => .letRec (step :: path) member
  | .patCapture paths capture => .patCapture (CorePath.below step paths) capture

end CoreBinderSite

/-- Schemes inferred for binder-producing Core positions. Association-list form
    preserves construction order and does not pretend paths survive rewrites. -/
abbrev BinderSchemeMap := List (CoreBinderSite × PolyTy)

namespace BinderSchemeMap

/-- Rebase every binder key below one logical Core edge. -/
def below (step : CoreStep) (schemes : BinderSchemeMap) : BinderSchemeMap :=
  schemes.map fun (site, scheme) => (site.below step, scheme)

/-- Apply a type transformation to scheme bodies without changing binder keys
    or quantifier counts. -/
def mapTys (f : Ty → Ty) (schemes : BinderSchemeMap) : BinderSchemeMap :=
  schemes.map fun (site, scheme) => (site, { scheme with body := f scheme.body })

end BinderSchemeMap

private def foundPathDemo : Expr :=
  .found (.prim .int)
    (.app
      (.found (.arrow (.prim .int) (.prim .int)) (.var 0))
      (.found (.prim .int) (.primLit (.int 1))))

#guard match foundPathDemo.atCorePath [] with
  | some (.found (.prim .int) (.app _ _)) => true
  | _ => false

#guard match foundPathDemo.atCorePath [.appFun] with
  | some (.found (.arrow (.prim .int) (.prim .int)) (.var 0)) => true
  | _ => false

#guard match foundPathDemo.atCorePath [.appArg] with
  | some (.found (.prim .int) (.primLit (.int 1))) => true
  | _ => false
