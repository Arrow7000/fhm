import FHM.Core
import FHM.SurfaceLang
import FHM.Pretty
import FHM.PipelineShared
import FHM.Bounds.Ann
import FHM.Bounds.Erase

/-!
# Program type report (display layer)

Assembled once after erase + infer. Live, JSON, and hover pretty-print only this
report — no parallel HM/`bounds:` dumps and no print-time zips.

Ascription (`BinderAnn`) wins when present; otherwise HM `PolyTy`. Check still
uses `ProgramBoundsAnns.ofLower` (de Bruijn projection of the same erase package).
-/

namespace FHM.Bounds.Report

open FHM.Bounds
open FHM.Bounds.Erase

/-- One top-level binder’s display type — HM scheme plus optional erase ascription
and optional synthesized bounds pretty (from Check, when unascribed). -/
structure BindingReport where
  name : ValName
  hm : PolyTy
  bounds? : Option BinderAnn := none
  /-- Origin-synth pretty from Check when `bounds?` is none. -/
  synthPretty? : Option String := none

/-- Prefer solid ascription; if ascription still has `_` holes, prefer Check synth
when present (pin/pack story); else ascription text; else HM. -/
def BindingReport.pretty (b : BindingReport) : String :=
  match b.bounds?, b.synthPretty? with
  | some a, some s =>
      if a.hasHoles then s else BinderAnn.pretty a
  | some a, none => BinderAnn.pretty a
  | none, some s => s
  | none, none => b.hm.pretty

/-- Whole-program report: presentation-order binders + program body type. -/
structure ProgramReport where
  bindings : List BindingReport := []
  programHm : PolyTy
  bodyBounds? : Option BoundsAnnTy := none
  /-- Origin-synth pretty for the program body when `bodyBounds?` is none. -/
  programSynthPretty? : Option String := none

def ProgramReport.programPretty (r : ProgramReport) : String :=
  match r.bodyBounds?, r.programSynthPretty? with
  | some a, some s =>
      if a.hasHoles then s else BoundsAnnTy.pretty a
  | some a, none => BoundsAnnTy.pretty a
  | none, some s => s
  | none, none => r.programHm.pretty

/-- Lookup a binder report by name. -/
def ProgramReport.find? (r : ProgramReport) (n : ValName) : Option BindingReport :=
  r.bindings.find? fun b => b.name == n

/-- Peel leading arrow domains from a bounds ascription body. -/
def peelBoundsArrowDoms : Nat → BoundsAnnTy → List BoundsAnnTy
  | 0, _ => []
  | n + 1, .arrow d r => d :: peelBoundsArrowDoms n r
  | _, _ => []

/-- Head value-param domains from a binder ascription (scheme or mono). -/
def peelHeadDoms (n : Nat) : BinderAnn → List BoundsAnnTy
  | .mono a => peelBoundsArrowDoms n a
  | .scheme s => peelBoundsArrowDoms n s.body

/-- Drop `n` leading arrows from a bounds ascription body (residual codomain). -/
def dropBoundsArrows : Nat → BoundsAnnTy → BoundsAnnTy
  | 0, t => t
  | n + 1, .arrow _ r => dropBoundsArrows n r
  | _, t => t

/-- Residual bounds type of a binding RHS after `n` head value-params.
So `\xs -> …` under `let f : BL … → … = …` can hover `xs` as `BL …`, not `List`. -/
def BindingReport.rhsBoundsAfterHead (b : BindingReport) (nHead : Nat) : Option BoundsAnnTy :=
  b.bounds?.map fun ann =>
    let body := match ann with | .mono a => a | .scheme s => s.body
    dropBoundsArrows nHead body

/-- Domains for head params: bounds ann when present, else HM arrow peel. -/
def BindingReport.headParamDoms (b : BindingReport) (nHead : Nat) : List String :=
  match b.bounds? with
  | some ann =>
      let doms := peelHeadDoms nHead ann
      let nats :=
        match ann with
        | .scheme s => s.natBinders
        | .mono _ => []
      let tvars :=
        match ann with
        | .scheme s => s.tyBinders
        | .mono _ => []
      let prettyDoms := doms.map (BoundsAnnTy.prettyWith nats tvars)
      if prettyDoms.length < nHead then
        prettyDoms ++ List.replicate (nHead - prettyDoms.length) (Ty.pretty (.prim .unit))
      else
        prettyDoms.take nHead
  | none =>
      let rec peel : Nat → Ty → List Ty
        | 0, _ => []
        | n + 1, .arrow d r => d :: peel n r
        | _, _ => []
      let doms := peel nHead b.hm.body
      let padded :=
        if doms.length < nHead then
          doms ++ List.replicate (nHead - doms.length) (.prim .unit)
        else
          doms.take nHead
      padded.map (·.pretty)

/-- Assemble the display report from Infer schemes + the erase package.

`hmBindings` must already be in presentation order (`zipBindingTypes`).
`bounds?` is attached by name from `ep.toSurfaceAnns` — same erase truth Check reads. -/
def assembleFromBindings
    (hmBindings : List (ValName × PolyTy))
    (programHm : PolyTy)
    (ep : ErasedProgram) : ProgramReport :=
  let surf := ep.toSurfaceAnns
  { bindings := hmBindings.map fun ⟨n, σ⟩ =>
      { name := n
        hm := σ
        bounds? := (surf.byName.find? fun ⟨n', _⟩ => n' == n).map (·.2) }
    programHm := programHm
    bodyBounds? := surf.bodyAnn }

/-- Assemble from surface groups + Infer outer `letIn` schemes (SCC-undo zip). -/
def assembleProgramReport
    (groups : List (List Surface.Binding))
    (hmSchemes : List PolyTy)
    (programHm : PolyTy)
    (ep : ErasedProgram) : ProgramReport :=
  assembleFromBindings (zipBindingTypes groups hmSchemes) programHm ep

/-- Fill `synthPretty?` from Check (`bctx` ‖ `binderEnv`, 0 = innermost).
Also fills when ascription is present but still has `_` holes (so pretty can
prefer pin/pack over literal underscores). -/
def ProgramReport.enrichFromSynth
    (r : ProgramReport) (binderEnv : List ValName) (bctx : List String)
    (bodyPretty : Option String := none) : ProgramReport :=
  let byName : List (ValName × String) := binderEnv.zip bctx
  { r with
    bindings := r.bindings.map fun b =>
      let wantSynth :=
        match b.bounds? with
        | none => true
        | some a => a.hasHoles
      if !wantSynth then b
      else
        match (byName.find? fun ⟨n, _⟩ => n == b.name).map (·.2) with
        | some s => { b with synthPretty? := some s }
        | none => b
    programSynthPretty? :=
      let bodyHasHoles :=
        match r.bodyBounds? with
        | some a => a.hasHoles
        | none => true
      if bodyHasHoles then bodyPretty else r.programSynthPretty? }

#guard
  let σ : PolyTy := ⟨0, .prim .int⟩
  let br : BindingReport := { name := ⟨"x"⟩, hm := σ, bounds? := none }
  BindingReport.pretty br == "Int"

#guard
  let σ : PolyTy := ⟨1, .arrow (.bvar 0) (.customTy ⟨"List"⟩ [.bvar 0])⟩
  let ann : BinderAnn := .scheme {
    natBinders := []
    tyBinders := [⟨"a"⟩]
    body := .arrow
      (.fvar 0)
      (.list (.solid (.lit 1)) (.solid (.lit 1)) (.fvar 0))
  }
  let br : BindingReport := { name := ⟨"singleton"⟩, hm := σ, bounds? := some ann }
  BindingReport.pretty br == "∀ a. a → BL 1 1 a"

#guard
  let σ : PolyTy := ⟨1, .arrow (.bvar 0) (.customTy ⟨"List"⟩ [.bvar 0])⟩
  let ann : BinderAnn := .scheme {
    natBinders := [⟨"n"⟩]
    tyBinders := [⟨"a"⟩]
    body := .arrow
      (.fvar 0)
      (.list (.solid (.var ⟨.rigid, 0⟩)) (.solid (.var ⟨.rigid, 0⟩)) (.fvar 0))
  }
  let br : BindingReport := { name := ⟨"cons"⟩, hm := σ, bounds? := some ann }
  BindingReport.pretty br == "∀ (n : Nat) a. a → BL n n a"

end FHM.Bounds.Report
