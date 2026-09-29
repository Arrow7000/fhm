import FHM.Pretty

/-!
# Hindley--Milner program reports

Presentation-only report values shared by the HM live pipeline.  They contain
the inferred schemes and optional rendered names, with no bounds-sidecar state
or checker authority.
-/

namespace FHM.Unverified.HMReport

/-- One top-level binding's inferred scheme and presentation spelling. -/
structure BindingReport where
  name : ValName
  hm : PolyTy
  /-- A spelling which preserves authored type-variable names when available. -/
  synthPretty? : Option String := none

def BindingReport.pretty (b : BindingReport) : String :=
  b.synthPretty?.getD b.hm.pretty

/-- Presentation-order bindings plus the inferred type of the program body. -/
structure ProgramReport where
  bindings : List BindingReport := []
  programHm : PolyTy
  /-- A spelling which preserves authored type-variable names when available. -/
  programSynthPretty? : Option String := none

def ProgramReport.programPretty (r : ProgramReport) : String :=
  r.programSynthPretty?.getD r.programHm.pretty

/-- Lookup a top-level binding report by source name. -/
def ProgramReport.find? (r : ProgramReport) (name : ValName) : Option BindingReport :=
  r.bindings.find? fun binding => binding.name == name

end FHM.Unverified.HMReport
