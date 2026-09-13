import FHM.Bounds.Scope
import FHM.SurfaceBridge

/-! Construction-time count-name resolution. Unknown names are recorded, not
    rejected by HM lowering; only BL consumes these errors. -/

namespace SurfaceBridge.CountScope

open FHM.Bounds.Scope

def countNames : Surface.Count → List ValName
  | .lit _ | .inf => []
  | .var name => [name]
  | .add a b | .mul a b | .min a b | .max a b => countNames a ++ countNames b
  | .pred a => countNames a

def slotNames : Surface.CountSlot → List ValName
  | .hole => []
  | .solid c => countNames c

mutual
def typeNames : Surface.Ty → List ValName
  | .prim _ | .tvar _ => []
  | .pair a b | .arrow a b => typeNames a ++ typeNames b
  | .customTy _ args => typeNamesList args
  | .bl lo hi e => slotNames lo ++ slotNames hi ++ typeNames e

def typeNamesList : List Surface.Ty → List ValName
  | [] => []
  | a :: as => typeNames a ++ typeNamesList as
end

def resolve (scope : Lexical) (v : FHM.Bounds.Var) : FHM.Bounds.Var :=
  match v.kind with
  | .inferable => v
  | .rigid => ⟨.rigid, (scope[v.idx]?.map Prod.snd).getD 0⟩

def lowerTyScoped (ke : KindEnv) (tvs : List ValName) (scope : Lexical)
    (τ : Surface.Ty) : Option Ty :=
  (lowerTy ke tvs τ (scope.map Prod.fst)).map
    (FHM.Bounds.Scope.renameTy (resolve scope))

def lowerAnnScoped (ke : KindEnv) (tvs : List ValName) (scope : Lexical) :
    Option Surface.Ty → Option (Option Ty)
  | none => some none
  | some τ => (lowerTyScoped ke tvs scope τ).map some

def lowerPolyScoped (ke : KindEnv) (scope : Lexical) :
    Option Surface.PolyTy → Option (Option PolyTy)
  | none => some none
  | some σ =>
      let fs := σ.foralls.eraseDups
      (lowerTyScoped ke fs scope σ.body).map fun body => some ⟨fs.length, body⟩

def annotationMetadata (site : CoreBinderSite) (scope : Lexical)
    (ann : Option Surface.Ty) : Metadata :=
  let missing := ((ann.map typeNames).getD []).filter fun name =>
    !(scope.any fun pair => pair.1 == name)
  if missing.isEmpty then {} else ⟨[], [⟨site, missing.dedup, []⟩]⟩

def telescopeMetadata (site : CoreBinderSite) (own : Lexical) : Metadata :=
  let names := own.map Prod.fst
  let duplicates := names.filter fun name => (names.filter (· == name)).length > 1
  ⟨[⟨site, own⟩], if duplicates.isEmpty then [] else [⟨site, [], duplicates.dedup⟩]⟩

end SurfaceBridge.CountScope
