import FHM.AnnotationMatching

/-! Written schemes and their derived checking views. No checking mode is
stored in the source syntax. Hole-free annotations are complete signatures,
matching surface lowering; partial written foralls retain their written prefix. -/

mutual
def PartialCore.Template.toTy : TyTemplate → Option Ty
  | .fixed ty => some ty
  | .hole | .named _ => none
  | .arrow a b => return .arrow (← a.toTy) (← b.toTy)
  | .custom name args => return .customTy name (← completeTypes args)
def completeTypes : List TyTemplate → Option (List Ty)
  | [] => some []
  | template :: rest => return (← template.toTy) :: (← completeTypes rest)
end

mutual
def PartialCore.Template.openTyVarsFrom (d : Nat) (Xs : List Nat) : TyTemplate → TyTemplate
  | .fixed ty => .fixed (ty.openVarsFrom d Xs)
  | .hole => .hole
  | .named name => .named name
  | .arrow a b => .arrow (a.openTyVarsFrom d Xs) (b.openTyVarsFrom d Xs)
  | .custom name args => .custom name (openTemplateList d Xs args)
def openTemplateList (d : Nat) (Xs : List Nat) : List TyTemplate → List TyTemplate
  | [] => []
  | t :: ts => t.openTyVarsFrom d Xs :: openTemplateList d Xs ts
end

mutual
def PartialCore.Template.substSourceTyFvars (subst : List (Nat × Ty)) : TyTemplate → TyTemplate
  | .fixed ty => .fixed (ty.substFvars subst)
  | .hole => .hole
  | .named name => .named name
  | .arrow a b => .arrow (a.substSourceTyFvars subst) (b.substSourceTyFvars subst)
  | .custom name args => .custom name (substTemplateList subst args)
def substTemplateList (subst : List (Nat × Ty)) : List TyTemplate → List TyTemplate
  | [] => []
  | t :: ts => t.substSourceTyFvars subst :: substTemplateList subst ts
end

def PartialCore.Ann.isSignature : CheckAnn → Bool
  | .complete _ | .partialForall _ _ => true
  | .absent | .template _ => false

def PartialCore.Ann.rigidVars : CheckAnn → List Nat
  | .absent => []
  | .complete scheme => scheme.body.freeVars
  | .template t => t.rigidVars
  | .partialForall _ t => t.rigidVars

def PartialCore.Ann.ofScheme : Option PolyTy → CheckAnn
  | none => .absent
  | some scheme => .complete scheme

def PartialCore.Ann.openTyVarsFrom (d : Nat) (Xs : List Nat) : CheckAnn → CheckAnn
  | .absent => .absent
  | .complete scheme => .complete { scheme with
      body := scheme.body.openVarsFrom (d + scheme.paramCount) Xs }
  | .template t => .template (t.openTyVarsFrom d Xs)
  | .partialForall n t => .partialForall n (t.openTyVarsFrom (d + n) Xs)

def PartialCore.Ann.substSourceTyFvars (subst : List (Nat × Ty)) : CheckAnn → CheckAnn
  | .absent => .absent
  | .complete scheme => .complete { scheme with body := scheme.body.substFvars subst }
  | .template t => .template (t.substSourceTyFvars subst)
  | .partialForall n t => .partialForall n (t.substSourceTyFvars subst)

def PartialCore.Ann.recModeAnn : CheckAnn → Option PolyTy
  | .complete scheme => some scheme
  | _ => none

def PartialCore.Ann.recPrefixCount : CheckAnn → Nat
  | .partialForall count _ => count
  | _ => 0


def Option.paramCount (ann : Option (Scheme T)) : Nat :=
  ann.elim 0 Scheme.paramCount

def Option.annotationView : BindingAnn → CheckAnn
  | none => .absent
  | some ⟨count, template⟩ =>
      match template.toTy with
      | some ty => .complete ⟨count, ty⟩
      | none => if count = 0 then .template template else .partialForall count template

def Option.isSignature (ann : BindingAnn) : Bool := ann.annotationView.isSignature

@[simp] theorem Option.isSignature_annotationView (ann : BindingAnn) :
    ann.annotationView.isSignature = ann.isSignature := rfl

def Option.rigidVars (ann : BindingAnn) : List Nat :=
  ann.elim [] (fun scheme => scheme.body.rigidVars)

def Option.recModeAnn (ann : BindingAnn) : Option PolyTy := ann.annotationView.recModeAnn

def Option.recPrefixCount (ann : BindingAnn) : Nat := ann.annotationView.recPrefixCount

def Option.fromScheme (ann : Option PolyTy) : BindingAnn :=
  ann.map (Scheme.map PartialCore.Template.fixed)

def Option.openTyVarsFrom (depth : Nat) (names : List Nat) : BindingAnn → BindingAnn :=
  Option.map fun scheme =>
    ⟨scheme.paramCount, scheme.body.openTyVarsFrom (depth + scheme.paramCount) names⟩

def Option.substSourceTyFvars (subst : List (Nat × Ty)) : BindingAnn → BindingAnn :=
  Option.map (Scheme.map (PartialCore.Template.substSourceTyFvars subst))

theorem Option.annotationView_complete (template : TyTemplate)
    (h : template.toTy = some ty) (count : Nat) :
    (some (Scheme.mk count template)).annotationView = .complete ⟨count, ty⟩ := by
  simp only [Option.annotationView, h]

@[simp] theorem Option.annotationView_fromScheme (ann : Option PolyTy) :
    (Option.fromScheme ann).annotationView = PartialCore.Ann.ofScheme ann := by
  cases ann <;> rfl

@[simp] theorem Option.paramCount_fromScheme (ann : Option PolyTy) :
    (Option.fromScheme ann).paramCount = RecAnn.params ann := by
  cases ann <;> rfl

@[simp] theorem Option.paramCount_substSourceTyFvars (ann : BindingAnn) (subst) :
    (ann.substSourceTyFvars subst).paramCount = ann.paramCount := by
  cases ann <;> rfl

@[simp] theorem Option.paramCount_openTyVarsFrom (ann : BindingAnn) (depth names) :
    (ann.openTyVarsFrom depth names).paramCount = ann.paramCount := by
  cases ann <;> rfl

@[simp] theorem Option.annotationView_paramCount (ann : BindingAnn) :
    ann.annotationView.paramCount = ann.paramCount := by
  cases ann with
  | none => rfl
  | some scheme =>
    rcases scheme with ⟨count, template⟩
    cases ht : template.toTy with
    | some ty => simp [Option.annotationView, ht, Option.paramCount, PartialCore.Ann.paramCount]
    | none =>
      by_cases hc : count = 0 <;>
        simp [Option.annotationView, ht, hc, Option.paramCount, PartialCore.Ann.paramCount]

mutual
theorem PartialCore.Template.toTy_subst (t : TyTemplate) (S : Subst) :
    (t.substSourceTyFvars S).toTy = t.toTy.map S.onTy := by
  cases t with
  | fixed ty => rfl
  | hole | named => rfl
  | arrow a b =>
    simp only [PartialCore.Template.substSourceTyFvars, PartialCore.Template.toTy,
      a.toTy_subst S, b.toTy_subst S]
    cases a.toTy <;> cases b.toTy <;> simp [Subst.onTy_arrow]
  | custom name args =>
    simp only [PartialCore.Template.substSourceTyFvars, PartialCore.Template.toTy,
      completeTypes_subst args S]
    cases completeTypes args <;> simp [Subst.onTy_customTy]
theorem completeTypes_subst (ts : List TyTemplate) (S : Subst) :
    completeTypes (substTemplateList S ts) = (completeTypes ts).map (List.map S.onTy) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [substTemplateList, completeTypes, t.toTy_subst S, completeTypes_subst ts S]
    cases t.toTy <;> cases completeTypes ts <;> rfl
end

mutual
theorem PartialCore.Template.toTy_open (t : TyTemplate) (d : Nat) (Xs : List Nat) :
    (t.openTyVarsFrom d Xs).toTy = t.toTy.map (Ty.openVarsFrom d Xs) := by
  cases t with
  | fixed ty => rfl
  | hole | named => rfl
  | arrow a b =>
    simp only [PartialCore.Template.openTyVarsFrom, PartialCore.Template.toTy,
      a.toTy_open d Xs, b.toTy_open d Xs]
    cases a.toTy <;> cases b.toTy <;> simp [Ty.openVarsFrom_arrow]
  | custom name args =>
    simp only [PartialCore.Template.openTyVarsFrom, PartialCore.Template.toTy,
      completeTypes_open args d Xs]
    cases completeTypes args <;> simp [Ty.openVarsFrom_customTy]
theorem completeTypes_open (ts : List TyTemplate) (d : Nat) (Xs : List Nat) :
    completeTypes (openTemplateList d Xs ts) =
      (completeTypes ts).map (List.map (Ty.openVarsFrom d Xs)) := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [openTemplateList, completeTypes, t.toTy_open d Xs, completeTypes_open ts d Xs]
    cases t.toTy <;> cases completeTypes ts <;> rfl
end

theorem Option.annotationView_subst (ann : BindingAnn) (S : Subst) :
    (ann.substSourceTyFvars S).annotationView = ann.annotationView.substSourceTyFvars S := by
  cases ann with
  | none => rfl
  | some scheme =>
    rcases scheme with ⟨count, t⟩
    simp only [Option.substSourceTyFvars, Option.map_some, Scheme.map,
      Option.annotationView, t.toTy_subst]
    cases ht : t.toTy with
    | some ty => rfl
    | none => by_cases hc : count = 0 <;> simp [hc, PartialCore.Ann.substSourceTyFvars]

theorem Option.annotationView_open (ann : BindingAnn) (d : Nat) (Xs : List Nat) :
    (ann.openTyVarsFrom d Xs).annotationView = ann.annotationView.openTyVarsFrom d Xs := by
  cases ann with
  | none => rfl
  | some scheme =>
    rcases scheme with ⟨count, t⟩
    simp only [Option.openTyVarsFrom, Option.map_some, Option.annotationView, t.toTy_open]
    cases ht : t.toTy with
    | some ty => rfl
    | none => by_cases hc : count = 0 <;> simp [hc, PartialCore.Ann.openTyVarsFrom]

@[simp] theorem Option.recModeAnn_subst_source (ann : BindingAnn) (S : Subst) :
    (ann.substSourceTyFvars S).recModeAnn = ann.recModeAnn.map S.onPolyTy := by
  simp only [Option.recModeAnn, Option.annotationView_subst]
  cases ann.annotationView <;> rfl

@[simp] theorem Option.recPrefixCount_subst_source (ann : BindingAnn) (S : Subst) :
    (ann.substSourceTyFvars S).recPrefixCount = ann.recPrefixCount := by
  simp only [Option.recPrefixCount, Option.annotationView_subst]
  cases ann.annotationView <;> rfl

@[simp] theorem Option.isSignature_substTyFvars (ann : BindingAnn) (S : Subst) :
    (ann.substSourceTyFvars S).isSignature = ann.isSignature := by
  simp only [Option.isSignature, Option.annotationView_subst]
  cases ann.annotationView <;> rfl

/-- Normalize helper transport back to the corresponding authored scheme.
The forward commuting equations remain available for deliberate rewriting. -/
@[simp] theorem Option.annotationView_subst_back (ann : BindingAnn) (S : Subst) :
    ann.annotationView.substSourceTyFvars S = (ann.substSourceTyFvars S).annotationView :=
  (ann.annotationView_subst S).symm

@[simp] theorem Option.annotationView_open_back (ann : BindingAnn) (d : Nat) (Xs : List Nat) :
    ann.annotationView.openTyVarsFrom d Xs = (ann.openTyVarsFrom d Xs).annotationView :=
  (ann.annotationView_open d Xs).symm
