import SGPT.PSH.SigmaNativeAtlas

/-! ACTUAL global closed forms and real smooth-dd^c potentials glue on the
true disjoint-union manifold, with all original tensor fields proved. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {I : Type u} {C : I → Type u} [∀ c,TopologicalSpace (C c)] {n : I → ℕ}
  [∀ c,ChartedSpace (ComplexModel (n c)) (C c)] [∀ c,IsComplexManifold (n c) (C c)]

/-- Genuine smooth/closed/type/tensor fields on the ACTUAL disjoint union
are internally manufactured from actual native closed forms. -/
def sigmaGluedForm (F : ∀ c,ClosedRealOneOneForm (n c) (C c)) :
    AtlasClosedRealOneOneForm (sigmaNativeAtlas (n := n) (C := C)) where
  coeff := fun t => (F t.1).val.coeff t.2
  smooth := fun t => (F t.1).val.smooth t.2
  closed := fun t => (F t.1).2.1 t.2
  typeOneOne := fun t => (F t.1).2.2 t.2
  compatible := by
    rintro ⟨c,e⟩ ⟨d,f⟩ z hz w
    by_cases hcd : c=d
    · subst d
      rw [sigmaNativeAtlas_transition] at hz ⊢
      exact (F c).val.compatible e f z hz w
    · have he := sigmaNativeChart_transition_empty hcd e f
      change z∈((sigmaNativeChart ⟨c,e⟩).symm.trans (sigmaNativeChart ⟨d,f⟩)).source at hz
      rw [he] at hz
      exact False.elim hz

/-- Actual original closed tensors restrict to the SAME native coefficient
functions; genuine transition, closedness and type fields are preserved. -/
def sigmaRestrictedForm
    (theta : AtlasClosedRealOneOneForm (sigmaNativeAtlas (n := n) (C := C))) (c : I) :
    ClosedRealOneOneForm (n c) (C c) := by
  refine ⟨{
    coeff := fun e => theta.coeff ⟨c,e⟩
    smooth := fun e => theta.smooth ⟨c,e⟩
    compatible := ?_
  },(fun e => theta.closed ⟨c,e⟩),(fun e => theta.typeOneOne ⟨c,e⟩)⟩
  intro e f z hz w
  have hs : z∈(((sigmaNativeAtlas (n := n) (C := C)).chart ⟨c,e⟩).symm.trans
      ((sigmaNativeAtlas (n := n) (C := C)).chart ⟨c,f⟩)).source := by
    rwa [sigmaNativeAtlas_transition]
  have h := theta.compatible ⟨c,e⟩ ⟨c,f⟩ z hs w
  rwa [sigmaNativeAtlas_transition] at h

/-- Full actual coefficient readback under genuine restriction/gluing. -/
theorem sigmaRestrictedGluedForm_coeff (F : ∀ c,ClosedRealOneOneForm (n c) (C c))
    (c : I) (e : ComplexChart (n c) (C c)) (z : ComplexModel (n c)) :
    (sigmaRestrictedForm (sigmaGluedForm F) c).val.coeff e z=(F c).val.coeff e z := rfl

/-- The actual native class is unchanged under genuine form gluing and
restriction; the zero potential proves the ENTIRE native relation. -/
theorem sigmaRestrictedGluedForm_class (F : ∀ c,ClosedRealOneOneForm (n c) (C c)) (c : I) :
    RealBottChern.ofRepresentative (sigmaRestrictedForm (sigmaGluedForm F) c)=
      RealBottChern.ofRepresentative (F c) := by
  apply (RealBottChern.ofRepresentative_eq_iff _ _).mpr
  refine ⟨fun _ => 0,fun _ => contDiffOn_const,?_⟩
  intro e z hz
  rw [smoothDDC_zero,add_zero]
  rfl

/-- GENUINE global source relation iff actual native component relations:
the reverse implication GLUES one actual globally smooth real potential on
the entire original disjoint union, with its full dd^c tensor equality. -/
theorem originalBottChernRel_sigma_iff
    (theta eta : AtlasClosedRealOneOneForm (sigmaNativeAtlas (n := n) (C := C))) :
    OriginalBottChernRel theta eta ↔
      ∀ c,ClosedRealOneOneForm.BottChernRel (sigmaRestrictedForm theta c) (sigmaRestrictedForm eta c) := by
  constructor
  · rintro ⟨h,hh,heq⟩ c
    refine ⟨fun p : C c => h ⟨c,p⟩,?_,?_⟩
    · intro e
      have hs := hh ⟨c,e⟩
      change ContDiffOn ℝ ∞ (fun z => h ⟨c,e.val.symm z⟩) (e.val.target ∩ univ) at hs
      rw [Set.inter_univ] at hs
      exact hs
    · intro e z hz
      exact heq ⟨c,e⟩ z hz
  · intro hcomp
    choose h hh heq using hcomp
    refine ⟨fun p => h p.1 p.2,?_,?_⟩
    · rintro ⟨c,e⟩
      change ContDiffOn ℝ ∞ (fun z => h c (e.val.symm z)) (e.val.target ∩ univ)
      rw [Set.inter_univ]
      exact hh c e
    · rintro ⟨c,e⟩ z hz
      exact heq c e z hz

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
