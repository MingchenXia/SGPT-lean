import SGPT.PSH.AtlasBottChernQuotient

/-! Exact canonical comparison with the EXISTING native Bott--Chern
quotient, fixing the literal global smooth-dd^c convention and normalization. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff Classical
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- ALL genuine original fixed-model smooth-dd^c fields are EXACTLY those
of the accepted native relation, in both directions and arbitrary dimension. -/
theorem originalBottChernRel_fixedModel_iff
    (theta eta : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    OriginalBottChernRel theta eta ↔
      ClosedRealOneOneForm.BottChernRel (atlasClosedFormToNative theta) (atlasClosedFormToNative eta) := by
  constructor
  · rintro ⟨h,hh,heq⟩
    refine ⟨h,?_,heq⟩
    intro e
    have hhe := hh e
    change ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ univ) at hhe
    rw [Set.inter_univ] at hhe
    exact hhe
  · rintro ⟨h,hh,heq⟩
    refine ⟨h,?_,heq⟩
    intro e
    change ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ univ)
    rw [Set.inter_univ]
    exact hh e

/-- Actual quotient map from genuine original classes to the existing
native quotient, justified by the entire global difference relation. -/
def originalFixedModelToNative : OriginalRealBottChern (ofFixedModel n M) → RealBottChern n M :=
  Quotient.map atlasClosedFormToNative
    (fun theta eta h => (originalBottChernRel_fixedModel_iff theta eta).mp h)

/-- The SAME literal closed-form dictionary gives the actual inverse map. -/
def nativeToOriginalFixedModel : RealBottChern n M → OriginalRealBottChern (ofFixedModel n M) :=
  Quotient.map nativeClosedFormToAtlas (by
    intro theta eta h
    apply (originalBottChernRel_fixedModel_iff _ _).mpr
    exact h)

/-- GENUINE canonical equivalence with the accepted native cohomology;
no component product or quotient-equality flag is an input. -/
def originalFixedModelBottChernEquiv : OriginalRealBottChern (ofFixedModel n M) ≃ RealBottChern n M where
  toFun := originalFixedModelToNative
  invFun := nativeToOriginalFixedModel
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro theta
    change originalClass (nativeClosedFormToAtlas (atlasClosedFormToNative theta))=originalClass theta
    have h : nativeClosedFormToAtlas (atlasClosedFormToNative theta)=theta := by cases theta; rfl
    exact congrArg originalClass h
  right_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    rintro ⟨theta,htheta⟩
    cases theta
    rfl

/-- ACTUAL source representative readback, not merely an abstract bijection. -/
theorem originalFixedModelBottChernEquiv_class
    (theta : AtlasClosedRealOneOneForm (ofFixedModel n M)) :
    originalFixedModelBottChernEquiv (originalClass theta)=
      RealBottChern.ofRepresentative (atlasClosedFormToNative theta) := rfl

/-- ACTUAL native representative readback under the exact inverse. -/
theorem originalFixedModelBottChernEquiv_symm_class (theta : ClosedRealOneOneForm n M) :
    originalFixedModelBottChernEquiv.symm (RealBottChern.ofRepresentative theta)=
      originalClass (nativeClosedFormToAtlas theta) := rfl

end SGPT.PSH.VariableComplexAtlas.SourceCohomologyDraft
