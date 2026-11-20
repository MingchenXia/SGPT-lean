import SGPT.NAPotential.DHIntrinsic

/-! cutoff bounds follow from an actual common bound in the
source positive-curve order. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.NAPotential.DH
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M] {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- A positive common lower bound provides the real cutoff lower bound. -/
theorem cutoff_bddBelow_of_positive_lower_bound (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (h : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA Γ)
      (sourcePositiveTestCurveToNA (Γs i))) :
    BddBelow (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))) := by
  refine ⟨Γ.val.max, ?_⟩
  rintro x ⟨i, rfl⟩
  have hi := ((sourcePositiveTestCurveToNA_POrder_iff omega Γ (Γs i)).mp (h i)).cutoff_le
  simpa only [sourcePositiveTestCurveToNA_cutoff] using hi

/-- A positive common upper bound provides the real cutoff upper bound. -/
theorem cutoff_bddAbove_of_positive_upper_bound (omega : KahlerBackground n M)
    (Γs : ℕ → SourcePositiveIModelTestCurve θ) (Γ : SourcePositiveIModelTestCurve θ)
    (h : ∀ i, SourceNAPOrder (sourcePositiveTestCurveToNA (Γs i))
      (sourcePositiveTestCurveToNA Γ)) :
    BddAbove (range fun i => sourceNAPotentialCutoff omega (sourcePositiveTestCurveToNA (Γs i))) := by
  refine ⟨Γ.val.max, ?_⟩
  rintro x ⟨i, rfl⟩
  have hi := ((sourcePositiveTestCurveToNA_POrder_iff omega (Γs i) Γ).mp (h i)).cutoff_le
  simpa only [sourcePositiveTestCurveToNA_cutoff] using hi

end SGPT.NAPotential.DH
