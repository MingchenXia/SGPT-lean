import SGPT.Convex.GeometricMinkowskiPolarization
import SGPT.IGood.LogVolume

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric

open Set MeasureTheory SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

/-- The original dimension-zero mixed source value and the independent
geometric empty mixed volume agree. This uses the actual source empty-tuple
measure theorem, not a nonexistent positive-dimensional degree-two current. -/
theorem source_toric_mixed_volume_dim_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
    (ω : KahlerBackground 0 M)
    (θ : Fin 0 → AtlasClosedRealOneOneForm (ofFixedModel 0 M))
    (u : Fin 0 → M → EReal)
    (hu : ∀ i, (ofFixedModel 0 M).IsThetaPSH (θ i) (u i))
    (P : Fin 0 → Set (EuclideanSpace ℝ (Fin 0))) :
    (sourceGeneralMixedIVolume ω θ u hu).toReal =
      ((0 : ℕ).factorial : ℝ) * sourceGeometricMixedVolume P := by
  rw [SGPT.IGood.LogVolume.sourceGeneralMixedIVolume_eq_one_of_dim_zero ω θ u hu,
    sourceGeometricMixedVolume_empty]
  norm_num

end SGPT.Toric
