import SGPT.PSH.NativeLogBiholomorphicEquivalence
import SGPT.PSH.GeometricQOpenBiholomorphicNaturality

/-! Complete native logarithmic neighborhoods follow the actual open square. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.SourceLogSingularitiesDraft
open scoped Topology Manifold ContDiff
universe u

/-- Actual independently dimensional biholomorphism pulls an ACTUAL open
logarithmic neighborhood to its literal preimage. The full rational open
coefficient square, not a compatibility premise, identifies the divisor. -/
theorem native_log_neighborhood_preimage_of_dimensionEq
    {a b : ℕ} {M N : Type u} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (ComplexModel a) M] [IsComplexManifold a M]
    [ChartedSpace (ComplexModel b) N] [IsComplexManifold b N]
    (h : a=b) (D : EffectiveGeometricQDivisor b N) (u : N → EReal) (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ,ComplexModel a) 𝓘(ℂ,ComplexModel b) ∞ e)
    (hei : ContMDiff 𝓘(ℂ,ComplexModel b) 𝓘(ℂ,ComplexModel a) ∞ e.symm)
    (O : Opens N)
    (hu : NativeHasLogSingularitiesAlongAnyDimension
      (geometricQDivisorOpenRestrictionAnyDimension D O) (fun q : O => u q.val)) :
    NativeHasLogSingularitiesAlongAnyDimension
      (geometricQDivisorOpenRestrictionAnyDimension
        (geometricQDivisorBiholomorphicPreimageOfDimensionEq h D e he hei) (preimageOpen e O))
      (fun q : preimageOpen e O => u (e q.val)) := by
  subst b
  have hlocal := hu.comp_biholomorphic (openHomeomorph e O)
    (openHomeomorph_contMDiff e O he) (openHomeomorph_symm_contMDiff e O hei)
  rw [←openRestriction_biholomorphic_naturality D e O he hei] at hlocal
  exact hlocal

end SGPT.PSH.VariableComplexAtlas.SourceLogTransportDraft
