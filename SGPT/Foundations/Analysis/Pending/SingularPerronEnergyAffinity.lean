import SGPT.Foundations.Analysis.Pending.SingularGeodesicEnergyAffineLimits
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicGeneralNativeContinuity
import SGPT.Foundations.Analysis.Pending.AffineOfWeakSecondDerivative
import SGPT.Foundations.Analysis.Pending.SingularPerronWeakEnergyLaplacian

set_option autoImplicit false

/-! # Genuine same-type Perron energy affinity for arbitrary singular models -/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SingularPerronEnergyAffinity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

private theorem continuousOn_toReal_energy_interior (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) :
    ContinuousOn (fun t : ℝ => (energy θ φ hφ
      (finiteGeodesic θ.val u₀ u₁ t)).toReal) (Ioo (0 : ℝ) 1) := by
  have h := SingularModelGeodesicGeneralNativeContinuity.continuousOn_toReal_energy_closedSubgeodesicSlice
    omega ⟨u₀, hu₀⟩ ⟨u₁, hu₁⟩
  apply (h.mono Ioo_subset_Icc_self).congr
  intro t ht
  have heq : closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t =
      finiteGeodesic θ.val u₀ u₁ t := closedSubgeodesicSlice_eq_curve ht
  exact congrArg (fun u : M → EReal => (energy θ φ hφ u).toReal) heq.symm

/-- Actual compact-host weak energy and genuine native energy continuity internally produce interior affine constants, without a weak equation or affinity premise. -/
theorem exists_affine_toReal_energy_finiteGeodesic (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hEInf₀ : RelativeEInfinity θ φ u₀) (hEInf₁ : RelativeEInfinity θ φ u₁) :
    ∃ c₀ c₁ : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
      (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal = c₀ + c₁ * t := by
  apply AffineOfWeakSecondDerivative.exists_affine_of_integral_timeLaplacian
    (continuousOn_toReal_energy_interior omega hu₀ hu₁)
  intro ψ hψ hψc hψS
  have h := SingularPerronWeakEnergyLaplacian.integrable_and_integral_energy_timeLaplacian_eq_zero
    omega hu₀ hu₁ hEInf₀ hEInf₁ hψ hψc hψS
  simpa only [mul_comm] using h.2

/-- The internally proved same-type affine function and the genuine finite-energy endpoint limits give its actual endpoint chord over an arbitrary singular model. -/
theorem toReal_energy_finiteGeodesic_eq_chord (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hEInf₀ : RelativeEInfinity θ φ u₀) (hEInf₁ : RelativeEInfinity θ φ u₁)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal =
      (1 - t) * (energy θ φ hφ u₀).toReal + t * (energy θ φ hφ u₁).toReal :=
  SingularGeodesicEnergyAffineLimits.eq_chord_of_affine_and_endpoint_limits
    (exists_affine_toReal_energy_finiteGeodesic omega hu₀ hu₁ hEInf₀ hEInf₁)
    (SingularPerronGeneralEndpointEnergyContinuity.tendsto_toReal_energy_finiteGeodesic_left
      omega hu₀ hu₁)
    (SingularPerronGeneralEndpointEnergyContinuity.tendsto_toReal_energy_finiteGeodesic_right
      omega hu₀ hu₁) t ht

end

end SGPT.Foundations.Analysis.Pending.SingularPerronEnergyAffinity
