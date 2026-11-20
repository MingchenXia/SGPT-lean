import SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalMetricLimit
import SGPT.Foundations.Analysis.Pending.SingularModelGeodesicEndpointEnergy

set_option autoImplicit false

/-! # Genuine upper endpoint energy control for general singular finite-energy Perron curves -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularPerronGeneralEndpointEnergyUpper

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelEnergyTruncation MongeAmpereEnergyDecreasing
  SingularPerronCanonicalTruncationEnergy SingularPerronCanonicalMetricLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual canonical truncation energy limits and actual Perron order give upper energy control at the initial endpoint for arbitrary singularity-order E1 endpoints. -/
theorem eventually_toReal_energy_lt_left (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {a : ℝ}
    (ha : (energy θ φ hφ u₀).toReal < a) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal < a := by
  obtain ⟨j, hj⟩ := ((toReal_energy_tendsto_endpoint_truncation omega hu₀).eventually
    (Iio_mem_nhds ha)).exists
  have hE₀ := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₀.1.plurisubharmonic hu₀.1.relativePSHPreceq.2 j
  have hE₁ := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₁.1.plurisubharmonic hu₁.1.relativePSHPreceq.2 j
  have hstage := SingularModelGeodesicEndpointEnergy.tendsto_toReal_energy_finiteGeodesic_left (hφ := hφ)
    omega (relativeFiniteEnergyPreceq_truncation omega hu₀.1.relativePSHPreceq j)
    (relativeFiniteEnergyPreceq_truncation omega hu₁.1.relativePSHPreceq j)
    (hE₀.2.trans hE₁.2.symm)
  filter_upwards [hstage.eventually (Iio_mem_nhds hj), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with t hta ht₀ ht₁
  exact (SingularModelFiniteRealEnergy.toReal_energy_mono omega
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ⟨ht₀, ht₁⟩)
    (relativeFiniteEnergyPreceq_truncatedGeodesic omega
      hu₀.1.relativePSHPreceq hu₁.1.relativePSHPreceq j ⟨ht₀, ht₁⟩)
    (finiteGeodesic_mono (le_truncation φ u₀ j) (le_truncation φ u₁ j) t)).trans_lt hta

/-- The same actual canonical truncation producers give upper energy control at the terminal endpoint, with no equal-singularity-type or affinity assumption on the original endpoints. -/
theorem eventually_toReal_energy_lt_right (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {a : ℝ}
    (ha : (energy θ φ hφ u₁).toReal < a) :
    ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ),
      (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal < a := by
  obtain ⟨j, hj⟩ := ((toReal_energy_tendsto_endpoint_truncation omega hu₁).eventually
    (Iio_mem_nhds ha)).exists
  have hE₀ := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₀.1.plurisubharmonic hu₀.1.relativePSHPreceq.2 j
  have hE₁ := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₁.1.plurisubharmonic hu₁.1.relativePSHPreceq.2 j
  have hstage := SingularModelGeodesicEndpointEnergy.tendsto_toReal_energy_finiteGeodesic_right (hφ := hφ)
    omega (relativeFiniteEnergyPreceq_truncation omega hu₀.1.relativePSHPreceq j)
    (relativeFiniteEnergyPreceq_truncation omega hu₁.1.relativePSHPreceq j)
    (hE₀.2.trans hE₁.2.symm)
  filter_upwards [hstage.eventually (Iio_mem_nhds hj), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with t hta ht₁ ht₀
  exact (SingularModelFiniteRealEnergy.toReal_energy_mono omega
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ⟨ht₀, ht₁⟩)
    (relativeFiniteEnergyPreceq_truncatedGeodesic omega
      hu₀.1.relativePSHPreceq hu₁.1.relativePSHPreceq j ⟨ht₀, ht₁⟩)
    (finiteGeodesic_mono (le_truncation φ u₀ j) (le_truncation φ u₁ j) t)).trans_lt hta

end

end SGPT.Foundations.Analysis.Pending.SingularPerronGeneralEndpointEnergyUpper
