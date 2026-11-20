import SGPT.Foundations.Analysis.Pending.SingularPerronShiftedRooftopBarriers
import SGPT.Foundations.Analysis.Pending.SingularPerronGeneralEndpointEnergyUpper
import SGPT.Foundations.Analysis.Pending.SingularModelEnergyShiftedRooftopContinuity

set_option autoImplicit false

/-! # Actual general singular Perron energies recover both endpoint energies -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularPerronGeneralEndpointEnergyContinuity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularPerronShiftedRooftopBarriers
  SingularPerronGeneralEndpointEnergyUpper SingularModelEnergyShiftedRooftopContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Genuine shifted rooftop energy exhaustion and its actual affine Perron competitor give the full E1 initial lower endpoint estimate. -/
theorem eventually_lt_toReal_energy_left (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {a : ℝ}
    (ha : a < (energy θ φ hφ u₀).toReal) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      a < (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal := by
  obtain ⟨C, hC⟩ := ((toReal_energy_rooftop_add_const_tendsto omega hu₀ hu₁).eventually
    (Ioi_mem_nhds ha)).exists
  have hf : Continuous (fun t : ℝ =>
      (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal -
        C * t * modelVolume θ φ hφ) := by fun_prop
  have hl : Tendsto (fun t : ℝ =>
      (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal -
        C * t * modelVolume θ φ hφ) (𝓝[>] (0 : ℝ))
      (𝓝 (energy θ φ hφ (rooftop θ u₀ (fun x => u₁ x + (C : EReal)))).toReal) := by
    simpa using (hf.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  filter_upwards [hl.eventually (Ioi_mem_nhds hC), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with t hta ht₀ ht₁
  exact hta.trans_le (toReal_energy_shifted_rooftop_lower_left omega hu₀ hu₁ C ⟨ht₀, ht₁⟩)

/-- The genuine reversed shifted rooftop family gives the full E1 terminal lower endpoint estimate. -/
theorem eventually_lt_toReal_energy_right (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {a : ℝ}
    (ha : a < (energy θ φ hφ u₁).toReal) :
    ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ),
      a < (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal := by
  obtain ⟨C, hC⟩ := ((toReal_energy_rooftop_add_const_tendsto omega hu₁ hu₀).eventually
    (Ioi_mem_nhds ha)).exists
  have hf : Continuous (fun t : ℝ =>
      (energy θ φ hφ (rooftop θ u₁ (fun x => u₀ x + (C : EReal)))).toReal -
        C * (1 - t) * modelVolume θ φ hφ) := by fun_prop
  have hl : Tendsto (fun t : ℝ =>
      (energy θ φ hφ (rooftop θ u₁ (fun x => u₀ x + (C : EReal)))).toReal -
        C * (1 - t) * modelVolume θ φ hφ) (𝓝[<] (1 : ℝ))
      (𝓝 (energy θ φ hφ (rooftop θ u₁ (fun x => u₀ x + (C : EReal)))).toReal) := by
    simpa using (hf.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  filter_upwards [hl.eventually (Ioi_mem_nhds hC), self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with t hta ht₁ ht₀
  exact hta.trans_le (toReal_energy_shifted_rooftop_lower_right omega hu₀ hu₁ C ⟨ht₀, ht₁⟩)

/-- The genuine lower rooftop estimate and independent upper truncation estimate produce initial real energy continuity for arbitrary singularity-order E1 endpoints. -/
theorem tendsto_toReal_energy_finiteGeodesic_left (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) :
    Tendsto (fun t : ℝ => (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 (energy θ φ hφ u₀).toReal) :=
  tendsto_order.2 ⟨fun _ ha => eventually_lt_toReal_energy_left omega hu₀ hu₁ ha,
    fun _ ha => eventually_toReal_energy_lt_left omega hu₀ hu₁ ha⟩

/-- Both actual endpoint estimates give the corresponding terminal real energy limit without affinity or equal singularity types. -/
theorem tendsto_toReal_energy_finiteGeodesic_right (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) :
    Tendsto (fun t : ℝ => (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal)
      (𝓝[<] (1 : ℝ)) (𝓝 (energy θ φ hφ u₁).toReal) :=
  tendsto_order.2 ⟨fun _ ha => eventually_lt_toReal_energy_right omega hu₀ hu₁ ha,
    fun _ ha => eventually_toReal_energy_lt_right omega hu₀ hu₁ ha⟩

/-- Genuine E1 realification on actual interior Perron slices transfers the initial limit to the defining extended energy. -/
theorem tendsto_energy_finiteGeodesic_left (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) :
    Tendsto (fun t : ℝ => energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t))
      (𝓝[>] (0 : ℝ)) (𝓝 (energy θ φ hφ u₀)) := by
  have h := EReal.tendsto_coe.mpr (tendsto_toReal_energy_finiteGeodesic_left omega hu₀ hu₁)
  rw [SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hu₀] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with t ht₀ ht₁
  exact SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ⟨ht₀, ht₁⟩)

/-- The same actual finite-energy identities give the defining extended energy limit at the terminal endpoint. -/
theorem tendsto_energy_finiteGeodesic_right (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) :
    Tendsto (fun t : ℝ => energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t))
      (𝓝[<] (1 : ℝ)) (𝓝 (energy θ φ hφ u₁)) := by
  have h := EReal.tendsto_coe.mpr (tendsto_toReal_energy_finiteGeodesic_right omega hu₀ hu₁)
  rw [SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hu₁] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with t ht₁ ht₀
  exact SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ⟨ht₀, ht₁⟩)

end

end SGPT.Foundations.Analysis.Pending.SingularPerronGeneralEndpointEnergyContinuity
