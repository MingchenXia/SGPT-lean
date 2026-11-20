import SGPT.Foundations.Analysis.Pending.SingularPerronEnergyAffinity
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements

set_option autoImplicit false

/-! # The actual general singular-model finite-energy chord on the whole segment -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularGeodesicGeneralEnergyAffinity

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelEnergyTruncation
  SingularPerronCanonicalTruncationEnergy SingularGeodesicEnergyAffineLimits

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual same-type affinity at the genuine canonical truncations and their actual three energy limits give the full singularity-order E1 chord without any stage-affinity premise. -/
theorem toReal_energy_finiteGeodesic_eq_chord (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal =
      (1 - t) * (energy θ φ hφ u₀).toReal + t * (energy θ φ hφ u₁).toReal := by
  apply eq_chord_of_tendsto (toReal_energy_tendsto_truncatedGeodesic omega hu₀ hu₁ ht)
    (toReal_energy_tendsto_endpoint_truncation omega hu₀)
    (toReal_energy_tendsto_endpoint_truncation omega hu₁)
  intro j
  have hE₀ := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₀.1.plurisubharmonic hu₀.1.relativePSHPreceq.2 j
  have hE₁ := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₁.1.plurisubharmonic hu₁.1.relativePSHPreceq.2 j
  exact SingularPerronEnergyAffinity.toReal_energy_finiteGeodesic_eq_chord omega
    (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega hE₀)
    (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega hE₁)
    hE₀ hE₁ ht

/-- Genuine E1 realification transfers the actual full finite-energy chord to the defining extended energy for an arbitrarily singular reference. -/
theorem energy_finiteGeodesic_eq_chord (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t) =
      ((1 - t : ℝ) : EReal) * energy θ φ hφ u₀ + (t : EReal) * energy θ φ hφ u₁ := by
  have h := congrArg (fun r : ℝ => (r : EReal))
    (toReal_energy_finiteGeodesic_eq_chord omega hu₀ hu₁ ht)
  simpa only [EReal.coe_add, EReal.coe_mul,
    SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hu₀,
    SingularModelFiniteEnergyPreceq.coe_toReal_energy omega hu₁,
    SingularModelFiniteEnergyPreceq.coe_toReal_energy omega
      (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht)] using h

/-- The actual endpoint-completed general E1 Perron segment has its genuine finite real endpoint chord on the entire closed interval. -/
theorem toReal_energy_closedSubgeodesicSlice_eq_chord (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (energy θ φ hφ (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t)).toReal =
      (1 - t) * (energy θ φ hφ u₀).toReal + t * (energy θ φ hφ u₁).toReal := by
  by_cases h0 : t = 0
  · subst t
    simp only [closedSubgeodesicSlice_zero, sub_zero, one_mul, zero_mul, add_zero]
  by_cases h1 : t = 1
  · subst t
    simp only [closedSubgeodesicSlice_one, sub_self, zero_mul, one_mul, zero_add]
  have hI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  rw [closedSubgeodesicSlice_eq_curve hI]
  exact toReal_energy_finiteGeodesic_eq_chord omega hu₀ hu₁ hI

/-- The defining extended model energy is affine on the actual closed Perron segment for all genuine full singularity-order finite-energy endpoints and any singular model. -/
theorem energy_closedSubgeodesicSlice_eq_chord (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    energy θ φ hφ (closedSubgeodesicSlice (finiteGeodesic θ.val u₀ u₁) u₀ u₁ t) =
      ((1 - t : ℝ) : EReal) * energy θ φ hφ u₀ + (t : EReal) * energy θ φ hφ u₁ := by
  by_cases h0 : t = 0
  · subst t
    simp only [closedSubgeodesicSlice_zero, sub_zero, EReal.coe_one, EReal.coe_zero,
      one_mul, zero_mul, add_zero]
  by_cases h1 : t = 1
  · subst t
    simp only [closedSubgeodesicSlice_one, sub_self, EReal.coe_one, EReal.coe_zero,
      zero_mul, one_mul, zero_add]
  have hI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  rw [closedSubgeodesicSlice_eq_curve hI]
  exact energy_finiteGeodesic_eq_chord omega hu₀ hu₁ hI

end

end SGPT.Foundations.Analysis.Pending.SingularGeodesicGeneralEnergyAffinity
