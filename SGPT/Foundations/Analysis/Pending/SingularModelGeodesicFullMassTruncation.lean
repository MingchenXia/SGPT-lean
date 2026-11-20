import SGPT.Foundations.Analysis.Pending.SingularGeodesicGeneralEnergyAffinity

set_option autoImplicit false

/-!
# Actual full-mass Perron truncations over arbitrary singular models

Independent extension of Xia SGPT PDF0173's canonical decreasing-limit
argument to full-mass endpoints, before endpoint energy finiteness is
known. Actual finite-type stage geometry, actual defining energy limits,
and the proved stage chord give the genuine extended full-mass chord.
No bounded reference, endpoint E1 or target affinity is a premise.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelGeodesicFullMassTruncation

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelEnergyTruncation MongeAmpereEnergyDecreasing
  SingularPerronCanonicalTruncationEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Actual canonical Perron truncations converge pointwise for genuine full-mass endpoints, without requiring finite endpoint energy. -/
theorem tendsto_truncatedGeodesic_of_fullMass (omega : KahlerBackground n M)
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ) (t : ℝ) (x : M) :
    Tendsto (fun j => truncatedGeodesic θ.val φ u₀ u₁ j t x) atTop
      (𝓝 (finiteGeodesic θ.val u₀ u₁ t x)) := by
  have hE₀ (j : ℕ) := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₀.plurisubharmonic hu₀.relativePSHPreceq.2 j
  have hE₁ (j : ℕ) := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₁.plurisubharmonic hu₁.relativePSHPreceq.2 j
  exact FiniteGeodesicDecreasingEndpoints.tendsto_finiteGeodesic_of_antitone
    (finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hu₀ hu₁)
    (fun j => (hE₀ j).1) (fun j => (hE₁ j).1)
    (truncation_antitone φ u₀) (truncation_antitone φ u₁)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)
    (fun j => (FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity
      omega θ φ _ _ hφ (hE₀ j) (hE₁ j)).2.2.1) t x

/-- Genuine full-mass geometry gives the actual defining extended energy limit of interior Perron truncations, including a possibly negative-infinite limiting energy. -/
theorem energy_tendsto_truncatedGeodesic_of_fullMass (omega : KahlerBackground n M)
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun j => energy θ φ hφ (truncatedGeodesic θ.val φ u₀ u₁ j t)) atTop
      (𝓝 (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t))) :=
  SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone omega θ hφ
    (fun j => (relativeEInfinity_truncatedGeodesic omega hφ hu₀.relativePSHPreceq
      hu₁.relativePSHPreceq j ht).1)
    (relativeEInfinity_truncatedGeodesic omega hφ hu₀.relativePSHPreceq
      hu₁.relativePSHPreceq 0 ht).2.1
    (truncatedGeodesic_antitone θ.val φ u₀ u₁ t)
    (tendsto_truncatedGeodesic_of_fullMass omega hu₀ hu₁ t)

omit [ConnectedSpace M] in
private theorem endpoint_energy_limit (omega : KahlerBackground n M)
    {u : M → EReal} (hu : RelativePSHPreceq θ φ u) :
    Tendsto (fun j => energy θ φ hφ (truncation φ u j)) atTop
      (𝓝 (energy θ φ hφ u)) :=
  SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone omega θ hφ
    (fun j => (relativeEInfinity_truncation hφ.plurisubharmonic hu.1 hu.2 j).1)
    (relativeEInfinity_truncation hφ.plurisubharmonic hu.1 hu.2 0).2.1
    (truncation_antitone φ u)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)

/-- True canonical finite-type stage affinity and actual three defining energy limits give the actual extended energy chord for arbitrary full-mass endpoints, allowing negative-infinite energies. -/
theorem energy_finiteGeodesic_eq_chord_of_fullMass (omega : KahlerBackground n M)
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t) =
      ((1 - t : ℝ) : EReal) * energy θ φ hφ u₀ +
        (t : EReal) * energy θ φ hφ u₁ := by
  have hlim := FiniteGeodesicDecreasingEndpoints.tendsto_eRealChord
    (endpoint_energy_limit (hφ := hφ) omega hu₀.relativePSHPreceq)
    (endpoint_energy_limit (hφ := hφ) omega hu₁.relativePSHPreceq)
    (energy_ne_top_of_preceq (hφ := hφ) hu₀.relativePSHPreceq)
    (energy_ne_top_of_preceq (hφ := hφ) hu₁.relativePSHPreceq)
    (Ioo_subset_Icc_self ht)
  apply tendsto_nhds_unique (energy_tendsto_truncatedGeodesic_of_fullMass omega hu₀ hu₁ ht)
  apply hlim.congr
  intro j
  have hE₀ := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₀.plurisubharmonic hu₀.relativePSHPreceq.2 j
  have hE₁ := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₁.plurisubharmonic hu₁.relativePSHPreceq.2 j
  exact (SingularGeodesicGeneralEnergyAffinity.energy_finiteGeodesic_eq_chord omega
    (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega hE₀)
    (RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega hE₁) ht).symm

/-- A genuinely finite midpoint and right endpoint force finite energy of the genuinely full-mass left endpoint; no endpoint affinity or limit certificate is an input. -/
theorem relativeFiniteEnergyPreceq_left_of_midpoint (omega : KahlerBackground n M)
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (hmid : RelativeFiniteEnergyPreceq θ φ (finiteGeodesic θ.val u₀ u₁ (1 / 2)) hφ) :
    RelativeFiniteEnergyPreceq θ φ u₀ hφ := by
  refine (SingularModelFiniteEnergyPreceq.relativeFiniteEnergyPreceq_iff_bot_lt_energy omega hu₀).2 ?_
  by_contra hbot
  rw [not_lt, le_bot_iff] at hbot
  have h := energy_finiteGeodesic_eq_chord_of_fullMass omega hu₀ hu₁.1
    (t := 1 / 2) ⟨by norm_num, by norm_num⟩
  rw [hbot, EReal.coe_mul_bot_of_pos (by norm_num), EReal.bot_add] at h
  have hb := SingularModelFiniteEnergyPreceq.bot_lt_energy omega hmid
  rw [h] at hb
  exact lt_irrefl _ hb

end

end SGPT.Foundations.Analysis.Pending.SingularModelGeodesicFullMassTruncation
