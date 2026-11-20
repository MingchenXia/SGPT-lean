import SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalTruncationEnergy
import SGPT.Foundations.Analysis.Pending.SingularModelDarvasBasic

set_option autoImplicit false

/-! # Actual endpoint energy limits and native Darvas convergence of singular Perron truncations -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalMetricLimit

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelEnergyTruncation MongeAmpereEnergyDecreasing
  SingularPerronCanonicalTruncationEnergy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
  {hφ : IsModelPotential θ φ}

/-- Genuine singular-reference endpoint maxima internally produce actual finite energy in the full singularity-order class. -/
theorem relativeFiniteEnergyPreceq_truncation (omega : KahlerBackground n M)
    (hu : RelativePSHPreceq θ φ u) (j : ℕ) :
    RelativeFiniteEnergyPreceq θ φ (truncation φ u j) hφ :=
  RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
    (relativeEInfinity_truncation hφ.plurisubharmonic hu.1 hu.2 j)

/-- The actual defining extended energies of canonical endpoint truncations tend to the actual original energy over a singular model. -/
theorem energy_tendsto_endpoint_truncation (omega : KahlerBackground n M)
    (hu : RelativePSHPreceq θ φ u) :
    Tendsto (fun j => energy θ φ hφ (truncation φ u j)) atTop
      (𝓝 (energy θ φ hφ u)) :=
  SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone omega θ hφ
    (fun j => (relativeEInfinity_truncation hφ.plurisubharmonic hu.1 hu.2 j).1)
    (relativeEInfinity_truncation hφ.plurisubharmonic hu.1 hu.2 0).2.1
    (truncation_antitone φ u)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)

/-- Actual finite endpoint energy gives genuine real energy convergence of the actual endpoint truncations, without a bounded model or affinity assumption. -/
theorem toReal_energy_tendsto_endpoint_truncation (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) :
    Tendsto (fun j => (energy θ φ hφ (truncation φ u j)).toReal) atTop
      (𝓝 (energy θ φ hφ u).toReal) :=
  SingularModelFiniteRealEnergy.toReal_energy_tendsto_of_antitone omega
    (fun j => (relativeEInfinity_truncation hφ.plurisubharmonic
      hu.1.plurisubharmonic hu.1.relativePSHPreceq.2 j).1)
    (relativeEInfinity_truncation hφ.plurisubharmonic
      hu.1.plurisubharmonic hu.1.relativePSHPreceq.2 0).2.1
    (truncation_antitone φ u)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top) hu

omit [BorelSpace M] in
/-- The original actual rooftop-defined Darvas distance to an actual canonical endpoint truncation is its actual real energy gap. -/
theorem relativeD1_endpoint_truncation_eq_energy_sub
    (hu : IsThetaPshPotential θ.val u) (j : ℕ) :
    relativeD1 θ φ hφ (truncation φ u j) u =
      (energy θ φ hφ (truncation φ u j)).toReal - (energy θ φ hφ u).toReal := by
  rw [relativeD1_comm θ φ hφ]
  exact relativeD1_eq_sub_of_le hu (le_truncation φ u j)

/-- Genuine internally produced finite-energy endpoint truncations converge to the actual endpoint in its original Darvas distance. -/
theorem relativeD1_endpoint_truncation_tendsto_zero (omega : KahlerBackground n M)
    (hu : RelativeFiniteEnergyPreceq θ φ u hφ) :
    Tendsto (fun j => relativeD1 θ φ hφ (truncation φ u j) u) atTop (𝓝 0) :=
  SingularModelDarvasBasic.relativeD1_tendsto_zero_of_antitone omega
    (fun j => relativeFiniteEnergyPreceq_truncation omega hu.1.relativePSHPreceq j) hu
    (truncation_antitone φ u)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)

variable [ConnectedSpace M] {u₀ u₁ : M → EReal}

/-- Actual endpoint order and genuine Perron slices identify the native Darvas distance of every canonical stage slice with its actual real energy gap. -/
theorem relativeD1_truncatedGeodesic_eq_energy_sub (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) (j : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    relativeD1 θ φ hφ (truncatedGeodesic θ.val φ u₀ u₁ j t)
      (finiteGeodesic θ.val u₀ u₁ t) =
    (energy θ φ hφ (truncatedGeodesic θ.val φ u₀ u₁ j t)).toReal -
      (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal := by
  rw [relativeD1_comm θ φ hφ]
  exact relativeD1_eq_sub_of_le
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht).1.plurisubharmonic
    (finiteGeodesic_mono (le_truncation φ u₀ j) (le_truncation φ u₁ j) t)

/-- Actual canonical Perron stages converge to the genuine singular finite-energy Perron slice in the original native Darvas distance. -/
theorem relativeD1_truncatedGeodesic_tendsto_zero (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun j => relativeD1 θ φ hφ (truncatedGeodesic θ.val φ u₀ u₁ j t)
      (finiteGeodesic θ.val u₀ u₁ t)) atTop (𝓝 0) :=
  SingularModelDarvasBasic.relativeD1_tendsto_zero_of_antitone omega
    (fun j => relativeFiniteEnergyPreceq_truncatedGeodesic omega
      hu₀.1.relativePSHPreceq hu₁.1.relativePSHPreceq j ht)
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht)
    (truncatedGeodesic_antitone θ.val φ u₀ u₁ t)
    (tendsto_truncatedGeodesic omega hu₀ hu₁ t)

end

end SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalMetricLimit
