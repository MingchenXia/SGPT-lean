import SGPT.Foundations.Analysis.Pending.SingularModelEnergyTruncation
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteRealEnergy
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicDecreasingEndpoints
import SGPT.Foundations.Analysis.Pending.RelativePreceqStatements

set_option autoImplicit false

/-! # Actual canonical endpoint truncations and Perron energy limits over singular models -/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalTruncationEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  RelativePreceqClasses SingularModelEnergyTruncation MongeAmpereEnergyDecreasing

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The actual Perron curve of the two genuine extended-real endpoint truncations. -/
def truncatedGeodesic (θ : SmoothRealForm n M 2) (φ u₀ u₁ : M → EReal)
    (j : ℕ) : ℝ → M → EReal :=
  finiteGeodesic θ (truncation φ u₀ j) (truncation φ u₁ j)

/-- Actual endpoint maxima and actual Perron order make the canonical stage curves decreasing at every time and point. -/
theorem truncatedGeodesic_antitone (θ : SmoothRealForm n M 2) (φ u₀ u₁ : M → EReal)
    (t : ℝ) (x : M) : Antitone (fun j => truncatedGeodesic θ φ u₀ u₁ j t x) := by
  intro i j hij
  exact finiteGeodesic_mono (fun y => truncation_antitone φ u₀ y hij)
    (fun y => truncation_antitone φ u₁ y hij) t x

variable [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [ConnectedSpace M] {θ : ClosedRealOneOneForm n M}
  {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}

/-- Genuine singular-reference truncations and actual finite-type Perron producers give every actual interior stage slice the reference's actual singularity type. -/
theorem relativeEInfinity_truncatedGeodesic (omega : KahlerBackground n M)
    (hφ : IsModelPotential θ φ)
    (hu₀ : RelativePSHPreceq θ φ u₀) (hu₁ : RelativePSHPreceq θ φ u₁)
    (j : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeEInfinity θ φ (truncatedGeodesic θ.val φ u₀ u₁ j t) :=
  FiniteGeodesicsFullMassAnyDim.relativeEInfinity_finiteGeodesic omega θ φ _ _ hφ
    (relativeEInfinity_truncation hφ.plurisubharmonic hu₀.1 hu₀.2 j)
    (relativeEInfinity_truncation hφ.plurisubharmonic hu₁.1 hu₁.2 j) t ht

/-- Actual finite-type-to-E1 inclusion produces genuine finite energy of every canonical stage slice over an arbitrary singular model. -/
theorem relativeFiniteEnergyPreceq_truncatedGeodesic (omega : KahlerBackground n M)
    (hu₀ : RelativePSHPreceq θ φ u₀) (hu₁ : RelativePSHPreceq θ φ u₁)
    (j : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFiniteEnergyPreceq θ φ (truncatedGeodesic θ.val φ u₀ u₁ j t) hφ :=
  RelativePreceqStatements.relativeFiniteEnergyPreceq_of_relativeEInfinity omega
    (relativeEInfinity_truncatedGeodesic omega hφ hu₀ hu₁ j ht)

/-- Actual canonical truncated Perron curves tend to the actual original singular Perron curve, with subgeodesic witnesses internally produced from genuine endpoint classes. -/
theorem tendsto_truncatedGeodesic (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) (t : ℝ) (x : M) :
    Tendsto (fun j => truncatedGeodesic θ.val φ u₀ u₁ j t x) atTop
      (𝓝 (finiteGeodesic θ.val u₀ u₁ t x)) := by
  have hE₀ (j : ℕ) := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₀.1.plurisubharmonic hu₀.1.relativePSHPreceq.2 j
  have hE₁ (j : ℕ) := relativeEInfinity_truncation hφ.plurisubharmonic
    hu₁.1.plurisubharmonic hu₁.1.relativePSHPreceq.2 j
  exact FiniteGeodesicDecreasingEndpoints.tendsto_finiteGeodesic_of_antitone
    (finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hu₀.1 hu₁.1)
    (fun j => (hE₀ j).1) (fun j => (hE₁ j).1)
    (truncation_antitone φ u₀) (truncation_antitone φ u₁)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)
    (fun j => (FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity
      omega θ φ _ _ hφ (hE₀ j) (hE₁ j)).2.2.1) t x

/-- Genuine singular-model decreasing energy continuity gives actual extended-energy convergence of canonical Perron truncations. -/
theorem energy_tendsto_truncatedGeodesic (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun j => energy θ φ hφ (truncatedGeodesic θ.val φ u₀ u₁ j t)) atTop
      (𝓝 (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t))) :=
  SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone omega θ hφ
    (fun j => (relativeEInfinity_truncatedGeodesic omega hφ hu₀.1.relativePSHPreceq
      hu₁.1.relativePSHPreceq j ht).1)
    (relativeEInfinity_truncatedGeodesic omega hφ hu₀.1.relativePSHPreceq
      hu₁.1.relativePSHPreceq 0 ht).2.1
    (truncatedGeodesic_antitone θ.val φ u₀ u₁ t)
    (tendsto_truncatedGeodesic omega hu₀ hu₁ t)

/-- Actual finite limit energy allows real energy convergence as well, without a bounded reference or an affinity assumption. -/
theorem toReal_energy_tendsto_truncatedGeodesic (omega : KahlerBackground n M)
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun j => (energy θ φ hφ (truncatedGeodesic θ.val φ u₀ u₁ j t)).toReal) atTop
      (𝓝 (energy θ φ hφ (finiteGeodesic θ.val u₀ u₁ t)).toReal) :=
  SingularModelFiniteRealEnergy.toReal_energy_tendsto_of_antitone omega
    (fun j => (relativeEInfinity_truncatedGeodesic omega hφ hu₀.1.relativePSHPreceq
      hu₁.1.relativePSHPreceq j ht).1)
    (relativeEInfinity_truncatedGeodesic omega hφ hu₀.1.relativePSHPreceq
      hu₁.1.relativePSHPreceq 0 ht).2.1
    (truncatedGeodesic_antitone θ.val φ u₀ u₁ t)
    (tendsto_truncatedGeodesic omega hu₀ hu₁ t)
    (relativeFiniteEnergyPreceq_finiteGeodesic omega hu₀ hu₁ ht)

end

end SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalTruncationEnergy
