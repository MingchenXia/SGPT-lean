import SGPT.Foundations.Analysis.Pending.SingularModelNormalizedMixedCutoff
import SGPT.Foundations.Analysis.Pending.SingularModelFiniteEnergyMixedCocycle

set_option autoImplicit false

/-! # Scaled actual cutoff energy from the mixed mass-deficit limits in SGPT (4.47)

These are all-real-parameter energy limits. Identification with the radial
energy of a canonical ray requires the separate actual ray/affinity producers.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularModelScaledCutoffEnergy

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance DiagonalMass
  SingularModelNormalizedMixedCutoff SingularModelFiniteEnergyMixedGap
  SingularModelFiniteEnergyMixedCocycle SingularModelEnergyCocycle

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}

/-- The actual finite-type scaled cutoff energy is the average mixed mass deficit. -/
theorem tendsto_scaled_relativeEnergyOfMinimalType_realCutoff
    (omega : KahlerBackground n M)
    (hp : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ) :
    Tendsto (fun C : ℝ => relativeEnergyOfMinimalType θ φ (realCutoff φ u C) hp
      (relativeEInfinity_realCutoff hp hu (MoreSingularOn.of_le fun x _ => hup x) C).1 / C)
      atTop (𝓝 ((∑ k : Fin (n + 1),
        ((endpointMixedMass θ φ u hp hu k).toReal - (diagonalPotentialMass θ φ hp).toReal)) /
          (n + 1 : ℝ))) := by
  classical
  let ht := fun C => relativeEInfinity_realCutoff hp hu (MoreSingularOn.of_le fun x _ => hup x) C
  have hk (k : Fin (n + 1)) :
      Tendsto (fun C : ℝ => relativeEnergyTerm θ φ (realCutoff φ u C) hp (ht C).1 k / C)
        atTop (𝓝 ((endpointMixedMass θ φ u hp hu k).toReal -
          (diagonalPotentialMass θ φ hp).toReal)) := by
    simpa only [relativeEnergyTerm, endpointMixedMass, endpointMixedMeasure_eq_binaryMixedMeasure, Measure.real] using
      tendsto_normalized_binaryMixedMeasure_realCutoff omega hp hu hup
        (fun i => decide (i.val < k.val))
  have hs := (tendsto_finsetSum Finset.univ fun k _ => hk k).div_const (n + 1 : ℝ)
  apply hs.congr'
  apply Eventually.of_forall
  intro C
  change (∑ k : Fin (n + 1), relativeEnergyTerm θ φ (realCutoff φ u C) hp (ht C).1 k / C) /
    (n + 1 : ℝ) = relativeEnergyOfMinimalType θ φ (realCutoff φ u C) hp (ht C).1 / C
  rw [← Finset.sum_div]
  unfold relativeEnergyOfMinimalType
  ring

/-- The same actual cutoff limit holds for the genuine extended model energy,
using internally produced same type and proved extension agreement at every C. -/
theorem tendsto_scaled_toReal_energy_realCutoff (omega : KahlerBackground n M)
    (hp : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u) (hup : u ≤ φ) :
    Tendsto (fun C : ℝ => (energy θ φ hp (realCutoff φ u C)).toReal / C)
      atTop (𝓝 ((∑ k : Fin (n + 1),
        ((endpointMixedMass θ φ u hp.plurisubharmonic hu k).toReal -
          (diagonalPotentialMass θ φ hp.plurisubharmonic).toReal)) / (n + 1 : ℝ))) := by
  have h := tendsto_scaled_relativeEnergyOfMinimalType_realCutoff omega hp.plurisubharmonic hu hup
  apply h.congr'
  apply Eventually.of_forall
  intro C
  have he := energy_eq_of_relativeEInfinity omega θ hp
    (relativeEInfinity_realCutoff hp.plurisubharmonic hu (MoreSingularOn.of_le fun x _ => hup x) C)
  have her := congrArg EReal.toReal he
  simp only [EReal.toReal_coe] at her
  exact congrArg (fun z : ℝ => z / C) her.symm

end

end SGPT.Foundations.Analysis.Pending.SingularModelScaledCutoffEnergy
