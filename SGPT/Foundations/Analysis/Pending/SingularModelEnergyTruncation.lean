import SGPT.Foundations.Analysis.Pending.SingularModelEnergyExtendedContinuity

set_option autoImplicit false

/-!
# Canonical truncation of actual singular-model energy

Xia SGPT PDF0118, PDF0120--0121: max(u, phi-j) produces genuine
same-type potentials for an arbitrary singular reference. Their actual
finite energy formulas converge to the defining extended energy.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyTruncation

open FirstPass FirstPass.PositiveClasses RelativeEnergy RelativeDarvasDistance
  MongeAmpereEnergyDecreasing SingularModelEnergyCocycle

noncomputable section

/-- Singular-reference tails and their maxima converge at finite points and poles alike. -/
theorem tendsto_truncation_of_ne_top {X : Type*} {φ u : X → EReal}
    (hφ : ∀ x, φ x ≠ ⊤) (x : X) :
    Tendsto (fun j => truncation φ u j x) atTop (𝓝 (u x)) := by
  have htail : Tendsto (fun j : ℕ => φ x - ((j : ℝ) : EReal)) atTop (𝓝 ⊥) := by
    by_cases hbot : φ x = ⊥
    · simp [hbot]
    · rw [EReal.tendsto_nhds_bot_iff_real]
      intro r
      obtain ⟨N, hN⟩ := exists_nat_gt ((φ x).toReal - r)
      filter_upwards [eventually_ge_atTop N] with j hj
      rw [← EReal.coe_toReal (hφ x) hbot, ← EReal.coe_sub]
      apply EReal.coe_lt_coe_iff.mpr
      have hNj : (N : ℝ) ≤ j := by exact_mod_cast hj
      linarith
  have hc : Tendsto (fun _ : ℕ => u x) atTop (𝓝 (u x)) := tendsto_const_nhds
  simpa [truncation] using hc.max htail

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Max truncations by a singular genuine reference produce genuine E-infinity potentials. -/
theorem relativeEInfinity_truncation {θ : ClosedRealOneOneForm n M} {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (huφ : MoreSingularOn u φ univ) (j : ℕ) :
    RelativeEInfinity θ φ (truncation φ u j) := by
  have hs : SameSingularityTypeOn (fun x => φ x - ((j : ℝ) : EReal)) φ univ := by
    simpa only [EReal.coe_neg, ← sub_eq_add_neg] using
      sameSingularityTypeOn_add_const φ univ (-(j : ℝ))
  refine ⟨IsThetaPshPotential.max hu (hφ.sub_const (j : ℝ)), ?_⟩
  exact ⟨DominationPrincipleReduction.moreSingularOn_max huφ hs.1,
    hs.2.trans (MoreSingularOn.of_le fun x _ => le_max_right _ _)⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Actual finite truncation energy formulas converge for every singular model reference. -/
theorem energy_tendsto_truncation (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u)
    (huφ : MoreSingularOn u φ univ) :
    Tendsto (fun j => (relativeEnergyOfMinimalType θ φ (truncation φ u j)
      hφ.plurisubharmonic (relativeEInfinity_truncation hφ.plurisubharmonic hu huφ j).1 : EReal))
      atTop (𝓝 (energy θ φ hφ u)) := by
  have h := SingularModelEnergyExtendedContinuity.energy_tendsto_of_antitone omega θ hφ
    (fun j => (relativeEInfinity_truncation hφ.plurisubharmonic hu huφ j).1)
    (relativeEInfinity_truncation hφ.plurisubharmonic hu huφ 0).2.1
    (truncation_antitone φ u)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)
  simpa only [energy_eq_of_relativeEInfinity omega θ hφ
    (relativeEInfinity_truncation hφ.plurisubharmonic hu huφ _)] using h

/-- The actual defining extended energy is the infimum of singular same-type truncation formulas. -/
theorem energy_eq_iInf_truncation (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsModelPotential θ φ) (hu : IsThetaPshPotential θ.val u)
    (huφ : MoreSingularOn u φ univ) :
    energy θ φ hφ u = ⨅ j, (relativeEnergyOfMinimalType θ φ (truncation φ u j)
      hφ.plurisubharmonic (relativeEInfinity_truncation hφ.plurisubharmonic hu huφ j).1 : EReal) := by
  have h := (SingularModelEnergyExtendedContinuity.energy_iInf_of_antitone omega θ hφ
    (fun j => (relativeEInfinity_truncation hφ.plurisubharmonic hu huφ j).1)
    (relativeEInfinity_truncation hφ.plurisubharmonic hu huφ 0).2.1
    (truncation_antitone φ u)
    (tendsto_truncation_of_ne_top hφ.plurisubharmonic.1.quasiPlurisubharmonic.ne_top)).symm
  simpa only [energy_eq_of_relativeEInfinity omega θ hφ
    (relativeEInfinity_truncation hφ.plurisubharmonic hu huφ _)] using h

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyTruncation
