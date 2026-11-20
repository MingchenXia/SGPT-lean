import SGPT.Foundations.Analysis.Pending.ThetaPotentialCoordinateDistributions
import SGPT.Foundations.Analysis.Pending.CompactDdcCoordinateExpansion

set_option autoImplicit false

/-! # Natural theta potentials produce full local positive currents and actual compact pairings -/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.NaturalThetaPshFullCurrentTests

open FirstPass GlobalCurrentPotentials ThetaPshChartLimitGluing
  ThetaPotentialCoordinateDistributions ScalarLeviPositiveCurrent LocalPositiveCurrentGluing
  LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalSmoothScalarCurrents
  CompactVariableCurrentTests ScalarFullTestTranspose StronglyPositiveForms LocalCurrentLebesgue

attribute [local instance] LocalCurrentLebesgue.addCommGroupFormSpan

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- Full local current positivity is produced from the genuine theta potential itself. -/
theorem exists_full_positive_local_current
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal) (hu : IsThetaPshPotential θ u)
    (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)) (hz : z ∈ e.val.target) :
    ∃ (W : Opens (ComplexModel (m + 1))) (hW : W ≤ chartTarget e)
      (ρ : ComplexModel (m + 1) → ℝ) (hpot : IsSmoothLocalPotential θ e W ρ),
      z ∈ W ∧ IsPositive
        (ddc (scalarTopCurrent (restrictDistribution
          (potentialCoordinateDistribution (stdOrthonormalBasis ℝ (ComplexModel (m + 1))).toBasis
            θ u hu e) hW)) + ddcWedge (oneCurrent W) hpot.2.2.1) := by
  let b := (stdOrthonormalBasis ℝ (ComplexModel (m + 1))).toBasis
  have hvol : b.addHaar = volume :=
    (stdOrthonormalBasis ℝ (ComplexModel (m + 1))).addHaar_eq_volume
  have hlocal := isLocallyThetaPshDistribution_potentialCoordinateDistribution b θ u hu e
  rw [hvol] at hlocal
  obtain ⟨W, hW, ρ, hρ, hzW, hpot, hLevi⟩ := hlocal z hz
  let T := restrictDistribution (potentialCoordinateDistribution b θ u hu e) hW
  have hpos := isPositive_ddc_scalarTopCurrent hLevi
  have hadd : scalarTopCurrent (T + regularDistribution volume ρ hρ) =
      scalarTopCurrent T + scalarTopCurrent (regularDistribution volume ρ hρ) := by
    ext γ φ
    simp only [scalarTopCurrent_apply, LinearMap.add_apply, _root_.add_apply, mul_add]
  change IsPositive (ddc (scalarTopCurrent (T + regularDistribution volume ρ hρ))) at hpos
  rw [hadd, ddc_add, ddc_scalarTopCurrent_regularDistribution_eq_ddcWedge hpot.2.2.1] at hpos
  exact ⟨W, hW, ρ, hpot, hzW, hpos⟩

/-- The original unbounded potential has its actual scalar integral against every strong test. -/
theorem exists_full_compact_test_integral_nonnegative
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal) (hu : IsThetaPshPotential θ u)
    (e : ComplexChart (m + 1) M) (z : ComplexModel (m + 1)) (hz : z ∈ e.val.target) :
    ∃ (W : Opens (ComplexModel (m + 1))) (_hW : W ≤ chartTarget e)
      (ρ : ComplexModel (m + 1) → ℝ) (hpot : IsSmoothLocalPotential θ e W ρ), z ∈ W ∧
      ∀ α : 𝓓(W, RealForm (m + 1) (2 * m)), (∀ x, α x ∈ spCone m) →
        0 ≤ (∫ x in (W : Set (ComplexModel (m + 1))),
          scalarAdjointTest α x * (chartFunction u e x).toReal) +
          ∑ i, ddcWedge (oneCurrent W) hpot.2.2.1
            (formBasis (m + 1) m i) (coeffTest α i) := by
  obtain ⟨W, hW, ρ, hpot, hzW, hpos⟩ := exists_full_positive_local_current θ u hu e z hz
  let b := (stdOrthonormalBasis ℝ (ComplexModel (m + 1))).toBasis
  have hvol : b.addHaar = volume :=
    (stdOrthonormalBasis ℝ (ComplexModel (m + 1))).addHaar_eq_volume
  have hUL0 := quasiPsh_chart_locallyIntegrable b (Nat.succ_pos m) u hu.quasiPshPotential e
  rw [hvol] at hUL0
  have hUL : LocallyIntegrableOn (fun x => (chartFunction u e x).toReal) W volume :=
    hUL0.mono_set hW
  have hdist : restrictDistribution (potentialCoordinateDistribution b θ u hu e) hW =
      regularDistribution volume (fun x => (chartFunction u e x).toReal) hUL := by
    rw [potentialCoordinateDistribution, restrictDistribution_regularDistribution]
    ext φ
    simp only [regularDistribution_apply]
    rw [hvol]
  refine ⟨W, hW, ρ, hpot, hzW, ?_⟩
  intro α hα
  have hp := pairing_nonnegative _ hpos α hα
  simp only [LinearMap.add_apply, _root_.add_apply, Finset.sum_add_distrib] at hp
  rw [ddc_scalarTopCurrent_full_test_transpose, hdist, regularDistribution_apply] at hp
  have hsupport : (∫ x in (W : Set (ComplexModel (m + 1))),
      scalarAdjointTest α x * (chartFunction u e x).toReal) =
      ∫ x, scalarAdjointTest α x * (chartFunction u e x).toReal := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hzero : scalarAdjointTest α x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx ((scalarAdjointTest α).tsupport_subset h))
    rw [hzero, zero_mul]
  rw [hsupport]
  exact hp

end SGPT.Foundations.Analysis.Pending.NaturalThetaPshFullCurrentTests
