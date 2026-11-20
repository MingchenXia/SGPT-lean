import SGPT.Foundations.Analysis.Pending.MultiplierIdealLowerBound
import SGPT.Foundations.Analysis.Pending.MultiplierIdealUpperBound


set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.MultiplierIdealLimit

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.NonKahlerLocus FirstPass.BlowupSequences
  DemaillyApproximantDivisorialLelong FixedGermNormalOrder
  MultiplierIdealLowerBound MultiplierIdealUpperBound
  IntrinsicJacobianCoefficient

open scoped ENNReal NNReal

universe u

variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {π : Y → X} {E : Set Y} {u : X → EReal}

/-- Every positive integer bounds the manufactured ENTIRE multiplier coefficient
by the literal whole-prime raw reader, including infinite point values. -/
theorem actualMultiplierCoefficient_raw_generic_upper_bound
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) (p : ℕ) (hp : 0 < p) :
    (2 : ℝ≥0∞) * (actualMultiplierCoefficient hπ hE hu (show (0 : ℝ) < p by exact_mod_cast hp) : ℝ≥0∞) ≤
      ENNReal.ofReal (p : ℝ) *
        (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z) := by
  have hp0 : ENNReal.ofReal (p : ℝ) ≠ 0 := by positivity
  simp_rw [ENNReal.mul_iInf_of_ne hp0 ENNReal.ofReal_ne_top]
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  obtain ⟨Φ⟩ := DivisorFlattening.nonempty_of_regularAtDim (hE.2.2 y hy)
  have hb := originalStalkNormalOrder_pullback_multiplierIdeal_le_point hπ hu.1 Φ p hp
  rw [originalStalkNormalOrder_eq_actualMultiplierCoefficient hπ hE hu
    (show (0 : ℝ) < p by exact_mod_cast hp) y hy Φ] at hb
  simpa only [ENat.toENNReal_coe] using hb

/-- Level ONE of the actual strict lower bound internally rules out an infinite generic reader. -/
theorem rawGenericLelong_ne_top
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z) ≠ ⊤ := by
  have hb := actualMultiplierCoefficient_strict_raw_lelong_bound hπ hE hu
    (show (0 : ℝ) < 1 by norm_num)
  simp only [ENNReal.ofReal_one, one_mul] at hb
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb.le

/-- The produced ENTIRE original coefficients recover the finite raw reader along
EVERY positive integer, with the genuine fixed actual discrepancy error. -/
theorem tendsto_actualMultiplierCoefficient_ratio_real
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    Tendsto (fun n : ℕ =>
      (actualMultiplierCoefficient hπ hE hu (show (0 : ℝ) < (n + 1 : ℕ) by positivity) : ℝ) /
        (n + 1 : ℕ)) atTop
      (𝓝 ((⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z).toReal / 2)) := by
  let G : ℝ≥0∞ := ⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z
  let A : ℕ := representedLogDiscrepancy hπ hE
  let a : ℕ → ℕ := fun n => actualMultiplierCoefficient hπ hE hu
    (show (0 : ℝ) < (n + 1 : ℕ) by positivity)
  have hG : G ≠ ⊤ := rawGenericLelong_ne_top hπ hE hu
  have hbounds (n : ℕ) :
      G.toReal / 2 - (A : ℝ) / (n + 1 : ℕ) ≤ (a n : ℝ) / (n + 1 : ℕ) ∧
      (a n : ℝ) / (n + 1 : ℕ) ≤ G.toReal / 2 := by
    have hp : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hupp := actualMultiplierCoefficient_raw_generic_upper_bound hπ hE hu
      (n + 1) (Nat.succ_pos n)
    have hlow := actualMultiplierCoefficient_strict_raw_lelong_bound hπ hE hu hp
    have huppReal := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG) hupp
    have hlowReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlow.le
    have huR : 2 * (a n : ℝ) ≤ (n + 1 : ℕ) * G.toReal := by
      simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal hp.le] using huppReal
    have hlR : (n + 1 : ℕ) * G.toReal ≤ 2 * ((a n : ℝ) + (A : ℝ)) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp.le,
        ENNReal.toReal_ofReal (by positivity)] at hlowReal
      simpa only [Nat.cast_add, a, A, G] using hlowReal
    constructor
    · apply (le_div_iff₀ hp).mpr
      rw [sub_mul, div_mul_cancel₀ _ hp.ne']
      nlinarith
    · apply (div_le_iff₀ hp).mpr
      nlinarith
  have herr : Tendsto (fun n : ℕ => (A : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (A : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [mul_zero, mul_one_div] using h
  have hleft : Tendsto (fun n : ℕ => G.toReal / 2 - (A : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 (G.toReal / 2)) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := G.toReal / 2)).sub herr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hleft tendsto_const_nhds
  · intro n
    simpa only [a, Nat.cast_add, Nat.cast_one] using (hbounds n).1
  · intro n
    exact (hbounds n).2

/-- Literal extended ratios over ALL positive integers converge to the actual whole-prime raw half-reader. -/
theorem tendsto_actualMultiplierCoefficient_ratio
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    Tendsto (fun n : ℕ =>
      (actualMultiplierCoefficient hπ hE hu (show (0 : ℝ) < (n + 1 : ℕ) by positivity) : ℝ≥0∞) /
        (n + 1 : ℕ)) atTop
      (𝓝 ((⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z) / 2)) := by
  have hG := rawGenericLelong_ne_top hπ hE hu
  have hreal := tendsto_actualMultiplierCoefficient_ratio_real hπ hE hu
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hseq (n : ℕ) : ENNReal.ofReal
      ((actualMultiplierCoefficient hπ hE hu (show (0 : ℝ) < (n + 1 : ℕ) by positivity) : ℝ) /
        (n + 1 : ℕ)) =
      (actualMultiplierCoefficient hπ hE hu (show (0 : ℝ) < (n + 1 : ℕ) by positivity) : ℝ≥0∞) /
        (n + 1 : ℕ) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp only [ENNReal.ofReal_natCast]
  have htarget : ENNReal.ofReal
      ((⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z).toReal / 2) =
      (⨅ z ∈ E, lelongNumber (n := m + 1) (fun t => u (π t)) z) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_toReal hG]
    norm_num
  simpa only [Function.comp_def, hseq, htarget] using h

/-- The independently defined squared-log source reader is recovered by ALL integer ideals. -/
theorem tendsto_actualMultiplierCoefficient_ratio_squaredLog
    (hπ : AnalyticModificationLocalDiscrepancy.IsAnalyticModification (n := m + 1) π)
    (hE : IsClosedConnectedSubmanifold (m + 1) E m)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    Tendsto (fun n : ℕ =>
      (actualMultiplierCoefficient hπ hE hu (show (0 : ℝ) < (n + 1 : ℕ) by positivity) : ℝ≥0∞) /
        (n + 1 : ℕ)) atTop
      (𝓝 (⨅ z ∈ E, SquaredLogLelongSourceNormalization.squaredLogLelongNumber
        (n := m + 1) (fun t => u (π t)) z)) := by
  have h := tendsto_actualMultiplierCoefficient_ratio hπ hE hu
  rw [SquaredLogLelongSourceNormalization.iInf_lelongNumber_eq_two_mul_squaredLog
    (Nat.succ_ne_zero m)] at h
  have hc : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have ht : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  simpa only [mul_comm (2 : ℝ≥0∞), ENNReal.mul_div_cancel_right hc ht] using h

end SGPT.Foundations.Analysis.Pending.MultiplierIdealLimit
