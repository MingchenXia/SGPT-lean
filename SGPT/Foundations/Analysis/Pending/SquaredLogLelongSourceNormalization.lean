import SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
import Mathlib.Data.ENNReal.Inv

set_option autoImplicit false

/-! # Independent source squared-log growth and the literal native normalization -/

open Set Filter
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- The actual source growth formula, including its explicit zero-dimensional
convention. This is defined from squared logarithmic bounds, not from the
native reader by division. -/
def squaredLogLelongNumber (u : M → EReal) (x : M) : ℝ≥0∞ :=
  if n = 0 then 0 else
    ⨆ (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
        u y ≤ (((γ : ℝ) * Real.log
          (‖(complexChartAt (n := n) x).val y -
            (complexChartAt (n := n) x).val x‖ ^ 2) + C : ℝ) : EReal)),
      (γ : ℝ≥0∞)

/-- The two independently defined growth suprema have factor two, without
realifying the values of the original weight or either extended supremum. -/
theorem lelongNumber_eq_two_mul_squaredLog (hn : n ≠ 0) (u : M → EReal) (x : M) :
    lelongNumber (n := n) u x = 2 * squaredLogLelongNumber (n := n) u x := by
  apply le_antisymm
  · unfold lelongNumber
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨C, hC⟩ := hγ
    let δ : ℝ≥0 := γ / 2
    have hδ : (γ : ℝ) = 2 * (δ : ℝ) := by
      simp only [δ, NNReal.coe_div, NNReal.coe_ofNat]
      ring
    have hδle : (δ : ℝ≥0∞) ≤ squaredLogLelongNumber (n := n) u x := by
      rw [squaredLogLelongNumber, if_neg hn]
      refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
          u y ≤ (((γ : ℝ) * Real.log
            (‖(complexChartAt (n := n) x).val y -
              (complexChartAt (n := n) x).val x‖ ^ 2) + C : ℝ) : EReal)) =>
          (γ : ℝ≥0∞)) δ ⟨C, ?_⟩ le_rfl
      filter_upwards [hC] with y hy
      have heq : (δ : ℝ) * Real.log
          (‖(complexChartAt (n := n) x).val y -
            (complexChartAt (n := n) x).val x‖ ^ 2) + C =
          (γ : ℝ) * Real.log ‖(complexChartAt (n := n) x).val y -
            (complexChartAt (n := n) x).val x‖ + C := by
        rw [Real.log_pow, hδ]
        norm_num
        ring
      rwa [heq]
    have hcast : (γ : ℝ≥0∞) = 2 * (δ : ℝ≥0∞) := by
      exact_mod_cast hδ
    rw [hcast]
    gcongr
  · rw [squaredLogLelongNumber, if_neg hn, ENNReal.mul_iSup]
    refine iSup_le fun γ => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hγ => ?_
    obtain ⟨C, hC⟩ := hγ
    have hcast : 2 * (γ : ℝ≥0∞) = ((2 * γ : ℝ≥0) : ℝ≥0∞) := by
      norm_cast
    rw [hcast]
    unfold lelongNumber
    refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
        u y ≤ (((γ : ℝ) * Real.log
          ‖(complexChartAt (n := n) x).val y -
            (complexChartAt (n := n) x).val x‖ + C : ℝ) : EReal)) =>
        (γ : ℝ≥0∞)) (2 * γ) ⟨C, ?_⟩ le_rfl
    filter_upwards [hC] with y hy
    have heq : ((2 * γ : ℝ≥0) : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y -
          (complexChartAt (n := n) x).val x‖ + C =
        (γ : ℝ) * Real.log (‖(complexChartAt (n := n) x).val y -
          (complexChartAt (n := n) x).val x‖ ^ 2) + C := by
      rw [Real.log_pow]
      norm_num
      ring
    rwa [heq]

/-- Finite positive multiplication commutes with the whole-set reader,
including empty sets and infinite values. -/
theorem iInf_lelongNumber_eq_two_mul_squaredLog (hn : n ≠ 0)
    (u : M → EReal) (E : Set M) :
    (⨅ x ∈ E, lelongNumber (n := n) u x) =
      2 * ⨅ x ∈ E, squaredLogLelongNumber (n := n) u x := by
  simp_rw [lelongNumber_eq_two_mul_squaredLog hn,
    ← ENNReal.mul_iInf_of_ne (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]

/-- Whole-divisor order is unchanged by the source/native normalization;
the statement is literal on the same whole set, not on a local piece. -/
theorem iInf_lelongNumber_le_iff_squaredLog (hn : n ≠ 0)
    (u v : M → EReal) (E : Set M) :
    (⨅ x ∈ E, lelongNumber (n := n) v x) ≤
        ⨅ x ∈ E, lelongNumber (n := n) u x ↔
      (⨅ x ∈ E, squaredLogLelongNumber (n := n) v x) ≤
        ⨅ x ∈ E, squaredLogLelongNumber (n := n) u x := by
  rw [iInf_lelongNumber_eq_two_mul_squaredLog hn,
    iInf_lelongNumber_eq_two_mul_squaredLog hn]
  exact ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)

end
end SGPT.Foundations.Analysis.Pending.SquaredLogLelongSourceNormalization
