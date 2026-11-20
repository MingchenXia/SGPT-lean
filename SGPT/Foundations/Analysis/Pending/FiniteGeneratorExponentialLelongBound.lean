import SGPT.Foundations.Analysis.Pending.ActualFiniteGeneratorLelongNormalization
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

set_option autoImplicit false

/-! # A literal point reader bound from finite exponential domination

Actual finite log identities preserve poles and give the point estimate
needed for a genuine finite weighted-family and Jacobian error consumer.
Reference: supplementary direct logarithmic-exponent calculation.
-/

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.FiniteGeneratorExponentialLelongBound

open FirstPass FirstPass.NonKahlerLocus

noncomputable section

/-- Actual finite exponential domination bounds the literal logarithmic
reader, with no PSH/holomorphy/nonzero-family or finiteness premise. -/
theorem lelongNumber_generatorLog_le_scaled_of_exp_domination
    {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] {x : M} {ψ : M → EReal}
    (g : Fin N → M → ℂ) {p : ℝ} (hp : 0 < p)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hdom : ∀ᶠ y in 𝓝 x, EReal.exp ((p : EReal) * ψ y) ≤
      C * ∑ i, ENNReal.ofReal (‖g i y‖ ^ 2)) :
    lelongNumber (n := n) (generatorLog g) x ≤
      ENNReal.ofReal p * lelongNumber (n := n) ψ x := by
  have hCtop : C + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hC, by simp⟩
  have hCzero : C + 1 ≠ 0 := by positivity
  let L : ℝ := (ENNReal.log (C + 1)).toReal
  have hlog : ENNReal.log (C + 1) = (L : EReal) :=
    (EReal.coe_toReal (fun h => hCtop (ENNReal.log_eq_top_iff.mp h))
      (fun h => hCzero (ENNReal.log_eq_bot_iff.mp h))).symm
  have hle : ∀ᶠ y in 𝓝 x, (p : EReal) * ψ y ≤ generatorLog g y + (L : EReal) := by
    filter_upwards [hdom] with y hy
    have hsum : (∑ i, ENNReal.ofReal (‖g i y‖ ^ 2)) =
        ENNReal.ofReal (∑ i, ‖g i y‖ ^ 2) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖g i y‖)).symm
    have hy' : EReal.exp ((p : EReal) * ψ y) ≤
        (C + 1) * ENNReal.ofReal (∑ i, ‖g i y‖ ^ 2) := by
      rw [← hsum]
      apply hy.trans
      gcongr
      exact le_add_right le_rfl
    have hh := ENNReal.log_monotone hy'
    rw [EReal.log_exp, ENNReal.log_mul_add, hlog, ← generatorLog_eq_log_sum] at hh
    simpa only [add_comm] using hh
  have hconst : lelongNumber (n := n) (generatorLog g) x ≤
      lelongNumber (n := n) (fun y => generatorLog g y + (L : EReal)) x :=
    LelongNumberScaling.lelongNumber_le_add_of_eventually_le_const
      (Eventually.of_forall fun _ => le_rfl)
  calc
    _ ≤ lelongNumber (n := n) (fun y => generatorLog g y + (L : EReal)) x := hconst
    _ ≤ lelongNumber (n := n) (fun y => (p : EReal) * ψ y) x :=
      KahlerCurrentMax.lelongNumber_le_of_eventually_le
        (hle.filter_mono nhdsWithin_le_nhds)
    _ = _ := ActualLelongPositiveScaling.lelongNumber_smul_eq hp

/-- A genuine finite family supplies its least point jet before every raw
weight, coefficient and actual exponential domination datum. -/
theorem exists_point_order_le_scaled_of_exp_domination {m N : ℕ}
    (g : Fin N → ComplexModel (m + 1) → ℂ)
    (hg : ∀ i, ∀ᶠ y in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (g i) y)
    (hne : ∃ i, ¬ ∀ᶠ y in 𝓝 (0 : ComplexModel (m + 1)), g i y = 0) :
    ∃ a : ℕ,
      (∀ i k, k < a → iteratedFDeriv ℂ k (g i) 0 = 0) ∧
      (∃ i, iteratedFDeriv ℂ a (g i) 0 ≠ 0) ∧
      ∀ (ψ : ComplexModel (m + 1) → EReal) (p : ℝ), 0 < p →
        ∀ C : ℝ≥0∞, C ≠ ⊤ →
          (∀ᶠ y in 𝓝 (0 : ComplexModel (m + 1)), EReal.exp ((p : EReal) * ψ y) ≤
            C * ∑ i, ENNReal.ofReal (‖g i y‖ ^ 2)) →
          ENNReal.ofReal (2 * (a : ℝ)) ≤
            ENNReal.ofReal p * lelongNumber (n := m + 1) ψ 0 := by
  obtain ⟨a, hlow, hsome, hformula⟩ :=
    ActualFiniteGeneratorLelongNormalization.exists_finite_generator_lelong_normalization g hg hne
  have hzero : BoundedRealGermAt (fun _ : ComplexModel (m + 1) => (0 : ℝ)) 0 :=
    ⟨0, le_rfl, Eventually.of_forall fun _ => by simp⟩
  have hreader : lelongNumber (n := m + 1) (generatorLog g) 0 =
      ENNReal.ofReal (2 * (a : ℝ)) := by
    simpa using hformula 1 zero_lt_one (fun _ => 0) hzero
  refine ⟨a, hlow, hsome, ?_⟩
  intro ψ p hp C hC hdom
  rw [← hreader]
  exact lelongNumber_generatorLog_le_scaled_of_exp_domination g hp hC hdom

end
end SGPT.Foundations.Analysis.Pending.FiniteGeneratorExponentialLelongBound
