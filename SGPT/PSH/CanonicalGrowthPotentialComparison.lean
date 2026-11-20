import SGPT.PSH.CanonicalAnalyticGrowthGerm
import SGPT.Foundations.Analysis.FirstPass.AnalyticSingularities
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The SAME actual logarithmic potential produces the norm comparisons needed
by the canonical growth ideal. Fixed-centre only; nearby coherence is separate. -/

noncomputable section
open Set Filter SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology

namespace SGPT.PSH

private theorem normSq_zero_iff {X : Type*} {N : ℕ}
    (G : Fin N → X → ℂ) (x : X) :
    generatorNormSq G x = 0 ↔ ∀ i, G i x = 0 := by
  rw [← generatorVector_norm_sq, sq_eq_zero_iff, norm_eq_zero,
    generatorVector_eq_zero_iff]

/-- The actual two formulas and bounded real remainders manufacture a common
pole set and positive comparisons, including empty generator families. -/
theorem exists_generatorNormSq_comparison_of_same_logarithmic_potential
    {X : Type*} [TopologicalSpace X] {N M : ℕ}
    (G : Fin N → X → ℂ) (H : Fin M → X → ℂ)
    {u : X → EReal} {c : ℝ} {x : X} (hc : 0 < c)
    (b d : X → ℝ) (hb : BoundedRealGermAt b x) (hd : BoundedRealGermAt d x)
    (huG : u =ᶠ[𝓝 x] fun y => (c : EReal) * generatorLog G y + (b y : EReal))
    (huH : u =ᶠ[𝓝 x] fun y => (c : EReal) * generatorLog H y + (d y : EReal)) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ᶠ y in 𝓝 x,
      a * generatorNormSq G y ≤ generatorNormSq H y ∧
        generatorNormSq H y ≤ A * generatorNormSq G y := by
  obtain ⟨B, hB, hbB⟩ := hb
  obtain ⟨D, hD, hdD⟩ := hd
  let L : ℝ := (B + D) / c
  refine ⟨Real.exp (-L), Real.exp L, Real.exp_pos _, Real.exp_pos _, ?_⟩
  filter_upwards [huG, huH, hbB, hdD] with y hGy hHy hby hdy
  have heq : (c : EReal) * generatorLog G y + (b y : EReal) =
      (c : EReal) * generatorLog H y + (d y : EReal) := hGy.symm.trans hHy
  have hz : generatorNormSq G y = 0 ↔ generatorNormSq H y = 0 := by
    rw [normSq_zero_iff, normSq_zero_iff,
      ← scaled_generatorLog_add_eq_bot_iff G y hc (b y),
      ← scaled_generatorLog_add_eq_bot_iff H y hc (d y), heq]
  by_cases hGzero : generatorNormSq G y = 0
  · rw [hGzero, hz.mp hGzero]
    simp
  have hGpos : 0 < generatorNormSq G y :=
    lt_of_le_of_ne (generatorNormSq_nonneg G y) (Ne.symm hGzero)
  have hHzero : generatorNormSq H y ≠ 0 := fun h => hGzero (hz.mpr h)
  have hHpos : 0 < generatorNormSq H y :=
    lt_of_le_of_ne (generatorNormSq_nonneg H y) (Ne.symm hHzero)
  have hlogG : generatorLog G y = (Real.log (generatorNormSq G y) : EReal) := by
    rw [generatorLog_eq_log_sum]
    exact ENNReal.log_ofReal_of_pos hGpos
  have hlogH : generatorLog H y = (Real.log (generatorNormSq H y) : EReal) := by
    rw [generatorLog_eq_log_sum]
    exact ENNReal.log_ofReal_of_pos hHpos
  have heqR : c * Real.log (generatorNormSq G y) + b y =
      c * Real.log (generatorNormSq H y) + d y := by
    apply EReal.coe_injective
    simpa only [hlogG, hlogH, ← EReal.coe_mul, ← EReal.coe_add] using heq
  have hb' := abs_le.mp hby
  have hd' := abs_le.mp hdy
  have hupper : Real.log (generatorNormSq H y) - Real.log (generatorNormSq G y) ≤ L := by
    change _ ≤ (B + D) / c
    apply (le_div_iff₀ hc).mpr
    nlinarith
  have hlower : Real.log (generatorNormSq G y) - Real.log (generatorNormSq H y) ≤ L := by
    change _ ≤ (B + D) / c
    apply (le_div_iff₀ hc).mpr
    nlinarith
  constructor
  · calc
      Real.exp (-L) * generatorNormSq G y =
          Real.exp (-L + Real.log (generatorNormSq G y)) := by
            rw [Real.exp_add, Real.exp_log hGpos]
      _ ≤ Real.exp (Real.log (generatorNormSq H y)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = generatorNormSq H y := Real.exp_log hHpos
  · calc
      generatorNormSq H y = Real.exp (Real.log (generatorNormSq H y)) :=
        (Real.exp_log hHpos).symm
      _ ≤ Real.exp (L + Real.log (generatorNormSq G y)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp L * generatorNormSq G y := by
        rw [Real.exp_add, Real.exp_log hGpos]

private theorem normSum_squared_comparisons {X : Type*} {N : ℕ}
    (G : Fin N → X → ℂ) (y : X) :
    generatorNormSq G y ≤ (∑ i, ‖G i y‖) ^ 2 ∧
      (∑ i, ‖G i y‖) ^ 2 ≤ ((N : ℝ) + 1) * generatorNormSq G y := by
  constructor
  · exact Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg (G i y)
  · have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin N => ‖G i y‖) (fun _ : Fin N => (1 : ℝ))
    have hn : (∑ i, ‖G i y‖) ^ 2 ≤ (N : ℝ) * generatorNormSq G y := by
      simpa only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, generatorNormSq, mul_comm] using hcs
    nlinarith [generatorNormSq_nonneg G y]

/-- The original potential's two genuine analytic-type presentations determine
the same ideal of norm-bounded holomorphic germs, not arbitrary raw ideals. -/
theorem canonicalGrowthGermIdeal_eq_of_same_logarithmic_potential
    {n N M : ℕ} (G : Fin N → ComplexModel n → ℂ)
    (H : Fin M → ComplexModel n → ℂ) {u : ComplexModel n → EReal} {c : ℝ}
    (huG : LogarithmicTypeAt u c G 0) (huH : LogarithmicTypeAt u c H 0) :
    canonicalGrowthGermIdeal G = canonicalGrowthGermIdeal H := by
  obtain ⟨hc, _, b, hb, hGb⟩ := huG
  obtain ⟨_, _, d, hd, hHd⟩ := huH
  obtain ⟨a, A, ha, hA, hcomp⟩ :=
    exists_generatorNormSq_comparison_of_same_logarithmic_potential G H hc b d hb hd hGb hHd
  let α : ℝ := Real.sqrt (a / ((N : ℝ) + 1))
  let β : ℝ := Real.sqrt (A * ((M : ℝ) + 1))
  have hN : 0 < (N : ℝ) + 1 := by positivity
  have hM : 0 < (M : ℝ) + 1 := by positivity
  have hα : 0 < α := Real.sqrt_pos.mpr (div_pos ha hN)
  have hβ : 0 < β := Real.sqrt_pos.mpr (mul_pos hA hM)
  apply canonicalGrowthGermIdeal_eq_of_norm_comparison G H hα hβ
  filter_upwards [hcomp] with y hy
  have hG := normSum_squared_comparisons G y
  have hH := normSum_squared_comparisons H y
  have hSG : 0 ≤ ∑ i, ‖G i y‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hSH : 0 ≤ ∑ j, ‖H j y‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hαsq : α ^ 2 = a / ((N : ℝ) + 1) := Real.sq_sqrt (div_pos ha hN).le
  have hβsq : β ^ 2 = A * ((M : ℝ) + 1) := Real.sq_sqrt (mul_pos hA hM).le
  constructor
  · have hsq : (α * ∑ i, ‖G i y‖) ^ 2 ≤ (∑ j, ‖H j y‖) ^ 2 := by
      rw [mul_pow, hαsq]
      calc
        (a / ((N : ℝ) + 1)) * (∑ i, ‖G i y‖) ^ 2 ≤
            (a / ((N : ℝ) + 1)) * (((N : ℝ) + 1) * generatorNormSq G y) :=
          mul_le_mul_of_nonneg_left hG.2 (div_pos ha hN).le
        _ = a * generatorNormSq G y := by field_simp
        _ ≤ generatorNormSq H y := hy.1
        _ ≤ (∑ j, ‖H j y‖) ^ 2 := hH.1
    nlinarith [mul_nonneg hα.le hSG]
  · have hsq : (∑ j, ‖H j y‖) ^ 2 ≤ (β * ∑ i, ‖G i y‖) ^ 2 := by
      rw [mul_pow, hβsq]
      calc
        (∑ j, ‖H j y‖) ^ 2 ≤ ((M : ℝ) + 1) * generatorNormSq H y := hH.2
        _ ≤ ((M : ℝ) + 1) * (A * generatorNormSq G y) :=
          mul_le_mul_of_nonneg_left hy.2 hM.le
        _ ≤ (A * ((M : ℝ) + 1)) * (∑ i, ‖G i y‖) ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hG.1 (mul_pos hA hM).le]
    nlinarith [mul_nonneg hβ.le hSG]

end SGPT.PSH
