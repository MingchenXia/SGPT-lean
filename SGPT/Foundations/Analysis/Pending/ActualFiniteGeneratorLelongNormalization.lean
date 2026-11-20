import SGPT.Foundations.Analysis.Pending.ActualHolomorphicFiniteJetGrowth
import SGPT.Foundations.Analysis.Pending.AnalyticSingularityPoleLelong
import SGPT.Foundations.Analysis.Pending.IdealWeightLowerBound
import SGPT.Foundations.Analysis.Pending.CoordinateLogarithmLelongNormalization
import SGPT.Foundations.Analysis.Pending.ActualLelongPositiveScaling

set_option autoImplicit false

/-! # The actual point coefficient of an entire finite generator logarithm

The Taylor order, common growth estimate and nonzero line are produced from
the original holomorphic family. The squared norm contributes the literal
factor two. No global generic-prime or current normalization is inferred.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.ActualFiniteGeneratorLelongNormalization

open FirstPass FirstPass.NonKahlerLocus LelongNumberChartTransport

noncomputable section

private theorem log_lower_of_component {m N a : ℕ}
    {f : Fin N → ComplexModel (m + 1) → ℂ} {i : Fin N}
    {w : ComplexModel (m + 1)} {h : ℂ → ℂ} {t : ℂ} {L : ℝ}
    (ht : t ≠ 0) (hL : 0 < L) (hh : L ≤ ‖h t‖)
    (heq : f i (t • w) = t ^ a * h t) :
    ((2 * (a : ℝ) * Real.log ‖t‖ + 2 * Real.log L : ℝ) : EReal) ≤
      generatorLog f (t • w) := by
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hA : 0 < (‖t‖ ^ a * L) ^ 2 := by positivity
  have hfi : ‖t‖ ^ a * L ≤ ‖f i (t • w)‖ := by
    rw [heq, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hh (pow_nonneg (norm_nonneg _) _)
  have hS : (‖t‖ ^ a * L) ^ 2 ≤ generatorNormSq f (t • w) := by
    calc
      (‖t‖ ^ a * L) ^ 2 ≤ ‖f i (t • w)‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hfi 2
      _ ≤ ∑ j, ‖f j (t • w)‖ ^ 2 :=
        Finset.single_le_sum (f := fun j => ‖f j (t • w)‖ ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hlog := IdealWeightLowerBound.le_generatorLog_of_le_generatorNormSq hA hS
  have he : Real.log ((‖t‖ ^ a * L) ^ 2) =
      2 * (a : ℝ) * Real.log ‖t‖ + 2 * Real.log L := by
    rw [Real.log_pow, Real.log_mul (by positivity) hL.ne', Real.log_pow]
    push_cast
    ring
  simpa only [he] using hlog

private theorem lelong_generatorLog_eq_of_growth_and_line {m N a : ℕ}
    {f : Fin N → ComplexModel (m + 1) → ℂ} {K : ℝ}
    (hK : 0 < K)
    (hbound : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)),
      ∀ i, ‖f i x‖ ≤ K * ‖x‖ ^ a)
    {i : Fin N} {w : ComplexModel (m + 1)} {h : ℂ → ℂ}
    (hw : w ≠ 0) (hh : AnalyticAt ℂ h 0) (hh0 : h 0 ≠ 0)
    (heq : ∀ᶠ t in 𝓝 (0 : ℂ), f i (t • w) = t ^ a * h t) :
    lelongNumber (n := m + 1) (generatorLog f) 0 = ENNReal.ofReal (2 * (a : ℝ)) := by
  apply le_antisymm
  · apply lelongNumber_le_ofReal
    intro γ hγ
    by_contra hnot
    have hγpos : 0 < (γ : ℝ) - 2 * (a : ℝ) := sub_pos.mpr (lt_of_not_ge hnot)
    obtain ⟨C, hC⟩ := hγ
    have hC' : ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), x ≠ 0 →
        generatorLog f x ≤ (((γ : ℝ) * Real.log ‖x‖ + C : ℝ) : EReal) := by
      simpa only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
        id_eq, sub_zero, Set.mem_compl_iff, Set.mem_singleton_iff]
        using eventually_nhdsWithin_iff.mp hC
    have hlin : ContinuousAt (fun t : ℂ => t • w) 0 :=
      continuousAt_id.smul continuousAt_const
    have hCline : ∀ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 →
        generatorLog f (t • w) ≤
          (((γ : ℝ) * Real.log ‖t • w‖ + C : ℝ) : EReal) := by
      have hlin0 : Tendsto (fun t : ℂ => t • w) (𝓝 0) (𝓝 0) := by
        simpa only [zero_smul] using hlin.tendsto
      have hpull := hlin0.eventually hC'
      filter_upwards [hpull] with t ht htn
      exact ht (smul_ne_zero htn hw)
    let L : ℝ := ‖h 0‖ / 2
    have hL : 0 < L := by dsimp only [L]; exact half_pos (norm_pos_iff.mpr hh0)
    have hunit : ∀ᶠ t in 𝓝 (0 : ℂ), L ≤ ‖h t‖ := by
      have hlt : L < ‖h 0‖ := by dsimp only [L]; linarith [norm_pos_iff.mpr hh0]
      exact (hh.continuousAt.norm.tendsto.eventually (lt_mem_nhds hlt)).mono fun _ ht => ht.le
    obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff_ball.mp (heq.and (hunit.and hCline))
    let D : ℝ := (γ : ℝ) * Real.log ‖w‖ + C - 2 * Real.log L
    let T : ℝ := |D| / ((γ : ℝ) - 2 * (a : ℝ)) + |Real.log r| + 1
    let t : ℝ := Real.exp (-T)
    have hTD : D < ((γ : ℝ) - 2 * (a : ℝ)) * T := by
      have habs : D ≤ |D| := le_abs_self D
      have hdiv : ((γ : ℝ) - 2 * (a : ℝ)) *
          (|D| / ((γ : ℝ) - 2 * (a : ℝ))) = |D| := by field_simp
      dsimp only [T]
      nlinarith [abs_nonneg (Real.log r)]
    have hTr : -T < Real.log r := by
      have hdiv : 0 ≤ |D| / ((γ : ℝ) - 2 * (a : ℝ)) :=
        div_nonneg (abs_nonneg _) hγpos.le
      have hlog := neg_abs_le (Real.log r)
      dsimp only [T]
      linarith
    have ht : 0 < t := Real.exp_pos _
    have htr : t < r := by
      rw [← Real.exp_log hr]
      exact Real.exp_lt_exp.mpr hTr
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have htball : (t : ℂ) ∈ ball (0 : ℂ) r := by
      simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] using htr
    obtain ⟨hident, hlower, hupper⟩ := hsmall (t : ℂ) htball
    have hlo := log_lower_of_component htne hL hlower hident
    have hup := hupper htne
    have hreal : 2 * (a : ℝ) * Real.log t + 2 * Real.log L ≤
        (γ : ℝ) * (Real.log t + Real.log ‖w‖) + C := by
      have hboth := hlo.trans hup
      simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
        Real.log_mul ht.ne' (norm_pos_iff.mpr hw).ne', EReal.coe_le_coe_iff] using hboth
    have hlogt : Real.log t = -T := Real.log_exp _
    rw [hlogt] at hreal
    dsimp only [D] at hTD
    nlinarith
  · apply ofReal_le_lelongNumber (by positivity) (C := Real.log ((N : ℝ) * K ^ 2))
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hbound] with x hx _hxn
    have hupper := AnalyticSingularityPoleLelong.generatorLog_le_two_log_of_norm_le
      f x hK (pow_nonneg (norm_nonneg _) _) hx
    simp only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      id_eq, sub_zero]
    simpa only [Real.log_pow, mul_assoc] using hupper

/-- The actual finite holomorphic family internally supplies its least jet,
then the exact squared-logarithm point coefficient for every positive real
coefficient and every merely bounded real remainder. -/
theorem exists_finite_generator_lelong_normalization {m N : ℕ}
    (f : Fin N → ComplexModel (m + 1) → ℂ)
    (hf : ∀ i, ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), DifferentiableAt ℂ (f i) x)
    (hne : ∃ i, ¬ ∀ᶠ x in 𝓝 (0 : ComplexModel (m + 1)), f i x = 0) :
    ∃ a : ℕ,
      (∀ i k, k < a → iteratedFDeriv ℂ k (f i) 0 = 0) ∧
      (∃ i, iteratedFDeriv ℂ a (f i) 0 ≠ 0) ∧
      ∀ c : ℝ, 0 < c → ∀ b : ComplexModel (m + 1) → ℝ, BoundedRealGermAt b 0 →
        lelongNumber (n := m + 1) (fun x => (c : EReal) * generatorLog f x + (b x : EReal)) 0 =
          ENNReal.ofReal (2 * c * (a : ℝ)) := by
  obtain ⟨a, i, hlow, hi, K, hK, hbound, w, h, hw, hh, hh0, heq⟩ :=
    ActualHolomorphicFiniteJetGrowth.exists_finite_family_jet_growth f hf hne
  have hraw := lelong_generatorLog_eq_of_growth_and_line hK hbound hw hh hh0 heq
  refine ⟨a, hlow, ⟨i, hi⟩, fun c hc b hb => ?_⟩
  rw [CoordinateLogarithmLelongNormalization.lelongNumber_add_bounded_eq hb,
    ActualLelongPositiveScaling.lelongNumber_smul_eq hc, hraw,
    ← ENNReal.ofReal_mul hc.le]
  congr 1
  ring

end

end SGPT.Foundations.Analysis.Pending.ActualFiniteGeneratorLelongNormalization
