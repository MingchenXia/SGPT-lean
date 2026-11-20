import SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# A point pole of order `2n` forces vanishing

Blueprint node `relgen:pole-vanishing` (chapter `claude-tok-relgen`). In `ℂⁿ = ℝ^{2n}`, `n ≥ 1`,
the function `|w - p|^{-2n}` is not integrable near `p`
(`lintegral_ball_div_norm_pow_eq_top`: the dyadic shells `B(p, r 2^{-k}) \ B(p, r 2^{-k-1})`
all carry the same positive mass); hence a function `H`, continuous at `p`, with
`∫ |H|² |w - p|^{-2n} < ∞` near `p` vanishes at `p` (`eq_zero_of_lintegral_div_norm_pow_ne_top`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalRelGen

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

theorem finrank_real_complexModel (n : ℕ) : Module.finrank ℝ (ComplexModel n) = 2 * n := by
  rw [finrank_real_of_complex, finrank_euclideanSpace, Fintype.card_fin]

theorem sub_half_pow (a : ℝ) (m : ℕ) : a ^ m - (a / 2) ^ m = a ^ m * (1 - (1 / 2) ^ m) := by
  rw [div_eq_mul_one_div a 2, mul_pow]
  ring

theorem div_mul_mul_cancel' (c : ℝ) {a : ℝ} (ha : a ≠ 0) (b : ℝ) : c / a * (a * b) = c * b := by
  field_simp

/-- **`|w - p|^{-2n}` is not integrable near `p` in `ℂⁿ`** (`n ≥ 1`). -/
theorem lintegral_ball_div_norm_pow_eq_top (hn : 0 < n) (p : ComplexModel n) {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c) :
    ∫⁻ w in ball p r, ENNReal.ofReal (c / ‖w - p‖ ^ (2 * n)) = ⊤ := by
  set V : ℝ≥0∞ := volume (ball (0 : ComplexModel n) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume (0 : ComplexModel n) one_pos).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  let ρ : ℕ → ℝ := fun k => r / 2 ^ k
  have hρpos : ∀ k, 0 < ρ k := fun k => by positivity
  have hρsucc : ∀ k, ρ (k + 1) = ρ k / 2 := fun k => by
    simp only [ρ, pow_succ]; field_simp
  have hρle : ∀ k, ρ (k + 1) ≤ ρ k := fun k => by
    rw [hρsucc]; linarith [hρpos k]
  let S : ℕ → Set (ComplexModel n) := fun k => ball p (ρ k) \ ball p (ρ (k + 1))
  have hSmeas : ∀ k, MeasurableSet (S k) := fun k => measurableSet_ball.diff measurableSet_ball
  have hSdisj : Pairwise (Function.onFun Disjoint S) := by
    have hanti : Antitone fun k => ball p (ρ k) := by
      refine antitone_nat_of_succ_le fun k => ball_subset_ball (hρle k)
    intro k l hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · refine Set.disjoint_left.mpr fun w hwk hwl => hwk.2 ?_
      exact hanti (Nat.succ_le_of_lt h) hwl.1
    · refine Set.disjoint_left.mpr fun w hwk hwl => hwl.2 ?_
      exact hanti (Nat.succ_le_of_lt h) hwk.1
  have hSsub : (⋃ k, S k) ⊆ ball p r := by
    refine iUnion_subset fun k => ?_
    refine sdiff_subset.trans (ball_subset_ball ?_)
    exact div_le_self hr.le (one_le_pow₀ (by norm_num))
  -- every shell carries the same positive mass
  set ε₀ : ℝ≥0∞ := ENNReal.ofReal (c * (1 - (1 / 2) ^ (2 * n))) * V with hε₀
  have hε₀pos : ε₀ ≠ 0 := by
    have h1 : (1 / 2 : ℝ) ^ (2 * n) < 1 :=
      pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr (mul_pos hc (by linarith))).ne' hV0
  have hshell : ∀ k, ε₀ ≤ ∫⁻ w in S k, ENNReal.ofReal (c / ‖w - p‖ ^ (2 * n)) := by
    intro k
    have hlow : ∀ w ∈ S k, ENNReal.ofReal (c / ρ k ^ (2 * n)) ≤
        ENNReal.ofReal (c / ‖w - p‖ ^ (2 * n)) := by
      intro w hw
      have h1 : ‖w - p‖ < ρ k := by rw [← dist_eq_norm]; exact hw.1
      have h2 : ρ (k + 1) ≤ ‖w - p‖ := by
        rw [← dist_eq_norm]; exact not_lt.mp hw.2
      have h3 : 0 < ‖w - p‖ := lt_of_lt_of_le (hρpos (k + 1)) h2
      refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hc.le (by positivity) ?_)
      exact pow_le_pow_left₀ h3.le h1.le _
    have hvol : volume (S k) =
        ENNReal.ofReal (ρ k ^ (2 * n) * (1 - (1 / 2) ^ (2 * n))) * V := by
      rw [measure_sdiff (ball_subset_ball (hρle k)) measurableSet_ball.nullMeasurableSet
        measure_ball_lt_top.ne, Measure.addHaar_ball_of_pos volume p (hρpos k),
        Measure.addHaar_ball_of_pos volume p (hρpos (k + 1)), finrank_real_complexModel,
        hρsucc, ← ENNReal.sub_mul (fun _ _ => hVtop), ← ENNReal.ofReal_sub _ (by positivity)]
      congr 2
      exact sub_half_pow (ρ k) (2 * n)
    calc ε₀ = ENNReal.ofReal (c / ρ k ^ (2 * n)) * volume (S k) := by
          rw [hvol, ← mul_assoc,
            ← ENNReal.ofReal_mul (div_pos hc (pow_pos (hρpos k) _)).le,
            div_mul_mul_cancel' c (pow_pos (hρpos k) (2 * n)).ne']
      _ = ∫⁻ _ in S k, ENNReal.ofReal (c / ρ k ^ (2 * n)) := (setLIntegral_const _ _).symm
      _ ≤ _ := setLIntegral_mono' (hSmeas k) hlow
  have htop : ∫⁻ w in ⋃ k, S k, ENNReal.ofReal (c / ‖w - p‖ ^ (2 * n)) = ⊤ := by
    rw [lintegral_iUnion hSmeas hSdisj]
    refine top_le_iff.mp ?_
    calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, ε₀ := (ENNReal.tsum_const_eq_top_of_ne_zero hε₀pos).symm
      _ ≤ _ := ENNReal.tsum_le_tsum hshell
  exact top_le_iff.mp (htop ▸ lintegral_mono_set hSsub)

/-- **A point pole of order `2n` forces vanishing**: if `H` is continuous at `p` and
`∫_{B(p, r)} |H|² w / |x - p|^{2n} < ∞` for a weight `w ≥ c > 0`, then `H p = 0`. -/
theorem eq_zero_of_lintegral_div_norm_pow_ne_top (hn : 0 < n) {p : ComplexModel n}
    {H : ComplexModel n → ℂ} (hH : ContinuousAt H p) {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    {ω : ComplexModel n → ℝ≥0∞} (hω : ∀ x ∈ ball p r, ENNReal.ofReal c ≤ ω x)
    (hint : ∫⁻ x in ball p r, ENNReal.ofReal (‖H x‖ ^ 2) * ω x /
      ENNReal.ofReal (‖x - p‖ ^ (2 * n)) ≠ ⊤) : H p = 0 := by
  by_contra hp
  have hpos : 0 < ‖H p‖ ^ 2 / 4 := by positivity
  have hev : ∀ᶠ x in 𝓝 p, ‖H p‖ ^ 2 / 4 < ‖H x‖ ^ 2 := by
    have hc' : ContinuousAt (fun x => ‖H x‖ ^ 2) p := (hH.norm).pow 2
    have hlt : ‖H p‖ ^ 2 / 4 < ‖H p‖ ^ 2 := by
      have : 0 < ‖H p‖ ^ 2 := by positivity
      linarith
    exact continuousAt_const.eventually_lt hc' hlt
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set s := min δ r with hs
  have hs0 : 0 < s := lt_min hδ hr
  apply hint
  refine top_le_iff.mp ((lintegral_ball_div_norm_pow_eq_top hn p hs0
    (mul_pos hpos hc)).symm.le.trans ?_)
  refine (setLIntegral_mono' measurableSet_ball fun x hx => ?_).trans
    (lintegral_mono_set (ball_subset_ball (min_le_right δ r)))
  have hxδ : x ∈ ball p δ := ball_subset_ball (min_le_left δ r) hx
  have hxr : x ∈ ball p r := ball_subset_ball (min_le_right δ r) hx
  rcases eq_or_ne x p with rfl | hxp
  · have h0 : (0 : ℝ) ^ (2 * n) = 0 := zero_pow (by omega)
    simp [h0]
  have hxp' : 0 < ‖x - p‖ ^ (2 * n) := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxp)) _
  rw [ENNReal.ofReal_div_of_pos hxp']
  refine ENNReal.div_le_div_right ?_ _
  rw [ENNReal.ofReal_mul hpos.le]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hδs x hxδ).le) (hω x hxr)

end SGPT.Okounkov.TranscendentalRelGen
