import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The diagonal choice of `τ_k` (WN21 Corollary 6.5, measure-theoretic part; lane WN-CONV6)

Blueprint `tok-wn-conv6:diagonal` (chapter `claude-tok-wn-conv6`); source WN21 §6, proof of
Corollary 6.5.

Let `V < ∞`, `I_k : ℂ → [0, ∞]` with `I_k ≤ V`, and measures `ν_k` on `ℂ` with `ν_k(ℂ) ≤ 1`,
`ν_k {0} = 0`, which do not lose mass at the scale `e^{-k/2}`: for every `r > 0` there is `m > 0`
with `ν_k(B(0, r e^{-k/2})) ≥ m` for all `k`.  If `liminf_k ∫ I_k dν_k ≥ V`, then there are
`τ_k ≠ 0` with `e^{k/2} |τ_k| → 0` and `I_k(τ_k) → V` (`exists_tendsto_of_liminf_lintegral`).

No measurability of `I_k` is needed (only the splitting `∫ = ∫_B + ∫_{Bᶜ}` over a measurable `B`
and monotonicity, valid for the lower integral).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Diagonal

variable {V : ℝ≥0∞} {I : ℕ → ℂ → ℝ≥0∞} {ν : ℕ → Measure ℂ}

/-- **Mass bound.**  If `I_k + δ ≤ V` on `B \ {0}` with `ν_k {0} = 0` and `I_k ≤ V`, then
`∫ I_k dν_k + δ ν_k(B) ≤ V ν_k(ℂ)`. -/
theorem lintegral_add_le {k : ℕ} {B : Set ℂ} (hB : MeasurableSet B) {δ : ℝ≥0∞}
    (hI : ∀ τ, I k τ ≤ V) (h0 : ν k {0} = 0) (hBI : ∀ τ ∈ B, τ ≠ 0 → I k τ + δ ≤ V) :
    ∫⁻ τ, I k τ ∂ν k + δ * ν k B ≤ V * ν k univ := by
  have h0' : ∀ᵐ τ ∂ν k, τ ≠ 0 := by
    rw [ae_iff]; simpa using h0
  have hB1 : ∫⁻ τ in B, I k τ ∂ν k + δ * ν k B ≤ V * ν k B := by
    rw [← setLIntegral_const, ← lintegral_add_right _ measurable_const, ← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hB, ae_restrict_of_ae h0'] with τ hτB hτ0
    exact hBI τ hτB hτ0
  have hB2 : ∫⁻ τ in Bᶜ, I k τ ∂ν k ≤ V * ν k Bᶜ := by
    rw [← setLIntegral_const]
    exact lintegral_mono fun τ => hI τ
  calc ∫⁻ τ, I k τ ∂ν k + δ * ν k B
      = (∫⁻ τ in B, I k τ ∂ν k + δ * ν k B) + ∫⁻ τ in Bᶜ, I k τ ∂ν k := by
        rw [← lintegral_add_compl _ hB]; ring
    _ ≤ V * ν k B + V * ν k Bᶜ := add_le_add hB1 hB2
    _ = V * ν k univ := by rw [← mul_add, measure_add_measure_compl hB]

/-- **The key claim.**  For every `r > 0` and `δ > 0`, eventually in `k` there is `τ ≠ 0` with
`|τ| < r e^{-k/2}` and `V < I_k(τ) + δ`. -/
theorem eventually_exists (hV : V ≠ ⊤) (hI : ∀ k τ, I k τ ≤ V) (hν : ∀ k, ν k univ ≤ 1)
    (h0 : ∀ k, ν k {0} = 0)
    (hball : ∀ r : ℝ, 0 < r → ∃ m : ℝ≥0∞, m ≠ 0 ∧
      ∀ k : ℕ, m ≤ ν k (ball 0 (r * Real.exp (-((k : ℝ) / 2)))))
    (hlim : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∀ᶠ k in atTop, V ≤ ∫⁻ τ, I k τ ∂ν k + δ)
    {r : ℝ} (hr : 0 < r) {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδt : δ ≠ ⊤) :
    ∀ᶠ k : ℕ in atTop, ∃ τ : ℂ, τ ≠ 0 ∧ ‖τ‖ < r * Real.exp (-((k : ℝ) / 2)) ∧ V < I k τ + δ := by
  obtain ⟨m, hm0, hm⟩ := hball r hr
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hν 0))
    ((hm 0).trans (measure_mono (subset_univ _)))
  have hdm0 : δ * m ≠ 0 := mul_ne_zero hδ hm0
  have hdmt : δ * m ≠ ⊤ := ENNReal.mul_ne_top hδt hmt
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨k, hk1, hk2⟩ := (hcon.and_eventually (hlim (δ * m / 2)
    (ENNReal.div_ne_zero.mpr ⟨hdm0, ENNReal.ofNat_ne_top⟩))).exists
  push Not at hk1
  set B := ball (0 : ℂ) (r * Real.exp (-((k : ℝ) / 2))) with hBdef
  have hBI : ∀ τ ∈ B, τ ≠ 0 → I k τ + δ ≤ V := fun τ hτ hτ0 =>
    hk1 τ hτ0 (by simpa [hBdef] using hτ)
  have hmain := lintegral_add_le (I := I) (ν := ν) measurableSet_ball (hI k) (h0 k) hBI
  have hint : ∫⁻ τ, I k τ ∂ν k ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hV ENNReal.one_ne_top) ?_
    calc ∫⁻ τ, I k τ ∂ν k ≤ ∫⁻ τ, I k τ ∂ν k + δ * ν k B := le_self_add
      _ ≤ V * ν k univ := hmain
      _ ≤ V * 1 := by gcongr; exact hν k
  have h1 : ∫⁻ τ, I k τ ∂ν k + δ * m ≤ ∫⁻ τ, I k τ ∂ν k + δ * m / 2 := by
    calc ∫⁻ τ, I k τ ∂ν k + δ * m ≤ ∫⁻ τ, I k τ ∂ν k + δ * ν k B :=
          by gcongr; exact hm k
      _ ≤ V * ν k univ := hmain
      _ ≤ V * 1 := by gcongr; exact hν k
      _ = V := mul_one V
      _ ≤ _ := hk2
  have h2 := (ENNReal.add_le_add_iff_left hint).mp h1
  exact absurd h2 (not_le.mpr (ENNReal.half_lt_self hdm0 hdmt))

/-- **The diagonal choice** (WN21 Corollary 6.5): there are `τ_k ≠ 0` with `e^{k/2} |τ_k| → 0`
and `I_k(τ_k) → V`. -/
theorem exists_tendsto_of_liminf_lintegral (hV : V ≠ ⊤) (hI : ∀ k τ, I k τ ≤ V)
    (hν : ∀ k, ν k univ ≤ 1) (h0 : ∀ k, ν k {0} = 0)
    (hball : ∀ r : ℝ, 0 < r → ∃ m : ℝ≥0∞, m ≠ 0 ∧
      ∀ k : ℕ, m ≤ ν k (ball 0 (r * Real.exp (-((k : ℝ) / 2)))))
    (hlim : ∀ δ : ℝ≥0∞, δ ≠ 0 → ∀ᶠ k in atTop, V ≤ ∫⁻ τ, I k τ ∂ν k + δ) :
    ∃ τ : ℕ → ℂ, (∀ k, τ k ≠ 0) ∧
      Tendsto (fun k : ℕ => Real.exp ((k : ℝ) / 2) * ‖τ k‖) atTop (𝓝 0) ∧
      Tendsto (fun k => I k (τ k)) atTop (𝓝 V) := by
  classical
  -- the property `P j k`
  let P : ℕ → ℕ → Prop := fun j k => ∃ τ : ℂ, τ ≠ 0 ∧
    ‖τ‖ < (1 / ((j : ℝ) + 1)) * Real.exp (-((k : ℝ) / 2)) ∧ V < I k τ + ((j : ℝ≥0∞) + 1)⁻¹
  have hP : ∀ j, ∀ᶠ k in atTop, P j k := fun j =>
    eventually_exists hV hI hν h0 hball hlim (by positivity)
      (ENNReal.inv_ne_zero.mpr (by simp)) (ENNReal.inv_ne_top.mpr (by simp))
  choose N hN using fun j => (eventually_atTop.mp (hP j))
  -- a monotone threshold
  let N' : ℕ → ℕ := fun j => (Finset.range (j + 1)).sup N + j
  have hN'mono : Monotone N' := by
    intro i j hij
    have : (Finset.range (i + 1)).sup N ≤ (Finset.range (j + 1)).sup N :=
      Finset.sup_mono (Finset.range_subset_range.mpr (by omega))
    show (Finset.range (i + 1)).sup N + i ≤ (Finset.range (j + 1)).sup N + j
    omega
  have hN'N : ∀ j, N j ≤ N' j := fun j =>
    (Finset.le_sup (f := N) (Finset.mem_range.mpr (Nat.lt_succ_self j))).trans le_self_add
  have hN'j : ∀ j, j ≤ N' j := fun j => le_add_self
  let J : ℕ → ℕ := fun k => Nat.findGreatest (fun j => N' j ≤ k) k
  have hJspec : ∀ k, N' 0 ≤ k → N' (J k) ≤ k := fun k hk =>
    Nat.findGreatest_spec (P := fun j => N' j ≤ k) (Nat.zero_le k) hk
  have hJtend : Tendsto J atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro j
    refine ⟨N' j, fun k hk => ?_⟩
    exact Nat.le_findGreatest ((hN'j j).trans hk) hk
  have hPk : ∀ k, N' 0 ≤ k → P (J k) k := fun k hk =>
    hN (J k) k ((hN'N (J k)).trans (hJspec k hk))
  let τ : ℕ → ℂ := fun k =>
    if h : N' 0 ≤ k then Classical.choose (hPk k h) else 1
  have hτspec : ∀ k (h : N' 0 ≤ k), τ k = Classical.choose (hPk k h) := fun k h => by
    simp only [τ, dif_pos h]
  refine ⟨τ, fun k => ?_, ?_, ?_⟩
  · by_cases h : N' 0 ≤ k
    · rw [hτspec k h]; exact (Classical.choose_spec (hPk k h)).1
    · simp only [τ, dif_neg h]; exact one_ne_zero
  · -- `e^{k/2} |τ_k| < 1 / (J k + 1) → 0`
    have hJ0 : Tendsto (fun k => 1 / ((J k : ℝ) + 1)) atTop (𝓝 0) := by
      have : Tendsto (fun k => (J k : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop.comp hJtend)
      simp only [one_div]
      exact this.inv_tendsto_atTop
    refine squeeze_zero' (Eventually.of_forall fun k => by positivity) ?_ hJ0
    filter_upwards [eventually_ge_atTop (N' 0)] with k hk
    rw [hτspec k hk]
    have h := (Classical.choose_spec (hPk k hk)).2.1
    have hexp : Real.exp ((k : ℝ) / 2) * Real.exp (-((k : ℝ) / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    have hpos := Real.exp_pos ((k : ℝ) / 2)
    calc Real.exp ((k : ℝ) / 2) * ‖Classical.choose (hPk k hk)‖
        ≤ Real.exp ((k : ℝ) / 2) * ((1 / ((J k : ℝ) + 1)) * Real.exp (-((k : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left h.le hpos.le
      _ = 1 / ((J k : ℝ) + 1) := by
          rw [mul_comm (1 / ((J k : ℝ) + 1)), ← mul_assoc, hexp, one_mul]
  · -- `V - 1/(J k + 1) < I_k(τ_k) ≤ V`
    rw [ENNReal.tendsto_nhds hV]
    intro ε hε
    have hJε : ∀ᶠ k in atTop, ((J k : ℝ≥0∞) + 1)⁻¹ ≤ ε := by
      obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hε.ne'
      filter_upwards [hJtend.eventually_ge_atTop j] with k hk
      refine le_trans ?_ hj.le
      refine ENNReal.inv_le_inv.mpr ?_
      calc (j : ℝ≥0∞) ≤ (J k : ℝ≥0∞) := by exact_mod_cast hk
        _ ≤ (J k : ℝ≥0∞) + 1 := le_self_add
    filter_upwards [eventually_ge_atTop (N' 0), hJε] with k hk hkε
    rw [hτspec k hk]
    have h := (Classical.choose_spec (hPk k hk)).2.2
    refine ⟨?_, (hI k _).trans le_self_add⟩
    calc V - ε ≤ V - ((J k : ℝ≥0∞) + 1)⁻¹ := tsub_le_tsub_left hkε _
      _ ≤ I k (Classical.choose (hPk k hk)) := tsub_le_iff_right.mpr h.le

end Diagonal

end SGPT.Okounkov.TranscendentalWN
