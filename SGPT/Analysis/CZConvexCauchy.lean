import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convex combinations of tails of a bounded sequence in a Hilbert space

Lane CZ-LP (`claude-cz-lp`, node `czlp:convex`).  A bounded sequence `a` in a real inner product
space has convex combinations of its tails that form a Cauchy sequence
(`exists_cauchySeq_mem_convexHull`).  This is the elementary half of Mazur's lemma, proved with
the parallelogram law: choose `b_m` in the convex hull `S_m` of `{a_k : k ≥ m}` with almost minimal
norm; then `‖b_m - b_{m'}‖² ≤ 2(d² - d_m²) + 4/(m+1)` for `m ≤ m'`, where `d_m = inf_{S_m} ‖·‖ ↑ d`.

It replaces weak compactness when smooth approximations of a function with bounded Laplacian are
turned into approximations whose Laplacians converge strongly in `L²` (`LapClass3Approx`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

namespace SGPT.Analysis.CZLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Convex combinations of tails of a bounded sequence can be chosen Cauchy.** -/
theorem exists_cauchySeq_mem_convexHull (a : ℕ → E) {C : ℝ} (ha : ∀ k, ‖a k‖ ≤ C) :
    ∃ b : ℕ → E, (∀ m, b m ∈ convexHull ℝ (a '' Ici m)) ∧ CauchySeq b := by
  set S : ℕ → Set E := fun m => convexHull ℝ (a '' Ici m) with hS
  have hSne : ∀ m, (norm '' S m).Nonempty := fun m =>
    ⟨‖a m‖, a m, subset_convexHull ℝ _ ⟨m, le_refl m, rfl⟩, rfl⟩
  have hSbdd : ∀ m, BddBelow (norm '' S m) := fun m => ⟨0, by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg x⟩
  have hSanti : ∀ m m', m ≤ m' → S m' ⊆ S m := fun m m' hmm' =>
    convexHull_mono (image_mono fun k hk => le_trans hmm' hk)
  set d : ℕ → ℝ := fun m => sInf (norm '' S m) with hd
  have hd0 : ∀ m, 0 ≤ d m := fun m => le_csInf (hSne m) (by rintro _ ⟨x, -, rfl⟩; exact norm_nonneg x)
  have hdC : ∀ m, d m ≤ C := fun m =>
    (csInf_le (hSbdd m) ⟨a m, subset_convexHull ℝ _ ⟨m, le_refl m, rfl⟩, rfl⟩).trans (ha m)
  have hC0 : 0 ≤ C := (hd0 0).trans (hdC 0)
  have hdmono : Monotone d := fun m m' hmm' =>
    csInf_le_csInf (hSbdd m) (hSne m') (image_mono (hSanti m m' hmm'))
  have hdle : ∀ m x, x ∈ S m → d m ≤ ‖x‖ := fun m x hx => csInf_le (hSbdd m) ⟨x, hx, rfl⟩
  -- the limit of `d`
  set L : ℝ := ⨆ m, d m with hL
  have hbdd : BddAbove (range d) := ⟨C, by rintro _ ⟨m, rfl⟩; exact hdC m⟩
  have hdL : ∀ m, d m ≤ L := fun m => le_ciSup hbdd m
  have hdtend : Tendsto d atTop (𝓝 L) := tendsto_atTop_ciSup hdmono hbdd
  -- almost minimizers
  have hchoose : ∀ m, ∃ x ∈ S m, ‖x‖ ^ 2 ≤ d m ^ 2 + 1 / ((m : ℝ) + 1) := by
    intro m
    set ε : ℝ := 1 / (((m : ℝ) + 1) * (2 * C + 1)) with hε
    have hε0 : 0 < ε := by positivity
    have hε1 : ε ≤ 1 := by
      rw [hε, div_le_one (by positivity)]
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hSne m) (lt_add_of_pos_right (d m) hε0)
    refine ⟨x, hx, ?_⟩
    have h1 : ‖x‖ ≤ d m + ε := hlt.le
    have h2 : ‖x‖ ^ 2 ≤ (d m + ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (d m + ε) ^ 2 ≤ d m ^ 2 + ε * (2 * C + 1) := by
      nlinarith [hd0 m, hdC m]
    have h4 : ε * (2 * C + 1) = 1 / ((m : ℝ) + 1) := by
      rw [hε]; field_simp
    linarith
  choose b hbS hbn using hchoose
  refine ⟨b, hbS, ?_⟩
  -- the key estimate
  have hkey : ∀ m m', m ≤ m' → ‖b m - b m'‖ ^ 2 ≤ 2 * (L ^ 2 - d m ^ 2) + 4 / ((m : ℝ) + 1) := by
    intro m m' hmm'
    have hmid : (1 / 2 : ℝ) • (b m + b m') ∈ S m := by
      have hc : Convex ℝ (S m) := convex_convexHull ℝ _
      have := hc (hbS m) (hSanti m m' hmm' (hbS m')) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      simpa [smul_add] using this
    have hmidn : d m ≤ ‖(1 / 2 : ℝ) • (b m + b m')‖ := hdle m _ hmid
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hmidn
    have hpar := parallelogram_law_with_norm ℝ (b m) (b m')
    have hsq : (2 * d m) ^ 2 ≤ ‖b m + b m'‖ ^ 2 := by
      have : 2 * d m ≤ ‖b m + b m'‖ := by linarith
      exact pow_le_pow_left₀ (by linarith [hd0 m]) this 2
    have hm' : d m' ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (hd0 m') (hdL m') 2
    have hinv : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hmm')
    have e1 := hbn m
    have e2 := hbn m'
    have h4 : (2 * d m) ^ 2 = 4 * d m ^ 2 := by ring
    have h5 : 4 / ((m : ℝ) + 1) = 4 * (1 / ((m : ℝ) + 1)) := by ring
    linarith [hpar, hsq, hm', hinv, e1, e2, h4, h5]
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hlim : Tendsto (fun m => 2 * (L ^ 2 - d m ^ 2) + 4 / ((m : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => 2 * (L ^ 2 - d m ^ 2)) atTop (𝓝 (2 * (L ^ 2 - L ^ 2))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub (hdtend.pow 2))
    have h2 : Tendsto (fun m : ℕ => 4 / ((m : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 : ℝ)
      simpa [div_eq_mul_inv] using this
    simpa using h1.add h2
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) (ε ^ 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have hb := hkey N k hk
  have hN' := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hN'
  rw [dist_comm, dist_eq_norm]
  have hsq : ‖b N - b k‖ ^ 2 < ε ^ 2 := lt_of_le_of_lt hb (lt_of_le_of_lt (le_abs_self _) hN')
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

end SGPT.Analysis.CZLp
