import SGPT.Okounkov.TranscendentalExtensionCompare
import SGPT.Okounkov.TranscendentalExtensionPieces
import SGPT.Foundations.Analysis.Pending.KahlerCurrentMax
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Gentle analytic singularities have Hölder continuous exponentials

Blueprint `tok:ct-gentle` (package EXT). Source: DRWNXZ, proof of Theorem 6.4 ("using Definition
2.2(1), `e^φ ∈ C^α(V)` for some `α > 0`"); Xia, *Foundations of pluripotential theory*,
`lem:manifold-holder-operations` (3) (powers `f^γ`, `0 < γ ≤ 1`, of Hölder functions).

If `φ` has gentle analytic singularities of type `(c, 𝓘)` (book `def:analy-sing`,
`SGPT.PSH.SourceGentleAnalyticSingularities`), then `e^{φ/c}` is smooth, so
`e^φ = (e^{φ/c})^c` is Hölder continuous with exponent `min(c, 1)`
(`isChartHolder_expPotential_of_gentle`). The elementary estimates are
`|s^c - t^c| ≤ |s - t|^c` for `c ≤ 1` and `|s^c - t^c| ≤ c M^{c-1} |s - t|` on `[0, M]` for
`c ≥ 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff NNReal

namespace SGPT.Okounkov.TranscendentalExtension

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

/-- `|s^c - t^c| ≤ |s - t|^c` for `s, t ≥ 0` and `0 ≤ c ≤ 1`. -/
theorem abs_rpow_sub_rpow_le_of_le_one {s t c : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) : |s ^ c - t ^ c| ≤ |s - t| ^ c := by
  wlog hst : t ≤ s generalizing s t
  · rw [abs_sub_comm, abs_sub_comm s t]
    exact this ht hs (le_of_not_ge hst)
  have h1 : s ^ c ≤ (s - t) ^ c + t ^ c := by
    have := Real.rpow_add_le_add_rpow (sub_nonneg.mpr hst) ht hc0 hc1
    simpa using this
  have h2 : t ^ c ≤ s ^ c := Real.rpow_le_rpow ht hst hc0
  rw [abs_of_nonneg (sub_nonneg.mpr h2), abs_of_nonneg (sub_nonneg.mpr hst)]
  linarith

/-- `|s^c - t^c| ≤ c M^{c-1} |s - t|` for `s, t ∈ [0, M]` and `c ≥ 1`. -/
theorem abs_rpow_sub_rpow_le_of_one_le {s t c M : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hsM : s ≤ M)
    (htM : t ≤ M) (hc : 1 ≤ c) : |s ^ c - t ^ c| ≤ c * M ^ (c - 1) * |s - t| := by
  have hderiv : ∀ x ∈ Icc (0 : ℝ) M,
      HasDerivWithinAt (fun x => x ^ c) (c * x ^ (c - 1)) (Icc 0 M) x :=
    fun x _ => (Real.hasDerivAt_rpow_const (Or.inr hc)).hasDerivWithinAt
  have hbound : ∀ x ∈ Icc (0 : ℝ) M, ‖c * x ^ (c - 1)‖ ≤ c * M ^ (c - 1) := by
    intro x hx
    have hx0 : 0 ≤ x ^ (c - 1) := Real.rpow_nonneg hx.1 _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) hx0)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.1 hx.2 (by linarith)) (by linarith)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc 0 M)
    ⟨ht, htM⟩ ⟨hs, hsM⟩
  simpa [Real.norm_eq_abs] using this

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel k) M]
  [IsComplexManifold k M]

/-- **Powers of nonnegative chart-smooth functions are Hölder continuous**, with exponent
`min(c, 1)`. -/
theorem isChartHolder_rpow_of_chartSmooth {h : M → ℝ} (hh : ChartSmooth (n := k) h)
    (h0 : ∀ x, 0 ≤ h x) {c : ℝ} (hc : 0 < c) :
    IsChartHolder (k := k) (fun x => h x ^ c) := by
  refine ⟨min c 1, lt_min hc one_pos, min_le_right _ _, ?_⟩
  intro e he x hx
  let E : ComplexChart k M := ⟨e, he⟩
  have hsm : ContDiffOn ℝ ∞ (fun z => h (e.symm z)) e.target := hh E
  have hcd : ContDiffAt ℝ 1 (fun z => h (e.symm z)) (e x) :=
    (hsm.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).of_le
      (by exact_mod_cast le_top)
  obtain ⟨K, t, ht, hLip⟩ := hcd.exists_lipschitzOnWith
  have hcont : ContinuousAt h x :=
    (KahlerCurrentMax.continuous_of_chartSmooth hh).continuousAt
  set Mb : ℝ := h x + 1 with hMb
  have hMb0 : 0 < Mb := by linarith [h0 x]
  let V : Set M := (e.source ∩ e ⁻¹' t) ∩ {y | h y < Mb}
  have hV : V ∈ 𝓝 x :=
    inter_mem (inter_mem (e.open_source.mem_nhds hx) (e.continuousAt hx ht))
      (hcont.eventually (gt_mem_nhds (lt_add_one _)))
  have hlip : ∀ a ∈ V, ∀ b ∈ V, |h a - h b| ≤ K * ‖e a - e b‖ := by
    intro a ha b hb
    have := hLip.dist_le_mul (e a) ha.1.2 (e b) hb.1.2
    simpa only [Real.dist_eq, dist_eq_norm, e.left_inv ha.1.1, e.left_inv hb.1.1,
      Real.norm_eq_abs] using this
  refine ⟨V, hV, fun y hy => hy.1.1, ?_⟩
  by_cases hc1 : c ≤ 1
  · rw [min_eq_left hc1]
    refine ⟨(K : ℝ) ^ c, Real.rpow_nonneg K.coe_nonneg _, fun a ha b hb => ?_⟩
    calc |h a ^ c - h b ^ c| ≤ |h a - h b| ^ c :=
          abs_rpow_sub_rpow_le_of_le_one (h0 a) (h0 b) hc.le hc1
      _ ≤ ((K : ℝ) * ‖e a - e b‖) ^ c := Real.rpow_le_rpow (abs_nonneg _) (hlip a ha b hb) hc.le
      _ = (K : ℝ) ^ c * ‖e a - e b‖ ^ c := Real.mul_rpow K.coe_nonneg (norm_nonneg _)
  · push Not at hc1
    rw [min_eq_right hc1.le]
    have hA : 0 ≤ c * Mb ^ (c - 1) := mul_nonneg hc.le (Real.rpow_nonneg hMb0.le _)
    refine ⟨c * Mb ^ (c - 1) * K, mul_nonneg hA K.coe_nonneg, fun a ha b hb => ?_⟩
    rw [Real.rpow_one]
    calc |h a ^ c - h b ^ c| ≤ c * Mb ^ (c - 1) * |h a - h b| :=
          abs_rpow_sub_rpow_le_of_one_le (h0 a) (h0 b) ha.2.le hb.2.le hc1.le
      _ ≤ c * Mb ^ (c - 1) * (K * ‖e a - e b‖) := mul_le_mul_of_nonneg_left (hlip a ha b hb) hA
      _ = c * Mb ^ (c - 1) * K * ‖e a - e b‖ := by ring

/-- **Gentle analytic singularities give a Hölder continuous exponential** (DRWNXZ, proof of
Theorem 6.4). -/
theorem isChartHolder_expPotential_of_gentle {φ : M → EReal} {c : ℚ}
    {𝔞 : HolomorphicIdealSheaves.GermIdeal k M}
    (h : SGPT.PSH.SourceGentleAnalyticSingularities φ c 𝔞) :
    IsChartHolder (k := k) (expPotential φ) := by
  obtain ⟨-, -, ⟨hc, -⟩, hfin, hsm, -⟩ := h
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have heq : expPotential φ =
      fun x => (EReal.exp ((((c : ℝ)⁻¹ : ℝ) : EReal) * φ x)).toReal ^ (c : ℝ) := by
    funext x
    have hne : (((c : ℝ)⁻¹ : ℝ) : EReal) * φ x ≠ ⊤ := fun h' => hfin x (EReal.exp_eq_top_iff.mpr h')
    rw [← toReal_exp_smul hne hcR, ← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ hcR.ne',
      EReal.coe_one, one_mul]
    rfl
  rw [heq]
  exact isChartHolder_rpow_of_chartSmooth hsm (fun _ => ENNReal.toReal_nonneg) hcR

end SGPT.Okounkov.TranscendentalExtension
