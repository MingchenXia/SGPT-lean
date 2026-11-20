import SGPT.NPP.MetricJetUnitaryFrame
import SGPT.Foundations.Analysis.Pending.MollifierPeanoHessian

/-!
# Actual scaled cutoff for the directional Levi mass estimate

Complete blueprint: `blueprint/src/dnt-big-actual-levi-mass.tex`, written first.
Every cutoff and every derivative is the actual explicit inner-product bump.
This manufactures the numerical scaled Levi bound needed for the actual
positive-measure mass argument; it assumes no bound on a potential's Hessian.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.HolomorphicPullback
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open SGPT.Analysis.CZ

variable {n : ℕ}

/-- The actual raw unit cutoff, translated and dilated by the actual radius
`2r`; it is one on the actual ball of radius `r`. -/
def leviMassCutoff (y : ComplexModel n) (r : ℝ) (x : ComplexModel n) : ℝ :=
  explicitRadialRaw 1 one_pos 0 ((2 * r)⁻¹ • (x - y))

private theorem leviMassCutoff_eq_raw {r : ℝ} (hr : 0 < r) (y x : ComplexModel n) :
    leviMassCutoff y r x = explicitRadialRaw (2 * r) (by positivity) 0 (x - y) := by
  unfold leviMassCutoff explicitRadialRaw
  congr 1
  rw [smul_smul]
  congr 1
  simp only [shrinkingBump]
  field_simp

/-- Smoothness concerns the actual displayed cutoff formula. -/
theorem contDiff_leviMassCutoff (y : ComplexModel n) (r : ℝ) :
    ContDiff ℝ ∞ (leviMassCutoff y r) :=
  (explicitRadialRaw_contDiff 1 one_pos 0).comp
    ((contDiff_id.sub contDiff_const).const_smul _)

/-- Actual nonnegativity, used to dominate the actual positive Levi measure. -/
theorem leviMassCutoff_nonneg (y : ComplexModel n) (r : ℝ) (x : ComplexModel n) :
    0 ≤ leviMassCutoff y r x := explicitRadialRaw_nonneg 1 one_pos 0 _

/-- The actual cutoff is bounded by one. -/
theorem leviMassCutoff_le_one (y : ComplexModel n) (r : ℝ) (x : ComplexModel n) :
    leviMassCutoff y r x ≤ 1 := explicitRadialRaw_le_one 1 one_pos 0 _

/-- The same actual cutoff is one on the actual closed inner ball. -/
theorem leviMassCutoff_eq_one {r : ℝ} (hr : 0 < r) (y : ComplexModel n)
    {x : ComplexModel n} (hx : x ∈ closedBall y r) : leviMassCutoff y r x = 1 := by
  rw [leviMassCutoff_eq_raw hr]
  apply explicitRadialRaw_eq_one (2 * r) (by positivity)
  have hh : ‖x - y‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hx
  linarith

/-- The topological support of the actual cutoff lies in its actual outer ball. -/
theorem tsupport_leviMassCutoff_subset {r : ℝ} (hr : 0 < r) (y : ComplexModel n) :
    tsupport (leviMassCutoff y r) ⊆ closedBall y (2 * r) := by
  have heq : leviMassCutoff y r = fun x => explicitRadialRaw (2 * r) (by positivity) 0 (x - y) :=
    funext fun x => leviMassCutoff_eq_raw hr y x
  rw [heq]
  change tsupport (explicitRadialRaw (2 * r) (by positivity) 0 ∘ (Homeomorph.subRight y)) ⊆ _
  rw [tsupport_comp_eq_preimage, explicitRadialRaw_tsupport]
  intro x hx
  simpa only [mem_preimage, Homeomorph.subRight_apply, Nat.cast_zero, zero_add, div_one,
    mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hx

private theorem realHessian_leviMassCutoff (y : ComplexModel n) (r : ℝ)
    (x v w : ComplexModel n) :
    realHessian (leviMassCutoff y r) x v w =
      ((2 * r)⁻¹) ^ 2 * realHessian (explicitRadialRaw 1 one_pos 0)
        ((2 * r)⁻¹ • (x - y)) v w := by
  let L : ComplexModel n →L[ℝ] ComplexModel n :=
    (2 * r)⁻¹ • ContinuousLinearMap.id ℝ (ComplexModel n)
  let b : ComplexModel n := -((2 * r)⁻¹ • y)
  have heq : leviMassCutoff y r = fun x => explicitRadialRaw 1 one_pos 0 (b + L x) := by
    funext x
    simp only [leviMassCutoff, L, b, smul_apply,
      ContinuousLinearMap.id_apply, smul_sub]
    congr 1
    abel
  have hχ : ContDiff ℝ 2 (explicitRadialRaw (n := n) 1 one_pos 0) :=
    (explicitRadialRaw_contDiff 1 one_pos 0).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [heq, realHessian_comp_affine hχ L b x v w]
  simp only [L, b, smul_apply, ContinuousLinearMap.id_apply,
    realHessian_smul_left, realHessian_smul_right]
  have harg : -((2 * r)⁻¹ • y) + (2 * r)⁻¹ • x = (2 * r)⁻¹ • (x - y) := by
    rw [smul_sub]
    abel
  rw [harg]
  ring

/-- Actual compact derivative boundedness and actual affine scaling produce
one numerical Levi cutoff bound for all centers, radii and directions. -/
theorem exists_bound_scaled_levi_massCutoff :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ (y : ComplexModel n) (r : ℝ), 0 < r →
      ∀ x v : ComplexModel n,
        |leviForm (leviMassCutoff y r) x v| ≤ N * ‖v‖ ^ 2 / r ^ 2 ∧
        (x ∉ closedBall y (2 * r) → leviForm (leviMassCutoff y r) x v = 0) := by
  let χ : ComplexModel n → ℝ := explicitRadialRaw 1 one_pos 0
  have hχ2 : ContDiff ℝ 2 χ := (explicitRadialRaw_contDiff 1 one_pos 0).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hχs : HasCompactSupport χ := explicitRadialRaw_hasCompactSupport 1 one_pos 0
  obtain ⟨B, hB⟩ := (hχs.iteratedFDeriv 2).exists_bound_of_continuous
    (hχ2.continuous_iteratedFDeriv (by norm_num))
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hχb (x v w : ComplexModel n) : |realHessian χ x v w| ≤ B * (‖v‖ * ‖w‖) :=
    (abs_realHessian_le x v w).trans
      (mul_le_mul_of_nonneg_right (hB x) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  refine ⟨B, hB0, ?_⟩
  intro y r hr x v
  have hpow : 0 ≤ ((2 * r)⁻¹) ^ 2 := sq_nonneg _
  have hIv : ‖Complex.I • v‖ = ‖v‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  have h1 := hχb ((2 * r)⁻¹ • (x - y)) v v
  have h2 := hχb ((2 * r)⁻¹ • (x - y)) (Complex.I • v) (Complex.I • v)
  rw [hIv] at h2
  constructor
  · rw [leviForm, realHessian_leviMassCutoff, realHessian_leviMassCutoff]
    rw [show ((2 * r)⁻¹) ^ 2 * realHessian (explicitRadialRaw 1 one_pos 0)
      ((2 * r)⁻¹ • (x - y)) v v +
        ((2 * r)⁻¹) ^ 2 * realHessian (explicitRadialRaw 1 one_pos 0)
          ((2 * r)⁻¹ • (x - y)) (Complex.I • v) (Complex.I • v) =
      ((2 * r)⁻¹) ^ 2 * (realHessian χ ((2 * r)⁻¹ • (x - y)) v v +
        realHessian χ ((2 * r)⁻¹ • (x - y)) (Complex.I • v) (Complex.I • v)) by ring]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_mul, abs_of_nonneg hpow]
    have hs : |realHessian χ ((2 * r)⁻¹ • (x - y)) v v +
        realHessian χ ((2 * r)⁻¹ • (x - y)) (Complex.I • v) (Complex.I • v)| ≤
        2 * (B * ‖v‖ ^ 2) := by
      exact (abs_add_le _ _).trans (by nlinarith)
    have hh := mul_le_mul_of_nonneg_left hs hpow
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have hscale : ((2 * r)⁻¹) ^ 2 = 1 / (4 * r ^ 2) := by field_simp; ring
    rw [hscale] at hh ⊢
    calc
      _ ≤ (1 / (4 * r ^ 2) * (2 * (B * ‖v‖ ^ 2))) / 4 :=
        div_le_div_of_nonneg_right hh (by norm_num)
      _ = (B * ‖v‖ ^ 2 / r ^ 2) / 8 := by field_simp; ring
      _ ≤ B * ‖v‖ ^ 2 / r ^ 2 := by
        have hn : 0 ≤ B * ‖v‖ ^ 2 / r ^ 2 := div_nonneg
          (mul_nonneg hB0 (sq_nonneg _)) hr2.le
        nlinarith
  · intro hx
    have hx' : x ∉ tsupport (leviMassCutoff y r) := fun h => hx (tsupport_leviMassCutoff_subset hr y h)
    have hd : iteratedFDeriv ℝ 2 (leviMassCutoff y r) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx' (tsupport_iteratedFDeriv_subset 2 h))
    simp only [leviForm, realHessian, hd, zero_apply, zero_add, zero_div]

end SGPT.NPP.DNTBig
