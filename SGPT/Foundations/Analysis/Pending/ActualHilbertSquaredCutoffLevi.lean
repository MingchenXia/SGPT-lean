import SGPT.Foundations.Analysis.Pending.ConcentrationPotentialLevi
import SGPT.Foundations.Analysis.Pending.HessianLocalExtremum
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.MazurUlam

set_option autoImplicit false

/-! # Squared-cutoff Levi lower bounds for actual Hilbert-dual kernels

Riesz norm-attaining vectors internally produce scalar holomorphic lower
supports which agree with the actual kernels at the chosen point. The real
second-order local-minimum condition transfers the scalar cutoff estimate.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualHilbertSquaredCutoffLevi

open FirstPass ConcentrationPotentialLevi

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem exists_norm_attaining_vector (L : StrongDual ℂ H) :
    ∃ F : H, ‖F‖ ≤ 1 ∧ ‖L F‖ = ‖L‖ := by
  by_cases hL : L = 0
  · exact ⟨0, by simp, by simp [hL]⟩
  let q := (InnerProductSpace.toDual ℂ H).symm L
  have hqnorm : ‖q‖ = ‖L‖ := (InnerProductSpace.toDual ℂ H).symm.norm_map L
  have hqpos : 0 < ‖q‖ := by rw [hqnorm]; exact norm_pos_iff.mpr hL
  let F : H := (‖q‖⁻¹ : ℂ) • q
  have hFnorm : ‖F‖ = 1 := by
    dsimp only [F]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg q)]
    exact inv_mul_cancel₀ hqpos.ne'
  refine ⟨F, hFnorm.le, ?_⟩
  have hLF : L F = inner ℂ q F :=
    (InnerProductSpace.toDual_symm_apply (x := F) (y := L)).symm
  rw [hLF]
  dsimp only [F]
  simp only [inner_smul_right, inner_self_eq_norm_sq_to_K, norm_mul, norm_inv,
    norm_pow, Complex.norm_real, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg q), Real.norm_of_nonneg (norm_nonneg q)]
  rw [sq, ← mul_assoc, inv_mul_cancel₀ hqpos.ne', one_mul, hqnorm]

private theorem contDiffAt_squared_dual_norm
    {A : ComplexModel n → StrongDual ℂ H} {z : ComplexModel n}
    (hA : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ A y) :
    ContDiffAt ℝ 2 (fun y => ‖A y‖ ^ 2) z := by
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp hA
  have hAU : DifferentiableOn ℂ A U := fun y hy => (hUsub hy).differentiableWithinAt
  let T := (InnerProductSpace.toDual ℂ H).symm
  let T' := @IsometryEquiv.toRealLinearIsometryEquivOfMapZero
    (StrongDual ℂ H) H _ NormedSpace.complexToReal _ _ T.toIsometryEquiv T.map_zero
  have ht := (contDiff_norm_sq ℂ).comp_contDiffOn
    (T'.contDiff.comp_contDiffOn (FirstPass.contDiffOn_real_of_differentiableOn_complex hAU hU))
  have hs : ContDiffOn ℝ ∞ (fun y => ‖A y‖ ^ 2) U := by
    refine ht.congr fun y _ => ?_
    change ‖A y‖ ^ 2 = ‖T' (A y)‖ ^ 2
    rw [T'.norm_map]
  exact ((hs z hzU).contDiffAt (hU.mem_nhds hzU)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- The scalar squared-cutoff estimate holds for the actual norms of
holomorphic Hilbert-dual maps. No finite truncation or curvature input is used. -/
theorem neg_le_leviForm_log_sum_dual_of_nonneg
    {ι : Type*} [Fintype ι] {c : ι → ComplexModel n → ℝ}
    {A : ι → ComplexModel n → StrongDual ℂ H} {s : ℝ} (hs : 0 ≤ s)
    {z : ComplexModel n}
    (hpos : 0 < ∑ j, c j z ^ 2 * ‖A j z‖ ^ 2 + s)
    (hc : ∀ j, ContDiffAt ℝ 2 (c j) z)
    (hA : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (A j) y)
    (v : ComplexModel n) :
    -(2 * (∑ j, ‖A j z‖ ^ 2 *
        (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v)) /
      (∑ j, c j z ^ 2 * ‖A j z‖ ^ 2 + s)) ≤
      leviForm (fun y => Real.log (∑ j, c j y ^ 2 * ‖A j y‖ ^ 2 + s)) z v := by
  classical
  choose F hF hFeq using fun j : ι => exists_norm_attaining_vector (A j z)
  let G : ι → ComplexModel n → ℂ := fun j y => A j y (F j)
  have hG : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (G j) y := fun j =>
    (hA j).mono fun y hy => hy.clm_apply (differentiableAt_const (F j))
  have hnorm : ∀ j y, ‖G j y‖ ≤ ‖A j y‖ := by
    intro j y
    exact ((A j y).le_opNorm (F j)).trans
      (by simpa using mul_le_mul_of_nonneg_left (hF j) (norm_nonneg (A j y)))
  let S : ComplexModel n → ℝ := fun y => ∑ j, c j y ^ 2 * ‖A j y‖ ^ 2 + s
  let S₀ : ComplexModel n → ℝ := fun y => ∑ j, c j y ^ 2 * Complex.normSq (G j y) + s
  have heq : S₀ z = S z := by
    dsimp only [S₀, S]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by
      rw [Complex.normSq_eq_norm_sq]
      change c j z ^ 2 * ‖A j z (F j)‖ ^ 2 = _
      rw [hFeq j]
  have hle : ∀ y, S₀ y ≤ S y := by
    intro y
    dsimp only [S₀, S]
    apply add_le_add_left
    apply Finset.sum_le_sum
    intro j _
    rw [Complex.normSq_eq_norm_sq]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hnorm j y) 2) (sq_nonneg _)
  have hS : ContDiffAt ℝ 2 S z :=
    (ContDiffAt.sum fun j _ => (hc j).pow 2 |>.mul
      (contDiffAt_squared_dual_norm (hA j))).add contDiffAt_const
  have hS₀ : ContDiffAt ℝ 2 S₀ z :=
    (ContDiffAt.sum fun j _ => (hc j).pow 2 |>.mul
      (ConcentrationPotentialLevi.contDiffAt_normSq (hG j))).add contDiffAt_const
  have hSpos : 0 < S z := hpos
  have hS₀pos : 0 < S₀ z := by rw [heq]; exact hSpos
  have hlogS : ContDiffAt ℝ 2 (fun y => Real.log (S y)) z := hS.log hSpos.ne'
  have hlogS₀ : ContDiffAt ℝ 2 (fun y => Real.log (S₀ y)) z := hS₀.log hS₀pos.ne'
  have hmin : IsLocalMin (fun y => Real.log (S y) - Real.log (S₀ y)) z := by
    have hnear : ∀ᶠ y in 𝓝 z, 0 < S₀ y :=
      hS₀.continuousAt.eventually (lt_mem_nhds hS₀pos)
    filter_upwards [hnear] with y hy
    rw [heq, sub_self]
    exact sub_nonneg.mpr (Real.log_le_log hy (hle y))
  have hf := hlogS.sub hlogS₀
  have h1 := hmin.fderiv_fderiv_nonneg hf v
  have h2 := hmin.fderiv_fderiv_nonneg hf (Complex.I • v)
  have hlev : 0 ≤ leviForm (fun y => Real.log (S y) - Real.log (S₀ y)) z v := by
    simp only [leviForm, realHessian_eq_fderiv]
    positivity
  have hfun : (fun y => Real.log (S y) - Real.log (S₀ y)) =
      (fun y => Real.log (S y)) + -(fun y => Real.log (S₀ y)) := by
    funext y; rfl
  rw [hfun] at hlev
  change 0 ≤ leviForm ((fun y => Real.log (S y)) +
    (fun y => -Real.log (S₀ y))) z v at hlev
  rw [leviForm_add hlogS hlogS₀.neg] at hlev
  have hneg := leviForm_neg (fun y => Real.log (S₀ y)) z v
  change leviForm (fun y => -Real.log (S₀ y)) z v = _ at hneg
  rw [hneg] at hlev
  have hbound := ConcentrationPotentialLevi.neg_le_leviForm_log_sum_of_nonneg hs
    hS₀pos hc hG v
  have hnum : (∑ j, Complex.normSq (G j z) *
        (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v)) =
      ∑ j, ‖A j z‖ ^ 2 *
        (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.normSq_eq_norm_sq]
    change ‖A j z (F j)‖ ^ 2 * _ = _
    rw [hFeq j]
  change -(2 * _ / S₀ z) ≤ leviForm (fun y => Real.log (S₀ y)) z v at hbound
  rw [hnum, heq] at hbound
  exact hbound.trans (by linarith)

end SGPT.Foundations.Analysis.Pending.ActualHilbertSquaredCutoffLevi
