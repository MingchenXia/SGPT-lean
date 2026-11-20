import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorMass

/-!
# Uniform cutoff derivatives on concentric coordinate balls

A single smooth cutoff between two fixed concentric unit balls is
transported by translation and dilation. Its two actual directional
derivatives scale by `r⁻²`. The resulting constant depends only on the
dimension and the two fixed radius ratios, not on the center or scale.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Filter TopologicalSpace Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorMass
open scoped Topology Distributions ContDiff

variable {n : ℕ}

/-- Two actual derivatives of a test function are its genuine real Hessian,
with the outer derivative occupying the first Hessian slot. -/
theorem dTest_dTest_eq_realHessian {Ω : Opens (ComplexModel n)}
    (χ : 𝓓(Ω, ℝ)) (v w x : ComplexModel n) :
    dTest w (dTest v χ) x = realHessian (χ : ComplexModel n → ℝ) x w v := by
  have h2 : ContDiffAt ℝ 2 (χ : ComplexModel n → ℝ) x :=
    χ.contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hD : DifferentiableAt ℝ (fderiv ℝ (χ : ComplexModel n → ℝ)) x :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfun : (dTest v χ : ComplexModel n → ℝ) =
      fun y => fderiv ℝ (χ : ComplexModel n → ℝ) y v := funext (dTest_apply v χ)
  rw [dTest_apply, hfun, fderiv_clm_apply hD (differentiableAt_const v),
    realHessian_eq_fderiv]
  simp

/-- The inverse affine coordinate change has the inverse squared Hessian
scale, including arbitrary translated centers. -/
theorem realHessian_comp_inverse_affine
    {η : ComplexModel n → ℝ} (hη : ContDiff ℝ 2 η)
    (r : ℝ) (a x v w : ComplexModel n) :
    realHessian (fun z => η (r⁻¹ • (z - a))) x v w =
      (r⁻¹) ^ 2 * realHessian η (r⁻¹ • (x - a)) v w := by
  have hA (z : ComplexModel n) : -(r⁻¹ • a) + r⁻¹ • z = r⁻¹ • (z - a) := by
    rw [smul_sub]
    abel
  have h := realHessian_comp_affine hη
    (r⁻¹ • ContinuousLinearMap.id ℝ (ComplexModel n)) (-(r⁻¹ • a)) x v w
  simp only [smul_apply, ContinuousLinearMap.id_apply, hA,
    realHessian_smul_left, realHessian_smul_right] at h
  rw [h]
  ring

/-- Genuine smooth cutoffs on every translated ball, with a uniform
inverse-square bound for all the directional derivatives used in the
coefficient-current integration-by-parts formula. -/
theorem exists_scaled_cutoffs {t₀ t₁ : ℝ} (_ht₀ : 0 < t₀) (htt : t₀ < t₁) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : ComplexModel n) (r : ℝ), 0 < r →
        ∀ (Ω : Opens (ComplexModel n)), closedBall a (t₁ * r) ⊆ Ω →
          ∃ χ : 𝓓(Ω, ℝ),
            (∀ x ∈ closedBall a (t₀ * r), χ x = 1) ∧
            tsupport χ ⊆ closedBall a (t₁ * r) ∧
            (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
            ∀ i j x,
              |dTest (realBasis n j) (dTest (realBasis n i) χ) x| ≤ B / r ^ 2 := by
  classical
  obtain ⟨η, hη, hη1, hηs, hη01⟩ := exists_cutoff_unit
    (isCompact_closedBall (0 : ComplexModel n) t₀) isOpen_ball
    (closedBall_subset_ball htt)
  have hηc : HasCompactSupport η :=
    (isCompact_closedBall (0 : ComplexModel n) t₁).of_isClosed_subset
      (isClosed_tsupport η) (hηs.trans ball_subset_closedBall)
  let φ : 𝓓((⊤ : Opens (ComplexModel n)), ℝ) :=
    ⟨η, hη, hηc, fun _ _ => mem_univ _⟩
  have hbound : ∀ i j : Fin (n * 2), ∃ C : ℝ, ∀ x,
      |dTest (realBasis n j) (dTest (realBasis n i) φ) x| ≤ C := by
    intro i j
    obtain ⟨C, hC⟩ :=
      (dTest (realBasis n j) (dTest (realBasis n i) φ)).continuous.bounded_above_of_compact_support
        (dTest (realBasis n j) (dTest (realBasis n i) φ)).hasCompactSupport
    exact ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x⟩
  choose C hC using hbound
  let B : ℝ := ∑ i, ∑ j, |C i j|
  have hB0 : 0 ≤ B :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hCB : ∀ i j, C i j ≤ B := by
    intro i j
    exact (le_abs_self _).trans
      ((Finset.single_le_sum (fun k _ => abs_nonneg (C i k)) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (C k l))
          (Finset.mem_univ i)))
  refine ⟨B, hB0, ?_⟩
  intro a r hr Ω hball
  let χf : ComplexModel n → ℝ := fun z => η (r⁻¹ • (z - a))
  have hχf : ContDiff ℝ ∞ χf := by
    exact hη.comp (show ContDiff ℝ ∞ (fun z : ComplexModel n => (r⁻¹ : ℝ) • (z - a)) by
      fun_prop)
  have hnorm (x : ComplexModel n) : ‖r⁻¹ • (x - a)‖ = ‖x - a‖ / r := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    ring
  have hsupp : tsupport χf ⊆ closedBall a (t₁ * r) := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    have hηx : r⁻¹ • (x - a) ∈ tsupport η := subset_closure hx
    have hxnorm : ‖x - a‖ / r < t₁ := by
      simpa only [mem_ball, dist_zero_right, hnorm] using hηs hηx
    rw [mem_closedBall, dist_eq_norm]
    exact (div_lt_iff₀ hr).mp hxnorm |>.le
  have hχc : HasCompactSupport χf :=
    (isCompact_closedBall a (t₁ * r)).of_isClosed_subset (isClosed_tsupport χf) hsupp
  let χ : 𝓓(Ω, ℝ) := ⟨χf, hχf, hχc, hsupp.trans hball⟩
  refine ⟨χ, ?_, hsupp, fun x => hη01 _, ?_⟩
  · intro x hx
    apply hη1
    rw [mem_closedBall, dist_zero_right, hnorm, div_le_iff₀ hr]
    simpa only [mem_closedBall, dist_eq_norm] using hx
  · intro i j x
    rw [dTest_dTest_eq_realHessian]
    change |realHessian (fun z => η (r⁻¹ • (z - a))) x (realBasis n j) (realBasis n i)| ≤ B / r ^ 2
    rw [realHessian_comp_inverse_affine (hη.of_le (WithTop.coe_le_coe.mpr le_top)),
      abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hprof := (hC i j (r⁻¹ • (x - a))).trans (hCB i j)
    rw [dTest_dTest_eq_realHessian] at hprof
    change |realHessian η (r⁻¹ • (x - a)) (realBasis n j) (realBasis n i)| ≤ B at hprof
    calc (r⁻¹) ^ 2 * |realHessian η (r⁻¹ • (x - a)) (realBasis n j) (realBasis n i)|
        ≤ (r⁻¹) ^ 2 * B := mul_le_mul_of_nonneg_left hprof (sq_nonneg _)
      _ = B / r ^ 2 := by field_simp

end SGPT.PSH.HermitianBalayage
