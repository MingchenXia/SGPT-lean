import SGPT.Foundations.Analysis.Pending.LastVariableTaylorDivision
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.RemovableSingularity

set_option autoImplicit false

/-! # Actual Hilbert evaluation-form division across a coordinate hyperplane

The quotient is defined by division away from the hyperplane and the actual
Fréchet derivative on it. Scalar Cauchy division and its uniform norm bound
produce operator-norm holomorphy and smoothness of the squared dual norm.
This is a local division step, not a global gentle approximation theorem.
-/

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualHilbertEvaluationCoordinateDivision

section Dual

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Division off the hyperplane and the actual transverse derivative on it. -/
def coordinateQuotient (A : E × ℂ → StrongDual ℂ H) (x : E × ℂ) : StrongDual ℂ H :=
  if x.2 = 0 then fderiv ℂ A (x.1, 0) (0, 1) else x.2⁻¹ • A x

private theorem scalar_first_coefficient {f : E × ℂ → ℂ} {s ρ : ℝ}
    (hρ : 0 < ρ) (hρs : ρ < s)
    (hf : DifferentiableOn ℂ f (ball (0 : E) s ×ˢ ball (0 : ℂ) s))
    {z : E} (hz : z ∈ ball (0 : E) s) :
    lastCoeff f ρ 1 z = deriv (fun t => f (z, t)) 0 := by
  have hline : DifferentiableOn ℂ (fun t => f (z, t)) (ball (0 : ℂ) s) :=
    hf.comp ((differentiableOn_const z).prodMk differentiableOn_id)
      (fun _ ht => ⟨hz, ht⟩)
  have hc := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
    isOpen_ball (closedBall_subset_ball hρs) hline (mem_ball_self hρ)
  simpa only [lastCoeff, sub_zero, smul_eq_mul, Nat.reduceAdd,
    div_eq_mul_inv, mul_comm] using hc

private theorem scalar_quotient_apply {A : E × ℂ → StrongDual ℂ H} {s ρ : ℝ}
    (hρ : 0 < ρ) (hρs : ρ < s)
    (hA : DifferentiableOn ℂ A (ball (0 : E) s ×ˢ ball (0 : ℂ) s))
    (hzero : ∀ z ∈ ball (0 : E) s, A (z, 0) = 0) (F : H)
    {x : E × ℂ} (hx : x ∈ ball (0 : E) s ×ˢ ball (0 : ℂ) s) :
    coordinateQuotient A x F = lastQuot (fun y => A y F) ρ 1 x := by
  have hf := hA.clm_apply (differentiableOn_const (c := F))
  have hcoeff : lastCoeff (fun y => A y F) ρ 0 x.1 = 0 := by
    have he := eq_lastQuot_mul_add hρ hρs hf 1 (x.1, 0)
      ⟨hx.1, mem_ball_self (hρ.trans hρs)⟩
    simpa [hzero x.1 hx.1] using he.symm
  by_cases ht : x.2 = 0
  · have hAx : DifferentiableAt ℂ A (x.1, 0) :=
      hA.differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds
        ⟨hx.1, mem_ball_self (hρ.trans hρs)⟩)
    have heval := (ContinuousLinearMap.apply ℂ ℂ F).hasFDerivAt.comp (x.1, 0)
      hAx.hasFDerivAt
    have hline : HasDerivAt (fun t : ℂ => (x.1, t)) ((0 : E), (1 : ℂ)) 0 :=
      (hasDerivAt_const (0 : ℂ) x.1).prodMk (hasDerivAt_id (0 : ℂ))
    have hd : deriv (fun t => A (x.1, t) F) 0 = fderiv ℂ A (x.1, 0) (0, 1) F :=
      (heval.comp_hasDerivAt 0 hline).deriv
    simp only [coordinateQuotient, ht, if_true, lastQuot]
    exact hd.symm.trans (scalar_first_coefficient hρ hρs hf hx.1).symm
  · simp only [coordinateQuotient, ht, if_false, smul_apply,
      smul_eq_mul, lastQuot, Finset.sum_range_one, hcoeff, pow_one, pow_zero,
      zero_mul, sub_zero, div_eq_mul_inv]
    ring

private theorem differentiableAt_of_scalar_evaluations
    {Q : E → StrongDual ℂ H} {U : Set E} (hU : IsOpen U)
    (hq : ∀ F : H, DifferentiableOn ℂ (fun x => Q x F) U)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ U, ∀ F : H, ‖Q x F‖ ≤ C * ‖F‖)
    {z₀ : E} (hz₀ : z₀ ∈ U) : DifferentiableAt ℂ Q z₀ := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  have hdiff : ∀ F : H, DifferentiableAt ℂ (fun x => Q x F) z₀ := fun F =>
    (hq F).differentiableAt (hU.mem_nhds hz₀)
  let D₀ : H →ₗ[ℂ] (E →L[ℂ] ℂ) :=
    { toFun := fun F => fderiv ℂ (fun x => Q x F) z₀
      map_add' := fun F G => by
        simp only [ContinuousLinearMap.map_add]
        exact fderiv_add (hdiff F) (hdiff G)
      map_smul' := fun c F => by
        simp only [ContinuousLinearMap.map_smul]
        exact fderiv_const_smul (hdiff F) c }
  have hcauchy : ∀ F : H, ∀ v ∈ ball z₀ (r / 2),
      ‖fderiv ℂ (fun x => Q x F) v‖ ≤ C * ‖F‖ / (r / 4) := by
    intro F v hv
    have hsub : ball v (r / 2) ⊆ ball z₀ r := by
      intro u hu
      rw [mem_ball] at hu hv ⊢
      linarith [dist_triangle u v z₀]
    exact FirstPass.norm_fderiv_le_of_forall_norm_le ((hq F).mono (hsub.trans hrU))
      (fun u hu => hbound u (hrU (hsub hu)) F) (by positivity) (by linarith)
  let D : H →L[ℂ] (E →L[ℂ] ℂ) := D₀.mkContinuousOfExistsBound
    ⟨C / (r / 4), fun F => by
      have hd := hcauchy F z₀ (mem_ball_self (by positivity))
      calc ‖D₀ F‖ ≤ C * ‖F‖ / (r / 4) := hd
        _ = C / (r / 4) * ‖F‖ := by ring⟩
  refine ⟨D.flip, (hasFDerivAt_iff_isLittleO_nhds_zero (𝕜 := ℂ) (E := E)
    (F := StrongDual ℂ H) (f := Q) (f' := D.flip) (x := z₀)).mpr ?_⟩
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun u : E => ‖u‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C / (r / 4) / (r / 2 / 4)) ?_
  filter_upwards [ball_mem_nhds (0 : E) (by positivity : 0 < r / 2 / 8)] with u hu
  rw [mem_ball_zero_iff] at hu
  rw [Real.norm_of_nonneg (by positivity)]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun F => ?_
  have htaylor := FirstPass.norm_sub_sub_fderiv_le (f := fun x => Q x F)
    (z₀ := z₀) (δ := r / 2) (L := C * ‖F‖ / (r / 4)) (by positivity)
    ((hq F).mono ((ball_subset_ball (by linarith)).trans hrU)) (hcauchy F)
    (z := z₀) (u := u) (mem_ball_self (by positivity)) hu
  change ‖Q (z₀ + u) F - Q z₀ F - fderiv ℂ (fun x => Q x F) z₀ u‖ ≤ _
  calc ‖Q (z₀ + u) F - Q z₀ F - fderiv ℂ (fun x => Q x F) z₀ u‖
      ≤ C * ‖F‖ / (r / 4) / (r / 2 / 4) * ‖u‖ * ‖u‖ := htaylor
    _ = C / (r / 4) / (r / 2 / 4) * ‖u‖ ^ 2 * ‖F‖ := by ring

end Dual

/-- Actual norm-holomorphic division and smooth squared dual norm, including the zeros. -/
theorem exists_smooth_dual_coordinate_quotient {E H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : E × ℂ → StrongDual ℂ H}
    (hA : ∀ᶠ x in 𝓝 (0 : E × ℂ), DifferentiableAt ℂ A x)
    (hzero : ∀ᶠ z in 𝓝 (0 : E), A (z, 0) = 0) :
    ∃ r > 0,
      DifferentiableOn ℂ (coordinateQuotient A) (ball (0 : E × ℂ) r) ∧
      ContDiffOn ℝ ∞ (fun x => ‖coordinateQuotient A x‖ ^ 2) (ball (0 : E × ℂ) r) ∧
      ∀ x ∈ ball (0 : E × ℂ) r,
        A x = x.2 • coordinateQuotient A x ∧
        ‖A x‖ ^ 2 = ‖x.2‖ ^ 2 * ‖coordinateQuotient A x‖ ^ 2 := by
  have hzb : ∀ᶠ x in 𝓝 (0 : E × ℂ), A (x.1, 0) = 0 :=
    continuous_fst.tendsto (0 : E × ℂ) |>.eventually hzero
  have hnb : ∀ᶠ x in 𝓝 (0 : E × ℂ), ‖A x‖ ≤ ‖A 0‖ + 1 := by
    filter_upwards [hA.self_of_nhds.continuousAt.tendsto.eventually
      (ball_mem_nhds (A 0) zero_lt_one)] with x hx
    have hd : ‖A x - A 0‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hx
    calc ‖A x‖ = ‖(A x - A 0) + A 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖A x - A 0‖ + ‖A 0‖ := norm_add_le _ _
      _ ≤ ‖A 0‖ + 1 := by linarith
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.mp (hA.and (hzb.and hnb))
  rw [← ball_prod_same] at hball
  let U : Set (E × ℂ) := ball (0 : E) s ×ˢ ball (0 : ℂ) s
  have hU : IsOpen U := isOpen_ball.prod isOpen_ball
  have hAU : DifferentiableOn ℂ A U := fun x hx => (hball hx).1.differentiableWithinAt
  have hzU : ∀ z ∈ ball (0 : E) s, A (z, 0) = 0 := by
    intro z hz
    have hx : (z, (0 : ℂ)) ∈ ball (0 : E) s ×ˢ ball (0 : ℂ) s :=
      ⟨hz, mem_ball_self hs⟩
    exact (hball hx).2.1
  obtain ⟨C, hC, hquot⟩ := exists_norm_lastQuot_le (E := E) 1
    (half_pos hs) (half_lt_self hs)
  have happly : ∀ F : H, ∀ x ∈ U,
      coordinateQuotient A x F = lastQuot (fun y => A y F) (s / 2) 1 x :=
    fun F _ hx => scalar_quotient_apply (half_pos hs) (half_lt_self hs) hAU hzU F hx
  have hQscalar : ∀ F : H, DifferentiableOn ℂ (fun x => coordinateQuotient A x F) U := by
    intro F
    exact (differentiableOn_lastQuot (half_pos hs) (half_lt_self hs)
      (hAU.clm_apply (differentiableOn_const F)) 1).congr (fun x hx => happly F x hx)
  have hQbound : ∀ x ∈ U, ∀ F : H,
      ‖coordinateQuotient A x F‖ ≤ (C * (‖A 0‖ + 1)) * ‖F‖ := by
    intro x hx F
    rw [happly F x hx]
    have hb : ∀ y ∈ U, ‖A y F‖ ≤ (‖A 0‖ + 1) * ‖F‖ := by
      intro y hy
      exact (A y).le_opNorm F |>.trans (mul_le_mul_of_nonneg_right (hball hy).2.2
        (norm_nonneg F))
    have hq := hquot s ((‖A 0‖ + 1) * ‖F‖) (fun y => A y F)
      (hAU.clm_apply (differentiableOn_const F)) hb x hx
    exact hq.trans_eq (by ring)
  have hQU : DifferentiableOn ℂ (coordinateQuotient A) U := fun x hx =>
    (differentiableAt_of_scalar_evaluations hU hQscalar (by positivity) hQbound hx)
      |>.differentiableWithinAt
  have hQsmooth := FirstPass.contDiffOn_real_of_differentiableOn_complex hQU hU
  let T := (InnerProductSpace.toDual ℂ H).symm
  let T' := @IsometryEquiv.toRealLinearIsometryEquivOfMapZero
    (StrongDual ℂ H) H _ NormedSpace.complexToReal _ _ T.toIsometryEquiv T.map_zero
  have hnorm : ContDiffOn ℝ ∞ (fun x => ‖coordinateQuotient A x‖ ^ 2) U := by
    have ht := (contDiff_norm_sq ℂ).comp_contDiffOn (T'.contDiff.comp_contDiffOn hQsmooth)
    refine ht.congr fun x _ => ?_
    change ‖coordinateQuotient A x‖ ^ 2 = ‖T' (coordinateQuotient A x)‖ ^ 2
    rw [T'.norm_map]
  have hsub : ball (0 : E × ℂ) s ⊆ U := by
    intro x hx
    change x ∈ ball (0 : E) s ×ˢ ball (0 : ℂ) s
    rwa [ball_prod_same]
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · exact hQU.mono hsub
  · exact hnorm.mono hsub
  · intro x hx
    have hxU : x ∈ U := hsub hx
    have heq : A x = x.2 • coordinateQuotient A x := by
      by_cases ht : x.2 = 0
      · have hz : A x = 0 := by
          simpa only [← ht, Prod.eta] using hzU x.1 hxU.1
        rw [hz, ht]
        apply ContinuousLinearMap.ext
        intro F
        change (0 : ℂ) = (0 : ℂ) * coordinateQuotient A x F
        simp
      · simp [coordinateQuotient, ht, smul_smul]
    refine ⟨heq, ?_⟩
    rw [heq, norm_smul, mul_pow]

end SGPT.Foundations.Analysis.Pending.ActualHilbertEvaluationCoordinateDivision
