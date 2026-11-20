import SGPT.NPP.DN3RadialWeight
import SGPT.Foundations.Analysis.Pending.WirtingerCalculus
import SGPT.Foundations.Analysis.Pending.LeviWirtinger
import SGPT.Foundations.Analysis.Pending.OTWeakDbar
import SGPT.Foundations.Analysis.Pending.ComplexHessianDeterminant

/-!
# The divergence formulas of the Chern smoothing

Lane DN3 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, eq. `eq:chern-weight-divergence`).

FPT writes `χ(|s|²) s^I` as an antiholomorphic divergence for each monomial `s^I`.  We only need,
and prove, the coordinate-free version for an arbitrary holomorphic function: if `g` is
holomorphic on a ball about `0` with `g(0) = 0`, put
`g̃_l(s) = ∫₀¹ ∂g/∂s_l(t s) dt` (`hadamardCoeff`); then (Hadamard's lemma)
`g(s) = ∑_l s_l g̃_l(s)` (`sum_mul_hadamardCoeff`), and since `∂_{s̄_l} χ₁(|s|²) = χ(|s|²) s_l`
(`dbarDir_chiOne_normSq`),

  `χ(|s|²) g(s) = ∑_l ∂_{s̄_l}(χ₁(|s|²) g̃_l(s))`   (`chi_mul_eq_sum_dbarDir`),

provided the `g̃_l` are holomorphic (they are, as parametric integrals of holomorphic functions;
here their holomorphy is taken as an explicit hypothesis).  The Wirtinger derivative is TN's
`CauchyGreen.dbarDir v f x = (Df(x) v + i Df(x)(i v))/2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff InnerProductSpace

namespace SGPT.NPP.DN3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CauchyGreen

variable {n : ℕ}

/-! ### `∂̄` of a radial function -/

/-- `⟪s, e_l⟫_ℝ + i ⟪s, i e_l⟫_ℝ = s_l`. -/
theorem inner_coord_add_I_inner (s : ComplexModel n) (l : Fin n) :
    ((⟪s, coordinateVector l⟫_ℝ : ℝ) : ℂ) +
      I * ((⟪s, Complex.I • coordinateVector l⟫_ℝ : ℝ) : ℂ) = s l := by
  rw [ComplexHessianDeterminant.real_inner_eq_re, ComplexHessianDeterminant.real_inner_eq_re]
  simp only [coordinateVector, inner_smul_right, EuclideanSpace.inner_single_right, one_mul]
  apply Complex.ext <;> simp

/-- **`∂_{s̄_l}` of a radial function:** `∂_{s̄_l} φ(‖s‖²) = φ'(‖s‖²) s_l`. -/
theorem dbarDir_radial {φ : ℝ → ℝ} {φ' : ℝ} {s : ComplexModel n}
    (hφ : HasDerivAt φ φ' (‖s‖ ^ 2)) (l : Fin n) :
    dbarDir (coordinateVector l) (fun y => ((φ (‖y‖ ^ 2) : ℝ) : ℂ)) s = φ' * s l := by
  have hd : HasFDerivAt (fun y : ComplexModel n => φ (‖y‖ ^ 2)) (φ' • (2 • innerSL ℝ s)) s :=
    hφ.comp_hasFDerivAt s (hasStrictFDerivAt_norm_sq s).hasFDerivAt
  simp only [dbarDir, fderiv_ofReal_comp_apply hd.differentiableAt, hd.fderiv]
  have h := inner_coord_add_I_inner s l
  simp only [FunLike.coe_smul, Pi.smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [← h]
  push_cast
  ring

/-- `∂_{s̄_l} χ₁(‖s‖²) = χ(‖s‖²) s_l`. -/
theorem dbarDir_chiOne_normSq (s : ComplexModel n) (l : Fin n) :
    dbarDir (coordinateVector l) (fun y => ((chiOne n (‖y‖ ^ 2) : ℝ) : ℂ)) s =
      chi n (‖s‖ ^ 2) * s l :=
  dbarDir_radial (hasDerivAt_chiOne n _) l

/-! ### Hadamard's lemma and the divergence formula -/

/-- `g̃_l(s) = ∫₀¹ ∂g/∂s_l (t s) dt`. -/
def hadamardCoeff (g : ComplexModel n → ℂ) (l : Fin n) (s : ComplexModel n) : ℂ :=
  ∫ t in (0 : ℝ)..1, fderiv ℂ g (t • s) (coordinateVector l)

theorem sum_coord_smul (s : ComplexModel n) : ∑ l, s l • coordinateVector l = s := by
  ext j
  simp [coordinateVector, Pi.single_apply]

/-- **Hadamard's lemma** for a function holomorphic on `ball 0 R` with continuous derivative:
`g(s) - g(0) = ∑_l s_l g̃_l(s)`. -/
theorem sum_mul_hadamardCoeff {g : ComplexModel n → ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hgc : ContinuousOn (fderiv ℂ g) (ball 0 R)) {s : ComplexModel n} (hs : s ∈ ball 0 R) :
    ∑ l, s l * hadamardCoeff g l s = g s - g 0 := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, t • s ∈ ball (0 : ComplexModel n) R := by
    intro t ht
    rw [mem_ball_zero_iff] at hs ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖s‖ ≤ 1 * ‖s‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg s)
      _ = ‖s‖ := one_mul _
      _ < R := hs
  have hopen : IsOpen (ball (0 : ComplexModel n) R) := isOpen_ball
  have hdiff : ∀ y ∈ ball (0 : ComplexModel n) R, DifferentiableAt ℂ g y :=
    fun y hy => (hg y hy).differentiableAt (hopen.mem_nhds hy)
  -- the derivative along the segment
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => g (t • s)) (fderiv ℂ g (t • s) s) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => t • s) s t := by
      simpa using (hasDerivAt_id t).smul_const s
    have h2 := (hdiff _ (hseg t ht)).hasFDerivAt.restrictScalars ℝ
    exact h2.comp_hasDerivAt t h1
  -- the integrand is continuous on `[0, 1]`
  have hcont : ContinuousOn (fun t : ℝ => fderiv ℂ g (t • s) s) (Icc 0 1) := by
    have hc : ContinuousOn (fderiv ℂ g) (ball 0 R) := hgc
    refine (hc.comp ((continuous_id.smul continuous_const).continuousOn)
      fun t ht => hseg t ht).clm_apply continuousOn_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t (Ioo_subset_Icc_self ht))
    (hcont.intervalIntegrable_of_Icc zero_le_one)
  simp only [one_smul, zero_smul] at hftc
  rw [← hftc]
  have hsplit : ∀ t : ℝ, fderiv ℂ g (t • s) s =
      ∑ l, s l * fderiv ℂ g (t • s) (coordinateVector l) := by
    intro t
    have h := congrArg (fderiv ℂ g (t • s)) (sum_coord_smul s)
    rw [map_sum] at h
    simp only [map_smul, smul_eq_mul] at h
    exact h.symm
  simp_rw [hsplit]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [hadamardCoeff, ← intervalIntegral.integral_const_mul]
  · intro l _
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one ?_
    have hc : ContinuousOn (fderiv ℂ g) (ball 0 R) := hgc
    exact continuousOn_const.mul ((hc.comp ((continuous_id.smul
      continuous_const).continuousOn) fun t ht => hseg t ht).clm_apply continuousOn_const)

/-- **The divergence formula** (FPT `eq:chern-weight-divergence`, coordinate-free form): for `g`
holomorphic on `ball 0 R` with `g(0) = 0` and holomorphic coefficients `g̃_l`,
`χ(|s|²) g(s) = ∑_l ∂_{s̄_l}(χ₁(|s|²) g̃_l(s))`. -/
theorem chi_mul_eq_sum_dbarDir {g : ComplexModel n → ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball 0 R)) (hgc : ContinuousOn (fderiv ℂ g) (ball 0 R))
    (hg0 : g 0 = 0)
    (hcoef : ∀ l, DifferentiableOn ℂ (hadamardCoeff g l) (ball 0 R))
    {s : ComplexModel n} (hs : s ∈ ball 0 R) :
    (chi n (‖s‖ ^ 2) : ℂ) * g s =
      ∑ l, dbarDir (coordinateVector l)
        (fun y => ((chiOne n (‖y‖ ^ 2) : ℝ) : ℂ) * hadamardCoeff g l y) s := by
  have hopen : IsOpen (ball (0 : ComplexModel n) R) := isOpen_ball
  have hχd : DifferentiableAt ℝ (fun y : ComplexModel n => chiOne n (‖y‖ ^ 2)) s :=
    ((hasDerivAt_chiOne n _).comp_hasFDerivAt s
      (hasStrictFDerivAt_norm_sq s).hasFDerivAt).differentiableAt
  have hterm : ∀ l, dbarDir (coordinateVector l)
      (fun y => ((chiOne n (‖y‖ ^ 2) : ℝ) : ℂ) * hadamardCoeff g l y) s =
        chi n (‖s‖ ^ 2) * s l * hadamardCoeff g l s := by
    intro l
    have hc : DifferentiableAt ℂ (hadamardCoeff g l) s :=
      (hcoef l s hs).differentiableAt (hopen.mem_nhds hs)
    rw [dbarDir_ofReal_mul hχd (hc.restrictScalars ℝ), dbarDir_chiOne_normSq,
      OTChen.dbarDir_eq_zero_of_differentiableAt hc, mul_zero, add_zero]
  simp_rw [hterm]
  have h := sum_mul_hadamardCoeff hg hgc hs
  rw [hg0, sub_zero] at h
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end SGPT.NPP.DN3
