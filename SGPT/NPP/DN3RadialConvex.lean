import SGPT.NPP.DN3RadialSlope

/-!
# Convexity of the radial mean in `log r`

Lane DN3 (`thm:DNT23_C11bar`; FPT `lem:chern-joint-smoothing`, Steps 5 and 7: `H_u(x, e^s)` is a
convex nondecreasing function of `s`).

For a `C²` function `g` on `ℂⁿ` with radial mean `Φ_g(r) = ∫ g(rζ) χ(‖ζ‖²) dζ` (`radialMean`) put
`λ_g(r) = r Φ_g'(r)` (`radialSlope`).  Then

  `r λ_g'(r) = 4 r² ∫ L_g(rζ; ζ) χ(‖ζ‖²) dζ`   (`hasDerivAt_radialSlope_exp`),

where `L_g(y; v)` is the Levi form.  The proof differentiates under the integral sign twice
(`hasDerivAt_integral_mul_of_continuous`) and uses the rotation identity
`∫ r² D²g(rζ)(iζ, iζ) χ = ∫ r Dg(rζ)(ζ) χ` (`rotation_identity`), obtained by differentiating
twice the function `θ ↦ ∫ g(r e^{iθ} ζ) χ(‖ζ‖²) dζ`, which is constant because rotations preserve
Lebesgue measure and the kernel.

Consequently, for plurisubharmonic `g` (nonnegative Levi form), `s ↦ Φ_g(e^s)` has nondecreasing
derivative `λ_g(e^s) ≥ 0`: the radial mean is a convex nondecreasing function of `log r`
(`radialSlope_nonneg`, `radialLevi_nonneg`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace SGPT.NPP.DN3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open SGPT.Envelopes.LapClass

variable {n : ℕ}

/-! ### Differentiation under the integral sign against a compactly supported weight -/

/-- Differentiation under the integral sign against a continuous, compactly supported weight,
for a jointly continuous family with jointly continuous derivative. -/
theorem hasDerivAt_integral_mul_of_continuous {K : ComplexModel n → ℝ} (hK : Continuous K)
    (hKs : HasCompactSupport K) {f f' : ℝ → ComplexModel n → ℝ}
    (hfc : Continuous fun p : ℝ × ComplexModel n => f p.1 p.2)
    (hf'c : Continuous fun p : ℝ × ComplexModel n => f' p.1 p.2)
    (hd : ∀ θ ζ, HasDerivAt (fun θ => f θ ζ) (f' θ ζ) θ) (θ₀ : ℝ) :
    HasDerivAt (fun θ => ∫ ζ, f θ ζ * K ζ) (∫ ζ, f' θ₀ ζ * K ζ) θ₀ := by
  have hcomp : IsCompact (closedBall θ₀ 1 ×ˢ tsupport K) :=
    (isCompact_closedBall θ₀ 1).prod hKs
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hf'c.continuousOn
  have hfθ : ∀ θ, Continuous fun ζ => f θ ζ :=
    fun θ => hfc.comp (Continuous.prodMk continuous_const continuous_id)
  have hf'θ : ∀ θ, Continuous fun ζ => f' θ ζ :=
    fun θ => hf'c.comp (Continuous.prodMk continuous_const continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := ball θ₀ 1)
    (F := fun θ ζ => f θ ζ * K ζ) (F' := fun θ ζ => f' θ ζ * K ζ)
    (bound := fun ζ => M * |K ζ|) (ball_mem_nhds θ₀ one_pos)
    (Eventually.of_forall fun θ => ((hfθ θ).mul hK).aestronglyMeasurable)
    (((hfθ θ₀).mul hK).integrable_of_hasCompactSupport hKs.mul_left)
    ((hf'θ θ₀).mul hK).aestronglyMeasurable ?_
    ((hK.integrable_of_hasCompactSupport hKs).abs.const_mul M) ?_).2
  · refine Eventually.of_forall fun ζ θ hθ => ?_
    rw [norm_mul, Real.norm_eq_abs]
    by_cases hζ : ζ ∈ tsupport K
    · exact mul_le_mul_of_nonneg_right
        (hM (θ, ζ) ⟨ball_subset_closedBall hθ, hζ⟩) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hζ]
      simp
  · exact Eventually.of_forall fun ζ θ _ => (hd θ ζ).mul_const (K ζ)

theorem continuous_kernel : Continuous (kernel n) := (contDiff_kernel n).continuous

/-! ### The rotation identity -/

/-- Multiplication by a complex number of modulus one, as a real linear isometry of `ℂⁿ`. -/
def unitRotation (a : ℂ) (ha : ‖a‖ = 1) : ComplexModel n ≃ₗᵢ[ℝ] ComplexModel n where
  toFun x := a • x
  invFun x := a⁻¹ • x
  map_add' x y := smul_add a x y
  map_smul' c x := smul_comm a c x
  left_inv x := by
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    simp [smul_smul, inv_mul_cancel₀ ha0]
  right_inv x := by
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    simp [smul_smul, mul_inv_cancel₀ ha0]
  norm_map' x := by
    change ‖a • x‖ = ‖x‖
    rw [norm_smul, ha, one_mul]

/-- Rotations preserve the radial means of the weight. -/
theorem integral_rotate_mul_kernel (g : ComplexModel n → ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    ∫ ζ, g (a • ζ) * kernel n ζ = ∫ ζ, g ζ * kernel n ζ := by
  have h := (unitRotation (n := n) a ha).measurePreserving.integral_comp
    (unitRotation a ha).toHomeomorph.measurableEmbedding (fun ζ => g ζ * kernel n ζ)
  have hK : ∀ ζ : ComplexModel n, kernel n (a • ζ) = kernel n ζ :=
    (isRadialKernel_kernel n).circle_invariant a ha
  have hpt : ∀ ζ : ComplexModel n, g ((unitRotation (n := n) a ha) ζ) *
      kernel n ((unitRotation (n := n) a ha) ζ) = g (a • ζ) * kernel n ζ := by
    intro ζ
    change g (a • ζ) * kernel n (a • ζ) = _
    rw [hK]
  simp only [hpt] at h
  exact h

/-- **The rotation identity.**  For a `C²` function `g` and `r ∈ ℝ`,
`∫ r² D²g(rζ)(iζ, iζ) χ(‖ζ‖²) dζ = ∫ r Dg(rζ)(ζ) χ(‖ζ‖²) dζ`. -/
theorem rotation_identity {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g) (r : ℝ) :
    ∫ ζ, r ^ 2 * fderiv ℝ (fderiv ℝ g) (r • ζ) (Complex.I • ζ) (Complex.I • ζ) * kernel n ζ =
      ∫ ζ, r * fderiv ℝ g (r • ζ) ζ * kernel n ζ := by
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hDd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  -- the rotation `R θ = e^{iθ}`
  set R : ℝ → ℂ := fun θ => Complex.exp (θ * Complex.I) with hR
  have hRd : ∀ θ : ℝ, HasDerivAt R (Complex.I * R θ) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) (1 * Complex.I) θ :=
      (hasDerivAt_id θ).ofReal_comp.mul_const Complex.I
    have h2 := h1.cexp
    simp only [one_mul] at h2
    convert h2 using 1
    ring
  have hRc : Continuous R := by
    simp only [hR]; fun_prop
  have hRn : ∀ θ : ℝ, ‖R θ‖ = 1 := fun θ => by
    simp only [hR]; exact Complex.norm_exp_ofReal_mul_I θ
  -- the point `P θ ζ = r e^{iθ} ζ` and its velocity
  set P : ℝ → ComplexModel n → ComplexModel n := fun θ ζ => r • (R θ • ζ) with hP
  have hPd : ∀ θ ζ, HasDerivAt (fun θ => P θ ζ) (r • ((Complex.I * R θ) • ζ)) θ := by
    intro θ ζ
    exact ((hRd θ).smul_const ζ).const_smul r
  have hPc : Continuous fun p : ℝ × ComplexModel n => P p.1 p.2 := by
    simp only [hP]
    exact ((hRc.comp continuous_fst).smul continuous_snd).const_smul r
  set V : ℝ → ComplexModel n → ComplexModel n := fun θ ζ => r • ((Complex.I * R θ) • ζ)
    with hV
  have hVd : ∀ θ ζ, HasDerivAt (fun θ => V θ ζ) (r • ((Complex.I * (Complex.I * R θ)) • ζ)) θ := by
    intro θ ζ
    exact (((hRd θ).const_mul Complex.I).smul_const ζ).const_smul r
  have hVc : Continuous fun p : ℝ × ComplexModel n => V p.1 p.2 := by
    simp only [hV]
    exact (((hRc.comp continuous_fst).const_mul Complex.I).smul continuous_snd).const_smul r
  -- first and second θ-derivatives of `g (P θ ζ)`
  set A : ℝ → ComplexModel n → ℝ := fun θ ζ => fderiv ℝ g (P θ ζ) (V θ ζ) with hA
  set B : ℝ → ComplexModel n → ℝ := fun θ ζ =>
    fderiv ℝ (fderiv ℝ g) (P θ ζ) (V θ ζ) (V θ ζ) +
      fderiv ℝ g (P θ ζ) (r • ((Complex.I * (Complex.I * R θ)) • ζ)) with hB
  have hAd : ∀ θ ζ, HasDerivAt (fun θ => g (P θ ζ)) (A θ ζ) θ := fun θ ζ =>
    (hgd (P θ ζ)).hasFDerivAt.comp_hasDerivAt θ (hPd θ ζ)
  have hBd : ∀ θ ζ, HasDerivAt (fun θ => A θ ζ) (B θ ζ) θ := by
    intro θ ζ
    have h1 : HasDerivAt (fun θ => fderiv ℝ g (P θ ζ))
        (fderiv ℝ (fderiv ℝ g) (P θ ζ) (V θ ζ)) θ :=
      (hDd (P θ ζ)).hasFDerivAt.comp_hasDerivAt θ (hPd θ ζ)
    have h2 := h1.clm_apply (hVd θ ζ)
    convert h2 using 1
  have hAc : Continuous fun p : ℝ × ComplexModel n => A p.1 p.2 :=
    (hDc.comp hPc).clm_apply hVc
  have hBc : Continuous fun p : ℝ × ComplexModel n => B p.1 p.2 := by
    refine ((hD2c.comp hPc).clm_apply hVc).clm_apply hVc |>.add ?_
    refine (hDc.comp hPc).clm_apply ?_
    exact ((((hRc.comp continuous_fst).const_mul Complex.I).const_mul Complex.I).smul
      continuous_snd).const_smul r
  have hgc : Continuous fun p : ℝ × ComplexModel n => g (P p.1 p.2) := hg.continuous.comp hPc
  have hKs : HasCompactSupport (kernel n) := hasCompactSupport_kernel
  -- the radial mean is constant in `θ`
  have hconst : ∀ θ, ∫ ζ, g (P θ ζ) * kernel n ζ = ∫ ζ, g (r • ζ) * kernel n ζ := by
    intro θ
    exact integral_rotate_mul_kernel (fun ζ => g (r • ζ)) (R θ) (hRn θ)
  have hA0 : ∀ θ, ∫ ζ, A θ ζ * kernel n ζ = 0 := by
    intro θ
    have h1 := hasDerivAt_integral_mul_of_continuous continuous_kernel hKs hgc hAc hAd θ
    have h2 : HasDerivAt (fun θ => ∫ ζ, g (P θ ζ) * kernel n ζ) 0 θ := by
      simp_rw [hconst]; exact hasDerivAt_const _ _
    exact h1.unique h2
  have hB0 : ∫ ζ, B 0 ζ * kernel n ζ = 0 := by
    have h1 := hasDerivAt_integral_mul_of_continuous continuous_kernel hKs hAc hBc hBd 0
    have h2 : HasDerivAt (fun θ => ∫ ζ, A θ ζ * kernel n ζ) 0 0 := by
      simp_rw [hA0]; exact hasDerivAt_const _ _
    exact h1.unique h2
  -- evaluate at `θ = 0`
  have hR0 : R 0 = 1 := by simp [hR]
  have hB0' : ∀ ζ, B 0 ζ * kernel n ζ =
      r ^ 2 * fderiv ℝ (fderiv ℝ g) (r • ζ) (Complex.I • ζ) (Complex.I • ζ) * kernel n ζ -
        r * fderiv ℝ g (r • ζ) ζ * kernel n ζ := by
    intro ζ
    simp only [hB, hP, hV, hR0, mul_one, one_smul, Complex.I_mul_I]
    rw [show ((-1 : ℂ) • ζ) = -ζ by simp, smul_neg, map_neg]
    simp only [map_smul, smul_eq_mul]
    simp
    ring
  simp_rw [hB0'] at hB0
  rw [integral_sub] at hB0
  · linarith
  · exact ((continuous_const.mul (((hD2c.comp (continuous_const_smul r)).clm_apply
      (continuous_const_smul Complex.I)).clm_apply (continuous_const_smul Complex.I))).mul
      continuous_kernel).integrable_of_hasCompactSupport hKs.mul_left
  · exact ((continuous_const.mul ((hDc.comp (continuous_const_smul r)).clm_apply
      continuous_id)).mul continuous_kernel).integrable_of_hasCompactSupport hKs.mul_left

/-! ### The logarithmic slope and its derivative -/

/-- The logarithmic slope `λ_g(r) = r Φ_g'(r) = r ∫ Dg(rζ)(ζ) χ(‖ζ‖²) dζ`. -/
def radialSlope (g : ComplexModel n → ℝ) (r : ℝ) : ℝ :=
  r * ∫ ζ, fderiv ℝ g (r • ζ) ζ * kernel n ζ

/-- `4 r² ∫ L_g(rζ; ζ) χ(‖ζ‖²) dζ`, `L_g` the Levi form. -/
def radialLevi (g : ComplexModel n → ℝ) (r : ℝ) : ℝ :=
  4 * r ^ 2 * ∫ ζ, leviForm g (r • ζ) ζ * kernel n ζ

/-- `λ_g = r Φ_g'`. -/
theorem radialSlope_eq_mul_deriv {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 1 g) (r : ℝ) :
    radialSlope g r = r * deriv (radialMean g) r := by
  rw [radialSlope, (hasDerivAt_radialMean hg r).deriv]

/-- `d/ds Φ_g(e^s) = λ_g(e^s)`. -/
theorem hasDerivAt_radialMean_exp {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 1 g) (s : ℝ) :
    HasDerivAt (fun s => radialMean g (Real.exp s)) (radialSlope g (Real.exp s)) s := by
  have h := (hasDerivAt_radialMean hg (Real.exp s)).comp s (Real.hasDerivAt_exp s)
  rw [radialSlope, mul_comm]
  exact h

/-- **The slope formula** for `λ_g`: `λ_g(r) = 2 r² ∫ (∑ₘ g_{m m̄})(rζ) (-χ₁(‖ζ‖²)) dζ`. -/
theorem radialSlope_eq {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g) (r : ℝ) :
    radialSlope g r = 2 * r ^ 2 * ∫ ζ, levTr g (r • ζ) * -chiOne n (‖ζ‖ ^ 2) :=
  slope_integral_eq hg r

/-- `d/ds λ_g(e^s) = 4 e^{2s} ∫ L_g(e^s ζ; ζ) χ(‖ζ‖²) dζ`. -/
theorem hasDerivAt_radialSlope_exp {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g) (s : ℝ) :
    HasDerivAt (fun s => radialSlope g (Real.exp s)) (radialLevi g (Real.exp s)) s := by
  have hDd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  set r := Real.exp s with hr
  -- derivative of `I₁(t) = ∫ Dg(tζ)(ζ) χ`
  have hI : HasDerivAt (fun t : ℝ => ∫ ζ, fderiv ℝ g (t • ζ) ζ * kernel n ζ)
      (∫ ζ, fderiv ℝ (fderiv ℝ g) (r • ζ) ζ ζ * kernel n ζ) r := by
    refine hasDerivAt_integral_mul_of_continuous continuous_kernel hasCompactSupport_kernel
      (f := fun t ζ => fderiv ℝ g (t • ζ) ζ)
      (f' := fun t ζ => fderiv ℝ (fderiv ℝ g) (t • ζ) ζ ζ) ?_ ?_ ?_ r
    · exact (hDc.comp (continuous_fst.smul continuous_snd)).clm_apply continuous_snd
    · exact ((hD2c.comp (continuous_fst.smul continuous_snd)).clm_apply continuous_snd).clm_apply
        continuous_snd
    · intro t ζ
      have h1 : HasDerivAt (fun t : ℝ => t • ζ) ζ t := by
        simpa using (hasDerivAt_id t).smul_const ζ
      have h2 : HasDerivAt (fun t : ℝ => fderiv ℝ g (t • ζ))
          (fderiv ℝ (fderiv ℝ g) (t • ζ) ζ) t :=
        (hDd (t • ζ)).hasFDerivAt.comp_hasDerivAt t h1
      exact (ContinuousLinearMap.apply ℝ ℝ ζ).hasFDerivAt.comp_hasDerivAt t h2
  have hS : HasDerivAt (radialSlope g)
      (1 * (∫ ζ, fderiv ℝ g (r • ζ) ζ * kernel n ζ) +
        r * ∫ ζ, fderiv ℝ (fderiv ℝ g) (r • ζ) ζ ζ * kernel n ζ) r :=
    (hasDerivAt_id' r).mul hI
  have h := hS.comp s (Real.hasDerivAt_exp s)
  -- `r λ' = r I₁ + r² I₁'` and the rotation identity
  have hrot := rotation_identity hg r
  have hKs : HasCompactSupport (kernel n) := hasCompactSupport_kernel
  have hint1 : Integrable fun ζ => fderiv ℝ (fderiv ℝ g) (r • ζ) ζ ζ * kernel n ζ :=
    ((((hD2c.comp (continuous_const_smul r)).clm_apply continuous_id).clm_apply
      continuous_id).mul continuous_kernel).integrable_of_hasCompactSupport hKs.mul_left
  have hint2 : Integrable fun ζ => fderiv ℝ (fderiv ℝ g) (r • ζ) (Complex.I • ζ)
      (Complex.I • ζ) * kernel n ζ :=
    ((((hD2c.comp (continuous_const_smul r)).clm_apply (continuous_const_smul Complex.I)).clm_apply
      (continuous_const_smul Complex.I)).mul continuous_kernel).integrable_of_hasCompactSupport
        hKs.mul_left
  have hlev : ∀ ζ : ComplexModel n, leviForm g (r • ζ) ζ * kernel n ζ =
      (1 / 4 : ℝ) * (fderiv ℝ (fderiv ℝ g) (r • ζ) ζ ζ * kernel n ζ +
        fderiv ℝ (fderiv ℝ g) (r • ζ) (Complex.I • ζ) (Complex.I • ζ) * kernel n ζ) := by
    intro ζ
    simp only [leviForm, realHessian_eq_fderiv]
    ring
  have hrot' : ∫ ζ, fderiv ℝ g (r • ζ) ζ * kernel n ζ =
      r * ∫ ζ, fderiv ℝ (fderiv ℝ g) (r • ζ) (Complex.I • ζ) (Complex.I • ζ) * kernel n ζ := by
    have hr0 : r ≠ 0 := (Real.exp_pos s).ne'
    have e1 : ∫ ζ, r * fderiv ℝ g (r • ζ) ζ * kernel n ζ =
        r * ∫ ζ, fderiv ℝ g (r • ζ) ζ * kernel n ζ := by
      rw [← integral_const_mul]; congr 1; funext ζ; ring
    have e2 : ∫ ζ, r ^ 2 * fderiv ℝ (fderiv ℝ g) (r • ζ) (Complex.I • ζ) (Complex.I • ζ) *
        kernel n ζ = r ^ 2 *
          ∫ ζ, fderiv ℝ (fderiv ℝ g) (r • ζ) (Complex.I • ζ) (Complex.I • ζ) * kernel n ζ := by
      rw [← integral_const_mul]; congr 1; funext ζ; ring
    rw [e1, e2] at hrot
    have : r * (∫ ζ, fderiv ℝ g (r • ζ) ζ * kernel n ζ) =
        r * (r * ∫ ζ, fderiv ℝ (fderiv ℝ g) (r • ζ) (Complex.I • ζ) (Complex.I • ζ) *
          kernel n ζ) := by rw [← hrot]; ring
    exact mul_left_cancel₀ hr0 this
  have hfinal : radialLevi g r = (1 * (∫ ζ, fderiv ℝ g (r • ζ) ζ * kernel n ζ) +
      r * ∫ ζ, fderiv ℝ (fderiv ℝ g) (r • ζ) ζ ζ * kernel n ζ) * r := by
    rw [radialLevi]
    simp_rw [hlev]
    rw [integral_const_mul, integral_add hint1 hint2, hrot']
    ring
  rw [hfinal]
  exact h

/-- For plurisubharmonic `C²` functions the logarithmic slope is nonnegative. -/
theorem radialSlope_nonneg {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g)
    (hpsh : ∀ y v, 0 ≤ leviForm g y v) (r : ℝ) : 0 ≤ radialSlope g r := by
  rw [radialSlope_eq hg]
  refine mul_nonneg (by positivity) (integral_nonneg fun ζ => mul_nonneg ?_ ?_)
  · exact Finset.sum_nonneg fun p _ => hpsh _ _
  · exact neg_nonneg.mpr (chiOne_nonpos n _)

/-- For plurisubharmonic `C²` functions `d²/ds² Φ_g(e^s) = radialLevi g (e^s) ≥ 0`. -/
theorem radialLevi_nonneg {g : ComplexModel n → ℝ} (hpsh : ∀ y v, 0 ≤ leviForm g y v)
    (r : ℝ) : 0 ≤ radialLevi g r :=
  mul_nonneg (by positivity) (integral_nonneg fun ζ => mul_nonneg (hpsh _ _) (kernel_nonneg ζ))

end SGPT.NPP.DN3
