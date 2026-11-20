import SGPT.NPP.DN4Center

/-!
# The joint Levi estimate at a centre in terms of the logarithmic slopes

Lane DN4 (`thm:DNT23_C11bar`, big classes; FPT `lem:chern-joint-smoothing`, Step 5,
estimate `eq:chern-potential-joint-bound` with `λ₀` of FPT).

For the smoothing `Ψ_p(z, w) = ∫ p(F(z, w ζ)) χ(|ζ|²) dζ` of a `C²` function `p` that is
plurisubharmonic near `F(0, B̄(0, 2|w₀|))`, at the centre `z = 0` (`CenterData`), with
`g = p ∘ F(0, ·)` and its logarithmic slope `λ_g(r) = r ∂_r ∫ g(r ζ) χ(|ζ|²) dζ`
(`SGPT.NPP.DN3.radialSlope`), `r = |w₀|` (`CenterData.leviForm_joint_ge`):

  `L Ψ_p(0, w₀)[v, η] ≥ -A₁ r² |v|² λ_g(2r) - A₂ (|v|² + |v||η|) λ_g(r)`,

with constants depending only on `n` and the bounds of `CenterData`.  The trace masses of the core
estimate are converted by the rotation invariance of the weights (`integral_rotate`), the scaling
`L_{g(w₀·)}(ζ)[e] = |w₀|² L_g(w₀ζ)[e]` (`leviForm_smul_complex`) and the slope formula and
weight comparison (localised to plurisubharmonicity on a ball, `integral_levTr_chi_le_local`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace SGPT.NPP.DN4

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.NPP.DN3 SGPT.Envelopes.LapClass

variable {n : ℕ}

/-! ### Rotations and complex scalings -/

/-- Rotations preserve the Lebesgue measure: `∫ f(a ζ) dζ = ∫ f(ζ) dζ` for `|a| = 1`. -/
theorem integral_rotate (f : ComplexModel n → ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    ∫ ζ, f (a • ζ) = ∫ ζ, f ζ :=
  (unitRotation (n := n) a ha).measurePreserving.integral_comp
    (unitRotation a ha).toHomeomorph.measurableEmbedding f

/-- `L_g(y)[c e] = |c|² L_g(y)[e]` for complex `c`. -/
theorem leviForm_smul_complex {g : ComplexModel n → ℝ} {y : ComplexModel n}
    (hg : ContDiffAt ℝ 2 g y) (c : ℂ) (e : ComplexModel n) :
    leviForm g y (c • e) = ‖c‖ ^ 2 * leviForm g y e := by
  have hc : c • e = c.re • e + c.im • (I • e) := by
    conv_lhs => rw [← Complex.re_add_im c]
    rw [add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  have hs := hg.isSymmSndFDerivAt (by simp)
  have hII : I • I • e = -e := by rw [smul_smul, I_mul_I, neg_one_smul]
  rw [hc]
  simp only [leviForm, realHessian_eq_fderiv, smul_add, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, smul_comm I c.re,
    smul_comm I c.im, hII, map_neg, ContinuousLinearMap.neg_apply]
  rw [Complex.sq_norm, Complex.normSq_apply]
  have h1 := hs e (I • e)
  linear_combination (c.re * c.im / 2) * h1 - (c.re * c.im / 2) * h1

/-- `levTr (g ∘ (w₀ ·))(ζ) = |w₀|² levTr g (w₀ ζ)`. -/
theorem levTr_comp_smul {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g) (w₀ : ℂ)
    (ζ : ComplexModel n) :
    levTr (fun s => g (w₀ • s)) ζ = ‖w₀‖ ^ 2 * levTr g (w₀ • ζ) := by
  have hΦ : ContDiffAt ℂ 2 (fun s : ComplexModel n => w₀ • s) ζ :=
    (contDiff_id.const_smul w₀).contDiffAt
  have hd : fderiv ℂ (fun s : ComplexModel n => w₀ • s) ζ =
      w₀ • ContinuousLinearMap.id ℂ (ComplexModel n) :=
    ((hasFDerivAt_id ζ).const_smul w₀).fderiv
  simp only [levTr, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [SGPT.NPP.DN2.leviForm_comp_holomorphic hΦ hg.contDiffAt, hd]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  exact leviForm_smul_complex hg.contDiffAt w₀ _

/-- Moving the complex scaling `w₀ = r a` to the real scaling `r` in a radial integral. -/
theorem integral_radial_smul_complex (φ : ℝ → ℝ) (T : ComplexModel n → ℝ) {w₀ : ℂ}
    (hw0 : w₀ ≠ 0) :
    ∫ ζ, φ (‖ζ‖ ^ 2) * T (w₀ • ζ) = ∫ ζ, φ (‖ζ‖ ^ 2) * T (‖w₀‖ • ζ) := by
  have hn : 0 < ‖w₀‖ := norm_pos_iff.mpr hw0
  set a : ℂ := w₀ / (‖w₀‖ : ℂ) with ha
  have ha1 : ‖a‖ = 1 := by
    rw [ha, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, div_self hn.ne']
  have hw : ∀ ζ : ComplexModel n, w₀ • ζ = ‖w₀‖ • (a • ζ) := by
    intro ζ
    have hc : ((‖w₀‖ : ℝ) : ℂ) * (w₀ / ((‖w₀‖ : ℝ) : ℂ)) = w₀ := by
      have : ((‖w₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    rw [ha, ← Complex.coe_smul, smul_smul, hc]
  have h := integral_rotate (fun ζ => φ (‖ζ‖ ^ 2) * T (‖w₀‖ • ζ)) a ha1
  simp only [norm_smul, ha1, one_mul] at h
  simp_rw [hw]
  exact h

/-! ### The trace masses -/

/-- `∫ (-χ₁) levTr (g ∘ (w₀ ·)) = λ_g(|w₀|) / 2`. -/
theorem integral_negChiOne_levTr_eq {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g) {w₀ : ℂ}
    (hw0 : w₀ ≠ 0) :
    ∫ ζ, -chiOne n (‖ζ‖ ^ 2) * levTr (fun s => g (w₀ • s)) ζ = radialSlope g ‖w₀‖ / 2 := by
  simp_rw [levTr_comp_smul hg w₀]
  have e : ∀ ζ : ComplexModel n, -chiOne n (‖ζ‖ ^ 2) * (‖w₀‖ ^ 2 * levTr g (w₀ • ζ)) =
      ‖w₀‖ ^ 2 * ((fun t => -chiOne n t) (‖ζ‖ ^ 2) * levTr g (w₀ • ζ)) := fun ζ => by ring
  simp_rw [e]
  rw [integral_const_mul, integral_radial_smul_complex (fun t => -chiOne n t) (levTr g) hw0,
    radialSlope_eq hg]
  have e2 : ∀ ζ : ComplexModel n, (fun t => -chiOne n t) (‖ζ‖ ^ 2) * levTr g (‖w₀‖ • ζ) =
      levTr g (‖w₀‖ • ζ) * -chiOne n (‖ζ‖ ^ 2) := fun ζ => by simp only; ring
  simp_rw [e2]
  ring

/-- **Weight comparison, localised**: if `g` is plurisubharmonic on `B̄(0, 2ρ)` then
`ρ² ∫ levTr g(ρζ) χ ≤ (A_n/8) λ_g(2ρ)`. -/
theorem sq_mul_integral_levTr_le_local {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hpsh : ∀ y ∈ closedBall (0 : ComplexModel n) (2 * ρ), ∀ u, 0 ≤ leviForm g y u) :
    ρ ^ 2 * ∫ ζ, levTr g (ρ • ζ) * kernel n ζ ≤ weightConst n / 8 * radialSlope g (2 * ρ) := by
  set T : ComplexModel n → ℝ := fun y => max (levTr g y) 0 with hT
  have hTc : Continuous T := (SGPT.NPP.DN4.continuous_levTr hg).max continuous_const
  have hT0 : ∀ y, 0 ≤ T y := fun y => le_max_right _ _
  have hTeq : ∀ y ∈ closedBall (0 : ComplexModel n) (2 * ρ), T y = levTr g y := fun y hy =>
    max_eq_left (levTr_nonneg (hpsh y hy))
  have h := integral_mul_chi_le hTc hT0 ρ
  have h1 : ∫ ζ, levTr g (ρ • ζ) * kernel n ζ = ∫ ζ, T (ρ • ζ) * kernel n ζ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    by_cases hζ : ‖ζ‖ ≤ 1
    · simp only
      rw [hTeq]
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ]
      nlinarith [norm_nonneg ζ]
    · push Not at hζ
      simp [kernel_eq_zero n hζ.le]
  have h2 : ∫ ζ, T ((2 * ρ) • ζ) * -chiOne n (‖ζ‖ ^ 2) =
      ∫ ζ, levTr g ((2 * ρ) • ζ) * -chiOne n (‖ζ‖ ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    by_cases hζ : ‖ζ‖ ≤ 1
    · simp only
      rw [hTeq]
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      nlinarith [norm_nonneg ζ]
    · push Not at hζ
      simp [chiOne_normSq_eq_zero hζ.le]
  rw [h1, radialSlope_eq hg]
  rw [h2] at h
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  calc ρ ^ 2 * ∫ ζ, T (ρ • ζ) * kernel n ζ
      ≤ ρ ^ 2 * (weightConst n * ∫ ζ, levTr g ((2 * ρ) • ζ) * -chiOne n (‖ζ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h hρ2
    _ = weightConst n / 8 * (2 * (2 * ρ) ^ 2 *
          ∫ ζ, levTr g ((2 * ρ) • ζ) * -chiOne n (‖ζ‖ ^ 2)) := by ring

/-- `∫ χ levTr (g ∘ (w₀ ·)) ≤ (A_n/8) λ_g(2|w₀|)` if `g` is plurisubharmonic on `B̄(0, 2|w₀|)`. -/
theorem integral_chi_levTr_le {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g) {w₀ : ℂ}
    (hw0 : w₀ ≠ 0)
    (hpsh : ∀ y ∈ closedBall (0 : ComplexModel n) (2 * ‖w₀‖), ∀ u, 0 ≤ leviForm g y u) :
    ∫ ζ, chi n (‖ζ‖ ^ 2) * levTr (fun s => g (w₀ • s)) ζ ≤
      weightConst n / 8 * radialSlope g (2 * ‖w₀‖) := by
  simp_rw [levTr_comp_smul hg w₀]
  have e : ∀ ζ : ComplexModel n, chi n (‖ζ‖ ^ 2) * (‖w₀‖ ^ 2 * levTr g (w₀ • ζ)) =
      ‖w₀‖ ^ 2 * ((fun t => chi n t) (‖ζ‖ ^ 2) * levTr g (w₀ • ζ)) := fun ζ => by ring
  simp_rw [e]
  rw [integral_const_mul, integral_radial_smul_complex (fun t => chi n t) (levTr g) hw0]
  have e2 : ∀ ζ : ComplexModel n, (fun t => chi n t) (‖ζ‖ ^ 2) * levTr g (‖w₀‖ • ζ) =
      levTr g (‖w₀‖ • ζ) * kernel n ζ := fun ζ => by simp only [kernel]; ring
  simp_rw [e2]
  exact sq_mul_integral_levTr_le_local hg (norm_nonneg _) hpsh

/-! ### The joint Levi form at the centre -/

/-- The smoothing `Ψ_p(z, w) = ∫ p(F(z, w ζ)) χ(|ζ|²) dζ` of `p` along the fibre map `F`. -/
def jointSmoothing (F : ComplexModel n → ComplexModel n → ComplexModel n)
    (p : ComplexModel n → ℝ) : ComplexModel n × ℂ → ℝ :=
  fun q => ∫ ζ, p (F q.1 (q.2 • ζ)) * chi n (‖ζ‖ ^ 2)

/-- The Levi form of `Ψ_p` at `(0, w₀)` in the direction `(v, η)` is that of the integral along
the complex line `τ ↦ (τ v, w₀ + τ η)`. -/
theorem leviForm_jointSmoothing_eq_line {F : ComplexModel n → ComplexModel n → ComplexModel n}
    {p : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 (uncurryF F)) (hp : ContDiff ℝ 2 p) (w₀ : ℂ)
    (v : ComplexModel n) (η : ℂ) :
    leviForm (jointSmoothing F p) ((0 : ComplexModel n), w₀) (v, η) =
      leviForm (fun τ => ∫ ζ, p (lineCurve F w₀ v η τ ζ) * chi n (‖ζ‖ ^ 2)) 0 1 := by
  have hchi : ContDiff ℝ 2 (fun ζ : ComplexModel n => chi n (‖ζ‖ ^ 2)) :=
    (contDiff_chi_normSq (n := n)).of_le (by norm_cast)
  have hu : ∀ ζ : ComplexModel n, ContDiff ℝ 2
      (fun q : ComplexModel n × ℂ => p (F q.1 (q.2 • ζ)) * chi n (‖ζ‖ ^ 2)) := by
    intro ζ
    have hA : ContDiff ℝ 2 (fun q : ComplexModel n × ℂ =>
        ((q.1, q.2 • ζ) : ComplexModel n × ComplexModel n)) :=
      contDiff_fst.prodMk (contDiff_snd.smul contDiff_const)
    exact (hp.comp (hF.comp hA)).mul contDiff_const
  have hsupp1 : ∀ q ∈ (univ : Set (ComplexModel n × ℂ)), ∀ ζ : ComplexModel n, 1 < ‖ζ‖ →
      p (F q.1 (q.2 • ζ)) * chi n (‖ζ‖ ^ 2) = 0 := fun q _ ζ hζ => by
    rw [chi_normSq_eq_zero hζ.le, mul_zero]
  have hsupp2 : ∀ τ ∈ (univ : Set ℂ), ∀ ζ : ComplexModel n, 1 < ‖ζ‖ →
      p (lineCurve F w₀ v η τ ζ) * chi n (‖ζ‖ ^ 2) = 0 := fun τ _ ζ hζ => by
    rw [chi_normSq_eq_zero hζ.le, mul_zero]
  have hJ : ContDiffOn ℝ 2 (fun q : (ComplexModel n × ℂ) × ComplexModel n =>
      p (F q.1.1 (q.1.2 • q.2)) * chi n (‖q.2‖ ^ 2)) (univ ×ˢ univ) := by
    have hA : ContDiff ℝ 2 (fun q : (ComplexModel n × ℂ) × ComplexModel n =>
        ((q.1.1, q.1.2 • q.2) : ComplexModel n × ComplexModel n)) :=
      (contDiff_fst.comp contDiff_fst).prodMk ((contDiff_snd.comp contDiff_fst).smul contDiff_snd)
    exact ((hp.comp (hF.comp hA)).mul (hchi.comp contDiff_snd)).contDiffOn
  have hL : ContDiffOn ℝ 2 (fun q : ℂ × ComplexModel n =>
      p (lineCurve F w₀ v η q.1 q.2) * chi n (‖q.2‖ ^ 2)) (univ ×ˢ univ) :=
    ((hp.comp (contDiff_lineCurve hF)).mul (hchi.comp contDiff_snd)).contDiffOn
  rw [show jointSmoothing F p = fun q => ∫ ζ, p (F q.1 (q.2 • ζ)) * chi n (‖ζ‖ ^ 2) from rfl,
    leviForm_integral_of_contDiffOn (μ := volume)
      (F := fun q ζ => p (F q.1 (q.2 • ζ)) * chi n (‖ζ‖ ^ 2)) isOpen_univ hJ hsupp1
      (mem_univ _) (v, η),
    leviForm_integral_of_contDiffOn (μ := volume)
      (F := fun τ ζ => p (lineCurve F w₀ v η τ ζ) * chi n (‖ζ‖ ^ 2)) isOpen_univ hL hsupp2
      (mem_univ _) 1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
  simp only
  have e : (fun τ : ℂ => p (lineCurve F w₀ v η τ ζ) * chi n (‖ζ‖ ^ 2)) =
      fun τ : ℂ => (fun q : ComplexModel n × ℂ => p (F q.1 (q.2 • ζ)) * chi n (‖ζ‖ ^ 2))
        (((0 : ComplexModel n), w₀) + τ • (v, η)) := by
    funext τ
    simp [lineCurve, smul_eq_mul]
  rw [e]
  simp only [leviForm]
  rw [realHessian_complexLine (hu ζ), realHessian_complexLine (hu ζ)]
  simp

variable {F : ComplexModel n → ComplexModel n → ComplexModel n} {δ r₁ M₀ M₁ M₂ : ℝ}
  {w₀ η : ℂ} {v : ComplexModel n}

/-- **The joint Levi estimate at the centre** (FPT `eq:chern-potential-joint-bound`, with `λ₀` the
logarithmic slope `λ_g`, `g = p ∘ F(0, ·)`): for `0 < |w₀| = r < r₁/12` and `p` of class `C²`,
plurisubharmonic on `F(0, B̄(0, 2r))`,
`L Ψ_p(0, w₀)[v, η] ≥ -A₁ r² |v|² λ_g(2r) - A₂ (|v|² + |v||η|) λ_g(r)`. -/
theorem CenterData.leviForm_joint_ge (hD : CenterData F δ r₁ M₀ M₁ M₂) (hw : ‖w₀‖ < r₁ / 12)
    (hw0 : w₀ ≠ 0) {p : ComplexModel n → ℝ} (hp : ContDiff ℝ 2 p)
    (hpsh : ∀ ξ ∈ closedBall (0 : ComplexModel n) (2 * ‖w₀‖), ∀ u, 0 ≤ leviForm p (F 0 ξ) u)
    (v : ComplexModel n) (η : ℂ) :
    -(((n : ℝ) ^ 2 * (5 * (288 * M₀ * M₁ / r₁ ^ 2))) ^ 2 * (weightConst n / 8) * ‖w₀‖ ^ 2 *
          ‖v‖ ^ 2 * radialSlope (fun ξ => p (F 0 ξ)) (2 * ‖w₀‖)) -
        4 * (n : ℝ) ^ 2 * KR M₀ M₁ M₂ r₁ * (‖v‖ ^ 2 + ‖v‖ * ‖η‖) *
          radialSlope (fun ξ => p (F 0 ξ)) ‖w₀‖ ≤
      leviForm (jointSmoothing F p) ((0 : ComplexModel n), w₀) (v, η) := by
  have hr₁ : 0 < r₁ := hD.r₁_pos
  have h2r : 2 * ‖w₀‖ < r₁ := by linarith [norm_nonneg w₀]
  have hg : ContDiff ℝ 2 (fun ξ => p (F 0 ξ)) :=
    hp.comp (hD.smooth2.comp (contDiff_const.prodMk contDiff_id))
  -- plurisubharmonicity of `g = p ∘ F(0, ·)` on `B̄(0, 2r)`
  have hgpsh : ∀ y ∈ closedBall (0 : ComplexModel n) (2 * ‖w₀‖), ∀ u,
      0 ≤ leviForm (fun ξ => p (F 0 ξ)) y u := by
    intro y hy u
    have hyr : y ∈ ball (0 : ComplexModel n) r₁ := by
      rw [mem_ball, dist_zero_right]; rw [mem_closedBall, dist_zero_right] at hy; linarith
    have hΦ : ContDiffAt ℂ 2 (F 0) y :=
      (contDiffAt_of_differentiableOn_complex hD.holo0 isOpen_ball hyr).of_le (by norm_cast)
    rw [SGPT.NPP.DN2.leviForm_comp_holomorphic hΦ hp.contDiffAt]
    exact hpsh y hy _
  have hpsh1 : ∀ ζ ∈ closedBall (0 : ComplexModel n) 1, ∀ u, 0 ≤ leviForm p (F 0 (w₀ • ζ)) u := by
    intro ζ hζ u
    refine hpsh _ ?_ u
    rw [mem_closedBall, dist_zero_right, norm_smul]
    rw [mem_closedBall, dist_zero_right] at hζ
    nlinarith [norm_nonneg w₀, norm_nonneg ζ]
  have hcen := hD.leviForm_lineIntegral_ge (v := v) (η := η) hw hw0 hp hpsh1
  rw [← leviForm_jointSmoothing_eq_line hD.smooth2 hp] at hcen
  have hχ := integral_chi_levTr_le (g := fun ξ => p (F 0 ξ)) hg hw0 hgpsh
  have hχ₁ := integral_negChiOne_levTr_eq (g := fun ξ => p (F 0 ξ)) hg hw0
  beta_reduce at hχ hχ₁
  rw [hχ₁] at hcen
  have hK : 0 ≤ ((n : ℝ) ^ 2 * (5 * (288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖))) ^ 2 := sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hχ hK
  have e1 : ((n : ℝ) ^ 2 * (5 * (288 * M₀ * M₁ / r₁ ^ 2 * ‖w₀‖ * ‖v‖))) ^ 2 *
      (weightConst n / 8 * radialSlope (fun ξ => p (F 0 ξ)) (2 * ‖w₀‖)) =
      ((n : ℝ) ^ 2 * (5 * (288 * M₀ * M₁ / r₁ ^ 2))) ^ 2 * (weightConst n / 8) * ‖w₀‖ ^ 2 *
        ‖v‖ ^ 2 * radialSlope (fun ξ => p (F 0 ξ)) (2 * ‖w₀‖) := by ring
  rw [e1] at h1
  linarith

end SGPT.NPP.DN4
