import SGPT.NPP.DN2LogChart
import SGPT.NPP.DN3KernelSquare

/-!
# The Levi form of `p ∘ c` along a non-holomorphic family of curves

Lane DN4 (`thm:DNT23_C11bar`, big classes; FPT `lem:chern-joint-smoothing`,
`chapters/inputs/q10-big-envelope-regularity.tex`, Step 4, eq. `eq:chern-integrand-derivatives`).

FPT computes the joint Levi form of the smoothing `Ψ_p(z, w) = ∫ p(F(z, w ζ)) χ(|ζ|²) dζ` after a
holomorphic reparametrisation of the fibre.  We avoid that reparametrisation: along a complex
line `τ ↦ (τ v, w₀ + τ η)` the integrand is `p(c(τ, ζ))` with `c(τ, ζ) = F(τ v, (w₀ + τ η) ζ)`,
holomorphic in `ζ` but not in `τ`.  At `τ = 0` put `Φ = c(0, ·)` and

* `Ŷ = ∂_τ c = ½(D_τc(1) - i D_τc(i))`, `X̂ = ∂_τ̄ c = ½(D_τc(1) + i D_τc(i))`,
* `Q̂ = ∂_τ ∂_τ̄ c = ¼(D²_τc(1, 1) + D²_τc(i, i))`.

If `X̂ = DΦ · X` and `Q̂ - DŶ · X = DΦ · R` (pointwise; `X`, `R` are vectors), then with the
holomorphic derivative `ℓ(s) = ∂p(Φ s) · Ŷ(s)` (`holDeriv`)

  `L_τ(p ∘ c)(0) = L_p(Φ)[Ŷ] + L_p(Φ)[X̂] + 2 Re ∂_X ℓ + D(p ∘ Φ)(R)`   (`leviForm_curve_eq`).

The first term is the "square" of FPT, the second is nonnegative for plurisubharmonic `p`, and
the last two are integrated by parts in `ζ` (`SGPT.NPP.DN4Core`).  The Hermitian form of the
complex Hessian is handled through its real part `hermRe p y a b` (`hermRe_self` : it is the Levi
form on the diagonal), with `∂̄_b ∂_a p = hermRe(a, b) + i hermRe(a, i b)`
(`dbarDir_dDir_ofReal_eq`) and the Cauchy–Schwarz bounds `two_mul_abs_hermRe_le`,
`norm_dbarDir_dDir_ofReal_le`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric Complex
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.NPP.DN4

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.CauchyGreen
open SGPT.NPP.DN2

variable {n : ℕ}

/-! ### The real part of the Hermitian form of the complex Hessian -/

/-- `Re H_p(y)(a, b) = (D²p(a, b) + D²p(i a, i b)) / 4`. -/
def hermRe (p : ComplexModel n → ℝ) (y a b : ComplexModel n) : ℝ :=
  (realHessian p y a b + realHessian p y (I • a) (I • b)) / 4

theorem hermRe_self (p : ComplexModel n → ℝ) (y a : ComplexModel n) :
    hermRe p y a a = leviForm p y a := rfl

theorem hermRe_comm {p : ComplexModel n → ℝ} {y : ComplexModel n} (hp : ContDiffAt ℝ 2 p y)
    (a b : ComplexModel n) : hermRe p y a b = hermRe p y b a := by
  have hs := hp.isSymmSndFDerivAt (by simp)
  simp only [hermRe, realHessian_eq_fderiv]
  rw [hs a b, hs (I • a) (I • b)]

theorem hermRe_neg_right (p : ComplexModel n → ℝ) (y a b : ComplexModel n) :
    hermRe p y a (-b) = -hermRe p y a b := by
  simp only [hermRe, realHessian_eq_fderiv, smul_neg, map_neg]
  ring

theorem hermRe_smul_right (p : ComplexModel n → ℝ) (y a b : ComplexModel n) (t : ℝ) :
    hermRe p y a (t • b) = t * hermRe p y a b := by
  simp only [hermRe, realHessian_eq_fderiv, smul_comm I t b, map_smul, smul_eq_mul]
  ring

theorem leviForm_neg (p : ComplexModel n → ℝ) (y a : ComplexModel n) :
    leviForm p y (-a) = leviForm p y a := by
  simp only [leviForm, realHessian_eq_fderiv, smul_neg, map_neg, neg_apply,
    neg_neg]

theorem leviForm_I_smul (p : ComplexModel n → ℝ) (y a : ComplexModel n) :
    leviForm p y (I • a) = leviForm p y a := by
  have h : I • I • a = -a := by rw [smul_smul, I_mul_I, neg_one_smul]
  simp only [leviForm, h, realHessian_eq_fderiv, map_neg, neg_apply, neg_neg]
  ring

/-- `L(a + b) = L(a) + L(b) + 2 Re H(a, b)`. -/
theorem leviForm_add_eq {p : ComplexModel n → ℝ} {y : ComplexModel n} (hp : ContDiffAt ℝ 2 p y)
    (a b : ComplexModel n) :
    leviForm p y (a + b) = leviForm p y a + leviForm p y b + 2 * hermRe p y a b := by
  have hs := hp.isSymmSndFDerivAt (by simp)
  simp only [leviForm, hermRe, realHessian_eq_fderiv, smul_add, map_add,
    add_apply]
  rw [hs b a, hs (I • b) (I • a)]
  ring

/-- **Completing the square:** `L(a) + 2 Re H(a, b) ≥ -L(b)` when `L(a + b) ≥ 0`. -/
theorem neg_leviForm_le_add_two_hermRe {p : ComplexModel n → ℝ} {y : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p y) (a b : ComplexModel n) (hab : 0 ≤ leviForm p y (a + b)) :
    -leviForm p y b ≤ leviForm p y a + 2 * hermRe p y a b := by
  have h := leviForm_add_eq hp a b
  linarith

/-- **Cauchy–Schwarz:** `2 |Re H(a, b)| ≤ L(a) + L(b)` for a positive semidefinite Levi form. -/
theorem two_mul_abs_hermRe_le {p : ComplexModel n → ℝ} {y : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p y) (hpsh : ∀ v, 0 ≤ leviForm p y v) (a b : ComplexModel n) :
    2 * |hermRe p y a b| ≤ leviForm p y a + leviForm p y b := by
  have h1 := leviForm_add_eq hp a b
  have h2 := leviForm_add_eq hp a (-b)
  rw [hermRe_neg_right, leviForm_neg] at h2
  have h3 := hpsh (a + b)
  have h4 := hpsh (a + -b)
  rcases abs_cases (hermRe p y a b) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

/-- The second real derivative of `ofReal ∘ p` is the coercion of that of `p`. -/
theorem fderiv_fderiv_ofReal_apply {p : ComplexModel n → ℝ} {y : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p y) (a b : ComplexModel n) :
    fderiv ℝ (fderiv ℝ (fun x => (p x : ℂ))) y a b = (fderiv ℝ (fderiv ℝ p) y a b : ℂ) := by
  have hpc : ContDiffAt ℝ 2 (fun x => (p x : ℂ)) y :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp y hp
  rw [← fderiv_fderiv_apply_eq hpc, ← fderiv_fderiv_apply_eq hp]
  have hev : (fun x => fderiv ℝ (fun x => (p x : ℂ)) x b) =ᶠ[𝓝 y]
      fun x => ((fderiv ℝ p x b : ℝ) : ℂ) := by
    filter_upwards [(hp.eventually (by simp)).mono fun x hx => hx.differentiableAt
      (by norm_num)] with x hx using fderiv_ofReal_comp_apply hx b
  rw [hev.fderiv_eq]
  have hdiff : DifferentiableAt ℝ (fun x => fderiv ℝ p x b) y := by
    have hDD : DifferentiableAt ℝ (fderiv ℝ p) y :=
      (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    exact hDD.clm_apply (differentiableAt_const b)
  exact fderiv_ofReal_comp_apply hdiff a

/-- **The complex Hessian through its real part:** `∂̄_b ∂_a p = H(a, b) + i H(a, i b)`. -/
theorem dbarDir_dDir_ofReal_eq {p : ComplexModel n → ℝ} {y : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p y) (a b : ComplexModel n) :
    dbarDir b (dDir a (fun x => (p x : ℂ))) y =
      (hermRe p y a b : ℂ) + I * (hermRe p y a (I • b) : ℂ) := by
  have hpc : ContDiffAt ℝ 2 (fun x => (p x : ℂ)) y :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp y hp
  have hs := hp.isSymmSndFDerivAt (by simp)
  have hII : I • I • b = -b := by rw [smul_smul, I_mul_I, neg_one_smul]
  simp only [dbarDir, fderiv_dDir_apply hpc, fderiv_fderiv_ofReal_apply hp, hermRe,
    realHessian_eq_fderiv, hII, map_neg, neg_apply]
  rw [hs b a, hs b (I • a), hs (I • b) a, hs (I • b) (I • a)]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- `|∂̄_b ∂_a p| ≤ L(a) + L(b)` for a positive semidefinite Levi form. -/
theorem norm_dbarDir_dDir_ofReal_le {p : ComplexModel n → ℝ} {y : ComplexModel n}
    (hp : ContDiffAt ℝ 2 p y) (hpsh : ∀ v, 0 ≤ leviForm p y v) (a b : ComplexModel n) :
    ‖dbarDir b (dDir a (fun x => (p x : ℂ))) y‖ ≤ leviForm p y a + leviForm p y b := by
  rw [dbarDir_dDir_ofReal_eq hp]
  have h1 := two_mul_abs_hermRe_le hp hpsh a b
  have h2 := two_mul_abs_hermRe_le hp hpsh a (I • b)
  rw [leviForm_I_smul] at h2
  calc ‖(hermRe p y a b : ℂ) + I * (hermRe p y a (I • b) : ℂ)‖
      ≤ ‖(hermRe p y a b : ℂ)‖ + ‖I * (hermRe p y a (I • b) : ℂ)‖ := norm_add_le _ _
    _ = |hermRe p y a b| + |hermRe p y a (I • b)| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ leviForm p y a + leviForm p y b := by linarith

/-! ### The Levi form along a curve -/

/-- **Second-order chain rule along a curve:** for `γ : ℂ → ℂⁿ`,
`L(p ∘ γ)(0)[1] = (D²p(γ'1, γ'1) + D²p(γ'i, γ'i))/4 + Dp(¼(γ''(1,1) + γ''(i,i)))`. -/
theorem leviForm_comp_curve {γ : ℂ → ComplexModel n} {p : ComplexModel n → ℝ}
    (hγ : ContDiffAt ℝ 2 γ 0) (hp : ContDiffAt ℝ 2 p (γ 0)) :
    leviForm (fun τ => p (γ τ)) 0 1 =
      (realHessian p (γ 0) (fderiv ℝ γ 0 1) (fderiv ℝ γ 0 1) +
        realHessian p (γ 0) (fderiv ℝ γ 0 I) (fderiv ℝ γ 0 I)) / 4 +
      fderiv ℝ p (γ 0) ((4 : ℝ)⁻¹ • (fderiv ℝ (fderiv ℝ γ) 0 1 1 +
        fderiv ℝ (fderiv ℝ γ) 0 I I)) := by
  simp only [leviForm, realHessian_comp_vec hγ hp, smul_eq_mul, mul_one, map_smul, map_add]
  ring

/-- The polarisation of the real Hessian along `a = Y + X`, `b = i Y - i X`. -/
theorem realHessian_split {p : ComplexModel n → ℝ} {y : ComplexModel n} (hp : ContDiffAt ℝ 2 p y)
    (Y X : ComplexModel n) :
    (realHessian p y (Y + X) (Y + X) + realHessian p y (I • Y - I • X) (I • Y - I • X)) / 4 =
      leviForm p y Y + leviForm p y X +
        (realHessian p y Y X - realHessian p y (I • Y) (I • X)) / 2 := by
  have hs := hp.isSymmSndFDerivAt (by simp)
  simp only [leviForm, realHessian_eq_fderiv, map_add, map_sub, add_apply,
    sub_apply]
  rw [hs X Y, hs (I • X) (I • Y)]
  ring

/-! ### The Wirtinger derivatives of a curve family -/

/-- `∂_τ c(0, ζ) = ½(D_τ c(1) - i D_τ c(i))`. -/
def curveDz (c : ℂ → ComplexModel n → ComplexModel n) (ζ : ComplexModel n) : ComplexModel n :=
  (2 : ℝ)⁻¹ • (fderiv ℝ (fun τ => c τ ζ) 0 1 - I • fderiv ℝ (fun τ => c τ ζ) 0 I)

/-- `∂_τ̄ c(0, ζ) = ½(D_τ c(1) + i D_τ c(i))`. -/
def curveDzbar (c : ℂ → ComplexModel n → ComplexModel n) (ζ : ComplexModel n) :
    ComplexModel n :=
  (2 : ℝ)⁻¹ • (fderiv ℝ (fun τ => c τ ζ) 0 1 + I • fderiv ℝ (fun τ => c τ ζ) 0 I)

/-- `∂_τ ∂_τ̄ c(0, ζ) = ¼(D²_τ c(1, 1) + D²_τ c(i, i))`. -/
def curveLevi (c : ℂ → ComplexModel n → ComplexModel n) (ζ : ComplexModel n) : ComplexModel n :=
  (4 : ℝ)⁻¹ • (fderiv ℝ (fderiv ℝ (fun τ => c τ ζ)) 0 1 1 +
    fderiv ℝ (fderiv ℝ (fun τ => c τ ζ)) 0 I I)

theorem curveDz_add_curveDzbar (c : ℂ → ComplexModel n → ComplexModel n) (ζ : ComplexModel n) :
    curveDz c ζ + curveDzbar c ζ = fderiv ℝ (fun τ => c τ ζ) 0 1 := by
  simp only [curveDz, curveDzbar, ← smul_add]
  rw [sub_add_add_cancel, ← two_smul ℝ, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

theorem I_smul_curveDz_sub (c : ℂ → ComplexModel n → ComplexModel n) (ζ : ComplexModel n) :
    I • curveDz c ζ - I • curveDzbar c ζ = fderiv ℝ (fun τ => c τ ζ) 0 I := by
  simp only [curveDz, curveDzbar, ← smul_sub, smul_comm I ((2 : ℝ)⁻¹)]
  set a := fderiv ℝ (fun τ => c τ ζ) 0 1
  set b := fderiv ℝ (fun τ => c τ ζ) 0 I
  have h : I • (a - I • b - (a + I • b)) = (2 : ℝ) • b := by
    have e1 : a - I • b - (a + I • b) = -((2 : ℝ) • (I • b)) := by rw [two_smul]; abel
    rw [e1, smul_neg, smul_comm I (2 : ℝ), smul_smul I I, I_mul_I, neg_one_smul, smul_neg, neg_neg]
  rw [h, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]

/-! ### The holomorphic derivative `ℓ = ∂p(Φ)·Ŷ` -/

/-- `ℓ(s) = ∂p(Φ s) · Ŷ(s)`. -/
def holDeriv (p : ComplexModel n → ℝ) (Φ Y : ComplexModel n → ComplexModel n)
    (s : ComplexModel n) : ℂ :=
  dDir (Y s) (fun x => (p x : ℂ)) (Φ s)

/-- `∂_v p̂(y) = (Dp(y) v - i Dp(y)(i v)) / 2`. -/
theorem dDir_ofReal_eq {p : ComplexModel n → ℝ} {y : ComplexModel n}
    (hp : DifferentiableAt ℝ p y) (v : ComplexModel n) :
    dDir v (fun x => (p x : ℂ)) y = ((fderiv ℝ p y v : ℂ) - I * (fderiv ℝ p y (I • v) : ℂ)) / 2 := by
  simp only [dDir, fderiv_ofReal_comp_apply hp]

/-- Real parts of `∂_X` and `∂̄_k` of `ℓ = (L₁ - i L₂)/2` with real `L₁, L₂`. -/
theorem re_dDir_dbarDir_of_eq {ℓ : ComplexModel n → ℂ} {L₁ L₂ : ComplexModel n → ℝ}
    {ζ : ComplexModel n} {D₁ D₂ : ComplexModel n →L[ℝ] ℝ}
    (hℓ : ℓ =ᶠ[𝓝 ζ] fun s => ((L₁ s : ℂ) - I * (L₂ s : ℂ)) / 2)
    (h₁ : HasFDerivAt L₁ D₁ ζ) (h₂ : HasFDerivAt L₂ D₂ ζ) (X k : ComplexModel n) :
    2 * (dDir X ℓ ζ).re = (D₁ X - D₂ (I • X)) / 2 ∧
      (dbarDir k ℓ ζ).re = (D₁ k + D₂ (I • k)) / 4 := by
  have hd : HasFDerivAt (fun s => ((L₁ s : ℂ) - I * (L₂ s : ℂ)) / 2)
      ((2 : ℝ)⁻¹ • ((Complex.ofRealCLM.comp D₁) - I • (Complex.ofRealCLM.comp D₂))) ζ := by
    have e : (fun s => ((L₁ s : ℂ) - I * (L₂ s : ℂ)) / 2) =
        fun s => (2 : ℝ)⁻¹ • (Complex.ofRealCLM (L₁ s) - I • Complex.ofRealCLM (L₂ s)) := by
      funext s
      simp only [Complex.ofRealCLM_apply, smul_eq_mul, Complex.real_smul]
      push_cast; ring
    rw [e]
    exact (((Complex.ofRealCLM.hasFDerivAt.comp ζ h₁).sub
      ((Complex.ofRealCLM.hasFDerivAt.comp ζ h₂).const_smul I)).const_smul (2 : ℝ)⁻¹)
  have hf : fderiv ℝ ℓ ζ = (2 : ℝ)⁻¹ • ((Complex.ofRealCLM.comp D₁) -
      I • (Complex.ofRealCLM.comp D₂)) := by
    rw [hℓ.fderiv_eq, hd.fderiv]
  constructor
  · simp only [dDir, hf, smul_apply, sub_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.real_smul]
    simp [Complex.mul_re, Complex.mul_im]
    ring
  · simp only [dbarDir, hf, smul_apply, sub_apply,
      ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.real_smul]
    simp [Complex.mul_re, Complex.mul_im]
    ring

/-- **The derivatives of `ℓ = ∂p(Φ)·Ŷ`** for holomorphic `Φ`, `Ŷ`:
`2 Re ∂_X ℓ = (D²p(DΦ X, Ŷ) - D²p(i DΦ X, i Ŷ))/2 + Dp(DŶ X)` and
`Re ∂̄_k ℓ = Re H_p(Ŷ, DΦ k)`. -/
theorem re_dDir_holDeriv {p : ComplexModel n → ℝ} {Φ Y : ComplexModel n → ComplexModel n}
    {ζ : ComplexModel n} (hp : ContDiffAt ℝ 2 p (Φ ζ)) (hΦ : DifferentiableAt ℂ Φ ζ)
    (hY : DifferentiableAt ℂ Y ζ) (X k : ComplexModel n) :
    2 * (dDir X (holDeriv p Φ Y) ζ).re =
        (realHessian p (Φ ζ) (fderiv ℂ Φ ζ X) (Y ζ) -
          realHessian p (Φ ζ) (I • fderiv ℂ Φ ζ X) (I • Y ζ)) / 2 +
          fderiv ℝ p (Φ ζ) (fderiv ℂ Y ζ X) ∧
      (dbarDir k (holDeriv p Φ Y) ζ).re = hermRe p (Φ ζ) (Y ζ) (fderiv ℂ Φ ζ k) := by
  have hΦR : HasFDerivAt Φ ((fderiv ℂ Φ ζ).restrictScalars ℝ) ζ :=
    hΦ.hasFDerivAt.restrictScalars ℝ
  have hYR : HasFDerivAt Y ((fderiv ℂ Y ζ).restrictScalars ℝ) ζ :=
    hY.hasFDerivAt.restrictScalars ℝ
  have hDDp : DifferentiableAt ℝ (fderiv ℝ p) (Φ ζ) :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hc : HasFDerivAt (fun s => fderiv ℝ p (Φ s))
      ((fderiv ℝ (fderiv ℝ p) (Φ ζ)).comp ((fderiv ℂ Φ ζ).restrictScalars ℝ)) ζ :=
    hDDp.hasFDerivAt.comp ζ hΦR
  have h₁ := hc.clm_apply hYR
  have h₂ := hc.clm_apply (hYR.const_smul I)
  have hpd : ∀ᶠ s in 𝓝 ζ, DifferentiableAt ℝ p (Φ s) :=
    hΦ.continuousAt.eventually ((hp.eventually (by simp)).mono fun y hy =>
      hy.differentiableAt (by norm_num))
  have hℓ : holDeriv p Φ Y =ᶠ[𝓝 ζ] fun s =>
      (((fderiv ℝ p (Φ s) (Y s) : ℝ) : ℂ) - I * ((fderiv ℝ p (Φ s) (I • Y s) : ℝ) : ℂ)) / 2 := by
    filter_upwards [hpd] with s hs
    exact dDir_ofReal_eq hs (Y s)
  obtain ⟨hA, hB⟩ := re_dDir_dbarDir_of_eq hℓ h₁ h₂ X k
  have hs := hp.isSymmSndFDerivAt (by simp)
  have hII : ∀ v : ComplexModel n, I • I • v = -v := fun v => by
    rw [smul_smul, I_mul_I, neg_one_smul]
  refine ⟨?_, ?_⟩
  · rw [hA]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.flip_apply,
      smul_apply, map_smul, hII, map_neg, realHessian_eq_fderiv,
      Pi.smul_apply]
    ring
  · rw [hB]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.flip_apply,
      smul_apply, map_smul, hII, map_neg, hermRe, realHessian_eq_fderiv,
      Pi.smul_apply]
    rw [hs (Y ζ) (fderiv ℂ Φ ζ k), hs (I • Y ζ) (I • fderiv ℂ Φ ζ k)]
    ring

/-- **The pointwise identity** for the Levi form of `τ ↦ p(c(τ, ζ))` at `τ = 0`:
`L = L_p[Ŷ] + L_p[X̂] + 2 Re ∂_X ℓ + D(p ∘ Φ)(R)` when `X̂ = DΦ X` and `Q̂ - DŶ X = DΦ R`. -/
theorem leviForm_curve_eq {c : ℂ → ComplexModel n → ComplexModel n} {p : ComplexModel n → ℝ}
    {ζ : ComplexModel n} (hc : ContDiffAt ℝ 2 (fun τ => c τ ζ) 0)
    (hp : ContDiffAt ℝ 2 p (c 0 ζ)) (hΦ : DifferentiableAt ℂ (c 0) ζ)
    (hY : DifferentiableAt ℂ (curveDz c) ζ) (X R : ComplexModel n)
    (hX : fderiv ℂ (c 0) ζ X = curveDzbar c ζ)
    (hR : fderiv ℂ (c 0) ζ R = curveLevi c ζ - fderiv ℂ (curveDz c) ζ X) :
    leviForm (fun τ => p (c τ ζ)) 0 1 =
      leviForm p (c 0 ζ) (curveDz c ζ) + leviForm p (c 0 ζ) (curveDzbar c ζ) +
        2 * (dDir X (holDeriv p (c 0) (curveDz c)) ζ).re +
        fderiv ℝ (fun s => p (c 0 s)) ζ R := by
  have h1 : leviForm (fun τ => p (c τ ζ)) 0 1 =
      (realHessian p (c 0 ζ) (curveDz c ζ + curveDzbar c ζ) (curveDz c ζ + curveDzbar c ζ) +
        realHessian p (c 0 ζ) (I • curveDz c ζ - I • curveDzbar c ζ)
          (I • curveDz c ζ - I • curveDzbar c ζ)) / 4 +
      fderiv ℝ p (c 0 ζ) (curveLevi c ζ) := by
    rw [curveDz_add_curveDzbar, I_smul_curveDz_sub]
    exact leviForm_comp_curve (γ := fun τ => c τ ζ) hc hp
  have hsplit := realHessian_split hp (curveDz c ζ) (curveDzbar c ζ)
  have h2 := (re_dDir_holDeriv (p := p) (Φ := c 0) (Y := curveDz c) hp hΦ hY X X).1
  rw [hX] at h2
  have hpd : DifferentiableAt ℝ p (c 0 ζ) := hp.differentiableAt (by norm_num)
  have hchain : fderiv ℝ (fun s => p (c 0 s)) ζ R = fderiv ℝ p (c 0 ζ) (fderiv ℂ (c 0) ζ R) := by
    have h := (hpd.hasFDerivAt.comp ζ (hΦ.hasFDerivAt.restrictScalars ℝ)).fderiv
    exact congrArg (fun L : ComplexModel n →L[ℝ] ℝ => L R) h
  have hR' : fderiv ℝ (fun s => p (c 0 s)) ζ R = fderiv ℝ p (c 0 ζ) (curveLevi c ζ) -
      fderiv ℝ p (c 0 ζ) (fderiv ℂ (curveDz c) ζ X) := by
    rw [hchain, hR, map_sub]
  have hs := hp.isSymmSndFDerivAt (by simp)
  have hsym1 : realHessian p (c 0 ζ) (curveDzbar c ζ) (curveDz c ζ) =
      realHessian p (c 0 ζ) (curveDz c ζ) (curveDzbar c ζ) := by
    simp only [realHessian_eq_fderiv]; exact hs _ _
  have hsym2 : realHessian p (c 0 ζ) (I • curveDzbar c ζ) (I • curveDz c ζ) =
      realHessian p (c 0 ζ) (I • curveDz c ζ) (I • curveDzbar c ζ) := by
    simp only [realHessian_eq_fderiv]; exact hs _ _
  linarith

end SGPT.NPP.DN4
