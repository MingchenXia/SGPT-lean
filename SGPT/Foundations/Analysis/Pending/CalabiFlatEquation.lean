import SGPT.Foundations.Analysis.Pending.CalabiFlatLaplacian

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Calabi's identity for a solution of `log det H = F`, at a point with `H = 1`

Let `u` be smooth on `ℂⁿ`, `H = (u_{jk̄})`, and suppose `log det H = F` near a point `x` with `H(x) = 1`,
`F` smooth. Then (`calabi_identity`), with `S` Calabi's quantity (`CalabiFlatLaplacian.calabiS`),

  `Σ_p ∂_p∂̄_p S(x) = |∇Γ|² + |∇̄Γ|² + 2 Re Σ_m tr(F_{··̄m} X_m*) - Ric(F_{··̄})`,

where `F_{··̄m} = ∂_m (F_{ab̄})` and `F_{··̄} = (F_{ab̄})` at `x`; this is the flat-reference form of PSS
(2.43)/(2.44) (`pss07-multiplier-krf:page-0009`). The equation enters through its second and third
derivatives (`complexHessian_at`, `wirtM_complexHessian_at`): `∂_a∂̄_b log det H = tr(P Z_{ab}) -
tr(P X_a P X_b*)` near `x` (`wirt_wirt_log_det`, Jacobi's formula) and its `∂_m` at `x`
(`wirt_logDetHess`); the fifth derivatives of `u` commute (`trace_dW`).

TN.4 B5, nonlinear track N4 (b), blueprint `bou:yau-c3-estimate`.
-/

open Set Filter Matrix Complex
open scoped Topology ContDiff ComplexConjugate

namespace SGPT.Foundations.Analysis.Pending.CalabiFlatEquation

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet CalabiFlatIdentity
  CalabiFlatLaplacian

noncomputable section

variable {n : ℕ} {u : ComplexModel n → ℝ}

theorem wirt_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : ℂ} {v : E}
    {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    wirt c v (fun y => f y - g y) x = wirt c v f x - wirt c v g x := by
  simp only [wirt, fderiv_fun_sub hf hg, _root_.sub_apply]
  ring

/-- The fifth derivatives commute: `tr(∂_m∂̄_b∂_a H) = Σ_p ∂_p∂̄_p∂_m H_{ab}`. -/
theorem trace_dW (hu : ContDiff ℝ ∞ u) (m a b : Fin n) (y : ComplexModel n) :
    (dW u m b a y).trace = ∑ p, dW u p p m y a b := by
  have hû := BlockiLocalEstimate.contDiff_ofReal_comp hu
  have hent : ∀ p q m a b, (fun y => dW u p q m y a b) = wirt (-I) (coordinateVector p)
      (wirt (-I) (coordinateVector m) (wirt (-I) (coordinateVector a) (wirt I (coordinateVector q)
        (wirt I (coordinateVector b) (fun z => (u z : ℂ)))))) := fun p q m a b => by
    funext y
    simp only [dW, wirtM_apply]
    rw [dZ_entry hu]
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [congrFun (hent m b a p p) y, congrFun (hent p p m a b) y,
    BlockiLocalEstimate.wirt_comm_fun (c := I) (v := coordinateVector b) (d := I)
      (w := coordinateVector p) hû]
  have h2 := contDiff_wirt (c := I) (v := coordinateVector p)
    (contDiff_wirt (c := I) (v := coordinateVector b) hû)
  rw [BlockiLocalEstimate.wirt_comm_fun (c := -I) (v := coordinateVector p) (d := -I)
      (w := coordinateVector m) (contDiff_wirt (c := -I) (v := coordinateVector a) h2),
    BlockiLocalEstimate.wirt_comm_fun (c := -I) (v := coordinateVector p) (d := -I)
      (w := coordinateVector a) h2]

/-- `∂̄_b log det H = tr(P X_b*)` where `det H > 0`. -/
theorem wirt_I_log_det (hu : ContDiff ℝ ∞ u) {y : ComplexModel n}
    (hy : 0 < (complexHessian u y).det.re) (b : Fin n) :
    wirt I (coordinateVector b) (fun z => ((Real.log (complexHessian u z).det.re : ℝ) : ℂ)) y =
      (invH u y * (dH u b y)ᴴ).trace := by
  have hDc : ∀ z, (((complexHessian u z).det.re : ℝ) : ℂ) = (complexHessian u z).det := fun z =>
    ofReal_re_det_of_isHermitian (isHermitian_complexHessian hu z)
  have hDcont : ContDiff ℝ ∞ (fun z => (complexHessian u z).det.re) :=
    Complex.reCLM.contDiff.comp (contDiff_det_complexHessian hu)
  have hdetne : (complexHessian u y).det ≠ 0 := by
    rw [← hDc y]; exact_mod_cast hy.ne'
  rw [wirt_ofReal_log (hDcont.differentiable (by simp) y) hy.ne']
  have hfun : (fun z => (((complexHessian u z).det.re : ℝ) : ℂ)) =
      fun z => (complexHessian u z).det := funext hDc
  rw [hfun, wirt_det_eq_det_mul_trace (fun i j => (mSmooth_complexHessian hu).mdiffAt y i j)
    hdetne, hDc y, mul_div_cancel_left₀ _ hdetne, wirtM_I_complexHessian hu]
  rfl

/-- The function `∂_a∂̄_b log det H = tr(P Z_{ab}) - tr(P X_a P X_b*)`. -/
def logDetHess (u : ComplexModel n → ℝ) (a b : Fin n) (y : ComplexModel n) : ℂ :=
  (invH u y * dZ u a b y).trace - (invH u y * dH u a y * invH u y * (dH u b y)ᴴ).trace

theorem wirt_wirt_log_det (hu : ContDiff ℝ ∞ u) {y : ComplexModel n}
    (hy : 0 < (complexHessian u y).det.re) (a b : Fin n) :
    wirt (-I) (coordinateVector a) (wirt I (coordinateVector b)
      (fun z => ((Real.log (complexHessian u z).det.re : ℝ) : ℂ))) y = logDetHess u a b y := by
  have hDcont : Continuous (fun z => (complexHessian u z).det.re) :=
    (Complex.reCLM.contDiff.comp (contDiff_det_complexHessian hu)).continuous
  have hpos : ∀ᶠ z in 𝓝 y, 0 < (complexHessian u z).det.re :=
    continuousAt_const.eventually_lt hDcont.continuousAt hy
  have hdet : (complexHessian u y).det ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hy; exact lt_irrefl _ hy
  rw [wirt_congr (hpos.mono fun z hz => wirt_I_log_det hu hz b)]
  have hP := mdiffAt_invH hu hdet
  have hXh := (mSmooth_dH hu b).conjTranspose.mdiffAt y
  rw [wirt_trace (hP.mul hXh), wirtM_mul hP hXh, wirtM_invH hu hdet,
    wirtM_negI_conjTranspose ((mSmooth_dH hu b).mdiffAt y)]
  have e1 : wirtM I (coordinateVector a) (dH u b) y = dZ u b a y := rfl
  have e2 : wirtM (-I) (coordinateVector a) (complexHessian u) y = dH u a y := rfl
  rw [e1, e2, dZ_conjTranspose hu]
  simp only [logDetHess, Matrix.neg_mul, trace_add, trace_neg]
  ring

/-- `∂_m` of `∂_a∂̄_b log det H` at a point with `H = 1`. -/
theorem wirt_logDetHess (hu : ContDiff ℝ ∞ u) {x : ComplexModel n} (hx : complexHessian u x = 1)
    (m a b : Fin n) :
    wirt (-I) (coordinateVector m) (logDetHess u a b) x =
      -(dH u m x * dZ u a b x).trace + (dW u m b a x).trace +
        (dH u m x * dH u a x * (dH u b x)ᴴ).trace - (dV u m a x * (dH u b x)ᴴ).trace +
        (dH u a x * dH u m x * (dH u b x)ᴴ).trace - (dH u a x * dZ u m b x).trace := by
  have hd := det_ne_zero_of_eq_one hu hx
  have hP := mdiffAt_invH hu hd
  have hZ := (mSmooth_dZ hu a b).mdiffAt x
  have hXa := (mSmooth_dH hu a).mdiffAt x
  have hXhb := (mSmooth_dH hu b).conjTranspose.mdiffAt x
  change wirt (-I) (coordinateVector m) (fun y => (invH u y * dZ u a b y).trace -
    (invH u y * dH u a y * invH u y * (dH u b y)ᴴ).trace) x = _
  rw [wirt_sub (hP.mul hZ).differentiableAt_trace
      (((hP.mul hXa).mul hP).mul hXhb).differentiableAt_trace,
    wirt_trace (hP.mul hZ), wirt_trace (((hP.mul hXa).mul hP).mul hXhb), wirtM_mul hP hZ,
    wirtM_mul ((hP.mul hXa).mul hP) hXhb, wirtM_mul (hP.mul hXa) hP, wirtM_mul hP hXa,
    wirtM_negI_invH hu hx, wirtM_negI_dH_conjTranspose hu hx, invH_eq_one hu hx]
  have e1 : wirtM (-I) (coordinateVector m) (dZ u a b) x = dW u m b a x := rfl
  have e2 : wirtM (-I) (coordinateVector m) (dH u a) x = dV u m a x := rfl
  rw [e1, e2]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.add_mul, Matrix.neg_mul,
    Matrix.mul_neg, trace_add, trace_neg]
  ring

section Equation

variable {F : ComplexModel n → ℝ} {x : ComplexModel n} (hu : ContDiff ℝ ∞ u)
  (hF : ContDiff ℝ ∞ F) (hx : complexHessian u x = 1)
  (heq : ∀ᶠ y in 𝓝 x, Real.log (complexHessian u y).det.re = F y)
include hu hF hx heq

theorem eventually_complexHessian_eq (a b : Fin n) :
    ∀ᶠ y in 𝓝 x, complexHessian F y a b = logDetHess u a b y := by
  have hpos : ∀ᶠ y in 𝓝 x, 0 < (complexHessian u y).det.re := by
    have hDcont : Continuous (fun z => (complexHessian u z).det.re) :=
      (Complex.reCLM.contDiff.comp (contDiff_det_complexHessian hu)).continuous
    have h1 : (0 : ℝ) < (complexHessian u x).det.re := by simp [hx]
    exact continuousAt_const.eventually_lt hDcont.continuousAt h1
  have h2 : ∀ᶠ y in 𝓝 x, (fun z => ((F z : ℝ) : ℂ)) =ᶠ[𝓝 y]
      fun z => ((Real.log (complexHessian u z).det.re : ℝ) : ℂ) :=
    heq.eventually_nhds.mono fun y hy => hy.mono fun z hz => by simp only [hz]
  have h3 : ∀ᶠ y in 𝓝 x, wirt I (coordinateVector b) (fun z => ((F z : ℝ) : ℂ)) =ᶠ[𝓝 y]
      wirt I (coordinateVector b) (fun z => ((Real.log (complexHessian u z).det.re : ℝ) : ℂ)) :=
    h2.eventually_nhds.mono fun y hy => hy.mono fun z hz => wirt_congr hz
  filter_upwards [h3, hpos] with y hy hy'
  rw [complexHessian_eq_wirt (AubinYauLocalStep.contDiffAt_two hF y) a b, wirt_congr hy,
    wirt_wirt_log_det hu hy' a b]

theorem complexHessian_at (a b : Fin n) :
    complexHessian F x a b = (dZ u a b x).trace - (dH u a x * (dH u b x)ᴴ).trace := by
  rw [(eventually_complexHessian_eq hu hF hx heq a b).self_of_nhds, logDetHess,
    invH_eq_one hu hx, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one]

theorem wirtM_complexHessian_at (m a b : Fin n) :
    wirtM (-I) (coordinateVector m) (complexHessian F) x a b =
      -(dH u m x * dZ u a b x).trace + (dW u m b a x).trace +
        (dH u m x * dH u a x * (dH u b x)ᴴ).trace - (dV u m a x * (dH u b x)ᴴ).trace +
        (dH u a x * dH u m x * (dH u b x)ᴴ).trace - (dH u a x * dZ u m b x).trace := by
  rw [wirtM_apply, wirt_congr (eventually_complexHessian_eq hu hF hx heq a b),
    wirt_logDetHess hu hx]

/-- **Calabi's identity for a solution of `log det H = F`** at a point with `H = 1` (flat reference
metric; PSS (2.43)/(2.44) with `R̂ = 0`, `pss07-multiplier-krf:page-0009`):
`Σ_p ∂_p∂̄_p S = |∇Γ|² + |∇̄Γ|² + 2 Re Σ_m tr(F_{··̄m} X_m*) - Ric(F_{··̄})`. -/
theorem calabi_identity :
    ∑ p, wirt (-I) (coordinateVector p) (wirt I (coordinateVector p) (calabiS u)) x =
      ∑ p, ∑ m, (calA (fun m => dH u m x) (fun p m => dV u p m x) p m *
          (calA (fun m => dH u m x) (fun p m => dV u p m x) p m)ᴴ).trace +
        ∑ m, ∑ q, (calB (fun m => dH u m x) (fun m q => dZ u m q x) m q *
          (calB (fun m => dH u m x) (fun m q => dZ u m q x) m q)ᴴ).trace +
        (∑ m, (wirtM (-I) (coordinateVector m) (complexHessian F) x * (dH u m x)ᴴ).trace +
          star (∑ m, (wirtM (-I) (coordinateVector m) (complexHessian F) x * (dH u m x)ᴴ).trace)) -
        ricTerm (fun m => dH u m x) (complexHessian F x) := by
  rw [sum_wirt_wirt_calabiS hu hx]
  refine calabiFlatSum_eq _ _ _ _ _ _ (fun m a b => congrFun (dH_symm hu m a b) x)
    (fun p m => dV_symm hu p m x) (fun p m a b => dV_symm' hu p m a b x)
    (fun m q a b => dZ_symm hu m q a b x) (fun m q a b => dZ_symm' hu m q a b x)
    (fun m q => dZ_conjTranspose hu m q x) (fun a b => ?_) (fun m a b => ?_)
  · rw [complexHessian_at hu hF hx heq]; ring
  · rw [Matrix.sum_apply, ← trace_dW hu, wirtM_complexHessian_at hu hF hx heq]; ring

end Equation

end

end SGPT.Foundations.Analysis.Pending.CalabiFlatEquation
