import SGPT.Foundations.Analysis.Pending.WirtingerLogDet
import SGPT.Foundations.Analysis.Pending.AubinYauMatrixBounds

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Błocki's local estimate for the second-derivative bound (LNM 2038, Lemma 5.14)

For a smooth real function `u` on `ℂⁿ` whose complex Hessian `H = (u_{jk̄})` is positive definite at
`x`, and a direction `ζ ≠ 0` (`blocki_local_estimate`):

  `u^{jk̄} (log u_{ζζ̄})_{jk̄}(x) ≥ (log det H)_{ζζ̄}(x) / u_{ζζ̄}(x)`,

where `u_{ζζ̄} = leviForm u · ζ` and the left side is `Re tr(H(x)⁻¹ · Hess_ℂ(log u_{ζζ̄})(x))`.
Source: Z. Błocki, *The Calabi–Yau theorem*, LNM 2038, Lemma 5.14 (`lnm2038-monge-ampere:page-0223`).

## Proof (as in the source)

With `P = H⁻¹`, `X = ∂_ζ H`, `Y = ∂̄_ζ ∂_ζ H` at `x` and `w = ζ̄`:
* `(log det H)_{ζζ̄} = tr(P Y) - tr(P X* P X)` (`WirtingerLogDet.leviForm_log_det_complexHessian`);
* the fourth and third derivatives commute: `∂_a∂̄_b u_{ζζ̄} = Y_{ab}` and `∂_a u_{ζζ̄} = (X w)_a`;
* `Hess_ℂ log L = Hess_ℂ L / L - ∂L ∂̄L / L²`, so
  `Re tr(P Hess_ℂ log u_{ζζ̄}) = Re tr(P Y)/L - (Xw)* P (Xw)/L²`;
* the Schwarz inequality `(Xw)* P (Xw) ≤ (w* H w) · tr(P X* P X)` and `w* H w = u_{ζζ̄}`
  (`re_star_dotProduct_inv_mulVec_le`; the source diagonalises `H`, here `H = R⁻ᴴ R⁻¹`).

TN.4 B5, nonlinear track N3.
-/

open Set Filter Matrix Complex
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BlockiLocalEstimate

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet SemiconcaveHessian

noncomputable section

/-! ### The Schwarz inequality for matrices -/

section MatrixSchwarz

variable {n : ℕ}

theorem re_star_dotProduct_self (a : Fin n → ℂ) : (star a ⬝ᵥ a).re = ∑ i, ‖a i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.star_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul']
  norm_cast

theorem re_trace_conjTranspose_mul_self (N : Matrix (Fin n) (Fin n) ℂ) :
    (Nᴴ * N).trace.re = ∑ j, ∑ i, ‖N i j‖ ^ 2 := by
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

theorem norm_sum_mul_sq_le (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖b j‖ ^ 2 := by
  calc ‖∑ j, a j * b j‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖b j‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖b j‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- `|N s|² ≤ tr(Nᴴ N) |s|²`. -/
theorem re_star_mulVec_dotProduct_le (N : Matrix (Fin n) (Fin n) ℂ) (s : Fin n → ℂ) :
    (star (N *ᵥ s) ⬝ᵥ (N *ᵥ s)).re ≤ (Nᴴ * N).trace.re * (star s ⬝ᵥ s).re := by
  rw [re_star_dotProduct_self, re_trace_conjTranspose_mul_self, re_star_dotProduct_self,
    Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [mulVec, dotProduct]
  exact norm_sum_mul_sq_le _ _

/-- **The Schwarz inequality of Lemma 5.14**: for positive definite `H`,
`(Xw)* H⁻¹ (Xw) ≤ (w* H w) · tr(H⁻¹ X* H⁻¹ X)`. -/
theorem re_star_dotProduct_inv_mulVec_le {H X : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef)
    (w : Fin n → ℂ) :
    (star (X *ᵥ w) ⬝ᵥ (H⁻¹ *ᵥ (X *ᵥ w))).re ≤
      (star w ⬝ᵥ (H *ᵥ w)).re * (H⁻¹ * Xᴴ * H⁻¹ * X).trace.re := by
  classical
  obtain ⟨R, hdet, hHR, -⟩ :=
    ConcentrationEigenvalueBound.exists_simultaneous_diagonalization hH hH
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hRR : R * R⁻¹ = 1 := mul_nonsing_inv R hRu
  have hSH : (star R) * H = R⁻¹ := by
    calc (star R) * H = (star R) * H * (R * R⁻¹) := by rw [hRR, Matrix.mul_one]
      _ = ((star R) * H * R) * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = R⁻¹ := by rw [hHR, Matrix.one_mul]
  have hHinv : H⁻¹ = R * (star R) := by
    refine inv_eq_left_inv ?_
    rw [Matrix.mul_assoc, hSH, hRR]
  set s : Fin n → ℂ := R⁻¹ *ᵥ w with hs
  have hw : w = R *ᵥ s := by rw [hs, mulVec_mulVec, hRR, one_mulVec]
  set N : Matrix (Fin n) (Fin n) ℂ := star R * X * R with hN
  have h1 : star (X *ᵥ w) ⬝ᵥ (H⁻¹ *ᵥ (X *ᵥ w)) = star (N *ᵥ s) ⬝ᵥ (N *ᵥ s) := by
    have e1 : X *ᵥ w = (X * R) *ᵥ s := by rw [hw, mulVec_mulVec]
    rw [e1, hHinv, AubinYauMatrixBounds.star_mulVec_dotProduct_mulVec]
    have e2 := AubinYauMatrixBounds.star_mulVec_dotProduct_mulVec N 1 s
    rw [one_mulVec] at e2
    rw [e2]
    congr 2
    simp only [hN, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_one, Matrix.mul_assoc]
  have h2 : star w ⬝ᵥ (H *ᵥ w) = star s ⬝ᵥ s := by
    rw [hw, AubinYauMatrixBounds.star_mulVec_dotProduct_mulVec, hHR, one_mulVec]
  have h3 : (H⁻¹ * Xᴴ * H⁻¹ * X).trace = (Nᴴ * N).trace := by
    rw [hHinv, hN]
    simp only [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [trace_mul_comm R]
    simp only [Matrix.mul_assoc]
  rw [h1, h2, h3, mul_comm]
  exact re_star_mulVec_dotProduct_le N s

end MatrixSchwarz

/-! ### Scalar calculus -/

section Scalar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_inv' {c : ℂ} {v : E} {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hx : f x ≠ 0) : wirt c v (fun y => (f y)⁻¹) x = -wirt c v f x / f x ^ 2 := by
  have hinv : DifferentiableAt ℝ (fun y => (f y)⁻¹) x := hf.inv hx
  have hev : (fun y => f y * (f y)⁻¹) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
    filter_upwards [hf.continuousAt.eventually_ne hx] with y hy
    exact mul_inv_cancel₀ hy
  have h0 := wirt_eq_zero_of_eventuallyEq_const (c := c) (v := v) hev
  rw [wirt_mul (f := f) (g := fun y => (f y)⁻¹) hf hinv] at h0
  have h1 : f x * wirt c v (fun y => (f y)⁻¹) x = -(wirt c v f x * (f x)⁻¹) :=
    eq_neg_of_add_eq_zero_right h0
  rw [eq_div_iff (pow_ne_zero 2 hx)]
  have h2 := congrArg (fun t => t * f x) h1
  rw [show f x * wirt c v (fun y => (f y)⁻¹) x * f x =
    wirt c v (fun y => (f y)⁻¹) x * f x ^ 2 by ring] at h2
  rw [h2, neg_mul, mul_assoc, inv_mul_cancel₀ hx, mul_one]

/-- Two directional operators commute on a smooth function (as functions). -/
theorem wirt_comm_fun {c d : ℂ} {v w : E} {g : E → ℂ} (hg : ContDiff ℝ ∞ g) :
    wirt c v (wirt d w g) = wirt d w (wirt c v g) :=
  funext fun _ => wirt_wirt_comm (hg.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))

end Scalar

section Hessian

variable {n : ℕ}

theorem coordinateVector_sum (ζ : ComplexModel n) : ∑ d, ζ d • coordinateVector d = ζ := by
  ext i
  simp only [coordinateVector, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Ne.symm hb])
    (by simp)]
  simp

/-- **The complex Hessian of `log L`**: `(log L)_{ab̄} = L_{ab̄}/L - L_a L_b̄ / L²`. -/
theorem complexHessian_log {L : ComplexModel n → ℝ} (hL : ContDiff ℝ ∞ L) {x : ComplexModel n}
    (hx : 0 < L x) (a b : Fin n) :
    complexHessian (fun y => Real.log (L y)) x a b =
      wirt (-I) (coordinateVector a) (wirt I (coordinateVector b) (fun y => (L y : ℂ))) x /
          (L x : ℂ) -
        wirt (-I) (coordinateVector a) (fun y => (L y : ℂ)) x *
          wirt I (coordinateVector b) (fun y => (L y : ℂ)) x / (L x : ℂ) ^ 2 := by
  have hpos : ∀ᶠ y in 𝓝 x, 0 < L y :=
    continuousAt_const.eventually_lt hL.continuous.continuousAt hx
  have hC2 : ContDiffAt ℝ 2 (fun y => Real.log (L y)) x :=
    (hL.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).log hx.ne'
  rw [complexHessian_eq_wirt hC2]
  have hLc : ContDiff ℝ ∞ (fun y => (L y : ℂ)) := ofRealCLM.contDiff.comp hL
  have hLd : ∀ y, DifferentiableAt ℝ (fun y => (L y : ℂ)) y := fun y =>
    hLc.differentiable (by simp) y
  have hdw : DifferentiableAt ℝ (wirt I (coordinateVector b) (fun y => (L y : ℂ))) x :=
    (contDiff_wirt hLc).differentiable (by simp) x
  have hev : wirt I (coordinateVector b) (fun y => ((Real.log (L y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => wirt I (coordinateVector b) (fun y => (L y : ℂ)) y * ((L y : ℂ))⁻¹ := by
    filter_upwards [hpos] with y hy
    rw [wirt_ofReal_log (hL.differentiable (by simp) y) hy.ne', div_eq_mul_inv]
  have hx' : (L x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [wirt_congr hev, wirt_mul (f := wirt I (coordinateVector b) (fun y => (L y : ℂ)))
    (g := fun y => ((L y : ℂ))⁻¹) hdw ((hLd x).inv hx'),
    wirt_inv' (f := fun y => (L y : ℂ)) (hLd x) hx']
  field_simp
  ring

variable {u : ComplexModel n → ℝ}

theorem contDiff_ofReal_comp (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (fun y => (u y : ℂ)) :=
  ofRealCLM.contDiff.comp hu

/-- The Levi form in a fixed direction, as two Wirtinger derivatives. -/
theorem ofReal_leviForm_eq_wirt (hu : ContDiff ℝ ∞ u) (ζ y : ComplexModel n) :
    ((leviForm u y ζ : ℝ) : ℂ) = wirt I ζ (wirt (-I) ζ (fun z => (u z : ℂ))) y := by
  rw [← CauchyGreen.dbarDir_dDir_ofReal_eq_leviForm
    (hu.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) ζ, dbarDir_eq_wirt]
  congr 1
  funext z
  simp only [CauchyGreen.dDir, wirt]
  ring

theorem leviForm_eq_re_wirt (hu : ContDiff ℝ ∞ u) (ζ : ComplexModel n) :
    (fun y => leviForm u y ζ) = fun y => (wirt I ζ (wirt (-I) ζ (fun z => (u z : ℂ))) y).re := by
  funext y
  rw [← ofReal_leviForm_eq_wirt hu ζ y, Complex.ofReal_re]

theorem contDiff_leviForm (hu : ContDiff ℝ ∞ u) (ζ : ComplexModel n) :
    ContDiff ℝ ∞ (fun y => leviForm u y ζ) := by
  rw [leviForm_eq_re_wirt hu ζ]
  exact reCLM.contDiff.comp (contDiff_wirt (contDiff_wirt (contDiff_ofReal_comp hu)))

theorem complexHessian_apply_eq_wirt (hu : ContDiff ℝ ∞ u) (a b : Fin n) :
    (fun y => complexHessian u y a b) =
      wirt (-I) (coordinateVector a) (wirt I (coordinateVector b) (fun z => (u z : ℂ))) :=
  funext fun _ => complexHessian_eq_wirt
    (hu.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) a b

/-- The fourth derivatives commute: `∂_a ∂̄_b u_{ζζ̄} = ∂̄_ζ ∂_ζ u_{ab̄}`. -/
theorem wirt_wirt_leviForm (hu : ContDiff ℝ ∞ u) (ζ x : ComplexModel n) (a b : Fin n) :
    wirt (-I) (coordinateVector a) (wirt I (coordinateVector b)
        (fun y => ((leviForm u y ζ : ℝ) : ℂ))) x =
      wirtM I ζ (fun y => wirtM (-I) ζ (complexHessian u) y) x a b := by
  have hF := contDiff_ofReal_comp hu
  have hL : (fun y => ((leviForm u y ζ : ℝ) : ℂ)) =
      wirt I ζ (wirt (-I) ζ (fun z => (u z : ℂ))) := funext (ofReal_leviForm_eq_wirt hu ζ)
  rw [hL]
  simp only [wirtM_apply]
  rw [complexHessian_apply_eq_wirt hu a b]
  rw [wirt_comm_fun (c := I) (v := coordinateVector b) (d := I) (w := ζ) (contDiff_wirt hF),
    wirt_comm_fun (c := I) (v := coordinateVector b) (d := -I) (w := ζ) hF,
    wirt_comm_fun (c := -I) (v := coordinateVector a) (d := I) (w := ζ)
      (contDiff_wirt (contDiff_wirt hF)),
    wirt_comm_fun (c := -I) (v := coordinateVector a) (d := -I) (w := ζ) (contDiff_wirt hF)]

/-- The third derivatives: `∂_a u_{ζζ̄} = (∂_ζ H · ζ̄)_a`. -/
theorem wirt_leviForm (hu : ContDiff ℝ ∞ u) (ζ x : ComplexModel n) (a : Fin n) :
    wirt (-I) (coordinateVector a) (fun y => ((leviForm u y ζ : ℝ) : ℂ)) x =
      (wirtM (-I) ζ (complexHessian u) x *ᵥ fun d => star (ζ d)) a := by
  have hF := contDiff_ofReal_comp hu
  have hL : (fun y => ((leviForm u y ζ : ℝ) : ℂ)) =
      wirt I ζ (wirt (-I) ζ (fun z => (u z : ℂ))) := funext (ofReal_leviForm_eq_wirt hu ζ)
  rw [hL, ← wirt_comm_fun (c := -I) (v := ζ) (d := I) (w := ζ) hF,
    wirt_comm_fun (c := -I) (v := coordinateVector a) (d := -I) (w := ζ) (contDiff_wirt hF)]
  -- expand `∂̄_ζ` in the coordinate directions
  have hexp : wirt I ζ (fun z => (u z : ℂ)) =
      fun y => ∑ d, star (ζ d) * wirt I (coordinateVector d) (fun z => (u z : ℂ)) y := by
    funext y
    conv_lhs => rw [← coordinateVector_sum ζ]
    rw [← dbarDir_eq_wirt, CauchyGreen.dbarDir_sum_dir]
    rfl
  have hd : ∀ d y, DifferentiableAt ℝ (wirt I (coordinateVector d) (fun z => (u z : ℂ))) y :=
    fun d y => (contDiff_wirt hF).differentiable (by simp) y
  have hexp2 : wirt (-I) (coordinateVector a) (wirt I ζ (fun z => (u z : ℂ))) =
      fun y => ∑ d, star (ζ d) * complexHessian u y a d := by
    funext y
    rw [hexp, wirt_sum Finset.univ
      (f := fun d y => star (ζ d) * wirt I (coordinateVector d) (fun z => (u z : ℂ)) y)
      fun d _ => (hd d y).const_mul _]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [wirt_const_mul _ (hd d y), ← complexHessian_apply_eq_wirt hu a d]
  rw [hexp2]
  have hh : ∀ d, DifferentiableAt ℝ (fun y => complexHessian u y a d) x := fun d =>
    differentiable_complexHessian_apply hu a d x
  rw [wirt_sum Finset.univ (f := fun d y => star (ζ d) * complexHessian u y a d)
    fun d _ => (hh d).const_mul _]
  simp only [mulVec, dotProduct, wirtM_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [wirt_const_mul _ (hh d), mul_comm]

/-- `∂̄_b u_{ζζ̄} = conj(∂_b u_{ζζ̄})` (the function is real). -/
theorem wirt_I_ofReal_eq_conj {L : ComplexModel n → ℝ} (hL : Differentiable ℝ L)
    (v x : ComplexModel n) :
    wirt I v (fun y => (L y : ℂ)) x = conj (wirt (-I) v (fun y => (L y : ℂ)) x) := by
  have h := wirt_I_conj (v := v) (f := fun y => (L y : ℂ)) (x := x)
    ((ofRealCLM.differentiable.comp hL) x)
  simpa only [Complex.conj_ofReal] using h

end Hessian

/-! ### Lemma 5.14 -/

section Lemma

variable {n : ℕ} {u : ComplexModel n → ℝ}

/-- `u_{ζζ̄} = ζ̄* H ζ̄` (with `ζ̄` the coordinatewise conjugate). -/
theorem ofReal_leviForm_eq_dotProduct (hu : ContDiff ℝ ∞ u) (x ζ : ComplexModel n) :
    ((leviForm u x ζ : ℝ) : ℂ) =
      star (fun d => star (ζ d)) ⬝ᵥ (complexHessian u x *ᵥ fun d => star (ζ d)) := by
  rw [dotProduct_mulVec_complexHessian_eq_leviForm
    (hu.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
    coordCombination_star]

/-- **Błocki's Lemma 5.14** (`lnm2038-monge-ampere:page-0223`): for a smooth real `u` with
positive definite complex Hessian `H` at `x` and `ζ ≠ 0`,
`(log det H)_{ζζ̄}(x) / u_{ζζ̄}(x) ≤ Re tr(H(x)⁻¹ · Hess_ℂ(log u_{ζζ̄})(x))`. -/
theorem blocki_local_estimate (hu : ContDiff ℝ ∞ u) {x : ComplexModel n}
    (hpos : (complexHessian u x).PosDef) {ζ : ComplexModel n} (hζ : ζ ≠ 0) :
    leviForm (fun y => Real.log (complexHessian u y).det.re) x ζ / leviForm u x ζ ≤
      ((complexHessian u x)⁻¹ *
        complexHessian (fun y => Real.log (leviForm u y ζ)) x).trace.re := by
  set H := complexHessian u x with hHdef
  set P := H⁻¹ with hPdef
  set X := wirtM (-I) ζ (complexHessian u) x with hXdef
  set Y := wirtM I ζ (fun y => wirtM (-I) ζ (complexHessian u) y) x with hYdef
  set w : Fin n → ℂ := fun d => star (ζ d) with hwdef
  set c : Fin n → ℂ := X *ᵥ w with hcdef
  set Lx := leviForm u x ζ with hLxdef
  have hw0 : w ≠ 0 := by
    intro h
    apply hζ
    ext d
    have := congrFun h d
    simpa [hwdef] using this
  have hLxc : (Lx : ℂ) = star w ⬝ᵥ (H *ᵥ w) := ofReal_leviForm_eq_dotProduct hu x ζ
  have hLxre : Lx = (star w ⬝ᵥ (H *ᵥ w)).re := by
    rw [← hLxc, Complex.ofReal_re]
  have hLpos : 0 < Lx := by
    rw [hLxre]; exact hpos.re_dotProduct_pos hw0
  have hLsmooth := contDiff_leviForm hu ζ
  have hLdiff : Differentiable ℝ (fun y => leviForm u y ζ) := hLsmooth.differentiable (by simp)
  -- the complex Hessian of `log u_{ζζ̄}` at `x`
  have hHess : ∀ a b, complexHessian (fun y => Real.log (leviForm u y ζ)) x a b =
      Y a b / (Lx : ℂ) - c a * star (c b) / (Lx : ℂ) ^ 2 := by
    intro a b
    rw [complexHessian_log hLsmooth hLpos a b, wirt_wirt_leviForm hu ζ x a b,
      wirt_I_ofReal_eq_conj hLdiff, wirt_leviForm hu ζ x a, wirt_leviForm hu ζ x b]
    rfl
  -- its trace against `P`
  have htr : (P * complexHessian (fun y => Real.log (leviForm u y ζ)) x).trace =
      (P * Y).trace / (Lx : ℂ) - (star c ⬝ᵥ (P *ᵥ c)) / (Lx : ℂ) ^ 2 := by
    simp only [trace, diag_apply, mul_apply, hHess, mulVec, dotProduct, Pi.star_apply]
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_div, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  -- `(log det H)_{ζζ̄} = tr(P Y) - tr(P X* P X)`
  have hlog := leviForm_log_det_complexHessian hu hpos ζ
  rw [wirtM_I_complexHessian hu] at hlog
  have hlogre : leviForm (fun y => Real.log (complexHessian u y).det.re) x ζ =
      (P * Y).trace.re - (P * Xᴴ * P * X).trace.re := by
    have := congrArg Complex.re hlog
    simpa [Complex.sub_re] using this
  -- the Schwarz inequality
  have hCS : (star c ⬝ᵥ (P *ᵥ c)).re ≤ Lx * (P * Xᴴ * P * X).trace.re := by
    rw [hLxre]
    exact re_star_dotProduct_inv_mulVec_le hpos w
  rw [htr, hlogre, Complex.sub_re]
  have e1 : ((P * Y).trace / (Lx : ℂ)).re = (P * Y).trace.re / Lx := by
    rw [Complex.div_ofReal_re]
  have e2 : (star c ⬝ᵥ (P *ᵥ c) / (Lx : ℂ) ^ 2).re = (star c ⬝ᵥ (P *ᵥ c)).re / Lx ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.div_ofReal_re]
  rw [e1, e2, sub_div]
  have hL2 : 0 < Lx ^ 2 := by positivity
  have : (star c ⬝ᵥ (P *ᵥ c)).re / Lx ^ 2 ≤ (P * Xᴴ * P * X).trace.re / Lx := by
    rw [div_le_div_iff₀ hL2 hLpos]
    nlinarith
  linarith

end Lemma

end

end SGPT.Foundations.Analysis.Pending.BlockiLocalEstimate
