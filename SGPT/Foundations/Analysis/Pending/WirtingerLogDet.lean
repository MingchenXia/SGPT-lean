import SGPT.Foundations.Analysis.Pending.MixedHessianDivergence
import SGPT.Foundations.Analysis.Pending.LeviWirtinger

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Wirtinger derivatives of the determinant, the inverse and `log det` of a complex Hessian

For a matrix-valued function `M` with differentiable entries and the directional operators
`wirt c v` (`c = -i`: `∂_v`, `c = i`: `∂̄_v`) applied entrywise (`wirtM`):

* **Jacobi's formula** (`wirt_det`): `wirt c v (det M) = tr(adj M · wirtM c v M)`; at an invertible
  point this is `det M · tr(M⁻¹ · wirtM c v M)` (`wirt_det_eq_det_mul_trace`);
* **the derivative of the inverse** (`wirt_inv_apply`): `wirt c v (M⁻¹)ᵢⱼ = -(M⁻¹ · wirtM c v M · M⁻¹)ᵢⱼ`
  at a point where `det M ≠ 0`.

For a smooth real `u` on `ℂⁿ` with `H = (u_{jk̄})` positive definite at `x`, `D = det H` and a
direction `ζ`, with `X = ∂_ζ H(x)` and `Y = ∂̄_ζ ∂_ζ H(x)` (`leviForm_log_det_complexHessian`):

  `(log D)_{ζζ̄}(x) = tr(H⁻¹ Y) - tr(H⁻¹ X* H⁻¹ X)`,

the two differentiated equations in the proof of Błocki's Lemma 5.14
(`lnm2038-monge-ampere:page-0223`; LNM 2038 (5.6)–(5.7)).

TN.4 B5, nonlinear track N3 (the second-order Monge–Ampère estimate).
-/

open Set Filter Matrix Complex
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.WirtingerLogDet

open FirstPass FirstPass.MongeAmpere MixedHessian

noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- The directional operator `wirt c v`, applied entrywise to a matrix-valued function. -/
def wirtM (c : ℂ) (v : E) (M : E → Matrix ι ι ℂ) (x : E) : Matrix ι ι ℂ :=
  Matrix.of fun i j => wirt c v (fun y => M y i j) x

@[simp] theorem wirtM_apply (c : ℂ) (v : E) (M : E → Matrix ι ι ℂ) (x : E) (i j : ι) :
    wirtM c v M x i j = wirt c v (fun y => M y i j) x := rfl

theorem wirt_congr {c : ℂ} {v : E} {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) :
    wirt c v f x = wirt c v g x := by
  simp only [wirt, h.fderiv_eq]

theorem wirt_eq_zero_of_eventuallyEq_const {c : ℂ} {v : E} {f : E → ℂ} {x : E} {a : ℂ}
    (h : f =ᶠ[𝓝 x] fun _ => a) : wirt c v f x = 0 := by
  rw [wirt_congr h]
  simp [wirt]

theorem det_eq_sum (M : Matrix ι ι ℂ) :
    M.det = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i :=
  det_apply' M

theorem differentiableAt_det {M : E → Matrix ι ι ℂ} {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) :
    DifferentiableAt ℝ (fun y => (M y).det) x := by
  simp_rw [det_eq_sum]
  refine DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul ?_
  exact (HasFDerivAt.finsetProd fun i _ => (hM (σ i) i).hasFDerivAt).differentiableAt

/-- The determinant of a matrix with one column replaced, in the Leibniz expansion. -/
theorem det_updateCol_eq_sum (M : Matrix ι ι ℂ) (l : ι) (b : ι → ℂ) :
    (M.updateCol l b).det =
      ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        (b (σ l) * ∏ i ∈ Finset.univ.erase l, M (σ i) i) := by
  rw [det_eq_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp [Finset.ne_of_mem_erase hi]

/-- **Jacobi's formula**, adjugate form: `wirt c v (det M) = tr(adj M · wirtM c v M)`. -/
theorem wirt_det {c : ℂ} {v : E} {M : E → Matrix ι ι ℂ} {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) :
    wirt c v (fun y => (M y).det) x = (adjugate (M x) * wirtM c v M x).trace := by
  simp_rw [det_eq_sum]
  have hP : ∀ σ : Equiv.Perm ι, DifferentiableAt ℝ (fun y => ∏ i, M y (σ i) i) x := fun σ =>
    (HasFDerivAt.finsetProd fun i _ => (hM (σ i) i).hasFDerivAt).differentiableAt
  rw [wirt_sum Finset.univ (f := fun σ y => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M y (σ i) i)
    fun σ _ => (differentiableAt_const _).mul (hP σ)]
  simp_rw [wirt_const_mul _ (hP _)]
  have hσ : ∀ σ : Equiv.Perm ι, wirt c v (fun y => ∏ i, M y (σ i) i) x =
      ∑ l, wirt c v (fun y => M y (σ l) l) x * ∏ i ∈ Finset.univ.erase l, M x (σ i) i :=
    fun σ => wirt_prod Finset.univ (f := fun i y => M y (σ i) i) fun i _ => hM (σ i) i
  simp_rw [hσ]
  -- the right-hand side, column by column
  have hR : (adjugate (M x) * wirtM c v M x).trace =
      ∑ l, ((M x).updateCol l (fun k => wirtM c v M x k l)).det := by
    rw [trace]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [diag_apply, mul_apply, ← cramer_apply, cramer_eq_adjugate_mulVec, mulVec, dotProduct]
  rw [hR]
  simp_rw [det_updateCol_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/-- `adj A = det A • A⁻¹`. -/
theorem adjugate_eq_det_smul_inv' {A : Matrix ι ι ℂ} (hA : A.det ≠ 0) :
    adjugate A = A.det • A⁻¹ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hA, one_smul]

/-- **Jacobi's formula** at an invertible point. -/
theorem wirt_det_eq_det_mul_trace {c : ℂ} {v : E} {M : E → Matrix ι ι ℂ} {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) (hx : (M x).det ≠ 0) :
    wirt c v (fun y => (M y).det) x = (M x).det * ((M x)⁻¹ * wirtM c v M x).trace := by
  rw [wirt_det hM, adjugate_eq_det_smul_inv' hx, smul_mul_assoc, trace_smul, smul_eq_mul]

theorem inv_apply_eq (A : Matrix ι ι ℂ) (i j : ι) : A⁻¹ i j = (A.det)⁻¹ * adjugate A i j := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]

theorem differentiableAt_adjugate_apply {M : E → Matrix ι ι ℂ} {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) (i j : ι) :
    DifferentiableAt ℝ (fun y => adjugate (M y) i j) x := by
  simp_rw [adjugate_apply]
  refine differentiableAt_det fun a b => ?_
  by_cases h : a = j
  · subst h
    simp only [updateRow_self]
    exact differentiableAt_const _
  · simp only [updateRow_ne h]
    exact hM a b

theorem differentiableAt_inv_apply {M : E → Matrix ι ι ℂ} {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) (hx : (M x).det ≠ 0) (i j : ι) :
    DifferentiableAt ℝ (fun y => (M y)⁻¹ i j) x := by
  simp_rw [inv_apply_eq]
  exact ((differentiableAt_det hM).inv hx).mul (differentiableAt_adjugate_apply hM i j)

/-- **The derivative of the inverse**: `wirt c v (M⁻¹) = -M⁻¹ (wirtM c v M) M⁻¹` where
`det M ≠ 0`. -/
theorem wirt_inv_apply {c : ℂ} {v : E} {M : E → Matrix ι ι ℂ} {x : E}
    (hM : ∀ i j, DifferentiableAt ℝ (fun y => M y i j) x) (hx : (M x).det ≠ 0) (i j : ι) :
    wirt c v (fun y => (M y)⁻¹ i j) x = -((M x)⁻¹ * wirtM c v M x * (M x)⁻¹) i j := by
  -- `M y * (M y)⁻¹ = 1` near `x`
  have hdet : ∀ᶠ y in 𝓝 x, (M y).det ≠ 0 :=
    (differentiableAt_det hM).continuousAt.eventually_ne hx
  have hW : wirtM c v M x * (M x)⁻¹ + M x * wirtM c v (fun y => (M y)⁻¹) x = 0 := by
    ext a b
    have hev : (fun y => (M y * (M y)⁻¹) a b) =ᶠ[𝓝 x] fun _ => (1 : Matrix ι ι ℂ) a b := by
      filter_upwards [hdet] with y hy
      rw [mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hy)]
    have h0 := wirt_eq_zero_of_eventuallyEq_const (c := c) (v := v) hev
    simp only [mul_apply] at h0
    rw [wirt_sum Finset.univ (f := fun k y => M y a k * (M y)⁻¹ k b)
      fun k _ => (hM a k).fun_mul (differentiableAt_inv_apply hM hx k b)] at h0
    have hk : ∀ k, wirt c v (fun y => M y a k * (M y)⁻¹ k b) x =
        wirt c v (fun y => M y a k) x * (M x)⁻¹ k b +
          M x a k * wirt c v (fun y => (M y)⁻¹ k b) x := fun k =>
      wirt_mul (f := fun y => M y a k) (g := fun y => (M y)⁻¹ k b) (hM a k)
        (differentiableAt_inv_apply hM hx k b)
    simp_rw [hk] at h0
    rw [Finset.sum_add_distrib] at h0
    simpa [Matrix.add_apply, mul_apply] using h0
  have hu : IsUnit (M x).det := isUnit_iff_ne_zero.mpr hx
  have hsol : wirtM c v (fun y => (M y)⁻¹) x = -((M x)⁻¹ * wirtM c v M x * (M x)⁻¹) := by
    have h1 : M x * wirtM c v (fun y => (M y)⁻¹) x = -(wirtM c v M x * (M x)⁻¹) :=
      eq_neg_of_add_eq_zero_right hW
    calc wirtM c v (fun y => (M y)⁻¹) x
        = (M x)⁻¹ * (M x * wirtM c v (fun y => (M y)⁻¹) x) := by
          rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = -((M x)⁻¹ * wirtM c v M x * (M x)⁻¹) := by
          rw [h1, Matrix.mul_neg, Matrix.mul_assoc]
  have := congrFun (congrFun hsol i) j
  simpa using this

end General

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The chain rule for `log` of a positive (nonzero) real function. -/
theorem wirt_ofReal_log {c : ℂ} {v : E} {g : E → ℝ} {y : E} (hg : DifferentiableAt ℝ g y)
    (hy : g y ≠ 0) :
    wirt c v (fun z => ((Real.log (g z) : ℝ) : ℂ)) y = wirt c v (fun z => (g z : ℂ)) y / (g y : ℂ) := by
  have h1 : HasFDerivAt (fun z => ((Real.log (g z) : ℝ) : ℂ))
      (ofRealCLM.comp ((g y)⁻¹ • fderiv ℝ g y)) y :=
    ofRealCLM.hasFDerivAt.comp y (hg.hasFDerivAt.log hy)
  have h2 : HasFDerivAt (fun z => (g z : ℂ)) (ofRealCLM.comp (fderiv ℝ g y)) y :=
    ofRealCLM.hasFDerivAt.comp y hg.hasFDerivAt
  have hy' : (g y : ℂ) ≠ 0 := by exact_mod_cast hy
  simp only [wirt, h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply,
    _root_.smul_apply, ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_inv]
  field_simp

/-- The operators `∂̄_v` and `∂_v` exchange under complex conjugation. -/
theorem wirt_I_conj {v : E} {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    wirt I v (fun y => conj (f y)) x = conj (wirt (-I) v f x) := by
  have h := CauchyGreen.dbarDir_conj (v := v) hf
  rw [dbarDir_eq_wirt] at h
  rw [h]
  congr 1
  simp only [CauchyGreen.dDir, wirt]
  ring

end Real

section Hessian

variable {n : ℕ}

theorem contDiff_complexHessian_apply' {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    (j k : Fin n) : ContDiff ℝ ∞ (fun z => complexHessian u z j k) :=
  contDiff_complexHessian_apply hu j k

theorem differentiable_complexHessian_apply {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    (j k : Fin n) : Differentiable ℝ (fun z => complexHessian u z j k) :=
  (contDiff_complexHessian_apply hu j k).differentiable (by simp)

theorem contDiff_det_complexHessian {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (fun z => (complexHessian u z).det) := by
  simp_rw [det_eq_sum]
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => contDiff_complexHessian_apply hu _ _

theorem isHermitian_complexHessian {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    (z : ComplexModel n) : (complexHessian u z).IsHermitian :=
  complexHessian_isHermitian (hu.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))

/-- The determinant of a Hermitian matrix is real. -/
theorem ofReal_re_det_of_isHermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) :
    ((A.det.re : ℝ) : ℂ) = A.det := by
  have h : star A.det = A.det := by rw [← det_conjTranspose, hA.eq]
  exact Complex.conj_eq_iff_re.mp h

/-- `∂̄_ζ H = (∂_ζ H)*` for the complex Hessian of a real function. -/
theorem wirtM_I_complexHessian {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    (ζ x : ComplexModel n) :
    wirtM I ζ (complexHessian u) x = (wirtM (-I) ζ (complexHessian u) x)ᴴ := by
  ext a b
  have h : (fun y => complexHessian u y a b) = fun y => conj (complexHessian u y b a) := by
    funext y
    have := congrFun (congrFun (isHermitian_complexHessian hu y) a) b
    rw [conjTranspose_apply] at this
    rw [← this]
    rfl
  rw [wirtM_apply, h, wirt_I_conj (differentiable_complexHessian_apply hu b a x)]
  rfl

/-- **The second derivative of `log det` of a complex Hessian** at a point where it is positive
definite: `(log det H)_{ζζ̄} = tr(H⁻¹ ∂̄_ζ∂_ζ H) - tr(H⁻¹ ∂̄_ζ H H⁻¹ ∂_ζ H)`
(LNM 2038 (5.6)–(5.7), `lnm2038-monge-ampere:page-0223`). -/
theorem leviForm_log_det_complexHessian {u : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    {x : ComplexModel n} (hpos : (complexHessian u x).PosDef) (ζ : ComplexModel n) :
    (leviForm (fun y => Real.log (complexHessian u y).det.re) x ζ : ℂ) =
      ((complexHessian u x)⁻¹ * wirtM I ζ (fun y => wirtM (-I) ζ (complexHessian u) y) x).trace -
        ((complexHessian u x)⁻¹ * wirtM I ζ (complexHessian u) x * (complexHessian u x)⁻¹ *
          wirtM (-I) ζ (complexHessian u) x).trace := by
  set H := complexHessian u with hHdef
  set D : ComplexModel n → ℝ := fun y => (H y).det.re with hDdef
  have hHd : ∀ i j y, DifferentiableAt ℝ (fun z => H z i j) y := fun i j y =>
    differentiable_complexHessian_apply hu i j y
  have hDc : ∀ y, ((D y : ℝ) : ℂ) = (H y).det := fun y =>
    ofReal_re_det_of_isHermitian (isHermitian_complexHessian hu y)
  have hDcont : ContDiff ℝ ∞ D := Complex.reCLM.contDiff.comp (contDiff_det_complexHessian hu)
  have hDx : 0 < D x := by
    have := hpos.det_pos
    exact (Complex.pos_iff.mp this).1
  have hDpos : ∀ᶠ y in 𝓝 x, 0 < D y :=
    continuousAt_const.eventually_lt hDcont.continuous.continuousAt hDx
  -- first derivative of `log D` near `x`
  have hfirst : (fun y => wirt (-I) ζ (fun z => ((Real.log (D z) : ℝ) : ℂ)) y) =ᶠ[𝓝 x]
      fun y => ∑ i, ∑ j, (H y)⁻¹ i j * wirt (-I) ζ (fun z => H z j i) y := by
    filter_upwards [hDpos] with y hy
    have hdetne : (H y).det ≠ 0 := by
      rw [← hDc y]; exact_mod_cast hy.ne'
    rw [wirt_ofReal_log (hDcont.differentiable (by simp) y) hy.ne']
    have hfun : (fun z => ((D z : ℝ) : ℂ)) = fun z => (H z).det := funext hDc
    rw [hfun, wirt_det_eq_det_mul_trace (fun i j => hHd i j y) hdetne, hDc y,
      mul_div_cancel_left₀ _ hdetne, trace]
    simp only [diag_apply, mul_apply, wirtM_apply]
  -- the second derivative
  have hxdet : (H x).det ≠ 0 := by
    rw [← hDc x]; exact_mod_cast hDx.ne'
  have hlevi : (leviForm (fun y => Real.log (D y)) x ζ : ℂ) =
      wirt I ζ (fun y => wirt (-I) ζ (fun z => ((Real.log (D z) : ℝ) : ℂ)) y) x := by
    have hC2 : ContDiffAt ℝ 2 (fun y => Real.log (D y)) x :=
      ((hDcont.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).log hDx.ne')
    rw [← CauchyGreen.dbarDir_dDir_ofReal_eq_leviForm hC2 ζ, dbarDir_eq_wirt]
    congr 1
    funext y
    simp only [CauchyGreen.dDir, wirt]
    ring
  rw [hlevi, wirt_congr hfirst]
  have hdi : ∀ i j, DifferentiableAt ℝ (fun y => (H y)⁻¹ i j) x := fun i j =>
    differentiableAt_inv_apply (fun a b => hHd a b x) hxdet i j
  have hdw : ∀ i j, DifferentiableAt ℝ (fun y => wirt (-I) ζ (fun z => H z j i) y) x :=
    fun i j => (contDiff_wirt (contDiff_complexHessian_apply hu j i)).differentiable
      (by simp) x
  rw [wirt_sum Finset.univ (f := fun i y => ∑ j, (H y)⁻¹ i j * wirt (-I) ζ (fun z => H z j i) y)
    fun i _ => DifferentiableAt.fun_sum fun j _ => (hdi i j).fun_mul (hdw i j)]
  have hij : ∀ i, wirt I ζ (fun y => ∑ j, (H y)⁻¹ i j * wirt (-I) ζ (fun z => H z j i) y) x =
      ∑ j, (wirt I ζ (fun y => (H y)⁻¹ i j) x * wirt (-I) ζ (fun z => H z j i) x +
        (H x)⁻¹ i j * wirt I ζ (fun y => wirt (-I) ζ (fun z => H z j i) y) x) := by
    intro i
    rw [wirt_sum Finset.univ (f := fun j y => (H y)⁻¹ i j * wirt (-I) ζ (fun z => H z j i) y)
      fun j _ => (hdi i j).fun_mul (hdw i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact wirt_mul (f := fun y => (H y)⁻¹ i j) (g := fun y => wirt (-I) ζ (fun z => H z j i) y)
      (hdi i j) (hdw i j)
  simp_rw [hij, wirt_inv_apply (fun a b => hHd a b x) hxdet]
  simp only [trace, diag_apply, mul_apply, wirtM_apply, Finset.sum_add_distrib, neg_mul,
    Finset.sum_neg_distrib]
  rw [sub_eq_add_neg, add_comm]

end Hessian

end

end SGPT.Foundations.Analysis.Pending.WirtingerLogDet
