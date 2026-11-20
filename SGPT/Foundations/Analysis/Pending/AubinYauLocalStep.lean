import SGPT.Foundations.Analysis.Pending.BlockiLocalEstimate
import Mathlib.Analysis.InnerProductSpace.Positive

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The local step of Błocki's second-derivative estimate

At a local maximum `z₀` of Błocki's comparison function
`α̃ = log u_{ζζ̄} - log ρ_{ζζ̄} - κ (u - ρ)` (`lnm2038-monge-ampere:page-0222`), with `|ζ| = 1`,
`(u_{jk̄}(z₀))` positive definite, `ρ_{v v̄}(z₀) ≥ c₀ |v|²`, `(ρ_{ζζ̄})_{v v̄}(z₀) ≤ M₀ |v|²`,
`(log det(u_{jk̄}))_{ζζ̄}(z₀) ≥ -K₀` and `κ c₀ ≥ K₀ + M₀/c₀ + 1`, the trace of the inverse complex Hessian
is bounded: `tr (u_{jk̄}(z₀))⁻¹ ≤ κ n` (`re_trace_inv_le_of_isLocalMax`). This is the inequality
`0 ≥ u^{ij̄}α̃_{ij̄} ≥ ... + (-C₆ + A/C₇) ∑ 1/u_{iī} - nA` of `lnm2038-monge-ampere:page-0224` in the
nondegenerate case (`f = e^G`, so Błocki's `C₄`-term and his AM–GM step are replaced by
`1/u_{ζζ̄} ≤ tr (u_{jk̄})⁻¹`, `one_le_leviForm_mul_re_trace_inv`).

Tools: traces against a positive semidefinite `P = ∑ vᵢ vᵢ*` are sums of Levi forms
(`re_trace_mul_complexHessian_eq_sum`), so Levi-form bounds give trace bounds.

TN.4 B5, nonlinear track N3.
-/

open Set Filter Matrix Complex
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.AubinYauLocalStep

open FirstPass FirstPass.MongeAmpere MixedHessian WirtingerLogDet SemiconcaveHessian
  BlockiLocalEstimate

noncomputable section

variable {n : ℕ}

/-! ### Traces against positive semidefinite matrices -/

theorem norm_sq_coordCombination (y : Fin n → ℂ) :
    ‖coordCombination y‖ ^ 2 = ∑ j, ‖y j‖ ^ 2 := by
  rw [ComplexHessianDeterminant.coordCombination_eq_toLp, EuclideanSpace.norm_sq_eq]
  simp

theorem coordCombination_ne_zero {y : Fin n → ℂ} (hy : y ≠ 0) : coordCombination y ≠ 0 := by
  intro h
  apply hy
  have h2 := norm_sq_coordCombination y
  rw [h, norm_zero] at h2
  have : ∀ j ∈ Finset.univ, ‖y j‖ ^ 2 = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg fun j _ => by positivity).mp ?_
    rw [← h2]; ring
  funext j
  have := this j (Finset.mem_univ j)
  simpa using this

theorem trace_vecMulVec_mul (v : Fin n → ℂ) (H : Matrix (Fin n) (Fin n) ℂ) :
    (vecMulVec v (star v) * H).trace = star v ⬝ᵥ (H *ᵥ v) := by
  rw [vecMulVec_mul, trace_vecMulVec, dotProduct_comm, ← dotProduct_mulVec]

theorem trace_mul_vecMulVec (P : Matrix (Fin n) (Fin n) ℂ) (g : Fin n → ℂ) :
    (P * vecMulVec g (star g)).trace = star g ⬝ᵥ (P *ᵥ g) := by
  rw [trace_mul_comm, trace_vecMulVec_mul]

/-- A trace against `P = ∑ vᵢ vᵢ*` is a sum of Levi forms. -/
theorem re_trace_mul_complexHessian_eq_sum {m : ℕ} (v : Fin m → Fin n → ℂ)
    {f : ComplexModel n → ℝ} {z : ComplexModel n} (hf : ContDiffAt ℝ 2 f z) :
    ((∑ i, vecMulVec (v i) (star (v i))) * complexHessian f z).trace.re =
      ∑ i, leviForm f z (coordCombination (v i)) := by
  rw [Finset.sum_mul, trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_vecMulVec_mul, dotProduct_mulVec_complexHessian_eq_leviForm hf, Complex.ofReal_re]

theorem re_trace_sum_vecMulVec {m : ℕ} (v : Fin m → Fin n → ℂ) :
    (∑ i, vecMulVec (v i) (star (v i))).trace.re = ∑ i, ‖coordCombination (v i)‖ ^ 2 := by
  rw [trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [trace_vecMulVec, norm_sq_coordCombination, ← re_star_dotProduct_self, dotProduct_comm]

/-- Upper Levi-form bounds give trace bounds against positive semidefinite matrices. -/
theorem re_trace_mul_complexHessian_le {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef)
    {f : ComplexModel n → ℝ} {z : ComplexModel n} (hf : ContDiffAt ℝ 2 f z) {B : ℝ}
    (hB : ∀ w, leviForm f z w ≤ B * ‖w‖ ^ 2) :
    (P * complexHessian f z).trace.re ≤ B * P.trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  rw [re_trace_mul_complexHessian_eq_sum v hf, re_trace_sum_vecMulVec, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hB _

/-- Lower Levi-form bounds give trace bounds against positive semidefinite matrices. -/
theorem le_re_trace_mul_complexHessian {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef)
    {f : ComplexModel n → ℝ} {z : ComplexModel n} (hf : ContDiffAt ℝ 2 f z) {B : ℝ}
    (hB : ∀ w, B * ‖w‖ ^ 2 ≤ leviForm f z w) :
    B * P.trace.re ≤ (P * complexHessian f z).trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  rw [re_trace_mul_complexHessian_eq_sum v hf, re_trace_sum_vecMulVec, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => hB _

theorem re_trace_nonneg {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) : 0 ≤ P.trace.re := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hP
  rw [re_trace_sum_vecMulVec]
  positivity

/-- Positivity of the Levi form makes the complex Hessian positive definite. -/
theorem posDef_complexHessian {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (hpos : ∀ v, v ≠ 0 → 0 < leviForm u z v) :
    (complexHessian u z).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨complexHessian_isHermitian hu, fun x hx => ?_⟩
  rw [dotProduct_mulVec_complexHessian_eq_leviForm hu]
  exact_mod_cast hpos _ (coordCombination_ne_zero hx)

/-- `1 ≤ u_{ζζ̄} · tr (u_{jk̄})⁻¹` for `|ζ| = 1` (`λ_min ≥ 1 / tr H⁻¹`). -/
theorem one_le_leviForm_mul_re_trace_inv {u : ComplexModel n → ℝ} {z : ComplexModel n}
    (hu : ContDiffAt ℝ 2 u z) (hpos : (complexHessian u z).PosDef) {ζ : ComplexModel n}
    (hζ : ‖ζ‖ = 1) : 1 ≤ leviForm u z ζ * ((complexHessian u z)⁻¹).trace.re := by
  classical
  set H := complexHessian u z
  obtain ⟨R, hdet, hHR, -⟩ :=
    ConcentrationEigenvalueBound.exists_simultaneous_diagonalization hpos hpos
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hRR : R * R⁻¹ = 1 := mul_nonsing_inv R hRu
  have hSH : (star R) * H = R⁻¹ := by
    calc (star R) * H = (star R) * H * (R * R⁻¹) := by rw [hRR, Matrix.mul_one]
      _ = ((star R) * H * R) * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = R⁻¹ := by rw [hHR, Matrix.one_mul]
  have hHinv : H⁻¹ = R * (star R) := by
    refine inv_eq_left_inv ?_
    rw [Matrix.mul_assoc, hSH, hRR]
  set w : Fin n → ℂ := fun d => star (ζ d)
  set s : Fin n → ℂ := R⁻¹ *ᵥ w
  have hw : w = R *ᵥ s := by simp only [s]; rw [mulVec_mulVec, hRR, one_mulVec]
  have hL : leviForm u z ζ = (star s ⬝ᵥ s).re := by
    have h := dotProduct_mulVec_complexHessian_eq_leviForm hu w
    rw [show coordCombination w = ζ from coordCombination_star ζ] at h
    rw [← Complex.ofReal_re (leviForm u z ζ), ← h, hw,
      AubinYauMatrixBounds.star_mulVec_dotProduct_mulVec, hHR, one_mulVec]
  have htr : (H⁻¹).trace = (Rᴴ * R).trace := by
    rw [hHinv, trace_mul_comm, star_eq_conjTranspose]
  have hw1 : (star w ⬝ᵥ w).re = 1 := by
    rw [re_star_dotProduct_self]
    have := norm_sq_coordCombination w
    rw [show coordCombination w = ζ from coordCombination_star ζ, hζ] at this
    rw [← this]; ring
  have hCS := re_star_mulVec_dotProduct_le R s
  rw [← hw, hw1] at hCS
  rw [hL, htr, mul_comm]
  exact hCS

/-- `Re tr(P · Hess_ℂ log L) ≤ Re tr(P · Hess_ℂ L) / L` for `P ≥ 0`, `L > 0` (the gradient term
of `log` has a sign). -/
theorem re_trace_mul_complexHessian_log_le {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef)
    {L : ComplexModel n → ℝ} (hL : ContDiff ℝ ∞ L) {z : ComplexModel n} (hz : 0 < L z) :
    (P * complexHessian (fun y => Real.log (L y)) z).trace.re ≤
      (P * complexHessian L z).trace.re / L z := by
  set g : Fin n → ℂ := fun a => wirt (-I) (coordinateVector a) (fun y => (L y : ℂ)) z
  have hLd : Differentiable ℝ L := hL.differentiable (by simp)
  have hHess : complexHessian (fun y => Real.log (L y)) z =
      ((L z : ℂ))⁻¹ • complexHessian L z - ((L z : ℂ) ^ 2)⁻¹ • vecMulVec g (star g) := by
    ext a b
    rw [complexHessian_log hL hz a b, wirt_I_ofReal_eq_conj hLd]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, Pi.star_apply,
      g]
    rw [complexHessian_eq_wirt (hL.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
      Complex.star_def]
    ring
  rw [hHess, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, trace_sub, trace_smul, trace_smul,
    smul_eq_mul, smul_eq_mul, Complex.sub_re, ← Complex.ofReal_inv, Complex.re_ofReal_mul,
    ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.re_ofReal_mul, trace_mul_vecMulVec]
  have hnn : 0 ≤ (star g ⬝ᵥ (P *ᵥ g)).re := hP.re_dotProduct_nonneg g
  have : 0 ≤ ((L z) ^ 2)⁻¹ * (star g ⬝ᵥ (P *ᵥ g)).re := by positivity
  rw [div_eq_inv_mul]
  linarith

/-! ### The local step -/

theorem complexHessian_fun_add {f g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) :
    complexHessian (fun y => f y + g y) z = complexHessian f z + complexHessian g z :=
  complexHessian_add hf hg

theorem complexHessian_const_mul {f : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (c : ℝ) :
    complexHessian (fun y => c * f y) z = (c : ℂ) • complexHessian f z :=
  complexHessian_smul hf c

theorem contDiffAt_two {f : ComplexModel n → ℝ} (hf : ContDiff ℝ ∞ f) (z : ComplexModel n) :
    ContDiffAt ℝ 2 f z :=
  hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

/-- **The local step** (`lnm2038-monge-ampere:page-0224`, nondegenerate case): at a local maximum
`z₀` of `log u_{ζζ̄} - log ρ_{ζζ̄} - κ (u - ρ)` with `|ζ| = 1`, under the bounds described in the
module docstring, `tr (u_{jk̄}(z₀))⁻¹ ≤ κ n`. -/
theorem re_trace_inv_le_of_isLocalMax {u ρ : ComplexModel n → ℝ} (hu : ContDiff ℝ ∞ u)
    (hρ : ContDiff ℝ ∞ ρ) {z₀ ζ : ComplexModel n} (hζ : ‖ζ‖ = 1)
    (hpos : (complexHessian u z₀).PosDef) {κ c₀ M₀ K₀ : ℝ} (hc₀ : 0 < c₀) (hK₀ : 0 ≤ K₀)
    (hM₀ : 0 ≤ M₀)
    (hρlow : ∀ w, c₀ * ‖w‖ ^ 2 ≤ leviForm ρ z₀ w)
    (hρM : ∀ w, leviForm (fun y => leviForm ρ y ζ) z₀ w ≤ M₀ * ‖w‖ ^ 2)
    (hdet : -K₀ ≤ leviForm (fun y => Real.log (complexHessian u y).det.re) z₀ ζ)
    (hκ : K₀ + M₀ / c₀ + 1 ≤ κ * c₀)
    (hmax : IsLocalMax (fun z => Real.log (leviForm u z ζ) - Real.log (leviForm ρ z ζ) -
      κ * (u z - ρ z)) z₀) :
    ((complexHessian u z₀)⁻¹).trace.re ≤ κ * n := by
  classical
  set H := complexHessian u z₀ with hHdef
  set P := H⁻¹ with hPdef
  have hP : P.PosSemidef := hpos.posSemidef.inv
  have hζ0 : ζ ≠ 0 := by
    intro h; rw [h, norm_zero] at hζ; exact zero_ne_one hζ
  set Lu : ComplexModel n → ℝ := fun y => leviForm u y ζ with hLudef
  set Lρ : ComplexModel n → ℝ := fun y => leviForm ρ y ζ with hLρdef
  have hLu : ContDiff ℝ ∞ Lu := contDiff_leviForm hu ζ
  have hLρ : ContDiff ℝ ∞ Lρ := contDiff_leviForm hρ ζ
  have hLρ0 : c₀ ≤ Lρ z₀ := by
    have := hρlow ζ; rw [hζ] at this; simpa using this
  have hLρpos : 0 < Lρ z₀ := hc₀.trans_le hLρ0
  have hone := one_le_leviForm_mul_re_trace_inv (contDiffAt_two hu z₀) hpos hζ
  have hLupos : 0 < Lu z₀ := by
    have hw : (fun d => star (ζ d)) ≠ 0 := by
      intro h; apply hζ0; ext d; have := congrFun h d; simpa using this
    have := hpos.re_dotProduct_pos hw
    rw [show Lu z₀ = (star (fun d => star (ζ d)) ⬝ᵥ (H *ᵥ fun d => star (ζ d))).re from by
      rw [← ofReal_leviForm_eq_dotProduct hu z₀ ζ, Complex.ofReal_re]]
    exact this
  set trP := P.trace.re with htrP
  have htrP0 : 0 ≤ trP := re_trace_nonneg hP
  -- the four pieces of `α̃`
  have h1 : ContDiffAt ℝ 2 (fun z => Real.log (Lu z)) z₀ :=
    (contDiffAt_two hLu z₀).log hLupos.ne'
  have h2 : ContDiffAt ℝ 2 (fun z => Real.log (Lρ z)) z₀ :=
    (contDiffAt_two hLρ z₀).log hLρpos.ne'
  have hfun : (fun z => Real.log (leviForm u z ζ) - Real.log (leviForm ρ z ζ) -
      κ * (u z - ρ z)) = fun z => Real.log (Lu z) + ((-1) * Real.log (Lρ z) +
        (-κ) * (u z + (-1) * ρ z)) := by
    funext z; simp only [hLudef, hLρdef]; ring
  have hu2 := contDiffAt_two hu z₀
  have hρ2 := contDiffAt_two hρ z₀
  have hB1 : ContDiffAt ℝ 2 (fun z => (-1) * Real.log (Lρ z)) z₀ := contDiffAt_const.mul h2
  have hB2 : ContDiffAt ℝ 2 (fun z => (-1) * ρ z) z₀ := contDiffAt_const.mul hρ2
  have hB3 : ContDiffAt ℝ 2 (fun z => u z + (-1) * ρ z) z₀ := hu2.add hB2
  have hB5 : ContDiffAt ℝ 2 (fun z => (-κ) * (u z + (-1) * ρ z)) z₀ := contDiffAt_const.mul hB3
  have hB4 : ContDiffAt ℝ 2 (fun z => (-1) * Real.log (Lρ z) + (-κ) * (u z + (-1) * ρ z)) z₀ :=
    hB1.add hB5
  have hHα : complexHessian (fun z => Real.log (leviForm u z ζ) - Real.log (leviForm ρ z ζ) -
      κ * (u z - ρ z)) z₀ = complexHessian (fun z => Real.log (Lu z)) z₀ +
        (((-1 : ℝ) : ℂ) • complexHessian (fun z => Real.log (Lρ z)) z₀ +
        ((-κ : ℝ) : ℂ) • (complexHessian u z₀ + ((-1 : ℝ) : ℂ) • complexHessian ρ z₀)) := by
    rw [hfun, complexHessian_fun_add h1 hB4, complexHessian_fun_add hB1 hB5,
      complexHessian_const_mul h2, complexHessian_const_mul hB3,
      complexHessian_fun_add hu2 hB2, complexHessian_const_mul hρ2]
  -- the maximum principle
  have hC2 : ContDiffAt ℝ 2 (fun z => Real.log (leviForm u z ζ) - Real.log (leviForm ρ z ζ) -
      κ * (u z - ρ z)) z₀ := by
    rw [hfun]; exact h1.add hB4
  have hmp := AubinYauMatrixBounds.re_trace_mul_complexHessian_nonpos hC2 hmax hP
  rw [hHα] at hmp
  simp only [Matrix.mul_add, Matrix.mul_smul, trace_add, trace_smul, smul_eq_mul,
    Complex.add_re, Complex.re_ofReal_mul] at hmp
  -- the four traces
  have hT1 : -K₀ * trP ≤ (P * complexHessian (fun z => Real.log (Lu z)) z₀).trace.re := by
    have hB := blocki_local_estimate hu hpos hζ0
    have : -K₀ * trP ≤ -K₀ / Lu z₀ := by
      rw [neg_mul, neg_div, neg_le_neg_iff, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_left ?_ hK₀
      rw [inv_le_iff_one_le_mul₀ hLupos, mul_comm]
      exact hone
    refine this.trans (le_trans ?_ hB)
    exact div_le_div_of_nonneg_right hdet hLupos.le
  have hT2 : (P * complexHessian (fun z => Real.log (Lρ z)) z₀).trace.re ≤ M₀ / c₀ * trP := by
    refine (re_trace_mul_complexHessian_log_le hP hLρ hLρpos).trans ?_
    have hM := re_trace_mul_complexHessian_le hP (contDiffAt_two hLρ z₀) hρM
    rw [div_le_iff₀ hLρpos]
    calc (P * complexHessian Lρ z₀).trace.re ≤ M₀ * trP := hM
      _ = M₀ / c₀ * trP * c₀ := by field_simp
      _ ≤ M₀ / c₀ * trP * Lρ z₀ := by
        exact mul_le_mul_of_nonneg_left hLρ0 (by positivity)
  have hT3 : (P * complexHessian u z₀).trace.re = n := by
    rw [hPdef, hHdef, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hpos.det_pos.ne')), trace_one]
    simp
  have hT4 : c₀ * trP ≤ (P * complexHessian ρ z₀).trace.re :=
    le_re_trace_mul_complexHessian hP (contDiffAt_two hρ z₀) hρlow
  rw [hT3] at hmp
  have hκpos : 0 < κ := by
    have : 0 < κ * c₀ := by
      have : 0 ≤ M₀ / c₀ := by positivity
      linarith
    exact pos_of_mul_pos_left this hc₀.le
  nlinarith [mul_le_mul_of_nonneg_left hT4 hκpos.le]

end

end SGPT.Foundations.Analysis.Pending.AubinYauLocalStep
