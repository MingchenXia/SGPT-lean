import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-! First source atom for the actual generic point sequence in ex:volbdivnetstrict.
Only actual complex polynomials and real exponential limits occur here. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.BDivisor.StrictSequenceNext

open Filter Topology Asymptotics

theorem complexPolynomial_mul_exp_neg_tendsto (p : Polynomial ℂ) :
    Tendsto (fun x : ℝ => p.eval (x : ℂ) * (Real.exp (-x) : ℂ)) atTop (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | monomial n a =>
      have ht : Tendsto (fun x : ℝ => ((x ^ n * Real.exp (-x) : ℝ) : ℂ))
          atTop (𝓝 (0 : ℂ)) := by
        convert! (Complex.continuous_ofReal.tendsto 0).comp
          (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n) using 1
      have ha : Tendsto (fun _ : ℝ => a) atTop (𝓝 a) := tendsto_const_nhds
      simpa [Polynomial.eval_monomial, Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc]
        using ha.mul ht
  | add p q hp hq =>
      simpa [Polynomial.eval_add, add_mul] using hp.add hq

theorem complexPolynomial_mul_exp_neg_scale_tendsto (p : Polynomial ℂ)
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => p.eval (x : ℂ) * (Real.exp (-c * x) : ℂ)) atTop (𝓝 0) := by
  let q : Polynomial ℂ := p.comp (Polynomial.C ((c : ℂ)⁻¹) * Polynomial.X)
  have hq (x : ℝ) : q.eval ((c * x : ℝ) : ℂ) = p.eval (x : ℂ) := by
    simp [q, Complex.ofReal_ne_zero.mpr hc.ne']
  have h := (complexPolynomial_mul_exp_neg_tendsto q).comp
    (tendsto_id.const_mul_atTop hc)
  simpa only [Function.comp_def, id_eq, hq, neg_mul] using h

theorem complexPolynomial_eventually_norm_pos (p : Polynomial ℂ) (hp : p ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x : ℝ in atTop, δ ≤ ‖p.eval (x : ℂ)‖ := by
  have hdegree : (1 : Polynomial ℂ).degree ≤ p.degree := by
    simp [Polynomial.degree_eq_natDegree hp]
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) atTop (Bornology.cobounded ℂ) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    simpa only [Complex.norm_real, Real.norm_eq_abs] using tendsto_abs_atTop_atTop
  have hb : (fun x : ℝ => (1 : ℂ)) =O[atTop] fun x => p.eval (x : ℂ) := by
    (convert! (Polynomial.isBigO_cobounded_of_degree_le
      (P := (1 : Polynomial ℂ)) (Q := p) hdegree).comp_tendsto ht using 1;
      simp only [Function.comp_def, Polynomial.eval_one])
  obtain ⟨C, hC, hbound⟩ := hb.exists_pos
  refine ⟨1 / C, one_div_pos.mpr hC, hbound.bound.mono ?_⟩
  intro x hx
  apply (div_le_iff₀ hC).mpr
  simpa only [norm_one, mul_comm] using hx

end SGPT.BDivisor.StrictSequenceNext
