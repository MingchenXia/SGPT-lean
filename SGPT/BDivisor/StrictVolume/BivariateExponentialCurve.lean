import SGPT.BDivisor.StrictVolume.PolynomialExponentialDecay

/-! Actual eventual avoidance of EVERY nonzero complex bivariate polynomial.
This constructs the missing sequence input for source ex:volbdivnetstrict. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.BDivisor.StrictSequenceNext

open Filter Topology

def iteratedPolynomialCurveValue (F : Polynomial (Polynomial ℂ)) (x : ℝ) : ℂ :=
  F.eval₂ (Polynomial.evalRingHom (x : ℂ)) (Real.exp x : ℂ)

theorem iteratedPolynomial_normalized_eval (F : Polynomial (Polynomial ℂ)) (x : ℝ) :
    iteratedPolynomialCurveValue F x * (Real.exp (-(F.natDegree : ℝ) * x) : ℂ) =
      (F.coeff F.natDegree).eval (x : ℂ) +
        ∑ i ∈ Finset.range F.natDegree,
          (F.coeff i).eval (x : ℂ) *
            (Real.exp (-((F.natDegree : ℝ) - (i : ℝ)) * x) : ℂ) := by
  have he (i : ℕ) :
      (Real.exp x : ℂ) ^ i * (Real.exp (-(F.natDegree : ℝ) * x) : ℂ) =
        (Real.exp (-((F.natDegree : ℝ) - (i : ℝ)) * x) : ℂ) := by
    calc
      _ = ((Real.exp x ^ i * Real.exp (-(F.natDegree : ℝ) * x) : ℝ) : ℂ) := by
        simp only [Complex.ofReal_mul, Complex.ofReal_pow]
      _ = (Real.exp ((i : ℝ) * x + -(F.natDegree : ℝ) * x) : ℂ) := by
        rw [Real.exp_add, Real.exp_nat_mul]
      _ = _ := congrArg (fun t : ℝ => (Real.exp t : ℂ)) (by ring)
  rw [iteratedPolynomialCurveValue, Polynomial.eval₂_eq_sum_range,
    Finset.sum_mul, Finset.sum_range_succ]
  simp only [Polynomial.coe_evalRingHom, mul_assoc, he, sub_self, neg_zero,
    zero_mul, Real.exp_zero, Complex.ofReal_one, mul_one]
  exact add_comm _ _

theorem iteratedPolynomial_curve_eventually_ne_zero (F : Polynomial (Polynomial ℂ))
    (hF : F ≠ 0) :
    ∀ᶠ x : ℝ in atTop, iteratedPolynomialCurveValue F x ≠ 0 := by
  let m := F.natDegree
  let E (x : ℝ) : ℂ := ∑ i ∈ Finset.range m,
    (F.coeff i).eval (x : ℂ) * (Real.exp (-((m : ℝ) - (i : ℝ)) * x) : ℂ)
  have hlead : F.coeff m ≠ 0 := by
    simpa only [m, Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hF
  obtain ⟨δ, hδ, hbound⟩ := complexPolynomial_eventually_norm_pos (F.coeff m) hlead
  have hE : Tendsto E atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      (tendsto_finsetSum (Finset.range m) fun i hi =>
        complexPolynomial_mul_exp_neg_scale_tendsto (F.coeff i) ((m : ℝ) - (i : ℝ))
          (sub_pos.mpr (by exact_mod_cast Finset.mem_range.mp hi)))
  have hnorm : Tendsto (fun x : ℝ => ‖E x‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hE.norm
  have hsmall : ∀ᶠ x : ℝ in atTop, ‖E x‖ < δ / 2 :=
    hnorm.eventually (gt_mem_nhds (half_pos hδ))
  filter_upwards [hbound, hsmall] with x hx hxSmall
  intro hzero
  have hid : iteratedPolynomialCurveValue F x * (Real.exp (-(m : ℝ) * x) : ℂ) =
      (F.coeff m).eval (x : ℂ) + E x := iteratedPolynomial_normalized_eval F x
  rw [hzero, zero_mul] at hid
  have heq : (F.coeff m).eval (x : ℂ) = -E x :=
    eq_neg_of_add_eq_zero_left hid.symm
  have hn : ‖(F.coeff m).eval (x : ℂ)‖ = ‖E x‖ := by rw [heq, norm_neg]
  rw [hn] at hx
  linarith

end SGPT.BDivisor.StrictSequenceNext
