import SGPT.BDivisor.StrictVolume.BivariateExponentialCurve

/-! The actual explicit point sequence required in source ex:volbdivnetstrict.
Projectivization and b-divisor geometry are separate subsequent source producers. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.BDivisor.StrictSequenceNext

open Filter Topology

def affineCurveEscapingSequence (n : ℕ) : ℂ × ℂ :=
  ((n : ℂ), (Real.exp (n : ℝ) : ℂ))

theorem affineCurveEscapingSequence_injective :
    Function.Injective affineCurveEscapingSequence := by
  intro i j hij
  have hx := congrArg Prod.fst hij
  change (i : ℂ) = (j : ℂ) at hx
  exact_mod_cast hx

theorem affineCurveEscapingSequence_eventually_outside
    (F : Polynomial (Polynomial ℂ)) (hF : F ≠ 0) :
    ∀ᶠ n : ℕ in atTop,
      F.eval₂ (Polynomial.evalRingHom (affineCurveEscapingSequence n).1)
        (affineCurveEscapingSequence n).2 ≠ 0 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h := ht.eventually (iteratedPolynomial_curve_eventually_ne_zero F hF)
  simpa only [iteratedPolynomialCurveValue, affineCurveEscapingSequence, Complex.ofReal_natCast]
    using h

theorem source_complex_affine_curve_escaping_sequence :
    ∃ s : ℕ → ℂ × ℂ, Function.Injective s ∧
      ∀ F : Polynomial (Polynomial ℂ), F ≠ 0 →
        {n : ℕ | F.eval₂ (Polynomial.evalRingHom (s n).1) (s n).2 = 0}.Finite := by
  refine ⟨affineCurveEscapingSequence, affineCurveEscapingSequence_injective, ?_⟩
  intro F hF
  obtain ⟨N, hN⟩ := eventually_atTop.mp (affineCurveEscapingSequence_eventually_outside F hF)
  refine (Set.finite_Iio N).subset ?_
  intro n hn
  show n < N
  by_contra h
  exact hN n (le_of_not_gt h) hn

end SGPT.BDivisor.StrictSequenceNext
