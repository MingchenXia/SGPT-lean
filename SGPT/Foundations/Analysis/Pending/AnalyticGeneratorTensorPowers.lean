import SGPT.Foundations.Analysis.Pending.IdealWeightProducts
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false

/-! # Actual finite tensor powers normalize analytic generator coefficients -/

open Set Filter
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.AnalyticGeneratorTensorPowers

open FirstPass

noncomputable section

/-- All ordered products of `r` genuine generators, reindexed by an actual
finite-cardinality equivalence. -/
def tensorPowerFamily {X : Type*} {N : ℕ} (f : Fin N → X → ℂ) (r : ℕ) :
    Fin (Fintype.card (Fin r → Fin N)) → X → ℂ :=
  fun s y => ∏ i : Fin r, f ((Fintype.equivFin (Fin r → Fin N)).symm s i) y

/-- Genuine finite product-of-sums gives the precise squared norm. -/
theorem generatorNormSq_tensorPowerFamily {X : Type*} {N : ℕ}
    (f : Fin N → X → ℂ) (r : ℕ) (y : X) :
    generatorNormSq (tensorPowerFamily f r) y = (generatorNormSq f y) ^ r := by
  have hsum : ∑ s : Fin (Fintype.card (Fin r → Fin N)),
      ‖tensorPowerFamily f r s y‖ ^ 2 =
      ∑ s : Fin r → Fin N, ∏ i : Fin r, ‖f (s i) y‖ ^ 2 := by
    refine (Fintype.sum_equiv (Fintype.equivFin (Fin r → Fin N))
      (fun s => ∏ i : Fin r, ‖f (s i) y‖ ^ 2)
      (fun s => ‖tensorPowerFamily f r s y‖ ^ 2) ?_).symm
    intro s
    simp only [tensorPowerFamily, Equiv.symm_apply_apply, norm_prod, Finset.prod_pow]
  rw [generatorNormSq, hsum]
  exact (Fintype.sum_pow (fun i : Fin N => ‖f i y‖ ^ 2) r).symm

/-- The actual finite products are holomorphic on the original true open set. -/
theorem holomorphicGeneratorsAt_tensorPowerFamily
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {N r : ℕ}
    {f : Fin N → E → ℂ} {x : E} (hf : HolomorphicGeneratorsAt f x) :
    HolomorphicGeneratorsAt (tensorPowerFamily f r) x := by
  obtain ⟨U, hU, hxU, hdiff⟩ := hf
  refine ⟨U, hU, hxU, fun s y hy => ?_⟩
  change DifferentiableWithinAt ℂ
    (fun z => ∏ i : Fin r, f ((Fintype.equivFin (Fin r → Fin N)).symm s i) z) U y
  exact (HasFDerivWithinAt.finsetProd fun i _ =>
    (hdiff ((Fintype.equivFin (Fin r → Fin N)).symm s i) y hy).hasFDerivWithinAt).differentiableWithinAt

/-- The extended logarithm retains the exact tensor degree even at poles. -/
theorem generatorLog_tensorPowerFamily {X : Type*} {N : ℕ}
    (f : Fin N → X → ℂ) (r : ℕ) (y : X) :
    generatorLog (tensorPowerFamily f r) y = ((r : ℝ) : EReal) * generatorLog f y := by
  rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
  change ENNReal.log (ENNReal.ofReal (generatorNormSq (tensorPowerFamily f r) y)) =
    ((r : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (generatorNormSq f y))
  rw [generatorNormSq_tensorPowerFamily, ENNReal.ofReal_pow (generatorNormSq_nonneg f y),
    ENNReal.log_pow, EReal.coe_natCast]

end

end SGPT.Foundations.Analysis.Pending.AnalyticGeneratorTensorPowers
