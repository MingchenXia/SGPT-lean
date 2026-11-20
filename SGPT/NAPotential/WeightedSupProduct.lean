import Mathlib.Data.ENNReal.Inv

/-!
# A monotone diagonal for extended nonnegative weights

The simultaneous regularization of a generator tuple and a singular weight
produces two increasing `ℝ≥0∞` sequences.  Their diagonal product has the
product of their suprema, including zeros and infinite limits.  This lemma
does not take any boundedness, solution, or division certificate as input.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.GAGAMult

open scoped ENNReal

/-- Two increasing extended nonnegative weights may be sent to their limits
along the same natural index, even when a limit is infinite. -/
theorem iSup_mul_of_monotone (a b : ℕ → ℝ≥0∞) (ha : Monotone a) (hb : Monotone b) :
    (⨆ k, a k * b k) = (⨆ k, a k) * ⨆ k, b k := by
  apply le_antisymm ENNReal.iSup_mul_le
  rw [ENNReal.iSup_mul]
  refine iSup_le fun i => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  exact (mul_le_mul' (ha (le_max_left i j)) (hb (le_max_right i j))).trans
    (le_iSup (fun k => a k * b k) (max i j))

end SGPT.NAPotential.GAGAMult
