import SGPT.Checks.Literature.BJDivisorial.PrimeDivisorNativeData
import SGPT.Foundations.PublishedEnvelope.Berkovich.SchemeGenericCenterValuations

/-! # The actual source trivial point retains its entire trivial field valuation
This supplies the genuine zero-dimensional/trivial-restriction branch of
the augmented source divisorial dictionary without inventing a prime divisor.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry TopologicalSpace
open scoped Classical NNReal

namespace SGPT.NAPotential.BJ.Divisorial
open SGPT.Foundations.PublishedEnvelope SGPT.Foundations.PublishedEnvelope.Berkovich SGPT.NAPotential.Berkovich
variable {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (.of ℂ))

/-- The actual original trivial point is trivial on EVERY field fraction. -/
theorem original_trivial_genericValuation :
    SchemeValuedPoint.genericValuation (pointEquiv p (BerkovichPoint.trivial p)).1 rfl =
      (1 : Valuation X.functionField ℝ≥0) := by
  apply Valuation.ext
  intro a
  by_cases ha : a = 0
  · subst a
    simp
  apply NNReal.eq
  change (((pointEquiv p (BerkovichPoint.trivial p)).1.residueVal
    (SchemeValuedPoint.genericResidueEquiv X (genericPoint X) rfl a)) : ℝ) = _
  rw [pointEquiv_residueVal, BerkovichPoint.trivial_valAt_of_ne_zero (f := p)
    ((map_ne_zero_iff _ (SchemeValuedPoint.genericResidueEquiv X
      (genericPoint X) rfl).injective).mpr ha)]
  simp [BerkovichPoint.expNeg, Valuation.one_apply_of_ne_zero ha]

/-- A field valuation whose restriction is not nontrivial is literally the
trivial valuation, including zero. -/
theorem valuation_eq_one_of_not_nontrivial {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) (h : ¬ v.IsNontrivial) :
    v = 1 := by
  apply Valuation.ext
  intro a
  by_cases ha : a = 0
  · subst a
    simp
  rw [Valuation.one_apply_of_ne_zero ha]
  by_contra hh
  exact h ⟨a, (map_ne_zero v).mpr ha, hh⟩

end SGPT.NAPotential.BJ.Divisorial
