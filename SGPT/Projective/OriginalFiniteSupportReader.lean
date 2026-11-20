import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Fintype.EquivFin

/-! Exact actual finite-support enumeration for original line combinations.
Blueprint: original-finite-support-reader.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open scoped BigOperators

/-- Enumerate the ACTUAL support, retaining its SAME coefficients and
generators. Empty support gives a genuine Fin0 sum. No representation input. -/
theorem originalLinearCombination_eq_supportFinSum
    {R A V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (v : A →₀ R) (w : A → V) :
    Finsupp.linearCombination R w v =
      ∑ i : Fin v.support.card,
        v ((v.support.equivFin.symm i).val) • w ((v.support.equivFin.symm i).val) := by
  classical
  change (∑ a ∈ v.support, v a • w a) = _
  exact (Finset.sum_attach v.support (fun a => v a • w a)).symm.trans
    (Equiv.sum_comp v.support.equivFin.symm (fun a : ↥v.support => v a.val • w a.val)).symm

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
