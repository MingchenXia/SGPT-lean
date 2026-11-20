import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.Data.Real.Basic

/-! Independent finite-support multilinear extension of arbitrary scalar
coefficients. No analytic or intersection-number data enter its definition.
Blueprint: finite-finsupp-multilinear-extension.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open scoped BigOperators
variable {I A : Type*} [Fintype I] [DecidableEq I]

/-- The genuine finite-support multilinear extension of independent scalar
coefficients, before any analytic comparison. -/
def finsuppMultilinearExtension (c : (I → A) → ℝ) :
    MultilinearMap ℝ (fun _ : I => A →₀ ℝ) ℝ := by
  classical
  exact (MultilinearMap.fromDFinsuppEquiv (fun _ : I => A) ℝ
    (fun p => MultilinearMap.mkPiRing ℝ I (c p))).compLinearMap
      (fun _ => (finsuppLequivDFinsupp ℝ).toLinearMap)

theorem finsuppMultilinearExtension_single (c : (I → A) → ℝ)
    (p : I → A) (r : I → ℝ) :
    finsuppMultilinearExtension c (fun i => Finsupp.single (p i) (r i)) =
      (∏ i, r i) * c p := by
  classical
  simp only [finsuppMultilinearExtension, MultilinearMap.compLinearMap_apply,
    LinearEquiv.coe_coe, finsuppLequivDFinsupp_apply_apply, Finsupp.toDFinsupp_single,
    MultilinearMap.fromDFinsuppEquiv_single, MultilinearMap.mkPiRing_apply, smul_eq_mul]

/-- Literal finite sum over the actual input supports, with the independent
coefficient of every actual tuple. No formal infinite summation is used. -/
theorem finsuppMultilinearExtension_apply (c : (I → A) → ℝ) (v : I → A →₀ ℝ) :
    finsuppMultilinearExtension c v =
      ∑ p ∈ Fintype.piFinset (fun i => (v i).support), (∏ i, v i (p i)) * c p := by
  classical
  simp only [finsuppMultilinearExtension, MultilinearMap.compLinearMap_apply,
    LinearEquiv.coe_coe, finsuppLequivDFinsupp_apply_apply,
    MultilinearMap.fromDFinsuppEquiv_apply, toDFinsupp_support,
    MultilinearMap.mkPiRing_apply, Finsupp.toDFinsupp_coe, smul_eq_mul]
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
