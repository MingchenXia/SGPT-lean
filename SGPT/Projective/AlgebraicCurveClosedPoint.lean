import SGPT.Foundations.Schemes.NativeSmoothFunctionFieldDimension
import SGPT.Foundations.Schemes.NativeFanoAffineChartDimension
import SGPT.Foundations.Schemes.FiniteTypeDomainClosedPointDimension
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! Actual closed-point codimension on the SAME original smooth integral
complex curve. Blueprint: algebraic-curve-native-degree.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open Algebra CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes TopologicalSpace
open scoped nonZeroDivisors

/-- Actual smooth dimension and actual finite-type closed-point height
produce codimension one at EVERY original closed point of the curve. -/
theorem closedPoint_coheight_eq_one {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℂ)) [SmoothOfRelativeDimension 1 f]
    (x : X) (hx : IsClosed ({x} : Set X)) : Order.coheight x = 1 := by
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  obtain ⟨V, hV, hxV, _hs⟩ := smooth_cotangent_affine_chart f 1 x
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  let := affineChartAlgebra f V
  let := schemeFunctionFieldAlgebra f
  let : IsScalarTower ℂ Γ(X, V) X.functionField := schemeFunctionField_affineChartScalarTower f V
  let : IsFractionRing Γ(X, V) X.functionField := functionField_isFractionRing_of_isAffineOpen X V hV
  let : Algebra.FiniteType ℂ Γ(X, V) := affineChartAlgebra_finiteType f hV
  let : Algebra.IsAlgebraic Γ(X, V) X.functionField :=
    IsLocalization.isAlgebraic X.functionField (nonZeroDivisors Γ(X, V))
  have hF := nativeSmoothFunctionField_trdeg f 1
  have htr : Algebra.trdeg ℂ Γ(X, V) = 1 := by
    have h := trdeg_add_eq ℂ Γ(X, V) (A := X.functionField)
    rw [trdeg_eq_zero (R := Γ(X, V)) (A := X.functionField), add_zero, hF] at h
    exact h
  have hdim : ringKrullDim Γ(X, V) = 1 := finiteTypeDomain_ringKrullDim_of_trdeg ℂ Γ(X, V) 1 htr
  let p : Spec (.of Γ(X, V)) := hV.primeIdealOf ⟨x, hxV⟩
  let : p.asIdeal.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  have hheight : (p.asIdeal.height : WithBot ℕ∞) = 1 :=
    (finiteTypeDomain_maximalIdeal_height_eq_dimension ℂ Γ(X, V) p.asIdeal).trans hdim
  have hp : Order.coheight p = 1 := by
    rw [← idealHeight_eq_coheight]
    exact_mod_cast hheight
  calc
    Order.coheight x = Order.coheight (hV.fromSpec p) :=
      (congrArg (fun y : X => Order.coheight y) (hV.fromSpec_primeIdealOf ⟨x, hxV⟩)).symm
    _ = Order.coheight p := coheight_eq_of_isOpenImmersion hV.fromSpec
    _ = 1 := hp

end SGPT.Projective.NumEq.AlgebraicCurveDegree
