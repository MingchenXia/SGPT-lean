import SGPT.Foundations.Envelope.AlgGeom.NativeNumericalCarrierComparison
import SGPT.Foundations.Envelope.AlgGeom.NativeRealNumericalClasses
import SGPT.Foundations.Envelope.Global.IntrinsicPSHComparisonContinuationNativeRealNumericalClasses

/-! Same-family specializations; no equality of closed-curve and all-map kernels. -/
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped TensorProduct
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonCurves

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

open NativeNumericalCarrierComparison NativeClosedCurveDegrees

section ClosedCurves
variable [IsProjective p]

/-- Original integer degrees of the literal closed integral curve family. -/
def closedIntegerFunctional (C : ClosedIntegralCurve X) : Additive X.Pic →ₗ[ℤ] ℤ :=
  (C.additiveDegree p).toIntLinearMap

/-- The original closed-curve integer common-kernel quotient. -/
abbrev ClosedIntegerQuotient := IntegerQuotient (closedIntegerFunctional p)

/-- The old real numerical carrier equals realification of its SAME integer family. -/
def closedQuotientComparison : NativeRealNumericalClasses.Space p ≃ₗ[ℝ]
    ℝ ⊗[ℤ] ClosedIntegerQuotient p :=
  quotientComparison (closedIntegerFunctional p)

/-- Every original Picard tensor survives the canonical carrier comparison literally. -/
theorem closedQuotientComparison_projection_tmul (r : ℝ) (a : Additive X.Pic) :
    closedQuotientComparison p (NativeRealNumericalClasses.projection p (r ⊗ₜ[ℤ] a)) =
      r ⊗ₜ[ℤ] (integerKernel (closedIntegerFunctional p)).mkQ a :=
  quotientComparison_mk_tmul (closedIntegerFunctional p) r a

/-- The comparison retains the SAME original invertible line and its original class. -/
theorem closedQuotientComparison_lineClass (L : X.Modules) (hL : IsInvertible L) :
    closedQuotientComparison p (NativeRealNumericalClasses.lineClass p L hL) =
      (1 : ℝ) ⊗ₜ[ℤ] (integerKernel (closedIntegerFunctional p)).mkQ
        (Additive.ofMul (CurvePicardDegrees.lineClass L hL)) :=
  closedQuotientComparison_projection_tmul p 1
    (Additive.ofMul (CurvePicardDegrees.lineClass L hL))

end ClosedCurves

/-- Actual integral projective curve maps, packaging only the existing geometric data. -/
structure IntegralCurveMap where
  carrier : Scheme.{u}
  integral : IsIntegral carrier
  structureMorphism : carrier ⟶ Spec (.of k)
  projective : IsProjectiveFactorization structureMorphism
  dimension : topologicalKrullDim carrier = 1
  morphism : carrier ⟶ X
  triangle : morphism ≫ p = structureMorphism

namespace IntegralCurveMap
variable (C : IntegralCurveMap p)

/-- The original descended integer degree, with no separation certificate. -/
def integerFunctional : Additive (NativeCurveNumericalClasses.NumericalClass p) →ₗ[ℤ] ℤ := by
  letI := C.integral
  exact (NativeCurveNumericalClasses.curveDegree p C.structureMorphism C.projective
    C.dimension C.morphism C.triangle).toAdditiveLeft.toIntLinearMap

/-- The existing original real degree for the same actual curve map. -/
def realFunctional : NativeCurveNumericalClasses.RealNumericalClass p →ₗ[ℝ] ℝ := by
  letI := C.integral
  exact NativeCurveNumericalClasses.realCurveDegree p C.structureMorphism C.projective
    C.dimension C.morphism C.triangle

/-- The original real degree is literally scalar extension of its original integer degree. -/
theorem realFunctional_eq :
    C.realFunctional p = NativeNumericalCarrierComparison.realFunctional (C.integerFunctional p) := by
  ext a
  rfl

end IntegralCurveMap

/-- Integer joint detection is produced by the existing actual numerical quotient. -/
theorem mapIntegerFunctional_jointly_detects
    (a : Additive (NativeCurveNumericalClasses.NumericalClass p))
    (ha : ∀ C : IntegralCurveMap p, C.integerFunctional p a = 0) : a = 0 := by
  change a.toMul = 1
  apply NativeCurveNumericalClasses.numericalClass_ext p a.toMul 1
  intro C hC q hq hdim i hi
  have h := ha ⟨C, hC, q, hq, hdim, i, hi⟩
  change Multiplicative.toAdd
    (NativeCurveNumericalClasses.curveDegree p q hq hdim i hi a.toMul) = 0 at h
  apply Multiplicative.ext
  simpa only [map_one, toAdd_one] using h

/-- ALL original curve-map degrees jointly detect the ENTIRE actual real numerical carrier. -/
theorem mapRealFunctional_jointly_detects
    (a : NativeCurveNumericalClasses.RealNumericalClass p)
    (ha : ∀ C : IntegralCurveMap p, C.realFunctional p a = 0) : a = 0 := by
  apply NativeNumericalCarrierComparison.realFunctional_jointly_detects
    (fun C : IntegralCurveMap p => C.integerFunctional p)
    (mapIntegerFunctional_jointly_detects p) a
  intro C
  rw [← C.realFunctional_eq p]
  exact ha C

/-- Equality on the original real carrier is detected by the SAME actual curve-map degrees. -/
theorem realNumericalClass_ext
    (a b : NativeCurveNumericalClasses.RealNumericalClass p)
    (h : ∀ {C : Scheme.{u}} [IsIntegral C]
      (q : C ⟶ Spec (.of k)) (hq : IsProjectiveFactorization q)
      (hdim : topologicalKrullDim C = 1) (i : C ⟶ X) (hi : i ≫ p = q),
      NativeCurveNumericalClasses.realCurveDegree p q hq hdim i hi a =
        NativeCurveNumericalClasses.realCurveDegree p q hq hdim i hi b) : a = b := by
  apply sub_eq_zero.mp
  apply mapRealFunctional_jointly_detects p
  intro C
  let : IsIntegral C.carrier := C.integral
  rw [map_sub, sub_eq_zero]
  exact h C.structureMorphism C.projective C.dimension C.morphism C.triangle

end SGPT.Foundations.Envelope.NativeNumericalCarrierComparisonCurves
