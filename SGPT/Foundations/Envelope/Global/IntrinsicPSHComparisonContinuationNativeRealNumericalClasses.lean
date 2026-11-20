import SGPT.Foundations.Envelope.Global.IntrinsicPSHComparisonContinuationNativeCurveNumericalClasses
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Real.Basic

/-!
# Actual real scalar extension of the original numerical Picard quotient

The primary real space is literally ℝ tensor over ℤ with the additive group
of the SAME original numerical Picard quotient. Genuine original whole
curve degrees extend canonically by scalar extension. They prove injection
of the native classes. Canonical native images span the actual real space,
giving actual finitely supported coefficients, without replacing the class
universe by degree vectors or assuming numerical invariance of metrics.
Route: owned `native-real-numerical-classes-route.tex`.
-/
open AlgebraicGeometry CategoryTheory TensorProduct
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.NativeCurveNumericalClasses
variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))

/-- The ACTUAL real scalar extension of the genuine original numerical Picard quotient. -/
abbrev RealNumericalClass := ℝ ⊗[ℤ] Additive (NumericalClass p)

/-- The canonical native class in its SAME actual real scalar extension. -/
def nativeRealClass (a : NumericalClass p) : RealNumericalClass p :=
  (1 : ℝ) ⊗ₜ[ℤ] Additive.ofMul a

/-- Actual original tensor classes become addition in the genuine real scalar extension. -/
theorem nativeRealClass_mul (a b : NumericalClass p) :
    nativeRealClass p (a * b) = nativeRealClass p a + nativeRealClass p b := by
  change (1 : ℝ) ⊗ₜ[ℤ] (Additive.ofMul a + Additive.ofMul b) = _
  exact TensorProduct.tmul_add _ _ _

/-- The SAME original integer curve degree extended canonically to the ACTUAL real class space. -/
def realCurveDegree {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C = 1) (i : C ⟶ X) (hi : i ≫ p = q) :
    RealNumericalClass p →ₗ[ℝ] ℝ :=
  (((Int.castAddHom ℝ).comp
    (curveDegree p q hq hdim i hi).toAdditiveLeft).toIntLinearMap).liftBaseChange ℝ

/-- Literal real pure tensors retain the exact SAME original whole integer degree. -/
theorem realCurveDegree_tmul {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C = 1) (i : C ⟶ X) (hi : i ≫ p = q)
    (r : ℝ) (a : NumericalClass p) :
    realCurveDegree p q hq hdim i hi (r ⊗ₜ[ℤ] Additive.ofMul a) =
      r * ((Multiplicative.toAdd (curveDegree p q hq hdim i hi a) : ℤ) : ℝ) := rfl

/-- The real degree of the canonical native class is its true original integer curve degree. -/
theorem realCurveDegree_nativeRealClass {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C = 1) (i : C ⟶ X) (hi : i ≫ p = q)
    (a : NumericalClass p) :
    realCurveDegree p q hq hdim i hi (nativeRealClass p a) =
      ((Multiplicative.toAdd (curveDegree p q hq hdim i hi a) : ℤ) : ℝ) := by
  exact (realCurveDegree_tmul p q hq hdim i hi 1 a).trans (one_mul _)

/-- ALL genuine original curve degrees prove injection of native classes into their actual scalar extension. -/
theorem nativeRealClass_injective : Function.Injective (nativeRealClass p) := by
  intro a b hab
  apply numericalClass_ext p a b
  intro C hC q hq hdim i hi
  have he := congrArg (realCurveDegree p q hq hdim i hi) hab
  rw [realCurveDegree_nativeRealClass, realCurveDegree_nativeRealClass] at he
  change Multiplicative.toAdd (curveDegree p q hq hdim i hi a) =
    Multiplicative.toAdd (curveDegree p q hq hdim i hi b)
  exact_mod_cast he

/-- Genuine native classes span the ENTIRE actual real scalar extension. -/
theorem span_nativeRealClass :
    Submodule.span ℝ (Set.range (nativeRealClass p)) = ⊤ := by
  apply top_unique
  intro z
  have hmem : z ∈ Submodule.span ℝ (Set.range (nativeRealClass p)) := by
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul r a =>
        have ht : r ⊗ₜ[ℤ] a = r • nativeRealClass p a.toMul := by
          change r ⊗ₜ[ℤ] a = r • ((1 : ℝ) ⊗ₜ[ℤ] a)
          rw [TensorProduct.smul_tmul']
          simp only [smul_eq_mul, mul_one]
        rw [ht]
        exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a.toMul, rfl⟩)
    | add z w hz hw => exact Submodule.add_mem _ hz hw
  exact fun _ => hmem

/-- EVERY genuine real numerical class has actual finite native-class coefficients. -/
theorem exists_finite_nativeRealClass_coefficients (a : RealNumericalClass p) :
    ∃ c : NumericalClass p →₀ ℝ, Finsupp.linearCombination ℝ (nativeRealClass p) c = a :=
  ((span_range_eq_top_iff_surjective_finsuppLinearCombination
    (R := ℝ) (v := nativeRealClass p)).mp (span_nativeRealClass p)) a

end SGPT.Foundations.Envelope.NativeCurveNumericalClasses

#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.RealNumericalClass
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.RealNumericalClass
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.nativeRealClass
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.nativeRealClass
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.nativeRealClass_mul
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.nativeRealClass_mul
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.realCurveDegree
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.realCurveDegree
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.realCurveDegree_tmul
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.realCurveDegree_tmul
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.realCurveDegree_nativeRealClass
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.realCurveDegree_nativeRealClass
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.nativeRealClass_injective
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.nativeRealClass_injective
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.span_nativeRealClass
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.span_nativeRealClass
#check @SGPT.Foundations.Envelope.NativeCurveNumericalClasses.exists_finite_nativeRealClass_coefficients
#print axioms SGPT.Foundations.Envelope.NativeCurveNumericalClasses.exists_finite_nativeRealClass_coefficients
