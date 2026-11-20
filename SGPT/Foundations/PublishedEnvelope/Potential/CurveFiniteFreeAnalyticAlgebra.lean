import SGPT.Foundations.PublishedEnvelope.Potential.FiniteFreeBanachAlgebra
import SGPT.Foundations.PublishedEnvelope.Potential.LineAffinoidRestrictions
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # The whole actual finite free curve algebra over a standard affinoid -/

open scoped NNReal Polynomial TensorProduct
noncomputable section

namespace SGPT.Foundations.PublishedEnvelope.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m : ℕ}
variable (U : FCStandardAffinoid w m)

/-- The ORIGINAL polynomial homomorphism supplies the actual scalar action on analytic functions. -/
instance polynomialAnalyticAlgebra : Algebra K[X] U.AnalyticFunctions :=
  U.polynomialAnalyticMap.toAlgebra

omit [IsAlgClosed K] in
theorem algebraMap_polynomial_analytic (p : K[X]) :
    algebraMap K[X] U.AnalyticFunctions p = U.polynomialAnalyticMap p := rfl

omit [IsAlgClosed K] in
/-- The polynomial action retains the already prescribed ORIGINAL coefficient map from K. -/
theorem polynomialAnalyticMap_C (a : K) :
    U.polynomialAnalyticMap (Polynomial.C a) = algebraMap K U.AnalyticFunctions a := rfl

variable {B ι : Type*} [CommRing B] [Algebra K[X] B] [Fintype ι]

/-- The whole original tensor algebra; no reduction or selected-point quotient is taken. -/
abbrev CurveAnalyticTensor (B : Type*) [CommRing B] [Algebra K[X] B] :=
  U.AnalyticFunctions ⊗[K[X]] B

/-- The actual basis obtained by scalar extension of the ORIGINAL finite free curve basis. -/
def curveAnalyticBasis (b : Module.Basis ι K[X] B) :
    Module.Basis ι U.AnalyticFunctions (U.CurveAnalyticTensor B) :=
  b.baseChange U.AnalyticFunctions

omit [IsAlgClosed K] [Fintype ι] in
theorem curveAnalyticBasis_apply (b : Module.Basis ι K[X] B) (i : ι) :
    U.curveAnalyticBasis b i = (1 : U.AnalyticFunctions) ⊗ₜ[K[X]] b i :=
  b.baseChange_apply U.AnalyticFunctions i

/-- A whole-ring copy with the CONSTRUCTED complete ultrametric ring norm. -/
def CurveAnalyticAlgebra (b : Module.Basis ι K[X] B) : Type _ :=
  SGPT.Foundations.PublishedEnvelope.FiniteFreeAnalyticCopy (U.curveAnalyticBasis b)

variable (b : Module.Basis ι K[X] B)

instance curveAnalyticCommRing : CommRing (U.CurveAnalyticAlgebra b) :=
  inferInstanceAs (CommRing (SGPT.Foundations.PublishedEnvelope.FiniteFreeAnalyticCopy (U.curveAnalyticBasis b)))

instance curveAnalyticScalarAlgebra : Algebra U.AnalyticFunctions (U.CurveAnalyticAlgebra b) :=
  inferInstanceAs (Algebra U.AnalyticFunctions
    (SGPT.Foundations.PublishedEnvelope.FiniteFreeAnalyticCopy (U.curveAnalyticBasis b)))

instance curveAnalyticNormedCommRing : NormedCommRing (U.CurveAnalyticAlgebra b) :=
  inferInstanceAs (NormedCommRing (SGPT.Foundations.PublishedEnvelope.FiniteFreeAnalyticCopy (U.curveAnalyticBasis b)))

instance curveAnalyticIsUltrametricDist : IsUltrametricDist (U.CurveAnalyticAlgebra b) :=
  inferInstanceAs (IsUltrametricDist (SGPT.Foundations.PublishedEnvelope.FiniteFreeAnalyticCopy (U.curveAnalyticBasis b)))

instance curveAnalyticCompleteSpace : CompleteSpace (U.CurveAnalyticAlgebra b) :=
  inferInstanceAs (CompleteSpace (SGPT.Foundations.PublishedEnvelope.FiniteFreeAnalyticCopy (U.curveAnalyticBasis b)))

/-- The genuine entire original algebra, coefficient map and multiplication are retained. -/
def curveAnalyticOriginalEquiv :
    U.CurveAnalyticAlgebra b ≃ₐ[U.AnalyticFunctions] U.CurveAnalyticTensor B :=
  SGPT.Foundations.PublishedEnvelope.FiniteFreeAnalyticCopy.originalAlgEquiv (U.curveAnalyticBasis b)

/-- Its topology is explicitly the actual finite-product topology of the original coefficients. -/
def curveAnalyticCoefficientUniformEquiv :
    U.CurveAnalyticAlgebra b ≃ᵤ (ι → U.AnalyticFunctions) :=
  SGPT.Foundations.PublishedEnvelope.FiniteFreeAnalyticCopy.coefficientUniformEquiv (U.curveAnalyticBasis b)

end SGPT.Foundations.PublishedEnvelope.Berkovich.RelativeSpectrum.FCStandardAffinoid
