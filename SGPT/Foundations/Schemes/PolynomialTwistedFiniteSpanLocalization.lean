import SGPT.Foundations.Schemes.PolynomialTwistedFiniteSpan
import SGPT.Foundations.Schemes.PolynomialTwistedCoordinateLocalization
import SGPT.Foundations.Schemes.HomogeneousCechDimensionShift

/-! # Actual coordinate localization of true finite twisted-section spans

The literal finite homogeneous span maps into the actual Γ-star localization.
Normalized evaluation gives a genuine injective coordinate map; literal
generator fractions have precisely their true native frame coefficients.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ) (M : (polynomialProj K n).Modules)
  {A : Type} [Fintype A] [DecidableEq A] (d : A → ℕ)
  (t : ∀ a, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M (d a))
  (i : Fin (n + 1))
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The genuine integral degree-zero coordinate fractions of the literal finite polynomial span. -/
abbrev polynomialTwistedFiniteSpanCoordinateDegreeZero :=
  localizedHomogeneousModulePiece
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
    (polynomialProjTwistedFiniteSpanPiece K n M d t) (MvPolynomial.X i) 1
    (polynomialCoordinate_X_degree i) 0

/-- The true homogeneous finite-span inclusion induces a true native coordinate localization map. -/
def polynomialTwistedFiniteSpanCoordinateInclusion :
    polynomialTwistedFiniteSpanCoordinateDegreeZero K n M d t i →ₗ[K]
      polynomialTwistedCoordinateDegreeZero K n M i :=
  localizedHomogeneousModuleMap
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
    (polynomialProjTwistedFiniteSpanPiece K n M d t)
    (polynomialProjTwistedSectionPiece K n M)
    (polynomialProjTwistedFiniteSpan K n M d t).subtype (fun _ _ h => h)
    (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) 0

omit [Fintype A] [DecidableEq A] in
/-- Native localization makes the actual finite-span coordinate inclusion injective, allowing all torsion. -/
theorem polynomialTwistedFiniteSpanCoordinateInclusion_injective :
    Function.Injective (polynomialTwistedFiniteSpanCoordinateInclusion K n M d t i) :=
  localizedHomogeneousModuleMap_injective
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
    (polynomialProjTwistedFiniteSpanPiece K n M d t)
    (polynomialProjTwistedSectionPiece K n M)
    (polynomialProjTwistedFiniteSpan K n M d t).subtype (fun _ _ h => h)
    Subtype.val_injective (MvPolynomial.X i) 1 (polynomialCoordinate_X_degree i) 0

/-- Actual normalized finite-span fractions evaluate in actual structurally scalar coordinate sections. -/
def polynomialTwistedFiniteSpanCoordinateMap :
    polynomialTwistedFiniteSpanCoordinateDegreeZero K n M d t i →ₗ[K]
      bundleSections M (polynomialProjCoordinateOpen K n i) :=
  (polynomialTwistedCoordinateDegreeZeroMap K n M i).comp
    (polynomialTwistedFiniteSpanCoordinateInclusion K n M d t i)

omit [Fintype A] [DecidableEq A] in
/-- True coordinate-power uniqueness makes the actual normalized finite-span map injective. -/
theorem polynomialTwistedFiniteSpanCoordinateMap_injective
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent] :
    Function.Injective (polynomialTwistedFiniteSpanCoordinateMap K n M d t i) :=
  (polynomialTwistedCoordinateDegreeZeroMap_injective K n M i).comp
    (polynomialTwistedFiniteSpanCoordinateInclusion_injective K n M d t i)

/-- A literal true generator divided by the actual coordinate to its genuine homogeneous degree. -/
def polynomialTwistedFiniteSpanCoordinateGeneratorFraction (a : A) :
    polynomialTwistedFiniteSpanCoordinateDegreeZero K n M d t i := by
  let m : polynomialProjTwistedFiniteSpan K n M d t :=
    ⟨polynomialProjTwistedFiniteGenerators K n M d t a, Submodule.subset_span ⟨a, rfl⟩⟩
  have hm : m ∈ polynomialProjTwistedFiniteSpanPiece K n M d t (d a : ℤ) :=
    polynomialProjTwistedSectionPiece_ofTwistedSection K n M (d a) (t a)
  exact ⟨LocalizedModule.mk m (homogeneousPowerDenominator (MvPolynomial.X i) (d a)),
    d a, m, (by simpa using hm), rfl⟩

omit [Fintype A] [DecidableEq A] in
/-- Genuine finite-span generator fractions map to the corresponding actual full twisted-section fractions. -/
theorem polynomialTwistedFiniteSpanCoordinateInclusion_generatorFraction (a : A) :
    (polynomialTwistedFiniteSpanCoordinateInclusion K n M d t i
      (polynomialTwistedFiniteSpanCoordinateGeneratorFraction K n M d t i a)).val =
    LocalizedModule.mk ((polynomialProjTwistingLine K n).ofTwistedSection M (d a) (t a))
      (homogeneousPowerDenominator (MvPolynomial.X i) (d a)) := by
  exact actualLocalizedModuleMap_mk _ _ _ _

omit [Fintype A] [DecidableEq A] in
/-- Every actual included generator fraction evaluates to its literal true native coordinate-frame coefficient. -/
theorem polynomialTwistedFiniteSpanCoordinateMap_generatorFraction (a : A) :
    polynomialTwistedFiniteSpanCoordinateMap K n M d t i
      (polynomialTwistedFiniteSpanCoordinateGeneratorFraction K n M d t i a) =
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (d a) i (t a) := by
  change polynomialTwistedLocalizedCoordinateEvaluation K n M i
    (polynomialTwistedFiniteSpanCoordinateInclusion K n M d t i
      (polynomialTwistedFiniteSpanCoordinateGeneratorFraction K n M d t i a)).val = _
  rw [polynomialTwistedFiniteSpanCoordinateInclusion_generatorFraction,
    polynomialTwistedLocalizedCoordinateEvaluation_mk,
    polynomialTwistedCoordinateCoefficientSum_of]

end

end SGPT.Foundations.Schemes
