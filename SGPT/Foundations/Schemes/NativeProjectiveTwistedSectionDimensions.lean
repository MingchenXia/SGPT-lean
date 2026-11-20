import SGPT.Foundations.Schemes.NativeProjectiveTwistedGlobalSectionComparison
import SGPT.Foundations.Schemes.FiniteGradedPolynomialDegreePieces

/-! # Actual projective section dimensions of the same fixed graded span

Every actual integer piece of the chart-generated span is finite. The genuine
canonical comparison then identifies actual later section dimensions, without
a Hilbert-polynomial or geometric-leading-coefficient hypothesis.
-/

open CategoryTheory AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [Field K] (n : ℕ) (M : (polynomialProj K n).Modules)
  [∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
    Γ(polynomialProjModuleChart M j, ⊤)]
  [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]

/-- Every degree of the true once-chosen finite span is finite over the structural field. -/
theorem polynomialProjChartGeneratedTwistedPiece_finite (a : ℤ) :
    Module.Finite K (polynomialProjChartGeneratedTwistedPiece K n M a) :=
  finiteGradedPolynomialPiece_finite (K := K) (I := Fin (n + 1))
    (polynomialProjChartGeneratedTwistedPiece K n M) a

/-- Dimension of the actual global sections of the genuine nonnegative tensor twist. -/
def polynomialProjTwistedSectionDimension (m : ℕ) : ℕ :=
  Module.finrank K (actualSchemeModuleBaseGlobalSections
    (polynomialProjModuleTensorTwist K n M m)
    (schemeConstantMap (polynomialProjStructureMap K n)))

/-- The actual canonical later comparison proves genuine section finiteness. -/
theorem polynomialProjTwistedGlobalSections_finite_of_le_bound (m : ℕ)
    (hm : polynomialProjChartGeneratedTwistedGlobalSectionComparisonBound K n M ≤ m) :
    Module.Finite K (actualSchemeModuleBaseGlobalSections
      (polynomialProjModuleTensorTwist K n M m)
      (schemeConstantMap (polynomialProjStructureMap K n))) := by
  let := polynomialProjChartGeneratedTwistedPiece_finite K n M (m : ℤ)
  let e := polynomialProjChartGeneratedTwistedGlobalSectionsEquiv K n M m hm
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- Later actual section dimensions equal the degree dimensions of the same span. -/
theorem polynomialProjTwistedSectionDimension_eq_fixedPiece (m : ℕ)
    (hm : polynomialProjChartGeneratedTwistedGlobalSectionComparisonBound K n M ≤ m) :
    polynomialProjTwistedSectionDimension K n M m =
      Module.finrank K (polynomialProjChartGeneratedTwistedPiece K n M (m : ℤ)) := by
  exact (polynomialProjChartGeneratedTwistedGlobalSectionsEquiv K n M m hm).finrank_eq

/-- One fixed bound supplies finite actual sections and exact fixed-span dimensions. -/
theorem polynomialProjTwistedSectionDimension_eventually_eq_fixedPiece :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      Module.Finite K (actualSchemeModuleBaseGlobalSections
        (polynomialProjModuleTensorTwist K n M m)
        (schemeConstantMap (polynomialProjStructureMap K n))) ∧
      polynomialProjTwistedSectionDimension K n M m =
        Module.finrank K (polynomialProjChartGeneratedTwistedPiece K n M (m : ℤ)) := by
  exact ⟨polynomialProjChartGeneratedTwistedGlobalSectionComparisonBound K n M,
    fun m hm => ⟨polynomialProjTwistedGlobalSections_finite_of_le_bound K n M m hm,
      polynomialProjTwistedSectionDimension_eq_fixedPiece K n M m hm⟩⟩

end

end SGPT.Foundations.Schemes
