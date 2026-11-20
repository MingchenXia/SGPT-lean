import SGPT.Foundations.Schemes.NativeProjectiveTwistedSectionDimensions
import SGPT.Foundations.Schemes.FiniteGradedPolynomialHilbertPolynomial

/-! # Eventual polynomial of actual projective twist sections

The genuine fixed-span comparison and derived Hilbert--Serre polynomial give
an eventual polynomial for literal global sections. Its bound is the ambient
projective dimension; intrinsic dimension and intersection coefficients remain
separate geometric obligations.
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

/-- Actual later global sections are finite and have a derived dimension polynomial. -/
theorem polynomialProjTwistedSectionDimension_eventualPolynomial :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ n ∧
      ∃ c : ℕ, ∀ m : ℕ, c ≤ m →
        Module.Finite K (actualSchemeModuleBaseGlobalSections
          (polynomialProjModuleTensorTwist K n M m)
          (schemeConstantMap (polynomialProjStructureMap K n))) ∧
        (polynomialProjTwistedSectionDimension K n M m : ℚ) = Q.eval (m : ℚ) := by
  obtain ⟨Q, hQdeg, _hQzero, a, hQ⟩ :=
    finiteGradedPolynomialPiece_eventualPolynomial (K := K) (I := Fin (n + 1))
      (polynomialProjChartGeneratedTwistedPiece K n M)
  let b := polynomialProjChartGeneratedTwistedGlobalSectionComparisonBound K n M
  refine ⟨Q, by simpa using hQdeg, max b a.toNat, fun m hm => ?_⟩
  have hbm : polynomialProjChartGeneratedTwistedGlobalSectionComparisonBound K n M ≤ m :=
    le_trans (le_max_left _ _) hm
  have ham : a ≤ (m : ℤ) := by omega
  refine ⟨polynomialProjTwistedGlobalSections_finite_of_le_bound K n M m hbm, ?_⟩
  rw [polynomialProjTwistedSectionDimension_eq_fixedPiece K n M m hbm]
  simpa using hQ (m : ℤ) ham

end

end SGPT.Foundations.Schemes
