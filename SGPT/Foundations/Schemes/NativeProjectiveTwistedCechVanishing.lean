import SGPT.Foundations.Schemes.NativeProjectiveTwistedGlobalSectionComparison

/-! # Uniform actual projective twist comparison and positive Čech vanishing

One genuine finite chart-generated graded span represents every nonnegative
twist. Its native positive vanishing transports to the actual structural-field
section complexes. A single bound also gives the canonical global-section
comparison, without a vanishing or saturation premise.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type) [Field K] (n : ℕ) (M : (polynomialProj K n).Modules)
  [∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
    Γ(polynomialProjModuleChart M j, ⊤)]
  [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]

/-- Actual twisted section complexes have uniformly zero positive native cohomology. -/
theorem polynomialProjFiniteChartTwistedCech_homology_eventually_isZero :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m → ∀ p : ℕ,
      IsZero ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
        (polynomialProjModuleTensorTwist K n M m) (polynomialProjCoordinateOpen K n)
        (schemeConstantMap (polynomialProjStructureMap K n)))).homology (p + 1)) := by
  obtain ⟨c, hc⟩ := finiteGradedPolynomialCoordinateCech_homology_eventually_isZero
    (K := K) (I := Fin (n + 1)) (polynomialProjChartGeneratedTwistedPiece K n M)
  refine ⟨c.toNat, fun m hm p => ?_⟩
  have hcm : c ≤ (m : ℤ) := by omega
  exact (hc (m : ℤ) hcm p).of_iso
    (nonemptySubsetCechHomologyIso
      (polynomialProjChartGeneratedTwistedAllDegreeNonemptySubsetIso K n M m) (p + 1)).symm

/-- One actual bound supplies canonical section bijectivity and every positive coordinate vanishing. -/
theorem polynomialProjChartGeneratedTwistedUniformComparison_eventually :
    ∃ b : ℕ, ∀ m : ℕ, b ≤ m →
      Function.Bijective (polynomialProjChartGeneratedTwistedDegreeToGlobalSections K n M m) ∧
      ∀ p : ℕ, IsZero ((subsetCechComplex (actualSchemeModuleBaseSubsetDiagram
        (polynomialProjModuleTensorTwist K n M m) (polynomialProjCoordinateOpen K n)
        (schemeConstantMap (polynomialProjStructureMap K n)))).homology (p + 1)) := by
  obtain ⟨bsections, hsections⟩ :=
    polynomialProjChartGeneratedTwistedDegreeToGlobalSections_eventually_bijective K n M
  obtain ⟨bpositive, hpositive⟩ :=
    polynomialProjFiniteChartTwistedCech_homology_eventually_isZero K n M
  exact ⟨max bsections bpositive, fun m hm =>
    ⟨hsections m (le_trans (le_max_left _ _) hm),
      hpositive m (le_trans (le_max_right _ _) hm)⟩⟩

end

end SGPT.Foundations.Schemes
