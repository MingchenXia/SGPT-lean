import SGPT.Foundations.Schemes.PolynomialTwistedChartGenerators
import SGPT.Foundations.Schemes.PolynomialTwistedFiniteSpanLocalization
import SGPT.Foundations.Schemes.HomogeneousSubsetLocalization
import SGPT.Foundations.Schemes.PolynomialTwistedCoordinateScalars

/-! # Actual coordinate generation by the genuine finite homogeneous span

The actual homogeneous inclusion respects native restrictions on all coordinate
subsets. Genuine finite chart-generator extensions will supply its actual
coordinate generation through true homogeneous coordinate-ring scalars.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ) (M : (polynomialProj K n).Modules)
attribute [local instance] MvPolynomial.gradedAlgebra

section ActualFamily

variable {A : Type} [Fintype A] [DecidableEq A] (d : A → ℕ)
  (t : ∀ a, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf M (d a))

/-- The literal finite-span inclusion is genuinely natural for all actual coordinate-subset localizations. -/
def polynomialTwistedFiniteSpanSubsetInclusion (k : ℤ) :
    homogeneousCoordinateSubsetDiagram
      (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjTwistedFiniteSpanPiece K n M d t)
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree k ⟶
    homogeneousCoordinateSubsetDiagram
      (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
      (polynomialProjTwistedSectionPiece K n M)
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree k :=
  homogeneousCoordinateSubsetDiagramMap
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
    (polynomialProjTwistedFiniteSpanPiece K n M d t)
    (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree
    (polynomialProjTwistedSectionPiece K n M)
    (polynomialProjTwistedFiniteSpan K n M d t).subtype (fun _ _ h => h) k

omit [Fintype A] [DecidableEq A] in
/-- Every actual coordinate-subset localization inclusion is injective, with no torsion-free assumption. -/
theorem polynomialTwistedFiniteSpanSubsetInclusion_injective (k : ℤ) (S : Finset (Fin (n + 1))) :
    Function.Injective ((polynomialTwistedFiniteSpanSubsetInclusion K n M d t k).app S) :=
  localizedHomogeneousModuleMap_injective
    (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
    (polynomialProjTwistedFiniteSpanPiece K n M d t)
    (polynomialProjTwistedSectionPiece K n M)
    (polynomialProjTwistedFiniteSpan K n M d t).subtype (fun _ _ h => h) Subtype.val_injective
    (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S)
    (S.card : ℤ) (homogeneousCoordinateSubsetProduct_degree _ _ polynomialCoordinate_X_degree S) k

/-- Genuine finite-span coordinate fractions map linearly to the native affine-chart module over its actual coordinate ring. -/
def polynomialTwistedFiniteSpanNativeChartMap (i : Fin (n + 1)) :
    polynomialTwistedFiniteSpanCoordinateDegreeZero K n M d t i →ₗ[polynomialProjCoordinateRing K n i]
      Γ(polynomialProjModuleChart M i, ⊤) :=
  (polynomialTwistedCoordinateChartMap K n i M).comp
    (polynomialCoordinateLocalizedPieceMap K n (polynomialProjTwistedFiniteSpanPiece K n M d t) i
      (polynomialProjTwistedSectionPiece K n M)
      (polynomialProjTwistedFiniteSpan K n M d t).subtype (fun _ _ h => h) 0)

omit [Fintype A] [DecidableEq A] in
/-- Each true finite-span generator fraction has its literal native affine-chart coefficient. -/
theorem polynomialTwistedFiniteSpanNativeChartMap_generatorFraction (i : Fin (n + 1)) (a : A) :
    polynomialTwistedFiniteSpanNativeChartMap K n M d t i
      (polynomialTwistedFiniteSpanCoordinateGeneratorFraction K n M d t i a) =
    (polynomialProjChartTopSectionsIso M i).inv
      (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (d a) i (t a)) :=
  congrArg (polynomialProjChartTopSectionsIso M i).inv
    (polynomialTwistedFiniteSpanCoordinateMap_generatorFraction K n M d t i a)

omit [Fintype A] [DecidableEq A] in
/-- Genuine coordinate-power uniqueness makes the actual native finite-span chart map injective. -/
theorem polynomialTwistedFiniteSpanNativeChartMap_injective
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent] (i : Fin (n + 1)) :
    Function.Injective (polynomialTwistedFiniteSpanNativeChartMap K n M d t i) :=
  (ConcreteCategory.bijective_of_isIso (polynomialProjChartTopSectionsIso M i).inv).injective.comp
    (polynomialTwistedFiniteSpanCoordinateMap_injective K n M d t i)

omit [Fintype A] [DecidableEq A] in
/-- Actual native chart generation by genuine coefficients makes the true finite-span localization surjective. -/
theorem polynomialTwistedFiniteSpanNativeChartMap_surjective (i : Fin (n + 1))
    (hgen : Submodule.span (polynomialProjCoordinateRing K n i)
      (Set.range (fun a => (polynomialProjChartTopSectionsIso M i).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (d a) i (t a)))) = ⊤) :
    Function.Surjective (polynomialTwistedFiniteSpanNativeChartMap K n M d t i) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact ⟨polynomialTwistedFiniteSpanCoordinateGeneratorFraction K n M d t i a,
    polynomialTwistedFiniteSpanNativeChartMap_generatorFraction K n M d t i a⟩

/-- Actual chart generation and true uniqueness identify the literal finite-span localization with the actual chart module. -/
def polynomialTwistedFiniteSpanNativeChartEquiv
    [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent] (i : Fin (n + 1))
    (hgen : Submodule.span (polynomialProjCoordinateRing K n i)
      (Set.range (fun a => (polynomialProjChartTopSectionsIso M i).inv
        (atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas M (d a) i (t a)))) = ⊤) :
    polynomialTwistedFiniteSpanCoordinateDegreeZero K n M d t i ≃ₗ[polynomialProjCoordinateRing K n i]
      Γ(polynomialProjModuleChart M i, ⊤) :=
  LinearEquiv.ofBijective (polynomialTwistedFiniteSpanNativeChartMap K n M d t i)
    ⟨polynomialTwistedFiniteSpanNativeChartMap_injective K n M d t i,
      polynomialTwistedFiniteSpanNativeChartMap_surjective K n M d t i hgen⟩

end ActualFamily

section GenuineChartGenerators

variable [∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
  Γ(polynomialProjModuleChart M j, ⊤)]
  [∀ j, (polynomialProjModuleChart M j).IsQuasicoherent]

/-- The genuinely constructed finite homogeneous span represents every actual affine-chart module, with no representation input. -/
def polynomialProjChartGeneratedTwistedCoordinateEquiv (i : Fin (n + 1)) :
    polynomialTwistedFiniteSpanCoordinateDegreeZero K n M
      (polynomialProjFiniteChartGeneratorDegree K n M) (polynomialProjFiniteChartGeneratorTwist K n M) i ≃ₗ[
        polynomialProjCoordinateRing K n i] Γ(polynomialProjModuleChart M i, ⊤) :=
  polynomialTwistedFiniteSpanNativeChartEquiv K n M
    (polynomialProjFiniteChartGeneratorDegree K n M) (polynomialProjFiniteChartGeneratorTwist K n M) i
    (polynomialProjFiniteChartGeneratorCoefficients_span K n M i)

end GenuineChartGenerators

/-- Native closed-immersion line geometry actually constructs a finite homogeneous family representing every genuine chart. -/
theorem closedPolynomialProjPushforward_exists_finite_twisted_chart_representation
    {X : Scheme} (f : X ⟶ polynomialProj K n) [IsClosedImmersion f]
    {L : X.Modules} (a : LineBundleAtlas L) :
    ∃ (m : Fin (n + 1) → ℕ) (d : (Σ j : Fin (n + 1), Fin (m j)) → ℕ)
      (t : ∀ b, bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
        ((Scheme.Modules.pushforward f).obj L) (d b)),
      ∀ j, Function.Bijective (polynomialTwistedFiniteSpanNativeChartMap K n
        ((Scheme.Modules.pushforward f).obj L) d t j) := by
  let M := (Scheme.Modules.pushforward f).obj L
  let : ∀ j, Module.Finite (polynomialProjCoordinateRing K n j)
      Γ(polynomialProjModuleChart M j, ⊤) := fun j => polynomialProjPushforwardChartSections_finite f a j
  let : ∀ j, (polynomialProjModuleChart M j).IsQuasicoherent :=
    fun j => polynomialProjPushforwardChart_isQuasicoherent f a j
  refine ⟨polynomialProjFiniteChartGeneratorCount K n M,
    polynomialProjFiniteChartGeneratorDegree K n M, polynomialProjFiniteChartGeneratorTwist K n M, ?_⟩
  intro j
  exact ⟨polynomialTwistedFiniteSpanNativeChartMap_injective K n M _ _ j,
    polynomialTwistedFiniteSpanNativeChartMap_surjective K n M _ _ j
      (polynomialProjFiniteChartGeneratorCoefficients_span K n M j)⟩

end

end SGPT.Foundations.Schemes
