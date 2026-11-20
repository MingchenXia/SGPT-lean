import SGPT.Foundations.Schemes.PolynomialTwistedSubsetEvaluation
import SGPT.Foundations.Schemes.NonemptySubsetCechComparison

/-! # Genuine natural normalized evaluation on nonempty intersections

Actual homogeneous localization arrows commute with actual sheaf restriction.
The native universal property proves compatibility without assuming injective
restriction or discarding localization torsion.
-/

open CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M : (polynomialProj K n).Modules) (i : Fin (n + 1))
  (S T : Finset (Fin (n + 1))) (hi : i ∈ S) (hST : S ⊆ T)

/-- True restriction preserves the actual normalized polynomial action in a common selected frame. -/
theorem polynomialTwistedSubsetPolynomialMap_restrict
    (p : MvPolynomial (Fin (n + 1)) K) :
    (polynomialProj K n).presheaf.map
      (homOfLE (actualSchemeSubsetOpen_antitone (polynomialProjCoordinateOpen K n) hST)).op
      (polynomialTwistedSubsetPolynomialMap K n i S hi p) =
      polynomialTwistedSubsetPolynomialMap K n i T (hST hi) p := by
  change (polynomialProj K n).presheaf.map _
    ((polynomialProj K n).presheaf.map _ (polynomialTwistedCoordinatePolynomialMap K n i p)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Native sheaf restriction is linear for the true common-frame normalized polynomial action. -/
def polynomialTwistedSubsetRestriction :
    polynomialTwistedSubsetSections K n M i S hi →ₗ[MvPolynomial (Fin (n + 1)) K]
      polynomialTwistedSubsetSections K n M i T (hST hi) where
  toFun := M.presheaf.map
    (homOfLE (actualSchemeSubsetOpen_antitone (polynomialProjCoordinateOpen K n) hST)).op
  map_add' := by intro x y; simp
  map_smul' p x := by
    change M.presheaf.map
      (homOfLE (actualSchemeSubsetOpen_antitone (polynomialProjCoordinateOpen K n) hST)).op
      (polynomialTwistedSubsetPolynomialMap K n i S hi p •
        (show bundleSections M (polynomialProjSubsetCoordinateOpen K n S) from x)) =
      polynomialTwistedSubsetPolynomialMap K n i T (hST hi) p •
        M.presheaf.map
          (homOfLE (actualSchemeSubsetOpen_antitone (polynomialProjCoordinateOpen K n) hST)).op x
    rw [Scheme.Modules.map_smul, polynomialTwistedSubsetPolynomialMap_restrict]

/-- Original genuine coefficient maps commute with actual subset restrictions. -/
theorem polynomialTwistedSubsetCoefficientMap_restrict :
    (polynomialTwistedSubsetRestriction K n M i S T hi hST).comp
      (polynomialTwistedSubsetCoefficientMap K n M i S hi) =
        polynomialTwistedSubsetCoefficientMap K n M i T (hST hi) := by
  apply LinearMap.ext
  intro x
  change M.presheaf.map _ (M.presheaf.map _ (polynomialTwistedCoordinateCoefficientSum K n M i x)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The true smaller-subset denominator acts invertibly on the actual larger intersection. -/
theorem polynomialTwistedSubsetSmallerLocalizationUnits :
    ∀ s : Submonoid.powers
      (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S),
      IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) K)
        (Module.End (MvPolynomial (Fin (n + 1)) K)
          (polynomialTwistedSubsetSections K n M i T (hST hi))) s) := by
  intro s
  obtain ⟨q, hq⟩ := s.property
  rw [← hq, map_pow]
  apply IsUnit.pow
  rw [Module.End.isUnit_iff]
  change Function.Bijective (fun t : bundleSections M (polynomialProjSubsetCoordinateOpen K n T) =>
    polynomialTwistedSubsetPolynomialMap K n i T (hST hi)
      (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S) • t)
  have hu : IsUnit (polynomialTwistedSubsetPolynomialMap K n i T (hST hi)
      (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) T)) := by
    rw [polynomialTwistedSubsetPolynomialMap_product]
    exact polynomialProjSubsetRegularRatioProduct_isUnit K n i T (hST hi)
  have hd : polynomialTwistedSubsetPolynomialMap K n i T (hST hi)
      (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S) ∣
      polynomialTwistedSubsetPolynomialMap K n i T (hST hi)
        (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) T) := by
    refine ⟨polynomialTwistedSubsetPolynomialMap K n i T (hST hi)
      (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) (T \ S)), ?_⟩
    rw [← map_mul, ← homogeneousCoordinateSubsetProduct_factor _ hST]
  exact (isUnit_of_dvd_unit hd hu).smul_bijective

/-- Actual native localization uniqueness gives the genuine full coefficient-evaluation square. -/
theorem polynomialTwistedSubsetLocalizedEvaluation_restrict :
    (polynomialTwistedSubsetLocalizedEvaluation K n M i T (hST hi)).comp
      (actualLocalizedModuleDivisorRestriction
        (M := polynomialProjTwistedSectionModule K n M)
        (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S)
        (homogeneousCoordinateSubsetProduct (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) T)
        (homogeneousCoordinateSubsetProduct_dvd _ hST)) =
    (polynomialTwistedSubsetRestriction K n M i S T hi hST).comp
      (polynomialTwistedSubsetLocalizedEvaluation K n M i S hi) := by
  apply IsLocalizedModule.ext
    (Submonoid.powers (homogeneousCoordinateSubsetProduct
      (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) S))
    (LocalizedModule.mkLinearMap _ (polynomialProjTwistedSectionModule K n M))
    (polynomialTwistedSubsetSmallerLocalizationUnits K n M i S T hi hST)
  rw [LinearMap.comp_assoc, actualLocalizedModuleDivisorRestriction_comp]
  rw [polynomialTwistedSubsetLocalizedEvaluation, LocalizedModule.lift_comp]
  rw [LinearMap.comp_assoc, polynomialTwistedSubsetLocalizedEvaluation, LocalizedModule.lift_comp]
  exact (polynomialTwistedSubsetCoefficientMap_restrict K n M i S T hi hST).symm

/-- Degree-zero evaluation genuinely commutes with every true nonempty-subset arrow. -/
theorem polynomialTwistedSubsetDegreeZeroMap_restrict
    (z : polynomialTwistedSubsetDegreeZero K n M S) :
    polynomialTwistedSubsetDegreeZeroMap K n M i T (hST hi)
      (homogeneousCoordinateSubsetRestriction
        (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
        (polynomialProjTwistedSectionPiece K n M)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K))
        polynomialCoordinate_X_degree hST 0 z) =
    (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
      (schemeConstantMap (polynomialProjStructureMap K n))).map (homOfLE hST)
        (polynomialTwistedSubsetDegreeZeroMap K n M i S hi z) :=
  LinearMap.congr_fun
    (polynomialTwistedSubsetLocalizedEvaluation_restrict K n M i S T hi hST) z.val

/-- Genuine frame-independent evaluation is a natural map of actual nonempty coordinate diagrams. -/
def polynomialTwistedNonemptySubsetEvaluation :
    nonemptySubsetDiagram
      (homogeneousCoordinateSubsetDiagram
        (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
        (polynomialProjTwistedSectionPiece K n M)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K)) polynomialCoordinate_X_degree 0) ⟶
      nonemptySubsetDiagram (actualSchemeModuleBaseSubsetDiagram M
        (polynomialProjCoordinateOpen K n) (schemeConstantMap (polynomialProjStructureMap K n))) where
  app S := @ModuleCat.ofHom K _
    (polynomialTwistedSubsetDegreeZero K n M S.val)
    ((actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
      (schemeConstantMap (polynomialProjStructureMap K n))).obj S.val) _ _ _ _
    (polynomialTwistedSubsetDegreeZeroMap K n M S.property.choose S.val S.property.choose_spec)
  naturality {S T} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change polynomialTwistedSubsetDegreeZeroMap K n M T.property.choose T.val T.property.choose_spec
      (homogeneousCoordinateSubsetRestriction
        (polynomialIntegralGrading (K := K) (I := Fin (n + 1)))
        (polynomialProjTwistedSectionPiece K n M)
        (fun j => (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) K))
        polynomialCoordinate_X_degree (leOfHom f) 0 z) =
      (actualSchemeModuleBaseSubsetDiagram M (polynomialProjCoordinateOpen K n)
        (schemeConstantMap (polynomialProjStructureMap K n))).map (homOfLE (leOfHom f))
          (polynomialTwistedSubsetDegreeZeroMap K n M S.property.choose S.val S.property.choose_spec z)
    rw [polynomialTwistedSubsetDegreeZeroMap_independent K n M T.property.choose T.val
      T.property.choose_spec S.property.choose ((leOfHom f) S.property.choose_spec)]
    exact polynomialTwistedSubsetDegreeZeroMap_restrict K n M S.property.choose S.val T.val
      S.property.choose_spec (leOfHom f) z

end
end SGPT.Foundations.Schemes
