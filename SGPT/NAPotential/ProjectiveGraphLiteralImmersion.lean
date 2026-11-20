import SGPT.NAPotential.ProjectiveGraphAffineImmersion
import SGPT.NAPotential.ProjectiveGraphCentredChart
import SGPT.NAPotential.ProjectiveGraphAnalyticMap

/-!
# The same original literal graph algebra and its actual native immersion

All coordinates, generation and structural compatibilities are manufactured
from the original coordinate chart and original rational functions.
Blueprint: `projective-graph-affine-immersion.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphLiteralImmersion

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MvPolynomial
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open ProjectiveGraphCentredChart ProjectiveGraphCoordinateCharts
open ProjectiveGraphProjection ProjectiveGraphAnalyticMap ProjectiveGraphAffineImmersion
open ProjectiveGraphSegreAlgebra ProjectiveGraphSegreEquations
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) (j : Fin (E.ambientDimension + 1))
  (hU : Nonempty (coordOpen E j)) {s : ℕ} (b : Fin s → X.functionField)

/-- The literal normalized original Segre vector, inside the SAME original graph algebra. -/
def literalCoordinates (k : Fin (segreDim E.ambientDimension s + 1)) :
    Algebra.adjoin Γ(X, coordOpen E j) (Set.range b) := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  exact ⟨chartRationalSegreCoordinates E j hU b k, by
    change chartRationalSegreCoordinates E j hU b k ∈
      (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)).restrictScalars ℂ
    rw [adjoin_coordGraph E j hU b]
    exact Algebra.subset_adjoin ⟨k, rfl⟩⟩

/-- The actual coordinate is exactly its original rational function. -/
theorem literalCoordinates_val (k : Fin (segreDim E.ambientDimension s + 1)) :
    (literalCoordinates E j hU b k : X.functionField) = chartRationalSegreCoordinates E j hU b k := rfl

/-- The actual original pivot entry is literally one in the original B. -/
theorem literalCoordinates_pivot : literalCoordinates E j hU b (coordSegrePivot E j s) = 1 := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  apply Subtype.ext
  exact chartRationalSegreCoordinates_pivot E j hU b

/-- The actual original normalized Segre entries generate the SAME literal original B. -/
theorem adjoin_literalCoordinates :
    letI := hU
    letI := affineChartAlgebra f (coordOpen E j)
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
    Algebra.adjoin ℂ (Set.range (literalCoordinates E j hU b)) = ⊤ := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  let B := Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)
  apply Subalgebra.map_injective (f := (B.restrictScalars ℂ).val) Subtype.val_injective
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
  have hrange : (B.restrictScalars ℂ).val '' Set.range (literalCoordinates E j hU b) =
      Set.range (chartRationalSegreCoordinates E j hU b) := by
    ext z
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, rfl⟩
  rw [hrange]
  exact (adjoin_coordGraph E j hU b).symm

/-- The SAME literal original graph algebra's native projective immersion. -/
def literalProjectiveMap : Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b))) ⟶
    polynomialProj ℂ (segreDim E.ambientDimension s) := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  exact projectiveMap (literalCoordinates E j hU b) (coordSegrePivot E j s)

instance literalProjectiveMap_isImmersion : IsImmersion (literalProjectiveMap E j hU b) := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  exact projectiveMap_isImmersion _ _ (literalCoordinates_pivot E j hU b) (adjoin_literalCoordinates E j hU b)

/-- Literal original graph projection and literal original complex-algebra structure agree. -/
theorem projection_structure :
    letI := hU
    letI := affineChartAlgebra f (coordOpen E j)
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
    projection (coordOpen E j) (isAffineOpen_coordOpen E j) b ≫ f =
      affineStructuralMap ℂ (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b))) := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  rw [projection, Category.assoc, affineChartStructuralMap_eq_affineStructuralMap f]
  simp only [affineProjection, affineStructuralMap, ← Spec.map_comp]
  congr 1
  ext c
  exact congrArg Subtype.val (IsScalarTower.algebraMap_apply ℂ Γ(X, coordOpen E j)
    (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)) c).symm

/-- The actual SAME native immersion has precisely the actual original graph structure morphism. -/
theorem literalProjectiveMap_overBase :
    literalProjectiveMap E j hU b ≫ polynomialProjStructureMap ℂ (segreDim E.ambientDimension s) =
      projection (coordOpen E j) (isAffineOpen_coordOpen E j) b ≫ f := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  rw [literalProjectiveMap, projectiveMap_structure, projection_structure E j hU b]

/-- Restriction of the same actual native immersion to any prescribed original open. -/
def literalOpenProjectiveMap
    (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens) :
    W.toScheme ⟶ polynomialProj ℂ (segreDim E.ambientDimension s) := W.ι ≫ literalProjectiveMap E j hU b

instance literalOpenProjectiveMap_isImmersion
    (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens) :
    IsImmersion (literalOpenProjectiveMap E j hU b W) := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  dsimp only [literalOpenProjectiveMap]
  infer_instance

/-- The prescribed original open preserves precisely the original product-map structure morphism. -/
theorem literalOpenProjectiveMap_overBase
    (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens) :
    literalOpenProjectiveMap E j hU b W ≫ polynomialProjStructureMap ℂ (segreDim E.ambientDimension s) =
      openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  rw [literalOpenProjectiveMap, Category.assoc, literalProjectiveMap_overBase]
  exact (Category.assoc _ _ _).symm

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphLiteralImmersion
