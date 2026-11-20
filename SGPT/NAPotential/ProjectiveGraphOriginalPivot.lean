import SGPT.NAPotential.ProjectiveGraphOriginalChart
import SGPT.NAPotential.ProjectiveGraphPivotScheme

/-!
# The original full Segre quotient has the literal original graph chart

Blueprint: `projective-graph-pivot-scheme.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphOriginalPivot

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite
open SGPT.NAPotential.FSPos
open ProjectiveGraphSegre ProjectiveGraphOriginalChart ProjectiveGraphPivotScheme

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) {s : ℕ}

local instance originalPivotNonempty : Nonempty (coordOpen E (genericCoordinateIndex E)) :=
  ⟨⟨genericPoint X, genericCoordinateIndex_mem E⟩⟩

/-- **Native original full-relation quotient chart equals Spec of the literal original A[b]**. -/
def originalGlobalChartSchemeIso (b : Fin s → X.functionField) :
    letI := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
    letI := schemeFunctionFieldAlgebra f
    (originalPivotOpen (A := ℂ) (rationalSegreCoordinates E b) (segrePivot E s)).toScheme ≅
      Spec (.of (Algebra.adjoin Γ(X, coordOpen E (genericCoordinateIndex E)) (Set.range b))) := by
  let := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E (genericCoordinateIndex E))
  let e : Algebra.adjoin ℂ (Set.range (originalSegreTail E b)) ≃+*
      Algebra.adjoin Γ(X, coordOpen E (genericCoordinateIndex E)) (Set.range b) :=
    (Subalgebra.equivOfEq _ _ (adjoin_originalSegreTail E b)).toRingEquiv
  exact originalPivotChartSchemeIso (A := ℂ) (rationalSegreCoordinates E b)
    (segrePivot E s) (rationalSegreCoordinates_pivot E b) ≪≫
      Scheme.Spec.mapIso e.toCommRingCatIso.symm.op

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphOriginalPivot
