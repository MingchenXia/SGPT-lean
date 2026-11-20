import SGPT.NAPotential.ProjectiveGraphNativePoint

/-!
# The actual original graph-open immersion has exactly the same native Segre point

Blueprint: `projective-graph-native-readback.tex`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPointSquare

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open ProjectiveGraphProjection ProjectiveGraphAnalyticMap ProjectiveGraphLiteralImmersion
open ProjectiveGraphCentredChart ProjectiveGraphNativeReadback ProjectiveGraphNativePoint

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) (j : Fin (E.ambientDimension + 1))
  [hU : Nonempty (coordOpen E j)] {s : ℕ} (b : Fin s → X.functionField)
  (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens)

/-- **Actual native graph-open point square**, built from the SAME original normalized Segre values. -/
theorem literalOpenProjectiveMap_point
    (p : SchemeComplexPoint (openStructureMap (f := f) (coordOpen E j) (isAffineOpen_coordOpen E j) b W)) :
    schemeComplexPointMap _ _ (literalOpenProjectiveMap E j hU b W)
      (literalOpenProjectiveMap_overBase E j hU b W) p =
        polynomialProjVectorChartPoint (segreDim E.ambientDimension s) (coordSegrePivot E j s)
          (fun k => ProjectiveGraphPointEvaluation.graphPointEval (f := f)
            (coordOpen E j) (isAffineOpen_coordOpen E j) b W p (literalCoordinates E j hU b k)) := by
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  let q : SchemeComplexPoint (affineStructuralMap ℂ
      (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))) :=
    ⟨p.val ≫ W.ι, by
      rw [← projection_structure E j hU b]
      exact (Category.assoc _ _ _).symm.trans p.property⟩
  have hpoint := projectiveMap_point (literalCoordinates E j hU b) (coordSegrePivot E j s)
    (literalCoordinates_pivot E j hU b) q
  have hvec : (fun k => affinePointAlgebra q (literalCoordinates E j hU b k)) =
      (fun k => ProjectiveGraphPointEvaluation.graphPointEval (f := f)
        (coordOpen E j) (isAffineOpen_coordOpen E j) b W p (literalCoordinates E j hU b k)) := by
    funext k
    exact (DFunLike.congr_fun (graphPointEval_eq_native E j b W p) (literalCoordinates E j hU b k)).symm
  apply Subtype.ext
  change p.val ≫ (W.ι ≫ literalProjectiveMap E j hU b) = _
  rw [← Category.assoc]
  simpa only [hvec, schemeComplexPointMap, q, literalProjectiveMap] using congrArg Subtype.val hpoint

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphPointSquare
