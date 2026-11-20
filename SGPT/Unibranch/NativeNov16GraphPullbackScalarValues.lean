import SGPT.Unibranch.NativeNov16OriginalPullbackValues
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
import SGPT.Unibranch.NativeNov16NormalGraphCoordinates

/-! Full original graph scalar pullbacks manufacture their actual every-point value readbacks.
Blueprint: native-nov16-graph-pullback-scalar-values.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.NativeNov16GraphPullbackScalarValues
open HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
open NativeNov16SectionCoordinateMorphism NativeNov16NormalGraphLift
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionFunctor
open PrimeNov16AnalyticNormalizationLocalGraph

set_option backward.isDefEq.respectTransparency.types false in
theorem pulledBaseScalar_value {n m : ℕ} {Z : Set (ComplexModel n)}
    (d : GraphPresentation n Z) (P : Opens (ComplexModel m)) (C : Set P)
    (hC : IsComplexAnalyticSubset (n := m) C) (W : Opens (TopCat.of C))
    (f : coordinateSource P C hC W ⟶ d.target) (F : ComplexModel n → ℂ)
    (hF : DifferentiableOn ℂ F (ballDomain (n := n) d.radius)) (x : W) :
    evaluate P C W x (pulledBaseScalar d P C hC W f F hF)=
      F (f.hom.left.base x).val.val.val := by
  let g := (f ≫ d.baseInclusion).hom.left
  have he : pullTopRingHom f.hom.left (baseScalarSection d F hF)=
      pullTopRingHom g (fullBaseScalarSection d F hF) := by
    rw [baseScalar_eq_pullFull,← pullTop_comp]
    rfl
  have hp : g ≫ subspacePointMap (n := n)
      {z : ballDomain (n := n) d.radius | z.val ∈ Z}=
      (actualSubspaceLocallyRingedSpace (n := m) C).ofRestrict W.isOpenEmbedding ≫
        subspacePointMap (n := m) C := Over.w (f ≫ d.baseInclusion).hom
  change HironakaActualAnalyticSubspaceResidue.actualSubspaceStalkEval (n := m) C x.val
    ((actualSubspaceSheaf (n := m) C).presheaf.germ W x.val x.property
      (openTopEquiv (actualSubspaceLocallyRingedSpace (n := m) C) W
        (pullTopRingHom f.hom.left (baseScalarSection d F hF))))=_
  rw [he]
  exact (NativeNov16OriginalPullbackValues.pullTop_value C
    {z : ballDomain (n := n) d.radius | z.val ∈ Z} W g hp x
      (fullBaseScalarSection d F hF)).trans
    (fullBaseScalar_value d F hF (g.base x))

end SGPT.Unibranch.NativeNov16GraphPullbackScalarValues
