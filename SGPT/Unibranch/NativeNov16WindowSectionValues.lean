import SGPT.Unibranch.NativeNov16OriginalPullbackValues
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalWindowSectionPullback

/-! Actual selected-open pullbacks internally preserve literal residue values.
Blueprint: native-nov16-window-section-values.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.NativeNov16WindowSectionValues
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspaceResidue
open PrimeNov16AnalyticNormalizationOriginalWindowSectionPullback

variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

set_option backward.isDefEq.respectTransparency.types false in
theorem pullWindow_value (C : Set M) (D : Set N)
    (W : Opens (actualSubspaceLocallyRingedSpace (n := n) C).toTopCat)
    (U : Opens (actualSubspaceLocallyRingedSpace (n := m) D).toTopCat)
    (f : (actualSubspaceLocallyRingedSpace (n := n) C).restrict W.isOpenEmbedding ⟶
      (actualSubspaceLocallyRingedSpace (n := m) D).restrict U.isOpenEmbedding)
    (hpoint : (f ≫ (actualSubspaceLocallyRingedSpace (n := m) D).ofRestrict U.isOpenEmbedding) ≫
      subspacePointMap (n := m) D =
      (actualSubspaceLocallyRingedSpace (n := n) C).ofRestrict W.isOpenEmbedding ≫
        subspacePointMap (n := n) C) (x : W)
    (s : ((actualSubspaceSheaf (n := m) D).presheaf.obj (op U)).carrier) :
    actualSubspaceStalkEval (n := n) C x.val
      ((actualSubspaceSheaf (n := n) C).presheaf.germ W x.val x.property
        (pullWindowRingHom f s)) =
      actualSubspaceStalkEval (n := m) D (f.base x).val
        ((actualSubspaceSheaf (n := m) D).presheaf.germ
          U (f.base x).val (f.base x).property s) := by
  let A := actualSubspaceLocallyRingedSpace (n := n) C
  let B := actualSubspaceLocallyRingedSpace (n := m) D
  let j := B.ofRestrict U.isOpenEmbedding
  let a := B.presheaf.germ U (f.base x).val (f.base x).property s
  have hg : (f ≫ j).stalkMap x a =
      f.stalkMap x ((B.restrictStalkIso U.isOpenEmbedding (f.base x)).inv a) := by
    rw [LocallyRingedSpace.stalkMap_comp]
    change f.stalkMap x (j.stalkMap (f.base x) a) = _
    rw [← B.restrictStalkIso_inv_eq_ofRestrict U.isOpenEmbedding (f.base x)]
    rfl
  have hv := congrArg (actualSubspaceStalkEval (n := n) C x.val)
    (pullWindow_germ f s x)
  apply hv.trans
  change actualSubspaceStalkEval (n := n) C x.val
    ((A.restrictStalkIso W.isOpenEmbedding x).hom
      (f.stalkMap x ((B.restrictStalkIso U.isOpenEmbedding (f.base x)).inv a))) = _
  rw [← hg]
  exact NativeNov16OriginalPullbackValues.restricted_stalk_value C D W (f ≫ j) hpoint x a

end SGPT.Unibranch.NativeNov16WindowSectionValues
