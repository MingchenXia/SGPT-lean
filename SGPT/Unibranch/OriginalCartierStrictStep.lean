import SGPT.Unibranch.EmbeddedBlowup
import SGPT.Unibranch.SourceMorphismExt
import SGPT.Foundations.Analysis.Pending.HironakaNormalCrossingsOrderedChoiceComparison

/-! The SAME native strict arrow of an actual ordered SNC Cartier blowup.
The physical ambient centre and its original ordered position stay explicit;
no nonempty Cartier step is relabelled as an empty ambient stage.
Blueprint first: `original-cartier-strict-step.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.Unibranch.OriginalCartierStrictStep
noncomputable section
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
  SGPT.Foundations.Analysis.Pending BlowupTowers NormalCrossings HironakaEmbeddedAnalytic
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps HironakaReducedComplexAnalyticSpaces
  HironakaNormalCrossingsOrderedChoiceComparison SourceReducedComplexSpace

variable {n : ℕ} {M Y : CMfd.{0} n}
  (F : List (Set M × ℕ)) (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length)
  {π : Y → M} (hπ : IsBlowupAlong n (F.get j).1 π)

/-- The actual inverse is derived for this SAME actual ordered centre and blowup. -/
def ambientBiholomorphism : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ M :=
  CartierBiholomorphism F hF j hπ

theorem ambientBiholomorphism_coe : (ambientBiholomorphism F hF j hπ : Y → M) = π :=
  CartierBiholomorphism_coe F hF j hπ

include F hF j hπ in
/-- ENTIRE literal conventional strict carrier, including all points over the Cartier centre. -/
theorem strictTransform_eq_preimage {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W) :
    strictTransform n π W = π ⁻¹' W := by
  have he : exceptionalLocus n π = ∅ := by
    rw [← ambientBiholomorphism_coe F hF j hπ]
    exact eq_empty_iff_forall_notMem.mpr
      (fun y => MarkedIdealTowerTransport.notMem_exceptionalLocus (ambientBiholomorphism F hF j hπ) y)
  rw [strictTransform,he,sdiff_empty]
  exact (hW.isClosed.preimage hπ.contMDiff.continuous).closure_eq

variable {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)

include hW in
private theorem carrier_dictionary (y : Y) :
    y ∈ strictTransform n π W ↔ ambientBiholomorphism F hF j hπ y ∈ W := by
  rw [strictTransform_eq_preimage F hF j hπ hW]
  change π y ∈ W ↔ ambientBiholomorphism F hF j hπ y ∈ W
  rw [ambientBiholomorphism_coe]

/-- Full quotient morphisms and BOTH inverse equations come from the genuine ambient inverse. -/
def rawIso : actualSubspaceLocallyRingedSpace (n := n) (strictTransform n π W) ≅
    actualSubspaceLocallyRingedSpace (n := n) W :=
  actualSubspaceBiholomorphicIso (ambientBiholomorphism F hF j hπ)
    (strictTransform n π W) W (carrier_dictionary F hF j hπ hW)

/-- The actual quotient isomorphism in the EXISTING ORIGINAL native category. -/
def nativeIso :
    ofClosedAnalytic (strictTransform n π W)
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hW) ≅
    ofClosedAnalytic W hW :=
  ObjectProperty.isoMk sourceReducedComplexSpaceProperty (Over.isoMk (rawIso F hF j hπ hW)
    (actualSubspaceMap_point (ambientBiholomorphism F hF j hπ).contMDiff
      (fun y hy => (carrier_dictionary F hF j hπ hW y).mp hy)))

/-- The ENTIRE constructed native map is the SAME already defined strict projection. -/
theorem nativeIso_hom_eq :
    (nativeIso F hF j hπ hW).hom = EmbeddedBlowup.strictTransformMorphism hπ hW := by
  apply morphism_eq_of_pointwise_eq
  intro y
  apply Subtype.ext
  change ambientBiholomorphism F hF j hπ y.val = π y.val
  exact congrFun (ambientBiholomorphism_coe F hF j hπ) y.val

include hF in
theorem strictProjection_isIso : IsIso (EmbeddedBlowup.strictTransformMorphism hπ hW) := by
  rw [← nativeIso_hom_eq F hF j hπ hW]
  infer_instance

/-- SAME complete original complex scalar triangle. -/
theorem nativeIso_scalar :
    (nativeIso F hF j hπ hW).hom.hom.left ≫ subspacePointMap (n := n) W =
      subspacePointMap (n := n) (strictTransform n π W) :=
  Over.w (nativeIso F hF j hπ hW).hom.hom

/-- SAME full ambient inclusion/projection square, with all quotient-sheaf maps. -/
theorem nativeIso_inclusion :
    (nativeIso F hF j hπ hW).hom.hom.left ≫ actualSubspaceInclusion (n := n) W =
      actualSubspaceInclusion (n := n) (strictTransform n π W) ≫
        ChartedSpace.locallyRingedSpaceMap π hπ.contMDiff := by
  rw [nativeIso_hom_eq,EmbeddedBlowup.strictTransformMorphism_left]
  exact (actualSubspaceMap_inclusion hπ.contMDiff
    (fun _ hy => (closure_minimal sdiff_subset (hW.isClosed.preimage hπ.contMDiff.continuous)) hy)).symm

end
end SGPT.Unibranch.OriginalCartierStrictStep
