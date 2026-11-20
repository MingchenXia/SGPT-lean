import SGPT.Unibranch.OriginalNativeModification
import SGPT.Unibranch.OriginalCommonResolution
import SGPT.Unibranch.OriginalSmoothDimension

/-! Paired actual good images derive native dimensions. Blueprint first:
`prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalGoodDimension
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceManifoldCharts
  HironakaReducedComplexAnalyticSpaces HironakaEmbeddedNativeMorphism HironakaResolutionSpaceComplex
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalCommonResolution

theorem native_dimensions_eq_of_actual_good_restrictions
    {n₀ n₁ : ℕ} {X : SourceReducedComplexSpace} {Y₀ Y₁ : Type}
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n₀) Y₀] [IsComplexManifold n₀ Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n₁) Y₁] [IsComplexManifold n₁ Y₁]
    (F₀ : wholeModel (n := n₀) Y₀ ⟶ X) (F₁ : wholeModel (n := n₁) Y₁ ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B)
    (hR₀ : LocallyRingedSpace.IsOpenImmersion (restrictedOriginalMorphism F₀ B hBc))
    (hR₁ : LocallyRingedSpace.IsOpenImmersion (restrictedOriginalMorphism F₁ B hBc))
    (hrange : range (restrictedOriginalMorphism F₁ B hBc).base =
      range (restrictedOriginalMorphism F₀ B hBc).base)
    (a : goodOpen F₁ B hBc) : n₀ = n₁ := by
  let G₀ := OriginalCommonResolution.goodOpen F₀ B hBc
  let G₁ := OriginalCommonResolution.goodOpen F₁ B hBc
  let x : G₁ := a
  let R₀ := OriginalCommonResolution.restrictedOriginalMorphism F₀ B hBc
  let R₁ := OriginalCommonResolution.restrictedOriginalMorphism F₁ B hBc
  let E := @openImmersionIsoOfRangeEq _ _ _ R₁ R₀ hR₁ hR₀ hrange
  have hfac : E.hom ≫ R₀ = R₁ :=
    @openImmersionIsoOfRangeEq_hom_fac _ _ _ R₁ R₀ hR₁ hR₀ hrange
  have hp₀ : R₀ ≫ X.obj.hom = subspacePointMap (n := n₀) (univ : Set G₀) :=
    Over.w ((nativeMorphism (M := G₀) (N := Y₀) contMDiff_subtype_val) ≫ F₀).hom
  have hp₁ : R₁ ≫ X.obj.hom = subspacePointMap (n := n₁) (univ : Set G₁) :=
    Over.w ((nativeMorphism (M := G₁) (N := Y₁) contMDiff_subtype_val) ≫ F₁).hom
  have hEp : E.hom ≫ subspacePointMap (n := n₀) (univ : Set G₀) =
      subspacePointMap (n := n₁) (univ : Set G₁) := by
    calc
      _ = E.hom ≫ (R₀ ≫ X.obj.hom) := congrArg (fun K => E.hom ≫ K) hp₀.symm
      _ = (E.hom ≫ R₀) ≫ X.obj.hom := (Category.assoc _ _ _).symm
      _ = R₁ ≫ X.obj.hom := congrArg (fun K => K ≫ X.obj.hom) hfac
      _ = _ := hp₁
  let Q₀ := actualSubspaceUnivIso (n := n₀) (M := G₀)
  let Q₁ := actualSubspaceUnivIso (n := n₁) (M := G₁)
  let D := Q₁.symm.trans (E.trans Q₀)
  have hQ₀ : Q₀.hom ≫ ambientPointMap n₀ G₀ =
      subspacePointMap (n := n₀) (univ : Set G₀) := rfl
  have hDp : D.hom ≫ ambientPointMap n₀ G₀ = ambientPointMap n₁ G₁ := by
    calc
      _ = Q₁.inv ≫ (E.hom ≫ (Q₀.hom ≫ ambientPointMap n₀ G₀)) := by
        simp only [D, Iso.trans_hom, Iso.symm_hom, Category.assoc]
      _ = Q₁.inv ≫ (E.hom ≫ subspacePointMap (n := n₀) (univ : Set G₀)) :=
        congrArg (fun K => Q₁.inv ≫ (E.hom ≫ K)) hQ₀
      _ = Q₁.inv ≫ subspacePointMap (n := n₁) (univ : Set G₁) :=
        congrArg (fun K => Q₁.inv ≫ K) hEp
      _ = _ := actualSubspaceUnivIso_inv_point (n := n₁) (M := G₁)
  exact (OriginalSmoothDimension.native_iso_dimension_eq D hDp x).symm

end SGPT.PSH.PrimeNov16OriginalGoodDimension
