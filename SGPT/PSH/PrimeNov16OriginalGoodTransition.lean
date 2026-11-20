import SGPT.PSH.PrimeNov16OriginalGoodDimension

/-! Genuine paired good-open transition; full BP first. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalGoodTransition
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceManifoldCharts
  HironakaReducedComplexAnalyticSpaces HironakaEmbeddedNativeMorphism HironakaResolutionSpaceComplex
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalCommonResolution OriginalSmoothSourceAnalytic

theorem exists_actual_good_transition
    {n : ℕ} {X : SourceReducedComplexSpace} {Y₀ Y₁ : Type}
    [TopologicalSpace Y₀] [ChartedSpace (ComplexModel n) Y₀] [IsComplexManifold n Y₀]
    [TopologicalSpace Y₁] [ChartedSpace (ComplexModel n) Y₁] [IsComplexManifold n Y₁]
    (F₀ : wholeModel (n := n) Y₀ ⟶ X) (F₁ : wholeModel (n := n) Y₁ ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B)
    (hR₀ : LocallyRingedSpace.IsOpenImmersion (restrictedOriginalMorphism F₀ B hBc))
    (hR₁ : LocallyRingedSpace.IsOpenImmersion (restrictedOriginalMorphism F₁ B hBc))
    (hrange : range (restrictedOriginalMorphism F₁ B hBc).base =
      range (restrictedOriginalMorphism F₀ B hBc).base) :
    ∃ e : goodOpen F₁ B hBc ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ goodOpen F₀ B hBc,
      (∀ y, pointMap F₀ (e y).val = pointMap F₁ y.val) ∧
      InjOn (pointMap F₀) (pointMap F₀ ⁻¹' Bᶜ) := by
  let R₀ := restrictedOriginalMorphism F₀ B hBc
  let R₁ := restrictedOriginalMorphism F₁ B hBc
  let E := @openImmersionIsoOfRangeEq _ _ _ R₁ R₀ hR₁ hR₀ hrange
  have hfac : E.hom ≫ R₀ = R₁ :=
    @openImmersionIsoOfRangeEq_hom_fac _ _ _ R₁ R₀ hR₁ hR₀ hrange
  have hEp : E.hom ≫ subspacePointMap (n := n) (univ : Set (goodOpen F₀ B hBc)) =
      subspacePointMap (n := n) (univ : Set (goodOpen F₁ B hBc)) := by
    have hp₀ : R₀ ≫ X.obj.hom = subspacePointMap (n := n) (univ : Set (goodOpen F₀ B hBc)) :=
      Over.w ((nativeMorphism (M := goodOpen F₀ B hBc) (N := Y₀) contMDiff_subtype_val) ≫ F₀).hom
    have hp₁ : R₁ ≫ X.obj.hom = subspacePointMap (n := n) (univ : Set (goodOpen F₁ B hBc)) :=
      Over.w ((nativeMorphism (M := goodOpen F₁ B hBc) (N := Y₁) contMDiff_subtype_val) ≫ F₁).hom
    rw [← hp₀, ← Category.assoc, hfac]
    exact hp₁
  let e := nativeDiffeomorph E hEp
  refine ⟨e, ?_, ?_⟩
  · intro y
    exact congrArg (fun K => K.base (⟨y, mem_univ y⟩ : (univ : Set (goodOpen F₁ B hBc)))) hfac
  · intro y hy z hz heq
    let p : (univ : Set (goodOpen F₀ B hBc)) := ⟨⟨y, hy⟩, mem_univ _⟩
    let q : (univ : Set (goodOpen F₀ B hBc)) := ⟨⟨z, hz⟩, mem_univ _⟩
    have hR : R₀.base p = R₀.base q := heq
    exact congrArg (fun w => w.val.val) (hR₀.base_open.injective hR)

end SGPT.PSH.PrimeNov16OriginalGoodTransition
