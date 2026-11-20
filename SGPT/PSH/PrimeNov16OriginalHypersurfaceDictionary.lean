import SGPT.PSH.PrimeNov16OriginalHypersurface
import SGPT.PSH.PrimeNov16OriginalMarkedComponentLift

/-! Primitive original local-hyperplane hypersurfaces and internally derived
native representatives for every original smooth source. Full blueprint first. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalHypersurfaceDictionary
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaEmbeddedNativeMorphism BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic


open PrimeNov16OriginalHypersurface

private theorem component_native_chart {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) :
    ∃ i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel n) M ⟶ Y.obj.left,
      LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ Y.obj.hom = ambientPointMap n M ∧
      ∀ x : M, i.base x = pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) x := by
  let J := I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c
  let Q := actualSubspaceUnivIso (n := n) (M := M)
  let i := Q.inv ≫ J.hom.left
  have hI : LocallyRingedSpace.IsOpenImmersion I.hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (SourceReducedComplexSpace.isoLeft I).hom
    infer_instance
  have hJ : LocallyRingedSpace.IsOpenImmersion J.hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ I.hom.hom.left hI _
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion hY c)
  have hi : LocallyRingedSpace.IsOpenImmersion i :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ Q.inv (by dsimp only [Q]; infer_instance) J.hom.left hJ
  refine ⟨i, hi, ?_, ?_⟩
  · change (Q.inv ≫ J.hom.left) ≫ Y.obj.hom = _
    calc
      (Q.inv ≫ J.hom.left) ≫ Y.obj.hom = Q.inv ≫ (J.hom.left ≫ Y.obj.hom) := Category.assoc _ _ _
      _ = Q.inv ≫ (wholeModel (n := n) M).obj.hom := congrArg (fun f => Q.inv ≫ f) (Over.w J.hom)
      _ = _ := actualSubspaceUnivIso_inv_point
  · intro x
    have hQ : (Q.inv.base x).val = x := congrArg (fun f => f.base x) Q.inv_hom_id
    exact congrArg J.hom.left.base (Subtype.ext hQ)

theorem original_hypersurface_of_native_submanifold
    {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c)
    (D : Set M) (k : ℕ) (hD : IsClosedConnectedSubmanifold n D k) (hk : k+1=n) :
    IsOriginalHypersurface Y
      (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) '' D) := by
  let J := I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c
  let E := pointMap J '' D
  let H : M ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hY c).obj.left :=
    (Homeomorph.Set.univ M).symm.trans (isoHomeomorph I)
  have hKclosed : IsClosedMap (pointMap J) :=
    (OriginalSmoothComponents.component_isClopen hY c).1.isClosedEmbedding_subtypeVal.isClosedMap.comp H.isClosedMap
  have hKinj : Function.Injective (pointMap J) := by
    intro x y hxy
    exact H.injective (Subtype.ext hxy)
  have hEclosed : IsClosed E := hKclosed D hD.1
  have hEconn : IsConnected E := hD.2.1.image (pointMap J) (continuous_pointMap J).continuousOn
  obtain ⟨i₀, hi₀, hp₀, hpoint⟩ := component_native_chart hY c M I
  have heq : ((fun x : M => i₀.base x) ⁻¹' E) = D := by
    ext z
    change i₀.base z ∈ E ↔ z ∈ D
    rw [hpoint z]
    constructor
    · rintro ⟨w, hw, hval⟩
      exact hKinj hval ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  refine ⟨hEclosed, hEconn, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨m, U, i, hi, hp, u, hu⟩ := hY (pointMap J z)
  obtain ⟨hdim, hiff⟩ := PrimeNov16OriginalLocalChartComparison.dimension_and_regularity_of_original_charts
    i₀ i hi₀ hi hp₀ hp z u ((hpoint z).trans hu.symm) E k
  have hreg₀ : RegularAtDim (n := n) ((fun x : M => i₀.base x) ⁻¹' E) z k := heq.symm ▸ hD.2.2 z hz
  have hreg := hiff.mp hreg₀
  have hm : m=k+1 := hdim.symm.trans hk.symm
  cases hm
  exact ⟨k, U, i, hi, hp, u, hu, hreg⟩

theorem original_hypersurface_iff_native_pullback
    {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth) {E : Set Y.obj.left}
    (c : ConnectedComponents Y.obj.left) (hEc : E ⊆ OriginalSmoothComponents.componentSet c)
    {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) :
    IsOriginalHypersurface Y E ↔ ∃ k : ℕ,
      IsClosedConnectedSubmanifold n
        (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) ⁻¹' E) k ∧
      k+1=n ∧
      pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) ''
        (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) ⁻¹' E) = E := by
  constructor
  · intro hE
    exact native_pullback_of_original_hypersurface hY hE c hEc M I
  · rintro ⟨k, hD, hk, himage⟩
    exact himage ▸ original_hypersurface_of_native_submanifold hY c M I _ k hD hk

end SGPT.PSH.PrimeNov16OriginalHypersurfaceDictionary
