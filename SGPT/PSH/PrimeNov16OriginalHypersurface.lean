import SGPT.PSH.PrimeNov16OriginalLocalChartComparison
import SGPT.PSH.PrimeNov16OriginalMarkedComponentLift

/-! Primitive original local-hyperplane hypersurfaces and internally derived
native representatives for every original smooth source. Full blueprint first. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalHypersurface
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  SGPT.Foundations.Analysis.FirstPass.BlowupSequences HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaEmbeddedNativeMorphism BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

/-- Genuine ORIGINAL local Euclidean charts and actual hyperplane flattening;
no global component/model/dictionary or quotient certificate is a field. -/
def IsOriginalHypersurface (Y : SourceReducedComplexSpace) (E : Set Y.obj.left) : Prop :=
  IsClosed E ∧ IsConnected E ∧ ∀ x ∈ E,
    ∃ (k : ℕ) (U : Opens (ComplexModel (k+1)))
      (i : ChartedSpace.locallyRingedSpace 𝓘(ℂ, ComplexModel (k+1)) U ⟶ Y.obj.left),
      LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ Y.obj.hom = ambientPointMap (k+1) U ∧
      ∃ u : U, i.base u = x ∧
        RegularAtDim (n := k+1) ((fun v : U => i.base v) ⁻¹' E) u k

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

theorem native_pullback_of_original_hypersurface
    {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth) {E : Set Y.obj.left}
    (hE : IsOriginalHypersurface Y E) (c : ConnectedComponents Y.obj.left)
    (hEc : E ⊆ OriginalSmoothComponents.componentSet c) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) :
    ∃ k : ℕ, IsClosedConnectedSubmanifold n
      (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) ⁻¹' E) k ∧
      k + 1 = n ∧
      pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) ''
        (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) ⁻¹' E) = E := by
  let J := I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c
  let D := pointMap J ⁻¹' E
  let H : M ≃ₜ (HironakaG1NoncompactSmoothComponentModel.componentObject hY c).obj.left :=
    (Homeomorph.Set.univ M).symm.trans (isoHomeomorph I)
  have himage : pointMap J '' D = E := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hy
      let p : (HironakaG1NoncompactSmoothComponentModel.componentObject hY c).obj.left := ⟨y, hEc hy⟩
      refine ⟨H.symm p, ?_, ?_⟩
      · change (H (H.symm p)).val ∈ E
        rw [H.apply_symm_apply]
        exact hy
      · change (H (H.symm p)).val = y
        rw [H.apply_symm_apply]
  have hDclosed : IsClosed D := hE.1.preimage (continuous_pointMap J)
  let : ConnectedSpace E := isConnected_iff_connectedSpace.mp hE.2.1
  let L : E → M := fun y => H.symm ⟨y.val, hEc y.property⟩
  have hL : Continuous L := H.symm.continuous.comp
    (continuous_subtype_val.subtype_mk (fun y : E => hEc y.property))
  have hLpoint (y : E) : pointMap J (L y) = y.val := by
    let p : (HironakaG1NoncompactSmoothComponentModel.componentObject hY c).obj.left := ⟨y.val, hEc y.property⟩
    exact congrArg Subtype.val (H.apply_symm_apply p)
  have hrange : range L = D := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      change pointMap J (L y) ∈ E
      rw [hLpoint]
      exact y.property
    · intro hz
      refine ⟨⟨pointMap J z, hz⟩, ?_⟩
      apply H.injective
      apply Subtype.ext
      exact hLpoint ⟨pointMap J z, hz⟩
  have hDconn : IsConnected D := hrange ▸ isConnected_range hL
  obtain ⟨i, hi, hip, hpoint⟩ := component_native_chart hY c M I
  have hregular (z : M) (hz : z ∈ D) : ∃ k : ℕ, k+1=n ∧ RegularAtDim (n := n) D z k := by
    obtain ⟨k, U, j, hj, hjp, u, hu, hreg⟩ := hE.2.2 (pointMap J z) hz
    obtain ⟨hdim, hiff⟩ := PrimeNov16OriginalLocalChartComparison.dimension_and_regularity_of_original_charts
      i j hi hj hip hjp z u ((hpoint z).trans hu.symm) E k
    have hr : RegularAtDim (n := n) ((fun x : M => i.base x) ⁻¹' E) z k := hiff.mpr hreg
    have heq : ((fun x : M => i.base x) ⁻¹' E) = D := by
      ext x
      change i.base x ∈ E ↔ pointMap J x ∈ E
      rw [hpoint x]
      rfl
    exact ⟨k, hdim.symm, heq ▸ hr⟩
  obtain ⟨z, hz⟩ := hDconn.nonempty
  obtain ⟨k, hk, _hr⟩ := hregular z hz
  refine ⟨k, ⟨hDclosed, hDconn, ?_⟩, hk, himage⟩
  intro y hy
  obtain ⟨r, hr, hreg⟩ := hregular y hy
  have hsame : r = k := Nat.add_right_cancel (hr.trans hk.symm)
  exact hsame ▸ hreg

theorem exists_actual_native_hypersurface
    {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth) {E : Set Y.obj.left}
    (hE : IsOriginalHypersurface Y E) :
    ∃ (c : ConnectedComponents Y.obj.left) (n : ℕ) (M : CMfd n)
      (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) (k : ℕ),
      IsClosedConnectedSubmanifold n
        (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) ⁻¹' E) k ∧
      k+1=n ∧
      pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) ''
        (pointMap (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c) ⁻¹' E) = E := by
  obtain ⟨x, hx⟩ := hE.2.1.nonempty
  let c := ConnectedComponents.mk x
  have hEc : E ⊆ OriginalSmoothComponents.componentSet c := by
    rw [OriginalSmoothComponents.componentSet_eq_connectedComponent]
    exact hE.2.1.subset_connectedComponent hx
  obtain ⟨n, M, ⟨I⟩⟩ := HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hY c
  obtain ⟨k, hk, hc, himage⟩ := native_pullback_of_original_hypersurface hY hE c hEc M I
  exact ⟨c, n, M, I, k, hk, hc, himage⟩

end SGPT.PSH.PrimeNov16OriginalHypersurface
