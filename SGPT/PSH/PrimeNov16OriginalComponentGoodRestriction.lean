import SGPT.PSH.PrimeNov16OriginalComponentPairing
import SGPT.Unibranch.OriginalCommonResolution

/-! Actual full original native component-good restriction.
Blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalComponentGoodRestriction
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceOpenRestriction
  HironakaReducedComplexAnalyticSpaces HironakaEmbeddedNativeMorphism BlowupTowers
private theorem openImmersion_lift {A B T : LocallyRingedSpace}
    (f : A ⟶ T) (g : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion f] [LocallyRingedSpace.IsOpenImmersion g]
    (hr : range g.base ⊆ range f.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift f g hr) := by
  have : IsIso (pullback.snd f g) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset f g hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance


theorem native_component_good_restriction
    {X Y : SourceReducedComplexSpace} (hY : Y.IsSmooth) (F : Y ⟶ X)
    (B : Set X.obj.left) (hBc : IsClosed B) (hiso : IsIsoOver F Bᶜ)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (E : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) :
    let F' := E.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c ≫ F
    LocallyRingedSpace.IsOpenImmersion (OriginalCommonResolution.restrictedOriginalMorphism F' B hBc) ∧
      range (OriginalCommonResolution.restrictedOriginalMorphism F' B hBc).base =
        PrimeNov16OriginalComponentPairing.componentGoodImage F B c := by
  let C := HironakaG1NoncompactSmoothComponentModel.componentObject hY c
  let j := HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c
  let F' := E.hom ≫ j ≫ F
  let O := OriginalCommonResolution.goodOpen F' B hBc
  let R := OriginalCommonResolution.restrictedOriginalMorphism F' B hBc
  let N := actualOpenSubspaceMap (n := n) (univ : Set M) O
  let E' := SourceReducedComplexSpace.isoLeft E
  have hEI : LocallyRingedSpace.IsOpenImmersion E.hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (SourceReducedComplexSpace.isoLeft E).hom
    infer_instance
  let J := (N ≫ E'.hom) ≫ j.hom.left
  have hJ : LocallyRingedSpace.IsOpenImmersion J := by
    have hN : LocallyRingedSpace.IsOpenImmersion N := by dsimp only [N]; infer_instance
    have hj : LocallyRingedSpace.IsOpenImmersion j.hom.left :=
      HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion hY c
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (N ≫ E'.hom)
      (@LocallyRingedSpace.IsOpenImmersion.comp _ _ _ N hN E'.hom hEI) j.hom.left hj
  obtain ⟨V, I, hI, hIr, hIF, _hIFr⟩ := hiso
  have hr : range J.base ⊆ range I.base := by
    rintro _ ⟨v, rfl⟩
    rw [hIr]
    exact v.val.property
  let := hI
  let := hJ
  let L := LocallyRingedSpace.IsOpenImmersion.lift I J hr
  have hfac : L ≫ I = J := LocallyRingedSpace.IsOpenImmersion.lift_fac I J hr
  have hL : LocallyRingedSpace.IsOpenImmersion L := openImmersion_lift I J hr
  have hR : L ≫ (I ≫ F.hom.left) = R := by
    rw [← Category.assoc, hfac]
    simp only [J, R, F', OriginalCommonResolution.restrictedOriginalMorphism, Category.assoc]
    rfl
  constructor
  · change LocallyRingedSpace.IsOpenImmersion R
    rw [← hR]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ L hL (I ≫ F.hom.left) hIF
  · let H : M ≃ₜ C.obj.left := (Homeomorph.Set.univ M).symm.trans (isoHomeomorph E)
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨j.hom.left.base (H v.val.val), ⟨?_, v.val.property⟩, rfl⟩
      exact (H v.val.val).property
    · rintro ⟨y, ⟨hyc, hyg⟩, rfl⟩
      let p : C.obj.left := ⟨y, hyc⟩
      let x := H.symm p
      have hx : H x = p := H.apply_symm_apply p
      have hgood : pointMap F' x ∈ Bᶜ := by
        change F.hom.left.base (j.hom.left.base (H x)) ∈ Bᶜ
        rw [hx]
        exact hyg
      let v : O := ⟨x, hgood⟩
      refine ⟨⟨v, mem_univ v⟩, ?_⟩
      change F.hom.left.base (j.hom.left.base (H x)) = F.hom.left.base y
      rw [hx]
      rfl

end SGPT.PSH.PrimeNov16OriginalComponentGoodRestriction
