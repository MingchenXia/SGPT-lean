import SGPT.PSH.PrimeNov16OriginalFibreDictionary
import SGPT.PSH.PrimeNov16OriginalModificationLocality
import SGPT.Foundations.Analysis.Pending.AnalyticModificationComposition

/-! SAME actual original smooth-source composition; all native factors produced.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalSmoothComposition
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
  AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalProperBimeromorphicNative

private theorem iso_component_open {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) :
    LocallyRingedSpace.IsOpenImmersion
      (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c).hom.left := by
  have hI : LocallyRingedSpace.IsOpenImmersion I.hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (SourceReducedComplexSpace.isoLeft I).hom
    infer_instance
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ I.hom.hom.left hI _
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion_isOpenImmersion hY c)

private theorem iso_component_range {Y : SourceReducedComplexSpace} (hY : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) {n : ℕ} (M : CMfd n)
    (I : wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hY c) :
    range (I.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c).hom.left.base =
      OriginalSmoothComponents.componentSet c :=
  (range_iso_hom_comp_base (SourceReducedComplexSpace.isoLeft I)
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c).hom.left).trans
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion_range hY c)

private theorem native_comp_pb {n : ℕ} (A B C : CMfd n)
    (f : wholeModel (n := n) A ⟶ wholeModel (n := n) B)
    (g : wholeModel (n := n) B ⟶ wholeModel (n := n) C)
    (hf : IsProperBimeromorphic f) (hg : IsProperBimeromorphic g) : IsProperBimeromorphic (f ≫ g) := by
  have hfm := isAnalyticModification_of_isProperBimeromorphic f hf
  have hgm := isAnalyticModification_of_isProperBimeromorphic g hg
  have hcomp := AnalyticModificationComposition.isAnalyticModification_comp hgm hfm
  have hfull : nativeMorphism hcomp.1 = f ≫ g :=
    SourceReducedComplexSpace.morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
  exact hfull ▸ nativeMorphism_isProperBimeromorphic hcomp

theorem isProperBimeromorphic_comp
    {S Y Z : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth) (hZ : Z.IsSmooth)
    (F : S ⟶ Y) (G : Y ⟶ Z) (hF : IsProperBimeromorphic F) (hG : IsProperBimeromorphic G) :
    IsProperBimeromorphic (F ≫ G) := by
  choose n M hI using fun c => HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hZ c
  let I c := Classical.choice (hI c)
  let ι := ConnectedComponents Z.obj.left
  choose cY N IY g hg hsqg using fun c : ι =>
    PrimeNov16OriginalMarkedComponentLift.exists_actual_marked_component_lift hY hZ G hG c (M c) (I c)
  choose cS P IS f hf hsqf using fun c : ι =>
    PrimeNov16OriginalMarkedComponentLift.exists_actual_marked_component_lift hS hY F hF (cY c) (N c) (IY c)
  let A (c : ι) := wholeModel (n := n c) (M c)
  let B (c : ι) := wholeModel (n := n c) (N c)
  let C (c : ι) := wholeModel (n := n c) (P c)
  let j (c : ι) : A c ⟶ Z := (I c).hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hZ c
  let m (c : ι) : B c ⟶ Y := (IY c).hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY (cY c)
  let k (c : ι) : C c ⟶ S := (IS c).hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS (cS c)
  have hj (c : ι) : LocallyRingedSpace.IsOpenImmersion (j c).hom.left := iso_component_open hZ c _ (I c)
  have hk (c : ι) : LocallyRingedSpace.IsOpenImmersion (k c).hom.left := iso_component_open hS (cS c) _ (IS c)
  have hrj (c : ι) : range (j c).hom.left.base = OriginalSmoothComponents.componentSet c := iso_component_range hZ c _ (I c)
  have hrk (c : ι) : range (k c).hom.left.base = OriginalSmoothComponents.componentSet (cS c) := iso_component_range hS (cS c) _ (IS c)
  have hpreG (c : ι) : G.hom.left.base ⁻¹' OriginalSmoothComponents.componentSet c =
      OriginalSmoothComponents.componentSet (cY c) := by
    have hmod := isAnalyticModification_of_isProperBimeromorphic (g c) (hg c)
    have hfull : nativeMorphism hmod.1 = g c := nativeMorphism_nativePointMap (g c)
    apply PrimeNov16OriginalFibreDictionary.component_preimage_eq_of_actual_native_lift
      hY hZ G hG (cY c) c (N c) (M c) (IY c) (I c) (nativePointMap (g c)) hmod
    rw [hfull]
    exact hsqg c
  have hpreF (c : ι) : F.hom.left.base ⁻¹' OriginalSmoothComponents.componentSet (cY c) =
      OriginalSmoothComponents.componentSet (cS c) := by
    have hmod := isAnalyticModification_of_isProperBimeromorphic (f c) (hf c)
    have hfull : nativeMorphism hmod.1 = f c := nativeMorphism_nativePointMap (f c)
    apply PrimeNov16OriginalFibreDictionary.component_preimage_eq_of_actual_native_lift
      hS hY F hF (cS c) (cY c) (P c) (N c) (IS c) (IY c) (nativePointMap (f c)) hmod
    rw [hfull]
    exact hsqf c
  have hjc : ∀ z : Z.obj.left, ∃ (c : ι) (a : (A c).obj.left), (j c).hom.left.base a = z := by
    intro z
    have hz : z ∈ range (j (ConnectedComponents.mk z)).hom.left.base := by rw [hrj]; rfl
    exact ⟨_, hz⟩
  have hkc : ∀ s : S.obj.left, ∃ (c : ι) (a : (C c).obj.left), (k c).hom.left.base a = s := by
    intro s
    let c := ConnectedComponents.mk ((F ≫ G).hom.left.base s)
    have ht : (F ≫ G).hom.left.base s ∈ OriginalSmoothComponents.componentSet c := rfl
    have hm : F.hom.left.base s ∈ OriginalSmoothComponents.componentSet (cY c) := hpreG c ▸ ht
    have hs : s ∈ OriginalSmoothComponents.componentSet (cS c) := hpreF c ▸ hm
    have hr : s ∈ range (k c).hom.left.base := (hrk c).symm ▸ hs
    exact ⟨c, hr⟩
  have hjd : Pairwise (fun c d : ι => Disjoint (range (j c).hom.left.base) (range (j d).hom.left.base)) := by
    intro c d hcd
    rw [hrj, hrj]
    exact OriginalSmoothComponents.componentSet_pairwise_disjoint hcd
  have hsq (c : ι) : k c ≫ (F ≫ G) = (f c ≫ g c) ≫ j c := by
    have hfq : f c ≫ m c = k c ≫ F := (hsqf c).trans (Category.assoc _ _ _).symm
    have hgq : g c ≫ j c = m c ≫ G := (hsqg c).trans (Category.assoc _ _ _).symm
    calc
      _ = (k c ≫ F) ≫ G := (Category.assoc _ _ _).symm
      _ = (f c ≫ m c) ≫ G := congrArg (fun q => q ≫ G) hfq.symm
      _ = f c ≫ (m c ≫ G) := Category.assoc _ _ _
      _ = f c ≫ (g c ≫ j c) := congrArg (fun q => f c ≫ q) hgq.symm
      _ = _ := (Category.assoc _ _ _).symm
  exact PrimeNov16OriginalModificationLocality.isProperBimeromorphic_of_actual_covers
    (F ≫ G) (hG.1.comp hF.1) j k (fun c => f c ≫ g c) hj hk hjc hkc hjd hsq
    (fun c => native_comp_pb (P c) (N c) (M c) (f c) (g c) (hf c) (hg c))

end SGPT.PSH.PrimeNov16OriginalSmoothComposition
