import SGPT.PSH.PrimeNov16OriginalDominatedComponent
import SGPT.PSH.PrimeNov16OriginalModificationLocality

/-! Actual original domination derives the SAME full proper-bimeromorphic map.
Full blueprint first: `prime-nov16-original-prime-models.tex`. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalDominatedMap
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

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

theorem isProperBimeromorphic_of_actual_domination
    {X Y S : SourceReducedComplexSpace} (hS : S.IsSmooth) (hY : Y.IsSmooth)
    (H : S ⟶ X) (P : Y ⟶ X) (hH : IsProperBimeromorphic H) (hP : IsProperBimeromorphic P)
    (G : S ⟶ Y) (hGP : G ≫ P = H) : IsProperBimeromorphic G := by
  let : T2Space Y.obj.left := Y.property.1
  have hGc : Continuous (fun z : S.obj.left => (G.hom.left.base z : Y.obj.left)) := G.hom.left.base.hom.continuous
  have hPc : Continuous (fun y : Y.obj.left => (P.hom.left.base y : X.obj.left)) := P.hom.left.base.hom.continuous
  have hcompProper : IsProperMap (fun z : S.obj.left => P.hom.left.base (G.hom.left.base z)) :=
    Eq.mp (congrArg (fun F : S ⟶ X => IsProperMap F.hom.left.base) hGP.symm) hH.1
  have hGproper : IsProperMap G.hom.left.base := isProperMap_of_comp_of_t2 (X := S.obj.left) (Y := Y.obj.left) (Z := X.obj.left) hGc hPc hcompProper
  obtain ⟨E₀, E₁, hE₀, hE₁, hi₀, hi₁, ht₀, ht₁, pair, hpair⟩ :=
    PrimeNov16OriginalComponentPairing.exists_original_good_component_pairing hS hY H P hH hP
  choose n₀ M₀ hI₀ using fun c => HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hS c
  choose n₁ M₁ hI₁ using fun c => HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hY c
  let I₀ c := Classical.choice (hI₀ c)
  let I₁ c := Classical.choice (hI₁ c)
  let ι := ConnectedComponents Y.obj.left
  let A₀ (c : ι) := wholeModel (n := n₀ (pair c)) (M₀ (pair c))
  let A₁ (c : ι) := wholeModel (n := n₁ c) (M₁ c)
  let k (c : ι) : A₀ c ⟶ S := (I₀ (pair c)).hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hS (pair c)
  let j (c : ι) : A₁ c ⟶ Y := (I₁ c).hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY c
  have hk (c : ι) : LocallyRingedSpace.IsOpenImmersion (k c).hom.left := iso_component_open hS (pair c) _ (I₀ (pair c))
  have hj (c : ι) : LocallyRingedSpace.IsOpenImmersion (j c).hom.left := iso_component_open hY c _ (I₁ c)
  have hrk (c : ι) : range (k c).hom.left.base = OriginalSmoothComponents.componentSet (pair c) := iso_component_range hS (pair c) _ (I₀ (pair c))
  have hrj (c : ι) : range (j c).hom.left.base = OriginalSmoothComponents.componentSet c := iso_component_range hY c _ (I₁ c)
  have hkc : ∀ s : S.obj.left, ∃ (c : ι) (a : (A₀ c).obj.left), (k c).hom.left.base a = s := by
    intro z
    have hz : z ∈ range (k (pair.symm (ConnectedComponents.mk z))).hom.left.base := by
      rw [hrk, pair.apply_symm_apply]
      rfl
    exact ⟨_, hz⟩
  have hjc : ∀ y : Y.obj.left, ∃ (c : ι) (a : (A₁ c).obj.left), (j c).hom.left.base a = y := by
    intro y
    have hy : y ∈ range (j (ConnectedComponents.mk y)).hom.left.base := by rw [hrj]; rfl
    exact ⟨_, hy⟩
  have hjd : Pairwise (fun c d : ι => Disjoint (range (j c).hom.left.base) (range (j d).hom.left.base)) := by
    intro c d hcd
    rw [hrj, hrj]
    exact OriginalSmoothComponents.componentSet_pairwise_disjoint hcd
  have hlocal (c : ι) : ∃ f : A₀ c ⟶ A₁ c,
      IsProperBimeromorphic f ∧ f ≫ j c = k c ≫ G := by
    obtain ⟨_hdim, f, hf, hfac⟩ :=
      PrimeNov16OriginalDominatedComponent.exists_actual_dominated_native_component_modification
        hS hY H P hH G hGP E₀ E₁ hE₀ hE₁ hi₀ hi₁ ht₀ ht₁ (pair c) c (hpair c)
        (M₀ (pair c)) (M₁ c) (I₀ (pair c)) (I₁ c)
    exact ⟨f, hf, hfac.trans (Category.assoc _ _ _).symm⟩
  choose f hf hfac using hlocal
  exact PrimeNov16OriginalModificationLocality.isProperBimeromorphic_of_actual_covers
    G hGproper j k f hj hk hjc hkc hjd (fun c => (hfac c).symm) hf

end SGPT.PSH.PrimeNov16OriginalDominatedMap
