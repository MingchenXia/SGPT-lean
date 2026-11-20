import SGPT.PSH.PrimeNov16OriginalPairedComponents
import SGPT.PSH.PrimeNov16DisjointBimeromorphic
import SGPT.Unibranch.HironakaG1NativeIsoOverDisjointCover

/-! Actual arbitrary original smooth-source common resolution.
Full blueprint first; no compactness, global dimension or connectedness premise. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace SGPT.PSH.PrimeNov16OriginalSmoothCommonResolution
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
  HironakaResolutionSpaceComplex HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  AnalyticModificationLocalDiscrepancy BlowupTowers
open SGPT.Unibranch SourceReducedComplexSpace OriginalNativeModification OriginalSmoothSourceAnalytic

private theorem analytic_union {X : SourceReducedComplexSpace} {A B : Set X.obj.left}
    (hA : X.IsAnalyticSubset A) (hB : X.IsAnalyticSubset B) : X.IsAnalyticSubset (A ∪ B) := by
  intro x
  let e := LocalEmbedding.ofPoint X x
  refine ⟨e, LocalEmbedding.mem_range_ofPoint X x,
    (Subtype.val '' (e.toPoint ⁻¹' A)) ∪ (Subtype.val '' (e.toPoint ⁻¹' B)),
    ConstantRankImage.IsComplexAnalyticSubset.union
      (hA.analytic_image_localEmbedding e) (hB.analytic_image_localEmbedding e), ?_⟩
  rw [preimage_union, preimage_union, preimage_image_eq _ Subtype.val_injective,
    preimage_image_eq _ Subtype.val_injective]

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

theorem exists_actual_original_smooth_common_resolution
    {X Y₀ Y₁ : SourceReducedComplexSpace} (hY₀ : Y₀.IsSmooth) (hY₁ : Y₁.IsSmooth)
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
    ∃ S : SourceReducedComplexSpace, S.IsSmooth ∧ ∃ (G₀ : S ⟶ Y₀) (G₁ : S ⟶ Y₁),
      IsProperBimeromorphic G₀ ∧ IsProperBimeromorphic G₁ ∧
      G₀ ≫ F₀ = G₁ ≫ F₁ ∧ IsResolution (G₁ ≫ F₁) := by
  obtain ⟨E₀, E₁, hE₀, hE₁, hi₀, hi₁, ht₀, ht₁, pair, hpair⟩ :=
    PrimeNov16OriginalComponentPairing.exists_original_good_component_pairing hY₀ hY₁ F₀ F₁ hF₀ hF₁
  let B := E₀ ∪ E₁
  have hBa : X.IsAnalyticSubset B := analytic_union hE₀ hE₁
  have hBc : IsClosed B := hBa.isClosed
  have hBt : interior B = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨y, rfl⟩ := hF₁.surjective x
    have hy := preimage_interior_subset_interior_preimage F₁.hom.left.base.hom.continuous hx
    rw [ht₁] at hy
    exact hy
  choose n₀ M₀ hI₀ using fun c => HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hY₀ c
  choose n₁ M₁ hI₁ using fun c => HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hY₁ c
  let I₀ c := Classical.choice (hI₀ c)
  let I₁ c := Classical.choice (hI₁ c)
  let ι := ConnectedComponents Y₁.obj.left
  let A₀ (c : ι) := wholeModel (n := n₀ (pair c)) (M₀ (pair c))
  let A₁ (c : ι) := wholeModel (n := n₁ c) (M₁ c)
  let j₀ (c : ι) : A₀ c ⟶ Y₀ := (I₀ (pair c)).hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₀ (pair c)
  let j₁ (c : ι) : A₁ c ⟶ Y₁ := (I₁ c).hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hY₁ c
  have hj₀ (c : ι) : LocallyRingedSpace.IsOpenImmersion (j₀ c).hom.left := iso_component_open hY₀ (pair c) _ (I₀ (pair c))
  have hj₁ (c : ι) : LocallyRingedSpace.IsOpenImmersion (j₁ c).hom.left := iso_component_open hY₁ c _ (I₁ c)
  have hr₀ (c : ι) : range (j₀ c).hom.left.base = OriginalSmoothComponents.componentSet (pair c) := iso_component_range hY₀ (pair c) _ (I₀ (pair c))
  have hr₁ (c : ι) : range (j₁ c).hom.left.base = OriginalSmoothComponents.componentSet c := iso_component_range hY₁ c _ (I₁ c)
  have hc₀ : ∀ y : Y₀.obj.left, ∃ (c : ι) (a : (A₀ c).obj.left), (j₀ c).hom.left.base a = y := by
    intro y
    have hy : y ∈ range (j₀ (pair.symm (ConnectedComponents.mk y))).hom.left.base := by
      rw [hr₀, pair.apply_symm_apply]
      rfl
    exact ⟨_, hy⟩
  have hc₁ : ∀ y : Y₁.obj.left, ∃ (c : ι) (a : (A₁ c).obj.left), (j₁ c).hom.left.base a = y := by
    intro y
    have hy : y ∈ range (j₁ (ConnectedComponents.mk y)).hom.left.base := by rw [hr₁]; rfl
    exact ⟨_, hy⟩
  have hd₀ : Pairwise (fun c d : ι => Disjoint (range (j₀ c).hom.left.base) (range (j₀ d).hom.left.base)) := by
    intro c d hcd
    rw [hr₀, hr₀]
    exact OriginalSmoothComponents.componentSet_pairwise_disjoint (fun he => hcd (pair.injective he))
  have hd₁ : Pairwise (fun c d : ι => Disjoint (range (j₁ c).hom.left.base) (range (j₁ d).hom.left.base)) := by
    intro c d hcd
    rw [hr₁, hr₁]
    exact OriginalSmoothComponents.componentSet_pairwise_disjoint hcd
  have hlocal (c : ι) : ∃ Z : SourceReducedComplexSpace, Z.IsSmooth ∧
      ∃ (g₀ : Z ⟶ A₀ c) (g₁ : Z ⟶ A₁ c), IsProperBimeromorphic g₀ ∧ IsProperBimeromorphic g₁ ∧
        g₀ ≫ (j₀ c ≫ F₀) = g₁ ≫ (j₁ c ≫ F₁) ∧
        IsIsoOver g₀ ((j₀ c ≫ F₀).hom.left.base ⁻¹' Bᶜ) ∧
        IsIsoOver g₁ ((j₁ c ≫ F₁).hom.left.base ⁻¹' Bᶜ) ∧
        interior ((g₁ ≫ (j₁ c ≫ F₁)).hom.left.base ⁻¹' B) = ∅ := by
    exact PrimeNov16OriginalPairedComponents.exists_actual_paired_component_common_maps
      hY₀ hY₁ F₀ F₁ hF₀.1 hF₁.1 E₀ E₁ hE₀ hE₁ hi₀ hi₁ ht₀ ht₁ (pair c) c (hpair c)
      (M₀ (pair c)) (M₁ c) (I₀ (pair c)) (I₁ c)
  choose Z hZ g₀ g₁ hg₀ hg₁ hsquare _hiso₀ hiso₁ hthin using hlocal
  let S := HironakaG1NativeDisjointCoproduct.coproduct Z
  let k (c : ι) := HironakaG1NativeDisjointCoproduct.inclusion Z c
  let G₀ : S ⟶ Y₀ := HironakaG1NativeDisjointCoproduct.desc Z (fun c => g₀ c ≫ j₀ c)
  let G₁ : S ⟶ Y₁ := HironakaG1NativeDisjointCoproduct.desc Z (fun c => g₁ c ≫ j₁ c)
  have hG₀ : IsProperBimeromorphic G₀ := PrimeNov16DisjointBimeromorphic.isProperBimeromorphic_desc j₀ hj₀ hc₀ hd₀ g₀ hg₀
  have hG₁ : IsProperBimeromorphic G₁ := PrimeNov16DisjointBimeromorphic.isProperBimeromorphic_desc j₁ hj₁ hc₁ hd₁ g₁ hg₁
  have hsq₀ (c : ι) : k c ≫ G₀ = g₀ c ≫ j₀ c := HironakaG1NativeDisjointCoproduct.inclusion_desc Z _ c
  have hsq₁ (c : ι) : k c ≫ G₁ = g₁ c ≫ j₁ c := HironakaG1NativeDisjointCoproduct.inclusion_desc Z _ c
  have hfull : G₀ ≫ F₀ = G₁ ≫ F₁ := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext
    intro c
    rw [← Category.assoc, hsq₀, Category.assoc, hsquare c, ← Category.assoc, ← hsq₁, Category.assoc]
  have hGiso : IsIsoOver G₁ (F₁.hom.left.base ⁻¹' Bᶜ) :=
    HironakaG1NativeIsoOverDisjointCover.isIsoOver_of_disjoint_cover G₁ j₁ k g₁ hj₁
      (fun c => HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion Z c) hc₁
      (HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective Z) hd₁ hsq₁ _
      (hBc.isOpen_compl.preimage F₁.hom.left.base.hom.continuous) hiso₁
  have hsourceThin : interior ((G₁ ≫ F₁).hom.left.base ⁻¹' B) = ∅ := by
    apply OriginalAnalyticCover.interior_eq_empty_of_openImmersion_cover k
      (fun c => HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion Z c)
      (HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective Z)
    intro c
    have heq : k c ≫ (G₁ ≫ F₁) = g₁ c ≫ (j₁ c ≫ F₁) := by
      rw [← Category.assoc, hsq₁, Category.assoc]
    exact (congrArg (fun H : Z c ⟶ X => interior (H.hom.left.base ⁻¹' B)) heq).trans (hthin c)
  have hS : S.IsSmooth := HironakaG1NativeDisjointCoproduct.isSmooth_coproduct Z hZ
  have hres : IsResolution (G₁ ≫ F₁) :=
    ⟨hS, hF₁.1.comp hG₁.1, B, hBa, hBt, hsourceThin, hi₁.comp hGiso⟩
  exact ⟨S, hS, G₀, G₁, hG₀, hG₁, hfull, hres⟩

end SGPT.PSH.PrimeNov16OriginalSmoothCommonResolution
