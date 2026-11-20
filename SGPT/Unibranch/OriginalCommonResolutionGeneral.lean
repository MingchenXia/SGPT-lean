import SGPT.Unibranch.OriginalSmoothComponentPairing
import SGPT.Unibranch.OriginalFiniteBimeromorphic

/-!
# Common resolutions over an arbitrary ORIGINAL compact complex space

Only ORIGINAL compact base and actual ORIGINAL resolutions (or original
smooth sources with ORIGINAL proper-bimeromorphic maps) enter. All source
compactness, finite components, native representations/dimensions, actual
paired common models, finite original object and global PB maps are derived.
Empty/disconnected/nonpure sources and ENTIRE original squares are retained.
Blueprint FIRST: `original-common-resolution-general.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology

namespace SGPT.Unibranch.OriginalCommonResolutionGeneral

open SourceReducedComplexSpace

noncomputable section

/-- Actual ORIGINAL compact base and ORIGINAL smooth PB source maps
internally construct a compact ORIGINAL smooth common model, with no
connectedness, purity, native representation or component packet input. -/
theorem exists_common_model_of_isProperBimeromorphic
    {X Y₀ Y₁ : SourceReducedComplexSpace} [CompactSpace X.obj.left]
    (hY₀ : Y₀.IsSmooth) (hY₁ : Y₁.IsSmooth)
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X)
    (hF₀ : IsProperBimeromorphic F₀) (hF₁ : IsProperBimeromorphic F₁) :
    ∃ (Z : SourceReducedComplexSpace) (_ : CompactSpace Z.obj.left),
      Z.IsSmooth ∧ ∃ (G₀ : Z ⟶ Y₀) (G₁ : Z ⟶ Y₁),
        IsProperBimeromorphic G₀ ∧ IsProperBimeromorphic G₁ ∧ G₀ ≫ F₀ = G₁ ≫ F₁ := by
  have hc₀ : IsCompact (univ : Set Y₀.obj.left) := by
    simpa only [preimage_univ] using hF₀.1.isCompact_preimage
      (isCompact_univ : IsCompact (univ : Set X.obj.left))
  have hc₁ : IsCompact (univ : Set Y₁.obj.left) := by
    simpa only [preimage_univ] using hF₁.1.isCompact_preimage
      (isCompact_univ : IsCompact (univ : Set X.obj.left))
  have : CompactSpace Y₀.obj.left := isCompact_univ_iff.mp hc₀
  have : CompactSpace Y₁.obj.left := isCompact_univ_iff.mp hc₁
  have : Finite (ConnectedComponents Y₁.obj.left) :=
    OriginalSmoothComponents.finite_connectedComponents hY₁
  obtain ⟨pair, hpairs⟩ :=
    OriginalSmoothComponentPairing.exists_original_paired_common_models hY₀ hY₁ F₀ F₁ hF₀ hF₁
  choose C hCc hCs g₀ g₁ hg₀ hg₁ hsquare using hpairs
  have : ∀ c, CompactSpace (C c).obj.left := hCc
  let W := OriginalFiniteCoproduct.coproduct C
  let j₀ (c : ConnectedComponents Y₁.obj.left) :
      OriginalSmoothComponents.componentObject hY₀ (pair c) ⟶ Y₀ :=
    OriginalSmoothComponents.componentInclusion hY₀ (pair c)
  let j₁ (c : ConnectedComponents Y₁.obj.left) :
      OriginalSmoothComponents.componentObject hY₁ c ⟶ Y₁ :=
    OriginalSmoothComponents.componentInclusion hY₁ c
  have hj₀ : ∀ c, LocallyRingedSpace.IsOpenImmersion (j₀ c).hom.left :=
    fun c => OriginalSmoothComponents.componentInclusion_isOpenImmersion hY₀ (pair c)
  have hj₁ : ∀ c, LocallyRingedSpace.IsOpenImmersion (j₁ c).hom.left :=
    OriginalSmoothComponents.componentInclusion_isOpenImmersion hY₁
  have hcover₀ : ∀ y : Y₀.obj.left, ∃ c a, (j₀ c).hom.left.base a = y := by
    intro y
    obtain ⟨c₀, a, ha⟩ := OriginalSmoothComponents.componentInclusion_jointly_surjective hY₀ y
    obtain ⟨c, hc⟩ := pair.surjective c₀
    subst c₀
    exact ⟨c, a, ha⟩
  have hcover₁ : ∀ y : Y₁.obj.left, ∃ c a, (j₁ c).hom.left.base a = y :=
    OriginalSmoothComponents.componentInclusion_jointly_surjective hY₁
  have hdisj₀ : Pairwise (fun c d =>
      Disjoint (range (j₀ c).hom.left.base) (range (j₀ d).hom.left.base)) := by
    intro c d hcd
    dsimp only [j₀]
    rw [OriginalSmoothComponents.componentInclusion_range,
      OriginalSmoothComponents.componentInclusion_range]
    exact OriginalSmoothComponents.componentSet_pairwise_disjoint (X := Y₀)
      (fun h => hcd (pair.injective h))
  have hdisj₁ : Pairwise (fun c d =>
      Disjoint (range (j₁ c).hom.left.base) (range (j₁ d).hom.left.base)) := by
    intro c d hcd
    dsimp only [j₁]
    rw [OriginalSmoothComponents.componentInclusion_range,
      OriginalSmoothComponents.componentInclusion_range]
    exact OriginalSmoothComponents.componentSet_pairwise_disjoint (X := Y₁) hcd
  let G₀ : W ⟶ Y₀ := OriginalFiniteCoproduct.desc C (fun c => g₀ c ≫ j₀ c)
  let G₁ : W ⟶ Y₁ := OriginalFiniteCoproduct.desc C (fun c => g₁ c ≫ j₁ c)
  have hG₀ : IsProperBimeromorphic G₀ :=
    OriginalFiniteBimeromorphic.isProperBimeromorphic_desc j₀ hj₀ hcover₀ hdisj₀ g₀ hg₀
  have hG₁ : IsProperBimeromorphic G₁ :=
    OriginalFiniteBimeromorphic.isProperBimeromorphic_desc j₁ hj₁ hcover₁ hdisj₁ g₁ hg₁
  refine ⟨W, OriginalFiniteCoproduct.compactSpace_coproduct C,
    OriginalFiniteCoproduct.isSmooth_coproduct C hCs, G₀, G₁, hG₀, hG₁, ?_⟩
  apply OriginalFiniteCoproduct.hom_ext C
  intro c
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun H : C c ⟶ Y₀ => H ≫ F₀)
      (OriginalFiniteCoproduct.inclusion_desc C (fun c => g₀ c ≫ j₀ c) c)).trans
      ((hsquare c).trans
        ((congrArg (fun H : C c ⟶ Y₁ => H ≫ F₁)
          (OriginalFiniteCoproduct.inclusion_desc C (fun c => g₁ c ≫ j₁ c) c).symm).trans
          (Category.assoc _ _ _))))

/-- The book-scope ORIGINAL common resolution: only CompactX and actual
given ORIGINAL IsResolution Fi enter, with all source properties derived. -/
theorem exists_common_resolution
    {X Y₀ Y₁ : SourceReducedComplexSpace} [CompactSpace X.obj.left]
    (F₀ : Y₀ ⟶ X) (F₁ : Y₁ ⟶ X) (hF₀ : IsResolution F₀) (hF₁ : IsResolution F₁) :
    ∃ (Z : SourceReducedComplexSpace) (_ : CompactSpace Z.obj.left)
      (G₀ : Z ⟶ Y₀) (G₁ : Z ⟶ Y₁),
      IsResolution G₀ ∧ IsResolution G₁ ∧ G₀ ≫ F₀ = G₁ ≫ F₁ := by
  obtain ⟨Z, hZc, hZs, G₀, G₁, hG₀, hG₁, hsquare⟩ :=
    exists_common_model_of_isProperBimeromorphic hF₀.1 hF₁.1 F₀ F₁ hF₀.2 hF₁.2
  exact ⟨Z, hZc, G₀, G₁, ⟨hZs, hG₀⟩, ⟨hZs, hG₁⟩, hsquare⟩

end

end SGPT.Unibranch.OriginalCommonResolutionGeneral
