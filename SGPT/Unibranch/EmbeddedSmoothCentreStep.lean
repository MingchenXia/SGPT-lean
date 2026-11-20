import SGPT.Unibranch.EmbeddedSmoothCentreRange
import SGPT.Unibranch.RIsoAModification
import SGPT.Unibranch.HironakaG11NativeTowerRepresentation
import SGPT.Unibranch.SourceMorphismExt
import SGPT.Foundations.Analysis.Pending.ResolutionDriver

/-! An actual intrinsic smooth-center blowup is the strict transform in an ambient blowup. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Unibranch

open CategoryTheory Set TopologicalSpace AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves SGPT.Foundations.Analysis.Pending
open SourceReducedComplexSpace SmoothCentreModification EmbeddedBlowup OriginalNativeModification
open HironakaIntrinsicReducedCentreIdealSheaf BlowupTowers

/-- The given intrinsic step over the reduced closed analytic subspace is identified over
that subspace with the strict transform in the blowup of the actual ambient center. -/
private theorem exists_ambient_strictTransform_iso_of_centreIdeal
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)
    {S Y : SourceReducedComplexSpace} (i : S ⟶ ofClosedAnalytic W hW)
    (p : Y ⟶ ofClosedAnalytic W hW) (hS : S.IsSmooth)
    (hi : Topology.IsClosedEmbedding i.hom.left.base)
    (hstalk : ∀ s : S.obj.left, Function.Surjective (i.hom.left.stalkMap s))
    (hthin : interior (range i.hom.left.base) = ∅)
    (hIdeal : IsIdealBlowup p
      (intrinsicReducedCentreIdealModule (ofClosedAnalytic W hW).obj.left (range i.hom.left.base))
      (intrinsicReducedCentreIdealInclusion (ofClosedAnalytic W hW).obj.left (range i.hom.left.base))) :
    ∃ (Z : CMfd.{0} n) (π : Z → M)
      (hπ : IsBlowupAlong n ((Subtype.val : W → M) '' range i.hom.left.base) π),
      ∃ e : Y ≅ ofClosedAnalytic (strictTransform n π W)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ hW), e.hom ≫ strictTransformMorphism hπ hW = p := by
  let C : Set M := (Subtype.val : W → M) '' range i.hom.left.base
  have htrace : (Subtype.val : W → M) ⁻¹' C = range i.hom.left.base :=
    Subtype.val_injective.preimage_image _
  have hCW : C ⊆ W := by
    rintro _ ⟨w, _, rfl⟩
    exact w.property
  have hd : Dense (range i.hom.left.base)ᶜ :=
    interior_eq_empty_iff_dense_compl.mp hthin
  have himage : (Subtype.val : W → M) '' (range i.hom.left.base)ᶜ = W \ C := by
    rw [← htrace]
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property, hw⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hdense : W ⊆ closure (W \ C) := by
    intro x hx
    have hw : (⟨x, hx⟩ : W) ∈ closure ((range i.hom.left.base)ᶜ) := hd ⟨x, hx⟩
    rw [closure_subtype, himage] at hw
    exact hw
  have hCthin : interior C = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxcl := hdense (hCW (interior_subset hx))
    have hdif : W \ C ⊆ (interior C)ᶜ := by
      intro y hy hyin
      exact hy.2 (interior_subset hyin)
    exact closure_minimal hdif isOpen_interior.isClosed_compl hxcl hx
  have hCsm : IsClosedSubmanifold n C :=
    isClosedSubmanifold_ambientImage_of_smoothCentre hW i hS hi hstalk
  obtain ⟨Z, π, hπ⟩ := ResolutionDriver.exists_blowup (Y := CMfd.of (n := n) M) C hCsm hCthin
  have hstrict := strictTransformMorphism_isIdealBlowup hπ hW hCW hdense
  rw [htrace] at hstrict
  obtain ⟨e, he, _⟩ := RIsoAModification.isIdealBlowup_exists_unique_iso hIdeal hstrict
  exact ⟨Z, π, hπ, e, he⟩

/-- The strict transform realizes the given intrinsic smooth-center step over the same space. -/
theorem exists_ambient_strictTransform_iso_of_smoothCentreBlowup
    {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    [IsComplexManifold n M] {W : Set M} (hW : IsComplexAnalyticSubset (n := n) W)
    {S Y : SourceReducedComplexSpace} (i : S ⟶ ofClosedAnalytic W hW)
    (p : Y ⟶ ofClosedAnalytic W hW) (hp : IsSmoothCentreBlowup p i) :
    ∃ (Z : CMfd.{0} n) (π : Z → M)
      (hπ : IsBlowupAlong n ((Subtype.val : W → M) '' range i.hom.left.base) π),
      ∃ e : Y ≅ ofClosedAnalytic (strictTransform n π W)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ hW), e.hom ≫ strictTransformMorphism hπ hW = p := by
  obtain ⟨hS, hi, hstalk, _, hthin, hIdeal, _⟩ := hp
  exact exists_ambient_strictTransform_iso_of_centreIdeal hW i p hS hi hstalk hthin hIdeal

/-- A certified closed reduced embedding extends over an actual smooth-center blowup step.
The equality is in the native category, including the full sheaf map. -/
theorem exists_certified_ambientStep_of_isSmoothCentreStep
    {n : ℕ} (A : CMfd.{0} n) {X Y : SourceReducedComplexSpace}
    (j : X ⟶ wholeModel (n := n) A)
    (hj : ∃ (W : Set A) (hW : IsComplexAnalyticSubset (n := n) W)
      (a : X ≅ ofClosedAnalytic W hW),
      a.hom ≫ OriginalClosedSubspaceFactorization.inclusion hW
        isComplexAnalyticSubset_univ (Set.subset_univ W) = j)
    (p : Y ⟶ X) (hp : IsSmoothCentreStep p) :
    ∃ (A' : CMfd.{0} n) (C : Set A) (β : A' → A) (hβ : IsBlowupAlong n C β)
      (j' : Y ⟶ wholeModel (n := n) A'),
      (∃ (W' : Set A') (hW' : IsComplexAnalyticSubset (n := n) W')
        (a' : Y ≅ ofClosedAnalytic W' hW'),
        a'.hom ≫ OriginalClosedSubspaceFactorization.inclusion hW'
          isComplexAnalyticSubset_univ (Set.subset_univ W') = j') ∧
      j' ≫ nativeMorphism (n := n) (m := n) hβ.contMDiff = p ≫ j := by
  obtain ⟨W, hW, a, ha⟩ := hj
  obtain ⟨S, i, hS, hi, hstalk, _, hthin, hIdeal, _⟩ := hp
  let i' := i ≫ a.hom
  have hi' : Topology.IsClosedEmbedding i'.hom.left.base :=
    (isoHomeomorph a).isClosedEmbedding.comp hi
  have hstalk' (s : S.obj.left) : Function.Surjective (i'.hom.left.stalkMap s) := by
    let : IsIso a.hom.hom.left := by
      change IsIso (isoLeft a).hom
      infer_instance
    change Function.Surjective ((i.hom.left ≫ a.hom.hom.left).stalkMap s)
    rw [LocallyRingedSpace.stalkMap_comp]
    exact (hstalk s).comp
      ((ConcreteCategory.isIso_iff_bijective
        (a.hom.hom.left.stalkMap (i.hom.left.base s))).mp inferInstance).2
  have hpre : (isoHomeomorph a).symm ⁻¹' range i.hom.left.base = range i'.hom.left.base := by
    ext y
    simp only [Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      change (isoHomeomorph a) (i.hom.left.base s) = y
      rw [hs, (isoHomeomorph a).apply_symm_apply]
    · rintro ⟨s, rfl⟩
      refine ⟨s, ?_⟩
      exact ((isoHomeomorph a).symm_apply_apply (i.hom.left.base s)).symm
  have hthin' : interior (range i'.hom.left.base) = ∅ := by
    rw [← hpre, ← (isoHomeomorph a).symm.preimage_interior, hthin, preimage_empty]
  have hIdeal' := HironakaG11NativeTowerRepresentation.isIdealBlowup_comp_baseIso
    (range i.hom.left.base) hIdeal a.symm
  change IsIdealBlowup (p ≫ a.hom)
    (intrinsicReducedCentreIdealModule (ofClosedAnalytic W hW).obj.left
      ((isoHomeomorph a).symm ⁻¹' range i.hom.left.base))
    (intrinsicReducedCentreIdealInclusion (ofClosedAnalytic W hW).obj.left
      ((isoHomeomorph a).symm ⁻¹' range i.hom.left.base)) at hIdeal'
  rw [hpre] at hIdeal'
  obtain ⟨A', β, hβ, a', ha'⟩ :=
    exists_ambient_strictTransform_iso_of_centreIdeal hW i' (p ≫ a.hom) hS hi' hstalk' hthin' hIdeal'
  let W' := strictTransform n β W
  let hW' := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
    hβ hW
  let incl := OriginalClosedSubspaceFactorization.inclusion hW
    isComplexAnalyticSubset_univ (Set.subset_univ W)
  let incl' := OriginalClosedSubspaceFactorization.inclusion hW'
    isComplexAnalyticSubset_univ (Set.subset_univ W')
  have hambient : incl' ≫ nativeMorphism (n := n) (m := n) hβ.contMDiff =
      strictTransformMorphism hβ hW ≫ incl :=
    morphism_eq_of_pointwise_eq _ _ (fun _ => rfl)
  refine ⟨A', _, β, hβ, a'.hom ≫ incl', ⟨W', hW', a', rfl⟩, ?_⟩
  calc
    (a'.hom ≫ incl') ≫ nativeMorphism hβ.contMDiff =
        a'.hom ≫ (strictTransformMorphism hβ hW ≫ incl) := by rw [Category.assoc, hambient]
    _ = (p ≫ a.hom) ≫ incl := by rw [← Category.assoc, ha']
    _ = p ≫ j := by
      rw [Category.assoc]
      exact congrArg (fun F => p ≫ F) ha

end SGPT.Unibranch
