import SGPT.Unibranch.OriginalNativeHSStrongFiniteRecipe
import SGPT.Unibranch.OriginalBimeromorphicSourceIso
import SGPT.Unibranch.OriginalLocalStrictWindowRegularity

/-! The SAME ordinary X/U strong finite recipe has FULL original-Reg
inverse and genuine IsResolution, with no new chosen endpoint or packet.
Blueprint FIRST: original-native-hs-strong-finite-resolution.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.OriginalNativeHSStrongFiniteResolution
noncomputable section
open SGPT.Foundations.Analysis.Pending SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus
  OriginalNativeHSStrongFiniteRecipe

variable (X : SourceReducedComplexSpace) (U : Opens X.obj.left)
  (hU : IsCompact (closure (U : Set X.obj.left)))

private abbrev baseInclusion := OriginalRelativelyCompactRestriction.inclusion
  (initialState X U hU).base (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU)

private theorem baseInclusion_open : LocallyRingedSpace.IsOpenImmersion (baseInclusion X U hU).hom.left :=
  OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _

private theorem whole_range : range (sourceInclusion X U hU).hom.left.base =
    (strongProjection X U hU).hom.left.base ⁻¹' range (baseInclusion X U hU).hom.left.base := by
  rw [OriginalRelativelyCompactRestriction.inclusion_range]
  exact Subtype.range_coe

theorem restrictedReg : IsIsoOver (restrictedProjection X U hU)
    (intrinsicRegularLocus (OriginalRelativelyCompactRestriction.restriction (initialState X U hU).base
      (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU)).obj) := by
  have hOld := (HironakaG1NativeStrongCleanup.strong_geometry (initialProjection X U hU)
    (initialResolution X U hU) (initialReg X U hU)).2.2.2.2.2
  have h := OriginalLocalStrictWindowRegularity.isIsoOver_of_open_square
    (strongProjection X U hU) (restrictedProjection X U hU) (sourceInclusion X U hU)
    (baseInclusion X U hU) (sourceInclusion_isOpenImmersion X U hU) (baseInclusion_open X U hU)
    (restricted_projection_square X U hU) (whole_range X U hU)
    (intrinsicRegularLocus (initialState X U hU).base.obj) hOld
  exact OriginalRelativelyCompactRestriction.inclusion_preimage_intrinsicRegularLocus
    (initialState X U hU).base (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU) ▸ h

theorem target_regular_preimage : (targetComparison X U hU).hom.hom.left.base ⁻¹'
    intrinsicRegularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj =
      intrinsicRegularLocus (OriginalRelativelyCompactRestriction.restriction (initialState X U hU).base
        (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU)).obj := by
  have hOpen : LocallyRingedSpace.IsOpenImmersion (targetComparison X U hU).hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (targetComparison X U hU)).hom
    infer_instance
  exact HironakaG11IntrinsicRegularOpenImmersion.preimage_intrinsicRegularLocus
    (targetComparison X U hU).hom.hom.left hOpen (Over.w (targetComparison X U hU).hom.hom)

theorem originalReg : IsIsoOver (projection X U hU)
    (intrinsicRegularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj) := by
  have hE : IsIsoOver (targetComparison X U hU).hom
      (intrinsicRegularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj) := by
    simpa only [Category.comp_id] using
      (IsIsoOver.id_of_isOpen (OriginalRelativelyCompactRestriction.restriction X U hU)
        (isOpen_intrinsicRegularLocus _)).precomp_iso (targetComparison X U hU)
  have hQ : IsIsoOver (restrictedProjection X U hU)
      ((targetComparison X U hU).hom.hom.left.base ⁻¹'
        intrinsicRegularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj) :=
    (target_regular_preimage X U hU).symm ▸ restrictedReg X U hU
  exact hE.comp hQ

theorem original_singular_preimage_thin : interior ((projection X U hU).hom.left.base ⁻¹'
    intrinsicSingularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj) = ∅ :=
  (finite X U hU).interior_preimage_eq_empty
    (OriginalIntrinsicSingularLocus.interior_intrinsicSingularLocus_eq_empty _)

theorem resolution : IsResolution (projection X U hU) := by
  refine ⟨source_smooth X U hU, proper X U hU,
    intrinsicSingularLocus (OriginalRelativelyCompactRestriction.restriction X U hU).obj,
    OriginalIntrinsicSingularLocus.isAnalyticSubset_intrinsicSingularLocus _,
    OriginalIntrinsicSingularLocus.interior_intrinsicSingularLocus_eq_empty _,
    original_singular_preimage_thin X U hU, ?_⟩
  simpa only [intrinsicSingularLocus, compl_compl] using originalReg X U hU

theorem surjective : Function.Surjective (projection X U hU).hom.left.base := (finite X U hU).surjective

end
end SGPT.Unibranch.OriginalNativeHSStrongFiniteResolution
