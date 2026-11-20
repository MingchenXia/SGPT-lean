import SGPT.Unibranch.OriginalNativeHSShadowOuterRun
import SGPT.Unibranch.HironakaG1NativeStrongFiniteReadout
import SGPT.Unibranch.OriginalNativePrescribedOpenHistory

/-! Ordinary ORIGINAL X/U/compactClosure -> SAME larger-base strong source,
actual literal prescribed-open arrow and REAL finite IsModification.
Blueprint FIRST: original-native-hs-strong-finite-recipe.tex.
Cleanup is on the genuine LARGER B, then restricted to precompact U_B.
No initial history/resolution/phase supplier or endpoint-to-finite shortcut. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.OriginalNativeHSStrongFiniteRecipe
noncomputable section
open SGPT.Foundations.Analysis.Pending SourceReducedComplexSpace OriginalNativeHSOuterHistory
  HironakaIntrinsicComplexAnalyticRegularLocus SmoothCentreModification

variable (X : SourceReducedComplexSpace) (U : Opens X.obj.left)
  (hU : IsCompact (closure (U : Set X.obj.left)))

/-- The actual initial factory is chosen on ORIGINAL closure U, not on U as its own base. -/
def initialState := OriginalNativeHSShadowOuterRun.nearCompactState X (closure (U : Set X.obj.left)) hU

def initialProjection : (initialState X U hU).source ⟶ (initialState X U hU).base :=
  (initialState X U hU).history.projection

theorem initialResolution : IsResolution (initialProjection X U hU) :=
  OriginalNativeHSShadowOuterRun.nearCompact_resolution X (closure (U : Set X.obj.left)) hU

theorem initialReg : IsIsoOver (initialProjection X U hU)
    (intrinsicRegularLocus (initialState X U hU).base.obj) :=
  (initialState X U hU).history.singularModification.isIsoOver_intrinsicRegularLocus

def strongSource : SourceReducedComplexSpace :=
  HironakaG1NativeStrongCleanup.strongSource (initialProjection X U hU) (initialResolution X U hU)

def strongProjection : strongSource X U hU ⟶ (initialState X U hU).base :=
  HironakaG1NativeStrongCleanup.strongMorphism (initialProjection X U hU) (initialResolution X U hU)

theorem strongProper : IsProperMap (strongProjection X U hU).hom.left.base :=
  (HironakaG1NativeStrongCleanup.strong_geometry (initialProjection X U hU)
    (initialResolution X U hU) (initialReg X U hU)).2.2.2.1

def prescribedOpen : Opens (initialState X U hU).base.obj.left :=
  OriginalNativePrescribedOpenHistory.pullbackOpen (initialState X U hU).inclusion U

theorem prescribedOpen_compactClosure :
    IsCompact (closure (prescribedOpen X U hU : Set (initialState X U hU).base.obj.left)) :=
  OriginalNativePrescribedOpenHistory.pullbackOpen_compactClosure (initialState X U hU).inclusion
    (initialState X U hU).inclusion_isOpenImmersion U hU (initialState X U hU).contains

def targetComparison : OriginalRelativelyCompactRestriction.restriction (initialState X U hU).base
    (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU) ≅
      OriginalRelativelyCompactRestriction.restriction X U hU :=
  OriginalNativePrescribedOpenHistory.comparison (initialState X U hU).inclusion
    (initialState X U hU).inclusion_isOpenImmersion U hU (initialState X U hU).contains

def source : SourceReducedComplexSpace :=
  OriginalRelativelyCompactRestriction.preimageRestriction (prescribedOpen X U hU)
    (strongProjection X U hU) (prescribedOpen_compactClosure X U hU) (strongProper X U hU)

def sourceInclusion : source X U hU ⟶ strongSource X U hU :=
  OriginalRelativelyCompactRestriction.inclusion (strongSource X U hU)
    (OriginalRelativelyCompactRestriction.preimageOpen (prescribedOpen X U hU) (strongProjection X U hU))
    (OriginalRelativelyCompactRestriction.isCompact_closure_preimage (prescribedOpen X U hU)
      (strongProjection X U hU) (prescribedOpen_compactClosure X U hU) (strongProper X U hU))

theorem sourceInclusion_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion X U hU).hom.left :=
  OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _

def restrictedProjection : source X U hU ⟶
    OriginalRelativelyCompactRestriction.restriction (initialState X U hU).base
      (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU) :=
  OriginalRelativelyCompactRestriction.restrictionProjection (prescribedOpen X U hU)
    (strongProjection X U hU) (prescribedOpen_compactClosure X U hU) (strongProper X U hU)

def projection : source X U hU ⟶ OriginalRelativelyCompactRestriction.restriction X U hU :=
  restrictedProjection X U hU ≫ (targetComparison X U hU).hom

/-- A REAL finite witness from restriction of the SAME actual initial physical history. -/
theorem initial_finite : IsModification (OriginalRelativelyCompactRestriction.restrictionProjection
    (prescribedOpen X U hU) (initialProjection X U hU) (prescribedOpen_compactClosure X U hU)
      (initialResolution X U hU).2.1) := by
  have hFinite := (OriginalNativePhysicalHistoryRestriction.restrict (initialState X U hU).history
    (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU)).singularModification.toIsModification
  exact OriginalNativePhysicalHistoryRestriction.projection_restrict (initialState X U hU).history
    (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU) ▸ hFinite

/-- Accepted S5 applies on true precompact U_B in the LARGER chosen B. -/
theorem restricted_finite : IsModification (restrictedProjection X U hU) :=
  HironakaG1NativeStrongFiniteReadout.strongMorphism_restriction_isModification
    (initialProjection X U hU) (initialResolution X U hU) (initialReg X U hU)
    (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU) (initial_finite X U hU)

theorem finite : IsModification (projection X U hU) :=
  HironakaG1NativeModificationIsoTransport.isModification_postcomp_iso (restricted_finite X U hU)
    (targetComparison X U hU)

theorem restricted_projection_square : restrictedProjection X U hU ≫
    OriginalRelativelyCompactRestriction.inclusion (initialState X U hU).base
      (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU) =
        sourceInclusion X U hU ≫ strongProjection X U hU :=
  OriginalRelativelyCompactRestriction.restrictionProjection_inclusion _ _ _ _

private theorem paste_target {A B C D E F : SourceReducedComplexSpace}
    (q : A ⟶ B) (e : B ⟶ C) (i : C ⟶ F) (b : B ⟶ D) (j : D ⟶ F)
    (l : A ⟶ E) (p : E ⟶ D) (he : e ≫ i = b ≫ j) (hq : q ≫ b = l ≫ p) :
    (q ≫ e) ≫ i = l ≫ p ≫ j := by
  calc
    (q ≫ e) ≫ i = q ≫ (e ≫ i) := Category.assoc _ _ _
    _ = q ≫ (b ≫ j) := congrArg (fun f => q ≫ f) he
    _ = (q ≫ b) ≫ j := (Category.assoc _ _ _).symm
    _ = (l ≫ p) ≫ j := congrArg (fun f => f ≫ j) hq
    _ = l ≫ p ≫ j := Category.assoc _ _ _

theorem projection_original_square : projection X U hU ≫ OriginalRelativelyCompactRestriction.inclusion X U hU =
    sourceInclusion X U hU ≫ strongProjection X U hU ≫ (initialState X U hU).inclusion :=
  paste_target (restrictedProjection X U hU) (targetComparison X U hU).hom
    (OriginalRelativelyCompactRestriction.inclusion X U hU)
    (OriginalRelativelyCompactRestriction.inclusion (initialState X U hU).base
      (prescribedOpen X U hU) (prescribedOpen_compactClosure X U hU))
    (initialState X U hU).inclusion (sourceInclusion X U hU) (strongProjection X U hU)
    (OriginalNativePrescribedOpenHistory.comparison_square (initialState X U hU).inclusion
      (initialState X U hU).inclusion_isOpenImmersion U hU (initialState X U hU).contains)
    (restricted_projection_square X U hU)

theorem source_smooth : (source X U hU).IsSmooth := by
  apply (OriginalIntrinsicSingularLocus.isSmooth_iff_intrinsicSingularLocus_eq_empty _).mpr
  have hOld : intrinsicSingularLocus (strongSource X U hU).obj = ∅ :=
    (OriginalIntrinsicSingularLocus.isSmooth_iff_intrinsicSingularLocus_eq_empty _).mp
      (HironakaG1NativeStrongCleanup.strong_geometry (initialProjection X U hU)
        (initialResolution X U hU) (initialReg X U hU)).1
  have hPull := OriginalRelativelyCompactRestriction.inclusion_preimage_intrinsicSingularLocus
    (strongSource X U hU)
    (OriginalRelativelyCompactRestriction.preimageOpen (prescribedOpen X U hU) (strongProjection X U hU))
    (OriginalRelativelyCompactRestriction.isCompact_closure_preimage (prescribedOpen X U hU)
      (strongProjection X U hU) (prescribedOpen_compactClosure X U hU) (strongProper X U hU))
  exact hPull.symm.trans (by simp only [hOld, preimage_empty]; rfl)

theorem proper : IsProperMap (projection X U hU).hom.left.base := (finite X U hU).isProperMap

theorem scalar : (projection X U hU).hom.left ≫
    (OriginalRelativelyCompactRestriction.restriction X U hU).obj.hom = (source X U hU).obj.hom :=
  Over.w (projection X U hU).hom

end
end SGPT.Unibranch.OriginalNativeHSStrongFiniteRecipe
