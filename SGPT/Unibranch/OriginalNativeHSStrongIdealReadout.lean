import SGPT.Unibranch.OriginalNativeHSStrongFiniteRecipe
import SGPT.Unibranch.HironakaG1NativeSmoothCleanupCore

/-! The ENTIRE original singular ideal on the SAME prescribed strong recipe.
Blueprint FIRST: original-native-hs-strong-ideal-readout.tex.
All inputs are ordinary X/U/compactClosure; no ideal/comparison packet,
new cleanup choice, radicalization or replacement native source is used. -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

namespace SGPT.Unibranch.OriginalNativeHSStrongIdealReadout
noncomputable section
open SGPT.Foundations.Analysis.Pending SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaIntrinsicReducedCentreIdealSheaf
  HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk
  HironakaNativePulledIdealComposition HironakaSingularModuleSheafStalk

variable (X : SourceReducedComplexSpace) (U : Opens X.obj.left)
  (hU : IsCompact (closure (U : Set X.obj.left)))

private abbrev B := (OriginalNativeHSStrongFiniteRecipe.initialState X U hU).base
private abbrev Z := OriginalNativeHSStrongFiniteRecipe.strongSource X U hU
private abbrev Y := OriginalNativeHSStrongFiniteRecipe.source X U hU
private abbrev V := OriginalRelativelyCompactRestriction.restriction X U hU
private abbrev j := (OriginalNativeHSStrongFiniteRecipe.initialState X U hU).inclusion
private abbrev r := OriginalNativeHSStrongFiniteRecipe.strongProjection X U hU
private abbrev l := OriginalNativeHSStrongFiniteRecipe.sourceInclusion X U hU
private abbrev i := OriginalRelativelyCompactRestriction.inclusion X U hU
private abbrev q := OriginalNativeHSStrongFiniteRecipe.projection X U hU

private theorem i_smooth : OriginalNativeSmoothLocalProduct.IsSmoothMorphism (i X U hU) :=
  OriginalNativeSmoothLocalProduct.isSmoothMorphism_of_isOpenImmersion _
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion X U hU)

private theorem j_smooth : OriginalNativeSmoothLocalProduct.IsSmoothMorphism (j X U hU) :=
  OriginalNativeSmoothLocalProduct.isSmoothMorphism_of_isOpenImmersion _
    (OriginalNativeHSStrongFiniteRecipe.initialState X U hU).inclusion_isOpenImmersion

/-- Exact entire original singular inverse set on the literal final arrow. -/
theorem singular_preimage :
    (q X U hU).hom.left.base ⁻¹' intrinsicSingularLocus (V X U hU).obj =
      (l X U hU).hom.left.base ⁻¹'
        ((r X U hU).hom.left.base ⁻¹' intrinsicSingularLocus (B X U hU).obj) := by
  have hi := OriginalNativeSmoothSingularLocus.preimage_intrinsicSingularLocus
    (i X U hU) (i_smooth X U hU)
  have hj := OriginalNativeSmoothSingularLocus.preimage_intrinsicSingularLocus
    (j X U hU) (j_smooth X U hU)
  have hs := congrArg (fun f : Y X U hU ⟶ X =>
    f.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)
    (OriginalNativeHSStrongFiniteRecipe.projection_original_square X U hU)
  change (q X U hU).hom.left.base ⁻¹'
      ((i X U hU).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) =
    (l X U hU).hom.left.base ⁻¹' ((r X U hU).hom.left.base ⁻¹'
      ((j X U hU).hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) at hs
  rw [hi, hj] at hs
  exact hs

/-- The old entire total ideal on the SAME larger-base strong source. -/
abbrev oldTotalIdeal := nativePulledIdealModule (r X U hU).hom.left
  (intrinsicReducedCentreIdealModule (B X U hU).obj.left (intrinsicSingularLocus (B X U hU).obj))
  (intrinsicReducedCentreIdealInclusion (B X U hU).obj.left (intrinsicSingularLocus (B X U hU).obj))

/-- Its literal original structure-unit inclusion. -/
abbrev oldTotalInclusion := nativePulledIdealInclusion (r X U hU).hom.left
  (intrinsicReducedCentreIdealModule (B X U hU).obj.left (intrinsicSingularLocus (B X U hU).obj))
  (intrinsicReducedCentreIdealInclusion (B X U hU).obj.left (intrinsicSingularLocus (B X U hU).obj))

/-- The entire original-singular image ideal of the LITERAL prescribed map. -/
abbrev totalIdeal := nativePulledIdealModule (q X U hU).hom.left
  (intrinsicReducedCentreIdealModule (V X U hU).obj.left (intrinsicSingularLocus (V X U hU).obj))
  (intrinsicReducedCentreIdealInclusion (V X U hU).obj.left (intrinsicSingularLocus (V X U hU).obj))

/-- The actual final original structure-unit inclusion. -/
abbrev totalInclusion := nativePulledIdealInclusion (q X U hU).hom.left
  (intrinsicReducedCentreIdealModule (V X U hU).obj.left (intrinsicSingularLocus (V X U hU).obj))
  (intrinsicReducedCentreIdealInclusion (V X U hU).obj.left (intrinsicSingularLocus (V X U hU).obj))

/-- Entire nonradical original stalk images, with all original scalar maps. -/
theorem wholeStalk (z : (Y X U hU).obj.left) :
    nativePulledIdealStalkIdeal (q X U hU).hom.left
      (intrinsicReducedCentreIdealModule (V X U hU).obj.left (intrinsicSingularLocus (V X U hU).obj))
      (intrinsicReducedCentreIdealInclusion (V X U hU).obj.left (intrinsicSingularLocus (V X U hU).obj)) z =
    nativePulledIdealStalkIdeal (l X U hU).hom.left
      (oldTotalIdeal X U hU) (oldTotalInclusion X U hU) z := by
  have hi := HironakaG1NativeSmoothCleanupCore.smoothBase_stalkIdeal_eq
    (i X U hU) (i_smooth X U hU) (q X U hU).hom.left z
  have hj := HironakaG1NativeSmoothCleanupCore.smoothBase_stalkIdeal_eq
    (j X U hU) (j_smooth X U hU) ((l X U hU).hom.left ≫ (r X U hU).hom.left) z
  have hs : (q X U hU).hom.left ≫ (i X U hU).hom.left =
      ((l X U hU).hom.left ≫ (r X U hU).hom.left) ≫ (j X U hU).hom.left := by
    exact (congrArg (fun f : Y X U hU ⟶ X => f.hom.left)
      (OriginalNativeHSStrongFiniteRecipe.projection_original_square X U hU)).trans
        (Category.assoc _ _ _).symm
  calc
    _ = nativePulledIdealStalkIdeal ((q X U hU).hom.left ≫ (i X U hU).hom.left)
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) z := hi.symm
    _ = nativePulledIdealStalkIdeal
        (((l X U hU).hom.left ≫ (r X U hU).hom.left) ≫ (j X U hU).hom.left)
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) z :=
      congrArg (fun f => nativePulledIdealStalkIdeal f _ _ z) hs
    _ = nativePulledIdealStalkIdeal ((l X U hU).hom.left ≫ (r X U hU).hom.left)
        (intrinsicReducedCentreIdealModule (B X U hU).obj.left (intrinsicSingularLocus (B X U hU).obj))
        (intrinsicReducedCentreIdealInclusion (B X U hU).obj.left (intrinsicSingularLocus (B X U hU).obj)) z := hj
    _ = _ := (stalkIdeal_comp (r X U hU).hom.left (l X U hU).hom.left _ _ z).symm

/-- ALL original section submodules coincide, not merely their supports. -/
theorem wholeSubmodule_eq :
    nativePulledIdealSubmodule (l X U hU).hom.left
      (oldTotalIdeal X U hU) (oldTotalInclusion X U hU) =
    nativePulledIdealSubmodule (q X U hU).hom.left
      (intrinsicReducedCentreIdealModule (V X U hU).obj.left (intrinsicSingularLocus (V X U hU).obj))
      (intrinsicReducedCentreIdealInclusion (V X U hU).obj.left (intrinsicSingularLocus (V X U hU).obj)) := by
  apply PresheafOfModules.Submodule.ext
  intro W
  ext t
  constructor
  · intro ht z hz
    exact (wholeStalk X U hU z).symm ▸ ht z hz
  · intro ht z hz
    exact wholeStalk X U hU z ▸ ht z hz

/-- The actual new unit-inclusion stalk range is the whole old image pullback. -/
theorem stalkRange_eq (z : (Y X U hU).obj.left) :
    LinearMap.range (stalkInclusionLinearMap (Y X U hU).obj.left.toSheafedSpace.sheaf
      (totalIdeal X U hU) (totalInclusion X U hU) z) =
      nativePulledIdealStalkIdeal (l X U hU).hom.left
        (oldTotalIdeal X U hU) (oldTotalInclusion X U hU) z :=
  (nativePulledIdealStalkInclusion_range (q X U hU).hom.left _ _ z).trans (wholeStalk X U hU z)

set_option maxHeartbeats 800000 in
/-- Full ideal-module iso supplied by literal equality of original unit submodules. -/
def wholeIdealIso : nativePulledIdealModule (l X U hU).hom.left
    (oldTotalIdeal X U hU) (oldTotalInclusion X U hU) ≅ totalIdeal X U hU where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (wholeSubmodule_eq X U hU).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (wholeSubmodule_eq X U hU).ge⟩
  hom_inv_id := by ext W t; rfl
  inv_hom_id := by ext W t; rfl

/-- Forward literal original unit inclusion triangle. -/
theorem wholeIdealIso_hom_comp_inclusion :
    (wholeIdealIso X U hU).hom ≫ totalInclusion X U hU =
      nativePulledIdealInclusion (l X U hU).hom.left
        (oldTotalIdeal X U hU) (oldTotalInclusion X U hU) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (wholeSubmodule_eq X U hU).le

/-- Inverse literal original unit inclusion triangle. -/
theorem wholeIdealIso_inv_comp_inclusion :
    (wholeIdealIso X U hU).inv ≫ nativePulledIdealInclusion (l X U hU).hom.left
        (oldTotalIdeal X U hU) (oldTotalInclusion X U hU) = totalInclusion X U hU := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (wholeSubmodule_eq X U hU).ge

end
end SGPT.Unibranch.OriginalNativeHSStrongIdealReadout
