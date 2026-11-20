import SGPT.Unibranch.OriginalNativeHSCurrentSmoothContext
import SGPT.Unibranch.OriginalNativeSmoothOpenLocality
import SGPT.Unibranch.OriginalNativeSmoothSingularLocus
import SGPT.Unibranch.HironakaG11LiftUniqueness

/-! Actual present smooth Context base geometry and ANY native lift uniqueness.
Blueprint FIRST: original-native-hs-current-smooth-uniqueness.tex.
No generic new density/extensionality engine or future map packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.OriginalNativeHSCurrentSmoothUniqueness
noncomputable section
open SGPT.Foundations.Analysis.Pending SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalNativeHSShadowOuterState OriginalNativeProductWindow
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeSmoothOpenLocality
  OriginalNativeSmoothSingularLocus OriginalNativeHSCurrentSmoothContext

variable {X Y : SourceReducedComplexSpace} {f : X ⟶ Y} {e0 : LocalEmbedding Y} {r : ℕ}
  {O : Opens (productAmbient e0 r)} {a : windowSpace e0 r O ⟶ X}
  {ha : LocallyRingedSpace.IsOpenImmersion a.hom.left} {hChart : a ≫ f = windowFirst e0 r O}
  {KS : Set X.obj.left} {KT : Set Y.obj.left} {S : State X KS} {T : State Y KT}
  (c : Context f e0 r O a ha hChart S T)

private theorem first_smooth : IsSmoothMorphism (windowFirst e0 r O) := by
  let hWP : MapsTo (Prod.fst : productAmbient e0 r → e0.ambient) O (⊤ : Opens e0.ambient) := fun _ _ => mem_univ _
  have hp := isSmoothMorphism_comp (nativeProjection e0 r ⊤ O hWP) (targetInclusion e0 ⊤)
    (nativeProjection_isSmooth e0 r ⊤ O hWP)
    (isSmoothMorphism_of_isOpenImmersion _ (targetInclusion_isOpenImmersion e0 ⊤))
  exact (nativeProjection_square e0 r ⊤ O hWP) ▸ hp

/-- The SAME actual baseMap is smooth from the REAL original product chart. -/
theorem baseMap_smooth : IsSmoothMorphism c.baseMap := by
  have hs : IsSmoothMorphism (c.sourceChartMap ≫ windowFirst e0 r O) :=
    isSmoothMorphism_comp _ _ (isSmoothMorphism_of_isOpenImmersion _ c.sourceChartMap_isOpenImmersion)
      first_smooth
  have he : c.baseMap ≫ c.targetBaseInclusion = c.sourceChartMap ≫ windowFirst e0 r O :=
    c.baseMap_square.trans c.sourceChartMap_projection.symm
  exact isSmoothMorphism_of_postcomp_openImmersion _ c.targetBaseInclusion
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _)
    ((congrArg IsSmoothMorphism he).mpr hs)

/-- ANY actual full lifts on the same prescribed endpoints and original square agree. -/
theorem maps_eq_over_original
    (u v : OriginalNativeHSCurrentOverlap.endpoint S c.sourceOpen c.sourceCompactClosure c.sourceRange ⟶
      OriginalNativeHSCurrentOverlap.endpoint T c.targetOpen c.targetCompactClosure c.targetRange)
    (hu : u ≫ c.targetHistory.projection ≫ c.targetBaseInclusion =
      c.sourceHistory.projection ≫ c.sourceBaseInclusion ≫ f)
    (hv : v ≫ c.targetHistory.projection ≫ c.targetBaseInclusion =
      c.sourceHistory.projection ≫ c.sourceBaseInclusion ≫ f) : u = v := by
  have hi := (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion
    Y c.targetOpen c.targetCompactClosure).base_open.injective
  have hbase : ∀ z, c.targetHistory.projection.hom.left.base (u.hom.left.base z) =
      c.targetHistory.projection.hom.left.base (v.hom.left.base z) := by
    intro z
    apply hi
    exact (congrArg (fun p => p.hom.left.base z) hu).trans (congrArg (fun p => p.hom.left.base z) hv).symm
  have hGood : ∀ z ∈ c.sourceHistory.projection.hom.left.base ⁻¹'
      intrinsicRegularLocus (OriginalRelativelyCompactRestriction.restriction X c.sourceOpen c.sourceCompactClosure).obj,
      c.targetHistory.projection.hom.left.base (u.hom.left.base z) ∈
        intrinsicRegularLocus (OriginalRelativelyCompactRestriction.restriction Y c.targetOpen c.targetCompactClosure).obj := by
    intro z hz
    have hup := congrArg (fun p => p.hom.left.base z) hu
    have hbp := congrArg (fun p => p.hom.left.base (c.sourceHistory.projection.hom.left.base z)) c.baseMap_square
    have he : c.targetHistory.projection.hom.left.base (u.hom.left.base z) =
        c.baseMap.hom.left.base (c.sourceHistory.projection.hom.left.base z) := hi (hup.trans hbp.symm)
    exact (congrArg (fun y => y ∈ intrinsicRegularLocus
      (OriginalRelativelyCompactRestriction.restriction Y c.targetOpen c.targetCompactClosure).obj) he).mpr
      ((smoothAt_regular_iff c.baseMap _ (baseMap_smooth c _)).mp hz)
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq u v
  intro z
  exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
    c.targetHistory.singularModification.isIsoOver_intrinsicRegularLocus
    u.hom.left.base.hom.continuous v.hom.left.base.hom.continuous hbase
    c.sourceHistory.singularModification.dense_preimage_intrinsicRegularLocus hGood) z

end
end SGPT.Unibranch.OriginalNativeHSCurrentSmoothUniqueness
