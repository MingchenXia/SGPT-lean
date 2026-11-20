import SGPT.Projective.OriginalPullbackFrameTransition
import SGPT.Foundations.Schemes.NativeGeneratedProjectionFormula
import SGPT.Foundations.Schemes.BundleTensorRightUnit
import SGPT.Foundations.Schemes.LineSectionTwistedAffineExactness

/-! Genuine projection/restriction for ANY actual original line. No positivity,
global generation, frame compatibility or projection-isomorphism input.
Blueprint: original-line-projection-formula.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite

variable {X Y : Scheme.{0}} (g : X ⟶ Y) {B : Y.Modules}

/-- Genuine original local frames and their proved adjunction square make
the ACTUAL canonical projection map invertible, for an arbitrary original line. -/
theorem originalLineProjectionMap_isIso (b : LineBundleAtlas B) (M : X.Modules) :
    IsIso (nativeSchemeProjectionMap g B M) := by
  apply nativeModuleHom_isIso_of_over_cover (nativeSchemeProjectionMap g B M)
    b.opens b.covers
  intro i
  let e := nativeSchemeLineProjectionLocalIso g ((Scheme.Modules.pullback g).obj B) M
    (b.frame i) (matePullbackFrame g (b.frame i))
  have he : e.hom = (SheafOfModules.overFunctor Y.ringCatSheaf (b.opens i)).map
      (nativeSchemeProjectionMap g B M) := by
    apply nativeSchemeLineProjectionLocalIso_hom
    intro W h s
    exact matePullbackFrame_coefficient_simple g (b.frame i) h s
  rw [← he]
  infer_instance

/-- The actual canonical projection followed by the actual right tensor unit
identifies the original tensor quotient with the SAME geometric pulled line. -/
def originalLineRestrictionIso (b : LineBundleAtlas B) :
    bundleTensor B ((Scheme.Modules.pushforward g).obj
        (SheafOfModules.unit X.ringCatSheaf)) ≅
      (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj B) := by
  let : IsIso (nativeSchemeProjectionMap g B (SheafOfModules.unit X.ringCatSheaf)) :=
    originalLineProjectionMap_isIso g b _
  exact asIso (nativeSchemeProjectionMap g B (SheafOfModules.unit X.ringCatSheaf)) ≪≫
    (Scheme.Modules.pushforward g).mapIso
      (bundleTensorRightUnitIso ((Scheme.Modules.pullback g).obj B))

/-- The actual restriction isomorphism reads t tensor 1 as the SAME original
adjunction-unit pullback of t on EVERY original open. -/
theorem originalLineRestrictionIso_tensorUnit (b : LineBundleAtlas B) (U : Y.Opens)
    (t : Γ(B, U)) :
    (originalLineRestrictionIso g b).hom.val.app (op U)
      (tensorSection B ((Scheme.Modules.pushforward g).obj
        (SheafOfModules.unit X.ringCatSheaf)) U t
          (show Γ((Scheme.Modules.pushforward g).obj
            (SheafOfModules.unit X.ringCatSheaf), U) from (1 : Γ(X, g ⁻¹ᵁ U)))) =
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app B).val.app (op U) t) := by
  change (bundleTensorRightUnitIso ((Scheme.Modules.pullback g).obj B)).hom.val.app
    (op (g ⁻¹ᵁ U))
      ((nativeSchemeProjectionMap g B (SheafOfModules.unit X.ringCatSheaf)).val.app (op U)
        (tensorSection B ((Scheme.Modules.pushforward g).obj
          (SheafOfModules.unit X.ringCatSheaf)) U t
            (show Γ((Scheme.Modules.pushforward g).obj
              (SheafOfModules.unit X.ringCatSheaf), U) from (1 : Γ(X, g ⁻¹ᵁ U))))) = _
  rw [nativeSchemeProjectionMap_tensorSection, nativeBundleTensorRightUnitIso_tensorSection,
    one_smul]

/-- For ANY original cutting line and original section, the actual quotient
map of an arbitrary DISTINCT original test line is the SAME geometric restriction. -/
theorem originalSectionZeroTensorRestriction_comp {L : Y.Modules}
    (a : LineBundleAtlas L) (s : Γ(L, ⊤)) (b : LineBundleAtlas B) :
    sectionZeroTensorRestriction a s B ≫
        (originalLineRestrictionIso (sectionZeroι a s) b).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction (sectionZeroι a s)).unit.app B := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  change (originalLineRestrictionIso (sectionZeroι a s) b).hom.val.app U
    ((sectionZeroTensorRestriction a s B).app U.unop t) = _
  rw [sectionZeroTensorRestriction_app]
  exact originalLineRestrictionIso_tensorUnit (sectionZeroι a s) b U.unop t

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
