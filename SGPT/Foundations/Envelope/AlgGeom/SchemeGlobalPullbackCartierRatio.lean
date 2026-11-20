import SGPT.Foundations.Envelope.AlgGeom.SchemeLineZeroSupportPullback
import SGPT.Foundations.Envelope.AlgGeom.ProjectiveLineCartierRatio
import SGPT.Support.ModularCurves.Picard.PullbackTensorObj
/-! # Actual global original model sections retain their genuine whole pulled Cartier ratio -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SGPT.Foundations.Envelope.SchemeGlobalPullbackCartierRatio
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem ne_zero_of_not_mem_support {X : Scheme.{u}} (M : X.Modules) (hM : IsInvertible M)
    (α : unitObj X ⟶ M) (x : X) (hx : x ∉ (LineSectionZeroIdeal.zeroIdeal M hM α).support) : α ≠ 0 := by
  intro hz
  obtain ⟨U,hU,⟨e⟩⟩ := IntegralLineImageModules.exists_affine_frame M hM x
  apply hx
  rw [SchemeLineZeroSupportPullback.mem_support_iff_coefficient_zero M hM α U.1 x hU e,hz]
  change X.evaluation U.1 x hU (e.hom.val.app (op (Over.mk (𝟙 U.1))) 0) = 0
  rw [map_zero,map_zero]

theorem pullbackSection_ne_zero {N Z : Scheme.{u}} (p : Z ⟶ N)
    (M : N.Modules) (hM : IsInvertible M) (α : unitObj N ⟶ M) (x : Z)
    (hx : p x ∉ (LineSectionZeroIdeal.zeroIdeal M hM α).support) :
    SchemeLineSectionEvaluation.pullbackSectionHom p α ≠ 0 := by
  apply ne_zero_of_not_mem_support _ (hM.pullback p) _ x
  rw [SchemeLineZeroSupportPullback.support_pullback p M hM α]
  exact hx

theorem pullback_zeroIdeal_isInvertible {N Z : Scheme.{u}} [IsIntegral Z] (p : Z ⟶ N)
    (M : N.Modules) (hM : IsInvertible M) (α : unitObj N ⟶ M) (x : Z)
    (hx : p x ∉ (LineSectionZeroIdeal.zeroIdeal M hM α).support) :
    (LineSectionZeroIdeal.zeroIdeal ((pullback p).obj M) (hM.pullback p)
      (SchemeLineSectionEvaluation.pullbackSectionHom p α)).IsInvertible :=
  LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero _ (hM.pullback p) _
    (pullbackSection_ne_zero p M hM α x hx)

def sectionRatioIsoOfTensorIso {Z : Scheme.{u}} [IsIntegral Z]
    (L T S : Z.Modules) (hT : IsInvertible T) (hS : IsInvertible S) (e : S ≅ L ⊗ T)
    (s : unitObj Z ⟶ S) (hs : s ≠ 0) (t : unitObj Z ⟶ T) (ht : t ≠ 0) :
    (LineSectionZeroIdeal.zeroIdeal T hT t).ratioModule
      (LineSectionZeroIdeal.zeroIdeal S hS s) ≅ L := by
  let I := LineSectionZeroIdeal.zeroIdeal T hT t
  let J := LineSectionZeroIdeal.zeroIdeal S hS s
  let eT : dualObj T ≅ I.toModules := IntegralLineImageModules.zeroSectionDualIso T hT t ht
  let eS : dualObj S ≅ J.toModules := IntegralLineImageModules.zeroSectionDualIso S hS s hs
  let eJ : dualObj J.toModules ≅ S :=
    dualIsoObj eS ≪≫ (ProjectiveLineCartierRatio.doubleDualLineIso S hS).symm
  exact (SGPT.Support.ModularCurves.monoidalTensorObjIso I.toModules (dualObj J.toModules)).symm ≪≫
    (eT.symm ⊗ᵢ eJ) ≪≫ (Iso.refl (dualObj T) ⊗ᵢ e) ≪≫
      (β_ (dualObj T) (L ⊗ T)) ≪≫ (α_ L T (dualObj T)) ≪≫
        whiskerLeftIso L hT.monoidalEvaluationIso ≪≫ ρ_ L

def pullbackRatioIso {N Z : Scheme.{u}} [IsIntegral Z] (p : Z ⟶ N)
    (M T : N.Modules) (hM : IsInvertible M) (hT : IsInvertible T)
    (α : unitObj N ⟶ M ⊗ T) (β : unitObj N ⟶ T) (x : Z)
    (hα : p x ∉ (LineSectionZeroIdeal.zeroIdeal (M ⊗ T)
      ((hM.tensorObj hT).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso M T)) α).support)
    (hβ : p x ∉ (LineSectionZeroIdeal.zeroIdeal T hT β).support) :
    (pullback p).obj M ≅
      (LineSectionZeroIdeal.zeroIdeal ((pullback p).obj T) (hT.pullback p)
        (SchemeLineSectionEvaluation.pullbackSectionHom p β)).ratioModule
      (LineSectionZeroIdeal.zeroIdeal ((pullback p).obj (M ⊗ T))
        (((hM.tensorObj hT).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso M T)).pullback p)
        (SchemeLineSectionEvaluation.pullbackSectionHom p α)) := by
  let hMT : IsInvertible (M ⊗ T) :=
    (hM.tensorObj hT).of_iso (SGPT.Support.ModularCurves.monoidalTensorObjIso M T)
  have hs := pullbackSection_ne_zero p (M ⊗ T) hMT α x hα
  have ht := pullbackSection_ne_zero p T hT β x hβ
  let : (pullback p).Monoidal := pullbackMonoidal p
  exact (sectionRatioIsoOfTensorIso ((pullback p).obj M) ((pullback p).obj T)
    ((pullback p).obj (M ⊗ T)) (hT.pullback p) (hMT.pullback p)
    (Functor.Monoidal.μIso (pullback p) M T).symm
    (SchemeLineSectionEvaluation.pullbackSectionHom p α) hs
    (SchemeLineSectionEvaluation.pullbackSectionHom p β) ht).symm
end SGPT.Foundations.Envelope.SchemeGlobalPullbackCartierRatio
