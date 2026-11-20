import SGPT.BDivisor.StrictVolume.MovingBlowup
import SGPT.BDivisor.StrictVolume.PencilCartier
import SGPT.Projective.SourceLinearHyperplaneClass
import SGPT.Toric.HyperplanePullbackChern

/-! Actual moving pi*H-E traces and genuine nef zero-volume Cartier b-divisors. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.BDivisor.MovingPencilNext

open Set
open SGPT.Projective SGPT.Projective.HyperplaneClassNext
open SGPT.Toric SGPT.Toric.BlowdownDraft SGPT.Toric.F1IntersectionDraft
open SGPT.BDivisor.MovingCentresNext SGPT.BDivisor.StrictPencilNext
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

theorem movedPencil_hyperplaneClass (a b : ℂ) :
    classPullback (movedPencilModification hs a b).contMDiff_map
      (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) =
      RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form := by
  change classPullback ((pointTranslation_contMDiff a b).comp
    (contMDiff_originalBlowdown hs)) _ = _
  calc
    _ = classPullback (contMDiff_originalBlowdown hs)
        (classPullback (pointTranslation_contMDiff a b)
          (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2)))) :=
      classPullback_comp _ _ _
    _ = classPullback (contMDiff_originalBlowdown hs)
        (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) :=
      congrArg (classPullback (contMDiff_originalBlowdown hs))
        (projectiveLinear_fsClass (pointTranslationLinearEquiv a b))
    _ = _ := (physicalOriginalHyperplane_firstChernClass_fs hs).symm

theorem movedPencilClass_eq_pullbackH_sub_E (a b : ℂ) :
    RealBottChern.ofRepresentative (originalPencilFsMetric hs).form =
      classPullback (movedPencilModification hs a b).contMDiff_map
        (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) -
        (show RealBottChern 2 (movedPencilModification hs a b).carrier from
          RealBottChern.ofRepresentative (originalExceptionalMetric hs).form) := by
  rw [movedPencil_hyperplaneClass hs a b]
  exact originalPencilFsClass_eq_H_sub_E hs

def movedPencilCartierBDivisor (a b : ℂ) :
    WeilBDivisor 2 (ComplexProjectiveSpace 2) (by decide) :=
  WeilBDivisor.cartierOf (by decide) (movedPencilModification hs a b)
    (RealBottChern.ofRepresentative (originalPencilFsMetric hs).form)

theorem movedPencilCartierBDivisor_onModel (a b : ℂ) :
    (movedPencilCartierBDivisor hs a b).onModel (movedPencilModification hs a b) =
      RealBottChern.ofRepresentative (originalPencilFsMetric hs).form :=
  (WeilBDivisor.isRealization_cartierOf (movedPencilModification hs a b) _).onModel_eq

theorem movedPencilCartierBDivisor_onModel_pullbackH_sub_E (a b : ℂ) :
    (movedPencilCartierBDivisor hs a b).onModel (movedPencilModification hs a b) =
      classPullback (movedPencilModification hs a b).contMDiff_map
        (RealBottChern.ofRepresentative (ComplexProjectiveSpace.fsClosedForm (N := 2))) -
        (show RealBottChern 2 (movedPencilModification hs a b).carrier from
          RealBottChern.ofRepresentative (originalExceptionalMetric hs).form) := by
  rw [movedPencilCartierBDivisor_onModel, movedPencilClass_eq_pullbackH_sub_E]

theorem movedPencilCartierBDivisor_isNefCartier (a b : ℂ) :
    (movedPencilCartierBDivisor hs a b).IsNefCartier :=
  WeilBDivisor.isNefCartier_cartierOf (movedPencilModification hs a b) _
    (polytopeToricKahlerBackground blowupGenerator hs)
    (classNefWithRespectTo_of_semipositive _ (originalPencilFsMetric_isSemipositive hs))

theorem movedPencilCartierBDivisor_isPseudoeffective (a b : ℂ) :
    (movedPencilCartierBDivisor hs a b).IsPseudoeffective := by
  apply (WeilBDivisor.isPseudoeffective_cartierOf_iff
    (movedPencilModification hs a b) _).mpr
  exact ⟨fun _ => (0 : EReal), (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
    (originalPencilFsMetric_isSemipositive hs)⟩

theorem movedPencilCartierBDivisor_volume_zero (a b : ℂ) :
    (movedPencilCartierBDivisor hs a b).vol = 0 := by
  apply le_antisymm _ zero_le
  have h := (movedPencilCartierBDivisor hs a b).vol_le_classVolume
    (movedPencilModification hs a b)
  rw [movedPencilCartierBDivisor_onModel] at h
  change (movedPencilCartierBDivisor hs a b).vol ≤
    sourceClassVolume (RealBottChern.ofRepresentative (originalPencilFsMetric hs).form) at h
  rwa [originalPencil_sourceClassVolume_zero] at h

end SGPT.BDivisor.MovingPencilNext
