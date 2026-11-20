import SGPT.BDivisor.StrictVolume.PencilClassDifference
import SGPT.Toric.PointBlowdownMass
import SGPT.BDivisor.PseudoeffectivePushforward
import SGPT.BDivisor.VolumeBDivisor

/-! The SAME actual fixed point-blowup model and physical nef Cartier b-divisor. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.BDivisor.StrictPencilNext

open SGPT.Toric SGPT.Toric.BlowdownDraft SGPT.Toric.F1IntersectionDraft
open SGPT.Toric.SourceBlowdownMassNext SGPT.Projective
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

def originalPencilModification : Modification 2 (ComplexProjectiveSpace 2) where
  carrier := PolytopeToricVariety blowupGenerator hs
  map := originalBlowdown hs
  isAnalyticModification := originalBlowdown_actualAnalyticModification hs

def originalPencilCartierBDivisor : WeilBDivisor 2 (ComplexProjectiveSpace 2) (by decide) :=
  WeilBDivisor.cartierOf (by decide) (originalPencilModification hs)
    (RealBottChern.ofRepresentative (originalPencilFsMetric hs).form)

theorem originalPencilCartierBDivisor_onModel :
    (originalPencilCartierBDivisor hs).onModel (originalPencilModification hs) =
      RealBottChern.ofRepresentative (originalPencilFsMetric hs).form :=
  (WeilBDivisor.isRealization_cartierOf (originalPencilModification hs) _).onModel_eq

theorem originalPencilCartierBDivisor_onModel_H_sub_E :
    (originalPencilCartierBDivisor hs).onModel (originalPencilModification hs) =
      RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric hs).form -
        RealBottChern.ofRepresentative (originalExceptionalMetric hs).form := by
  rw [originalPencilCartierBDivisor_onModel, originalPencilFsClass_eq_H_sub_E]

theorem originalPencilCartierBDivisor_isNefCartier :
    (originalPencilCartierBDivisor hs).IsNefCartier :=
  WeilBDivisor.isNefCartier_cartierOf (originalPencilModification hs) _
    (polytopeToricKahlerBackground blowupGenerator hs)
    (classNefWithRespectTo_of_semipositive _ (originalPencilFsMetric_isSemipositive hs))

theorem originalPencilCartierBDivisor_isNef :
    (originalPencilCartierBDivisor hs).IsNef :=
  (originalPencilCartierBDivisor_isNefCartier hs).isNef

theorem originalPencilCartierBDivisor_isPseudoeffective :
    (originalPencilCartierBDivisor hs).IsPseudoeffective := by
  apply (WeilBDivisor.isPseudoeffective_cartierOf_iff
    (originalPencilModification hs) _).mpr
  exact ⟨fun _ => (0 : EReal), (LocalPotentials.isThetaPshPotential_zero_iff _).mpr
    (originalPencilFsMetric_isSemipositive hs)⟩

theorem originalPencilCartierBDivisor_volume_zero :
    (originalPencilCartierBDivisor hs).vol = 0 := by
  apply le_antisymm _ zero_le
  have h := (originalPencilCartierBDivisor hs).vol_le_classVolume
    (originalPencilModification hs)
  rw [originalPencilCartierBDivisor_onModel] at h
  change (originalPencilCartierBDivisor hs).vol ≤
    sourceClassVolume (RealBottChern.ofRepresentative (originalPencilFsMetric hs).form) at h
  rwa [originalPencil_sourceClassVolume_zero] at h

/-- Source-only fixed-centre slice. Moving centres and modelwise convergence are separate. -/
theorem sourceOriginalFixedPencil :
    (originalPencilCartierBDivisor blowup_edgeSmooth).IsNefCartier ∧
    (originalPencilCartierBDivisor blowup_edgeSmooth).IsPseudoeffective ∧
    (originalPencilCartierBDivisor blowup_edgeSmooth).vol = 0 ∧
    (originalPencilCartierBDivisor blowup_edgeSmooth).onModel
        (originalPencilModification blowup_edgeSmooth) =
      RealBottChern.ofRepresentative (nativeSourceHyperplaneMetric blowup_edgeSmooth).form -
        RealBottChern.ofRepresentative (originalExceptionalMetric blowup_edgeSmooth).form :=
  ⟨originalPencilCartierBDivisor_isNefCartier _,
    originalPencilCartierBDivisor_isPseudoeffective _,
    originalPencilCartierBDivisor_volume_zero _, originalPencilCartierBDivisor_onModel_H_sub_E _⟩

end SGPT.BDivisor.StrictPencilNext
