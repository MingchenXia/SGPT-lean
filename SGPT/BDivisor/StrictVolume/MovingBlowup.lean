import SGPT.Projective.SourcePlaneTranslation
import SGPT.Toric.PointBlowdownMass
import SGPT.Foundations.Analysis.Pending.MarkedIdealBiholomorphism

/-! Genuine translated original point-ideal universal-property blowups. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SGPT.BDivisor.MovingPencilNext

open Set
open SGPT.Projective SGPT.Toric SGPT.Toric.BlowdownDraft
open SGPT.BDivisor.MovingCentresNext
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

def movedBlowupCentre (a b : ℂ) : ComplexProjectiveSpace 2 :=
  pointTranslation a b blowdownOrigin

theorem movedBlowupCentre_affinePoint (a b : ℂ) :
    movedBlowupCentre a b =
      ComplexProjectiveSpace.affinePoint 0 (WithLp.toLp 2 ![a, b]) := by
  have h0 : ComplexProjectiveSpace.affinePoint 0 (0 : ComplexModel 2) = blowdownOrigin := by
    apply (projective_mk_eq_blowdownOrigin_iff _ _).mpr
    constructor <;> simp [ComplexProjectiveSpace.affineLift]
  calc
    _ = pointTranslation a b (ComplexProjectiveSpace.affinePoint 0 (0 : ComplexModel 2)) :=
      congrArg (pointTranslation a b) h0.symm
    _ = _ := by simpa using pointTranslation_affinePoint a b (0 : ComplexModel 2)

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

def movedBlowdown (a b : ℂ) :
    PolytopeToricVariety blowupGenerator hs → ComplexProjectiveSpace 2 :=
  pointTranslation a b ∘ originalBlowdown hs

theorem movedBlowdown_isBlowupAlong (a b : ℂ) :
    IsBlowupAlong 2 ({movedBlowupCentre a b} : Set (ComplexProjectiveSpace 2))
      (movedBlowdown hs a b) := by
  let T := pointTranslation a b
  have h := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
    (projectiveLinearHomeomorph_symm_contMDiff (pointTranslationLinearEquiv a b))
    (pointTranslation_contMDiff a b)
    (fun x => T.symm_apply_apply x) (fun x => T.apply_symm_apply x)
    (originalBlowdown_isBlowupAlong hs)
  have hcentre : T.symm ⁻¹' ({blowdownOrigin} : Set (ComplexProjectiveSpace 2)) =
      {movedBlowupCentre a b} := by
    ext p
    change T.symm p = blowdownOrigin ↔ p = T blowdownOrigin
    constructor
    · intro hp
      exact (T.apply_symm_apply p).symm.trans (congrArg T hp)
    · rintro rfl
      exact T.symm_apply_apply blowdownOrigin
  change IsBlowupAlong 2 (T.symm ⁻¹' ({blowdownOrigin} : Set (ComplexProjectiveSpace 2)))
    (T ∘ originalBlowdown hs) at h
  rw [hcentre] at h
  exact h

def movedPencilModification (a b : ℂ) : Modification 2 (ComplexProjectiveSpace 2) where
  carrier := PolytopeToricVariety blowupGenerator hs
  map := movedBlowdown hs a b
  isAnalyticModification := PrescribedBlowupDomination.isAnalyticModification_of_isBlowupAlong
    (movedBlowdown_isBlowupAlong hs a b)

theorem movedBlowdown_exceptionalFibre (a b : ℂ) :
    {p : PolytopeToricVariety blowupGenerator hs |
      movedBlowdown hs a b p = movedBlowupCentre a b} =
        toricPrimeDivisor (blowupExceptionalRay hs) := by
  calc
    _ = {p : PolytopeToricVariety blowupGenerator hs |
        originalBlowdown hs p = blowdownOrigin} := by
      ext p
      exact (pointTranslation a b).injective.eq_iff
    _ = _ := originalBlowdown_fibre_origin hs

end SGPT.BDivisor.MovingPencilNext
