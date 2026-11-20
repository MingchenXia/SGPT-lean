import SGPT.Support.Alterations.Modification
import SGPT.Support.Alterations.Geometry.BlowupAlteration
import SGPT.Support.Alterations.Geometry.BlowupComplement

/-! # The actual global blowup as a modification -/

open AlgebraicGeometry CategoryTheory

namespace SGPT.Support.Alterations.Geometry.BlowupModification

universe u

open BlowupGluing

/-- The native global blowup in a proper-support ideal is a modification. -/
theorem blowupStructure_isModification {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (D : X.IdealSheafData) (hD : D.support ≠ ⊤) :
    IsModification (blowupStructure D) := by
  let := BlowupAlteration.blowupStructure_isProper D
  exact {
    sourceIntegral := BlowupIntegral.isIntegral_blowup D hD
    targetIntegral := inferInstance
    birational := BlowupComplement.blowupStructure_birationalOver D hD }

end SGPT.Support.Alterations.Geometry.BlowupModification
