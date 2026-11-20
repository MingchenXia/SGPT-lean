/-
Copyright (c) 2026. All rights reserved.
-/
import SGPT.Foundations.PublishedEnvelope.ProperBirationalSections

/-! # Original universally closed coefficient integrality from the existing affine-target theorem -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace SGPT.Foundations.PublishedEnvelope.UniversallyClosedSections
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}

/-- The SAME original coefficient RingHom is integral for EVERY universally closed map to an affine base. -/
theorem coefficientMap_isIntegral (f : Y ⟶ Spec (.of R)) [UniversallyClosed f] :
    (ProperBirationalSections.coefficientMap f).IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

end SGPT.Foundations.PublishedEnvelope.UniversallyClosedSections
