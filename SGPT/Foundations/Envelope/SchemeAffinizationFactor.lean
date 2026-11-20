/-
Copyright (c) 2026. All rights reserved.
-/
import SGPT.Foundations.Envelope.ProperBirationalSections

/-! # Whole original affinization coefficient identities and actual proper cancellation -/
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace SGPT.Foundations.Envelope.SchemeAffinizationFactor
variable {R : Type u} [CommRing R] {Y : Scheme.{u}}

/-- The ORIGINAL coefficient Spec morphism, with the SAME whole global-section ring. -/
abbrev coefficientProjection (f : Y ⟶ Spec (.of R)) : Spec Γ(Y,⊤) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (ProperBirationalSections.coefficientMap f))

/-- The ACTUAL canonical affinization retains the ENTIRE original affine-base scheme morphism. -/
theorem toSpecΓ_comp_coefficientProjection (f : Y ⟶ Spec (.of R)) :
    Y.toSpecΓ ≫ coefficientProjection f=f := by
  change Y.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop)=f
  rw [Spec.map_comp,← Category.assoc,← Scheme.toSpecΓ_naturality,Category.assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv,Category.comp_id]

/-- The WHOLE original canonical coefficient RingHom is literally identity on EVERY global section. -/
theorem coefficientMap_toSpecΓ :
    ProperBirationalSections.coefficientMap Y.toSpecΓ=RingHom.id Γ(Y,⊤) := by
  unfold ProperBirationalSections.coefficientMap
  rw [Scheme.toSpecΓ_appTop,Iso.inv_hom_id]
  rfl

/-- Actual original properness and genuine separated cancellation DERIVE properness of the SAME canonical map. -/
theorem isProper_toSpecΓ (f : Y ⟶ Spec (.of R)) [IsProper f] : IsProper Y.toSpecΓ := by
  have : IsProper (Y.toSpecΓ ≫ coefficientProjection f) := by
    rw [toSpecΓ_comp_coefficientProjection]
    infer_instance
  exact IsProper.of_comp Y.toSpecΓ (coefficientProjection f)

end SGPT.Foundations.Envelope.SchemeAffinizationFactor
