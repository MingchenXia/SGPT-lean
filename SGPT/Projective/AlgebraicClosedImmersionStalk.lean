import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Localization.Algebra

/-! The ACTUAL closed-immersion stalk kernel from the SAME actual affine
kernel and SAME actual original germ maps. No quotient certificate input.
Blueprint: algebraic-section-zero-stalk.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.AlgebraicCurveDegree
open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped nonZeroDivisors

/-- The actual original stalk kernel of a closed immersion is the actual
original affine kernel extended by the SAME actual original germ map. -/
theorem closedImmersion_stalk_kernel {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsClosedImmersion f]
    (U : Y.Opens) (hU : IsAffineOpen U) (x : X) (hx : f x ∈ U) :
    RingHom.ker (f.stalkMap x).hom =
      (RingHom.ker (f.app U).hom).map (Y.presheaf.germ U (f x) hx).hom := by
  let W := f ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage f
  let R := Γ(Y, U)
  let S := Γ(X, W)
  let A := Y.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let r : R →+* S := (f.app U).hom
  let tau : A →+* B := (f.stalkMap x).hom
  let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨f x, hx⟩ : U)
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hx⟩ : W)
  let p : Ideal R := (hU.primeIdealOf ⟨f x, hx⟩).asIdeal
  let q : Ideal S := (hW.primeIdealOf ⟨x, (hx : x ∈ W)⟩).asIdeal
  let : p.IsPrime := inferInstance
  let : q.IsPrime := inferInstance
  let : IsLocalization.AtPrime A p := hU.isLocalization_stalk ⟨f x, hx⟩
  let : IsLocalization.AtPrime B q := hW.isLocalization_stalk ⟨x, (hx : x ∈ W)⟩
  have hr : Function.Surjective r := f.app_surjective U hU
  have hsquare (t : R) : tau (algebraMap R A t) = algebraMap S B (r t) :=
    f.germ_stalkMap_apply U x hx t
  have hp : q.comap r = p := by
    ext t
    rw [Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff B q,
      ← IsLocalization.AtPrime.to_map_mem_maximal_iff A p]
    rw [← hsquare]
    change algebraMap R A t ∈ (maximalIdeal B).comap tau ↔ algebraMap R A t ∈ maximalIdeal A
    rw [IsLocalRing.maximalIdeal_comap tau]
  have hM : p.primeCompl.map r = q.primeCompl := by
    simpa only [hp] using (Ideal.map_primeCompl_comap_of_surjective r hr q)
  let rho : A →+* B := IsLocalization.map (M := p.primeCompl) (T := q.primeCompl) B r
    (hM.symm ▸ p.primeCompl.le_comap_map)
  have htau : tau = rho := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext t
    change tau (algebraMap R A t) = rho (algebraMap R A t)
    rw [hsquare, IsLocalization.map_eq]
  change RingHom.ker tau = (RingHom.ker r).map (algebraMap R A)
  rw [htau]
  exact IsLocalization.ker_map (S := A) B r hM

end SGPT.Projective.NumEq.AlgebraicCurveDegree
