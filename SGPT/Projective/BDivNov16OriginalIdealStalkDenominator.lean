import SGPT.Projective.BDivNov16FiniteIdealLocalizationClearing
import SGPT.Projective.BDivOriginalIdealStalk
import Mathlib.AlgebraicGeometry.Noetherian

/-! Blueprint first: BDivNov16OriginalIdealStalkDenominator.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.BDivNov16
open AlgebraicGeometry CategoryTheory

theorem originalIdeal_exists_common_denominator_of_stalk_generators
    {X : Scheme.{0}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (x : X) (U : X.affineOpens) (hx : x ∈ U.1) {r : ℕ} (a : Fin r → Γ(X,U))
    (ha : Ideal.span (Set.range fun i => X.presheaf.germ U.1 x hx (a i)) = D.stalkIdeal x) :
    ∃ t : Γ(X,U), x ∈ X.basicOpen t ∧
      ∀ b ∈ D.ideal U, t * b ∈ Ideal.span (Set.range a) := by
  let P := X.presheaf.stalk x
  let : Algebra Γ(X,U) P := (X.presheaf.germ U.1 x hx).hom.toAlgebra
  let Q := U.2.primeIdealOf ⟨x,hx⟩
  let : IsLocalization Q.asIdeal.primeCompl P := U.2.isLocalization_stalk ⟨x,hx⟩
  let : IsNoetherianRing Γ(X,U) := IsLocallyNoetherian.component_noetherian U
  let J := Ideal.span (Set.range a)
  have hmap : (D.ideal U).map (algebraMap Γ(X,U) P) ≤ J.map (algebraMap Γ(X,U) P) := by
    change (D.ideal U).map (X.presheaf.germ U.1 x hx).hom ≤
      (Ideal.span (Set.range a)).map (X.presheaf.germ U.1 x hx).hom
    rw [← D.stalkIdeal_eq_affine x U hx, Ideal.map_span, ← Set.range_comp]
    exact ha.ge
  obtain ⟨t,ht,hall⟩ := finiteIdeal_exists_uniform_localization_denominator
    Q.asIdeal.primeCompl (D.ideal U) J (D.ideal U).fg_of_isNoetherianRing hmap
  refine ⟨t,?_,hall⟩
  have himage : U.2.fromSpec Q ∈ X.basicOpen t := by
    rw [← U.2.fromSpec_image_basicOpen]
    exact ⟨Q,ht,rfl⟩
  simpa only [Q, U.2.fromSpec_primeIdealOf] using himage
end SGPT.Projective.BDivNov16
