import SGPT.NAPotential.BerkovichIdealValue
import SGPT.Projective.AlgebraicClosedImmersionStalk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable {X : Scheme.{0}}

/-- The actual ideal of affine section germs on the original scheme. -/
abbrev stalkIdeal (I : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  SGPT.NAPotential.Berkovich.stalkIdeal I x

private theorem affineImage_of_le (I : X.IdealSheafData) {U V : X.affineOpens}
    (e : U ≤ V) (x : X) (hx : x ∈ U.1) :
    (I.ideal U).map (X.presheaf.germ U.1 x hx).hom =
      (I.ideal V).map (X.presheaf.germ V.1 x (e hx)).hom := by
  rw [← I.map_ideal e, Ideal.map_map, ← CommRingCat.hom_comp]
  have hcomp : X.presheaf.map (homOfLE e).op ≫ X.presheaf.germ U.1 x hx =
      X.presheaf.germ V.1 x (e hx) :=
    X.presheaf.germ_res (homOfLE (show U.1 ≤ V.1 from e)) x hx
  exact congrArg (fun k : Γ(X, V.1) ⟶ X.presheaf.stalk x => (I.ideal V).map k.hom) hcomp

/-- Any affine open containing the point computes the same stalk ideal. -/
theorem stalkIdeal_eq_affine (I : X.IdealSheafData) (x : X) (U : X.affineOpens)
    (hx : x ∈ U.1) : I.stalkIdeal x = (I.ideal U).map (X.presheaf.germ U.1 x hx).hom := by
  unfold stalkIdeal SGPT.NAPotential.Berkovich.stalkIdeal
  refine le_antisymm (iSup_le fun V => iSup_le fun hv => ?_)
    (le_iSup_of_le U (le_iSup_of_le hx le_rfl))
  obtain ⟨W, hW, hxW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := U.1 ⊓ V.1) (x := x) ⟨hx, hv⟩
  let A : X.affineOpens := ⟨W, hW⟩
  exact ((affineImage_of_le I (U := A) (V := V) (hWUV.trans inf_le_right) x hxW).symm.trans
    (affineImage_of_le I (U := A) (V := U) (hWUV.trans inf_le_left) x hxW)).le

/-- The closed subscheme map has exactly this kernel at each original stalk. -/
theorem ker_stalkMap_subschemeι (I : X.IdealSheafData) (z : I.subscheme) :
    RingHom.ker (I.subschemeι.stalkMap z).hom = I.stalkIdeal (I.subschemeι z) := by
  obtain ⟨U, hx⟩ := SGPT.NAPotential.Berkovich.exists_affineOpen_mem (I.subschemeι z)
  rw [SGPT.Projective.NumEq.AlgebraicCurveDegree.closedImmersion_stalk_kernel
    I.subschemeι U.1 U.2 z hx, I.ker_subschemeι_app U, I.stalkIdeal_eq_affine _ U hx]

end

end AlgebraicGeometry.Scheme.IdealSheafData
