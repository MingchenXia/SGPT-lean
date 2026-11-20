import SGPT.Projective.OriginalPulledLocalFrame

/-! Actual original regular-function scalar square on genuine open
restrictions. Blueprint: original-pullback-scalar-square.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite

/-- The actual restricted morphism's scalar pullback is the SAME original
whole pullback/restriction, with genuine open transports and scalar ring
isomorphisms explicit. No scalar or map equality comparison premise. -/
theorem originalPullbackScalar_square {X Y : Scheme.{0}} (f : X ⟶ Y)
    (U W : Y.Opens) (r : Γ(Y, W)) :
    (f ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom (openSquarePreimageEq f U W).symm).op
      ((f ∣_ U).app (U.ι ⁻¹ᵁ W)
        ((U.ι.appIso (U.ι ⁻¹ᵁ W)).hom
          (Y.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op r))) =
      ((f ⁻¹ᵁ U).ι.appIso ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W))).hom
        (X.presheaf.map (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ W))).op
          (f.app W r)) := by
  let V := U.ι ⁻¹ᵁ W
  let A := U.ι ''ᵁ V
  let B := (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W)
  let hAW : A ⟶ W := homOfLE (U.ι.image_preimage_le W)
  let hTW := homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ W))
  let δ := (f ⁻¹ᵁ U).ι.opensFunctor.map (eqToHom (openSquarePreimageEq f U W).symm)
  have hs : (f ∣_ U).app V (Y.presheaf.map hAW.op r) =
      X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op
        (f.app A (Y.presheaf.map hAW.op r)) :=
    congrArg (fun γ => γ (Y.presheaf.map hAW.op r)) (morphismRestrict_app f U V)
  have hn : f.app A (Y.presheaf.map hAW.op r) =
      X.presheaf.map ((TopologicalSpace.Opens.map f.base).map hAW).op (f.app W r) :=
    congrArg (fun γ => γ r) (f.naturality hAW.op)
  rw [Scheme.Opens.ι_appIso, Scheme.Opens.ι_appIso]
  change (f ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom (openSquarePreimageEq f U W).symm).op
      ((f ∣_ U).app V (Y.presheaf.map hAW.op r)) =
    X.presheaf.map hTW.op (f.app W r)
  refine (congrArg (fun c => (f ⁻¹ᵁ U).toScheme.presheaf.map
    (eqToHom (openSquarePreimageEq f U W).symm).op c) hs).trans ?_
  refine (congrArg (fun c => (f ⁻¹ᵁ U).toScheme.presheaf.map
    (eqToHom (openSquarePreimageEq f U W).symm).op
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op c)) hn).trans ?_
  change ((X.presheaf.map ((TopologicalSpace.Opens.map f.base).map hAW).op ≫
    X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op ≫
      X.presheaf.map δ.op).hom) (f.app W r) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun h => (X.presheaf.map h).hom (f.app W r)) (Subsingleton.elim _ _)

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
