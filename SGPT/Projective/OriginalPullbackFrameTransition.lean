import SGPT.Projective.OriginalPullbackScalarSquare

/-! ANY original local frame: literal actual original pulled section
coefficients and overlap transition units, with no comparison premise.
Blueprint: original-pullback-frame-transition.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {L : Y.Modules}

/-- The SAME actual pulled LOCAL frame reads the ACTUAL original unit
pullback of every original local section as the ORIGINAL structural scalar
pullback of its SAME original coefficient. No coefficient square input. -/
theorem matePullbackFrame_coefficient_simple {U W : Y.Opens}
    (α : LocalBundleFrame L U) (j : W ⟶ U) (s : Γ(L, W)) :
    (matePullbackFrame f α).coefficients ((TopologicalSpace.Opens.map f.base).map j)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s) =
        f.app W (α.coefficients j s) := by
  let V := U.ι ⁻¹ᵁ W
  let A := U.ι ''ᵁ V
  let B := (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W)
  let T := (f ⁻¹ᵁ U).ι ''ᵁ B
  let hAW : A ⟶ W := homOfLE (U.ι.image_preimage_le W)
  let hTW : T ⟶ f ⁻¹ᵁ W := homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ W))
  let jA : A ⟶ U := homOfLE (U.ι_image_le V)
  let kT : T ⟶ f ⁻¹ᵁ U := homOfLE ((f ⁻¹ᵁ U).ι_image_le B)
  let η := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s
  have hR : α.coefficients jA (L.presheaf.map hAW.op s) =
      Y.presheaf.map hAW.op (α.coefficients j s) := α.coefficients_restrict j hAW s
  have hleft := matePullbackFrame_coefficient f α W jA kT s
  have hr := congrArg (fun c => (f ⁻¹ᵁ U).toScheme.presheaf.map
    (eqToHom (openSquarePreimageEq f U W).symm).op
      ((f ∣_ U).app V ((U.ι.appIso V).hom c))) hR
  have hright := hleft.trans (hr.trans (originalPullbackScalar_square f U W (α.coefficients j s)))
  have hL : (matePullbackFrame f α).coefficients kT
      (((Scheme.Modules.pullback f).obj L).presheaf.map hTW.op η) =
      X.presheaf.map hTW.op
        ((matePullbackFrame f α).coefficients ((TopologicalSpace.Opens.map f.base).map j) η) :=
    (matePullbackFrame f α).coefficients_restrict _ hTW η
  have hcomp := (congrArg (fun c => ((f ⁻¹ᵁ U).ι.appIso B).hom c) hL).symm.trans hright
  have hh := ((f ⁻¹ᵁ U).ι.appIso B).commRingCatIsoToRingEquiv.injective hcomp
  have hTeq : T = f ⁻¹ᵁ W := by
    apply le_antisymm ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ W))
    intro x hx
    exact ⟨⟨x, (leOfHom j) hx⟩, hx, rfl⟩
  have hArrow : hTW = eqToHom hTeq := Subsingleton.elim _ _
  let : IsIso hTW := by rw [hArrow]; infer_instance
  exact (asIso (X.presheaf.map hTW.op)).commRingCatIsoToRingEquiv.injective hh

/-- TRUE original regular transition units of the SAME actual pulled
frames equal the ORIGINAL structural pullback of the ORIGINAL units on
EVERY genuine overlap, with no transition comparison premise. -/
theorem matePullbackFrame_transition {U V W : Y.Opens}
    (α : LocalBundleFrame L U) (β : LocalBundleFrame L V) (i : W ⟶ U) (j : W ⟶ V) :
    (localBundleFrameTransition (matePullbackFrame f α) (matePullbackFrame f β)
      ((TopologicalSpace.Opens.map f.base).map i) ((TopologicalSpace.Opens.map f.base).map j)).val =
      f.app W (localBundleFrameTransition α β i j).val := by
  let s : Γ(L, W) := (α.coefficients i).symm 1
  let t := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s
  have hs : α.coefficients i s = 1 := (α.coefficients i).apply_symm_apply 1
  have ha : (matePullbackFrame f α).coefficients ((TopologicalSpace.Opens.map f.base).map i) t = 1 := by
    have h := matePullbackFrame_coefficient_simple f α i s
    exact h.trans ((congrArg (f.app W) hs).trans (map_one _))
  have hb := matePullbackFrame_coefficient_simple f β j s
  have ht := localBundleFrameTransition_coefficients (matePullbackFrame f α) (matePullbackFrame f β)
    ((TopologicalSpace.Opens.map f.base).map i) ((TopologicalSpace.Opens.map f.base).map j) t
  rw [ha, mul_one] at ht
  have ho := localBundleFrameTransition_coefficients α β i j s
  rw [hs, mul_one] at ho
  exact ht.symm.trans (hb.trans (congrArg (f.app W) ho))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
