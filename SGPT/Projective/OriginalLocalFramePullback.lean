import SGPT.Projective.OriginalFramePullbackCoefficients

/-! Actual ambient-to-local original pullback-unit section square.
Blueprint: original-local-frame-pullback.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

/-- The genuine original square proves the exact equality of the two
actual inverse-image opens. It is never identified by an assumption. -/
theorem openSquarePreimageEq (W : Y.Opens) :
    (f ∣_ U) ⁻¹ᵁ (U.ι ⁻¹ᵁ W) = (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage]

/-- Actual original composite pushforward transports are the original
presheaf transport along the PROVED genuine open equality. -/
theorem openSquarePushforwardCompIso_apply (M : (f ⁻¹ᵁ U).toScheme.Modules)
    (W : Y.Opens)
    (s : Γ((Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι).obj M, W)) :
    ((openSquarePushforwardCompIso f U).hom.app M).val.app (.op W) s =
      M.presheaf.map (eqToHom (openSquarePreimageEq f U W).symm).op s := by
  rfl

/-- The ACTUAL original pullback/restriction isomorphism retains the
actual original section-unit reader on EVERY ambient open and section. -/
theorem openSquarePullbackIso_section (L : Y.Modules) (W : Y.Opens) (s : Γ(L, W)) :
    ((openSquarePullbackIso f U).hom.app L).val.app
        (.op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W)))
      (((Scheme.Modules.pullback f).obj L).presheaf.map
        (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ W))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s)) =
      ((Scheme.Modules.pullback (f ∣_ U)).obj (L.restrict U.ι)).presheaf.map
        (eqToHom (openSquarePreimageEq f U W).symm).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (L.restrict U.ι)).val.app
          (.op (U.ι ⁻¹ᵁ W))
          (L.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op s)) := by
  have H := openSquarePullbackIso_unit f U L
  change ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app
          ((Scheme.Modules.pullback f).obj L))) ≫
      (Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f).map
        ((openSquarePullbackIso f U).hom.app L) =
    ((Scheme.Modules.restrictAdjunction U.ι).unit.app L ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (L.restrict U.ι))) ≫
      (openSquarePushforwardCompIso f U).hom.app
        ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)).obj L) at H
  have h := congrArg (fun γ => γ.val.app (.op W) s) H
  change ((openSquarePullbackIso f U).hom.app L).val.app
      (.op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W)))
      (((Scheme.Modules.pullback f).obj L).presheaf.map
        (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ W))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s)) =
    ((openSquarePushforwardCompIso f U).hom.app
      ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)).obj L)).val.app (.op W)
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (L.restrict U.ι)).val.app
        (.op (U.ι ⁻¹ᵁ W)) (L.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op s)) at h
  exact h.trans (openSquarePushforwardCompIso_apply f U
    ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)).obj L) W _)

/-- The manufactured ACTUAL original local pullback frame reads every
ORIGINAL ambient section through the original scalar pullback. All genuine
open transports are retained explicitly; no coefficient square is input. -/
theorem matePullbackFrameRestriction_coefficient {L : Y.Modules}
    (α : LocalBundleFrame L U) (W : Y.Opens)
    (j : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ⟶ U) (s : Γ(L, W)) :
    (matePullbackFrameRestriction f U α).hom.val.app
        (.op ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W)))
      (((Scheme.Modules.pullback f).obj L).presheaf.map
        (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ W))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s)) =
      (f ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom (openSquarePreimageEq f U W).symm).op
        ((f ∣_ U).app (U.ι ⁻¹ᵁ W)
          ((U.ι.appIso (U.ι ⁻¹ᵁ W)).hom
            (α.coefficients j (L.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op s)))) := by
  let V := U.ι ⁻¹ᵁ W
  let B := (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W)
  let t : Γ(L.restrict U.ι, V) := L.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op s
  let F := globalFramePullback (f ∣_ U) α.nativeRestriction
  let w := ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (L.restrict U.ι)).val.app (.op V) t
  have hc := congrArg (fun z => F.hom.val.app (.op B) z) (openSquarePullbackIso_section f U L W s)
  have hn := PresheafOfModules.naturality_apply F.hom.val
    (eqToHom (openSquarePreimageEq f U W).symm).op w
  have hr := (globalFramePullback_coefficient (f ∣_ U) α.nativeRestriction V t).trans
    (congrArg (fun c => (f ∣_ U).app V c) (nativeRestriction_frame_coefficient α V j t))
  exact hc.trans (hn.trans (congrArg (fun c =>
    (f ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom (openSquarePreimageEq f U W).symm).op c) hr))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
