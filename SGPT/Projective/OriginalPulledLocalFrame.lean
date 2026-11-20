import SGPT.Projective.OriginalLocalFramePullback

/-! Genuine original local pullback frames on the ACTUAL whole pulled
module-sheaf, with the proved original scalar readers retained.
Blueprint: original-pulled-local-frame.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Opposite

variable {X Y : Scheme.{0}} (f : X ⟶ Y)

/-- A genuine over-site frame of the SAME actual whole pulled sheaf, on
the TRUE original inverse-image open. -/
def matePullbackFrame {L : Y.Modules} {U : Y.Opens} (α : LocalBundleFrame L U) :
    LocalBundleFrame ((Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U) :=
  (Scheme.Modules.overEquiv (f ⁻¹ᵁ U)).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app _ ≪≫
      matePullbackFrameRestriction f U α ≪≫
      (Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app
        (SheafOfModules.unit X.ringCatSheaf)).symm)

/-- The actual native restriction of the SAME manufactured local frame
is EXACTLY the original unit-compatible pulled restricted frame. -/
theorem matePullbackFrame_nativeRestriction {L : Y.Modules} {U : Y.Opens}
    (α : LocalBundleFrame L U) :
    (matePullbackFrame f α).nativeRestriction = matePullbackFrameRestriction f U α := by
  apply Iso.ext
  simp [matePullbackFrame, LocalBundleFrame.nativeRestriction,
    Functor.FullyFaithful.preimageIso, Functor.mapIso]

/-- Actual original atlas pullback: SAME original sheaf pullback, SAME
index set, TRUE inverse-image opens and actual manufactured line frames. -/
def matePullbackAtlas {L : Y.Modules} (a : LineBundleAtlas L) :
    LineBundleAtlas ((Scheme.Modules.pullback f).obj L) where
  I := a.I
  opens i := f ⁻¹ᵁ a.opens i
  covers x := a.covers (f x)
  frame i := matePullbackFrame f (a.frame i)

/-- The genuine original pulled LOCAL frame retains the actual ambient
original section coefficient reader, with every real open transport kept. -/
theorem matePullbackFrame_coefficient {L : Y.Modules} {U : Y.Opens}
    (α : LocalBundleFrame L U) (W : Y.Opens)
    (j : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ⟶ U)
    (k : (f ⁻¹ᵁ U).ι ''ᵁ ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W)) ⟶ f ⁻¹ᵁ U)
    (s : Γ(L, W)) :
    ((f ⁻¹ᵁ U).ι.appIso ((f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W))).hom
      ((matePullbackFrame f α).coefficients k
        (((Scheme.Modules.pullback f).obj L).presheaf.map
          (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ W))).op
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s))) =
      (f ⁻¹ᵁ U).toScheme.presheaf.map (eqToHom (openSquarePreimageEq f U W).symm).op
        ((f ∣_ U).app (U.ι ⁻¹ᵁ W)
          ((U.ι.appIso (U.ι ⁻¹ᵁ W)).hom
            (α.coefficients j (L.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op s)))) := by
  let B := (f ⁻¹ᵁ U).ι ⁻¹ᵁ (f ⁻¹ᵁ W)
  let t := ((Scheme.Modules.pullback f).obj L).presheaf.map
    (homOfLE ((f ⁻¹ᵁ U).ι.image_preimage_le (f ⁻¹ᵁ W))).op
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (.op W) s)
  have hc := nativeRestriction_frame_coefficient (matePullbackFrame f α) B k t
  have he := congrArg (fun e => e.hom.val.app (.op B) t) (matePullbackFrame_nativeRestriction f α)
  exact hc.symm.trans (he.trans (matePullbackFrameRestriction_coefficient f U α W j s))

end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
