import SGPT.Foundations.Schemes.NativePowerResidueComparisonCoherence
import SGPT.Foundations.Schemes.NativeLineProjectionNaturality
import SGPT.Foundations.Schemes.NativePolynomialPullbackTwistComparison
import SGPT.Foundations.Schemes.NativeTwistedSectionActionNaturality

/-!
# Action compatibility for the original polarized residue comparison

The existing polarized residue isomorphism factors through the actual
tensor-power projection comparison. Its literal inverse on global sections
then retains the original line-bundle multiplication.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace SGPT.Foundations.Schemes

universe u
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

private theorem polarizedActionTensorIso_trans {Z : Scheme.{u}} {P Q R M : Z.Modules}
    (E : P ≅ Q) (F : Q ≅ R) :
    bundleTensorIso (E ≪≫ F) (Iso.refl M) =
      bundleTensorIso E (Iso.refl M) ≪≫ bundleTensorIso F (Iso.refl M) := by
  simpa only [Iso.refl_trans] using nativeBundleTensorIso_trans E F (Iso.refl M) (Iso.refl M)

private theorem polarizedActionTensorIso_symm {Z : Scheme.{u}} {P Q M : Z.Modules}
    (E : P ≅ Q) :
    bundleTensorIso E.symm (Iso.refl M) = (bundleTensorIso E (Iso.refl M)).symm := by
  apply Iso.ext
  rfl

private theorem polarizedActionIso_inv_hom_apply {Z : Scheme.{u}} {P Q : Z.Modules}
    (E : P ≅ Q) (U : Z.Opens) (s : bundleSections P U) :
    E.inv.val.app (.op U) (E.hom.val.app (.op U) s) = s :=
  congr($(E.hom_inv_id).val.app (.op U) |>.hom s)

variable {X : Scheme} (L : IntrinsicLineBundle X)
    {K : Type} [Field K] (n : ℕ) (f : X ⟶ polynomialProj K n) (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable (e : bundleTensorPower L.sheaf q ≅
    (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- The existing polarized residue comparison is exactly original residue
regrouping, tensor transport by the given polarization, and inverse actual
tensor-power projection comparison. -/
theorem nativePolarizedResiduePushforwardTensorTwistIso_eq_pullback (m r : ℕ) :
    nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r =
      (Scheme.Modules.pushforward f).mapIso
        (nativeLineTensorPowerResidueIso L.atlas q m r ≪≫
          bundleTensorIso (nativeLineTensorPowerIso e m) (Iso.refl (bundleTensorPower L.sheaf r))) ≪≫
        (nativePolynomialPullbackTwistIso K n f (bundleTensorPower L.sheaf r) m).symm := by
  let M := bundleTensorPower L.sheaf r
  let E := nativePolynomialTwistingPowerIso K n m
  have := nativePolynomialTwistingTensorPowerProjectionMap_isIso K n f m M
  have := nativePolynomialTwistingProjectionMap_isIso f m M
  have hn := nativeSchemeProjectionIso_inv_naturality f E M
  have hc : (Scheme.Modules.pushforward f).mapIso
      (bundleTensorIso ((Scheme.Modules.pullback f).mapIso E) (Iso.refl M)) ≪≫
      (asIso (nativeSchemeProjectionMap f
        (projectiveTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) m) M)).symm ≪≫
      bundleTensorIso E.symm (Iso.refl ((Scheme.Modules.pushforward f).obj M)) =
    (asIso (nativeSchemeProjectionMap f
      (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m) M)).symm := by
    have h := congrArg
      (fun a ↦ a ≪≫ bundleTensorIso E.symm (Iso.refl ((Scheme.Modules.pushforward f).obj M))) hn
    simpa [Iso.trans_assoc, polarizedActionTensorIso_symm] using h
  unfold nativePolarizedResiduePushforwardTensorTwistIso nativePolarizedResiduePushforwardIso
  rw [nativePolarizedLineResidueIso_eq_residue,
    polarizedActionTensorIso_trans, polarizedActionTensorIso_trans]
  simp only [Functor.mapIso_trans, Iso.trans_assoc]
  rw [hc]
  simp [nativePolynomialPullbackTwistIso, polarizedActionTensorIso_symm, M]

/-- The literal inverse of the existing polarized residue map evaluates as
inverse original regrouping after inverse polarization tensor transport. -/
theorem nativePolarizedResiduePushforwardTensorTwistIso_inv_apply (m r : ℕ)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
      ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m) :
    (nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r).inv.val.app (.op ⊤) t =
    L.nativeResidueSection q m r
      ((bundleTensorIso (nativeLineTensorPowerIso e m)
        (Iso.refl (bundleTensorPower L.sheaf r))).inv.val.app (.op ⊤)
        ((nativePolynomialPullbackTwistIso K n f (bundleTensorPower L.sheaf r) m).hom.val.app
          (.op ⊤) t)) := by
  rw [nativePolarizedResiduePushforwardTensorTwistIso_eq_pullback]
  rfl

/-- The inverse of the existing polarized residue comparison intertwines
actual projective twisted action with multiplication in the original line
powers, including the genuine arithmetic identification of their degrees. -/
theorem nativePolarizedResiduePushforwardTensorTwistIso_inv_globalAction (d m r : ℕ)
    (s : bundlePowerGlobalSections (polynomialProjTwistingLine K n).sheaf d)
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
      ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m) :
    HEq ((nativePolarizedResiduePushforwardTensorTwistIso L n f q e (d + m) r).inv.val.app
      (.op ⊤) (atlasTwistedGlobalAction (polynomialProjTwistingLine K n).atlas
        ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) d m s t))
      (atlasPowerGlobalMul L.atlas (q * d) (q * m + r)
        (L.nativePowerSection q d ((nativeLineTensorPowerIso e d).inv.val.app (.op ⊤)
          (nativePolynomialPullbackPowerSection K n f d s)))
        ((nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r).inv.val.app
          (.op ⊤) t)) := by
  let M := bundleTensorPower L.sheaf r
  let A (k : ℕ) := nativeLineTensorPowerIso e k
  let J (k : ℕ) := bundleTensorIso (A k) (Iso.refl M)
  let v := nativePolynomialPullbackPowerSection K n f d s
  let w : bundleTwistedGlobalSections
      ((Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf) M m :=
    (nativePolynomialPullbackTwistIso K n f M m).hom.val.app (.op ⊤) t
  have hn := nativeLineTensorPowerIso_twistedGlobalAction e (L.tensorPower q).atlas
    (nativePolynomialPullbackAtlas K n f) M d m
    ((A d).inv.val.app (.op ⊤) v) ((J m).inv.val.app (.op ⊤) w)
  have hv : (A d).hom.val.app (.op ⊤) ((A d).inv.val.app (.op ⊤) v) = v :=
    polarizedActionIso_inv_hom_apply (A d).symm ⊤ v
  have hw : (J m).hom.val.app (.op ⊤) ((J m).inv.val.app (.op ⊤) w) = w :=
    polarizedActionIso_inv_hom_apply (J m).symm ⊤ w
  change (J (d + m)).hom.val.app (.op ⊤)
      (atlasTwistedGlobalAction (L.tensorPower q).atlas M d m
        ((A d).inv.val.app (.op ⊤) v) ((J m).inv.val.app (.op ⊤) w)) =
    atlasTwistedGlobalAction (nativePolynomialPullbackAtlas K n f) M d m
      ((A d).hom.val.app (.op ⊤) ((A d).inv.val.app (.op ⊤) v))
      ((J m).hom.val.app (.op ⊤) ((J m).inv.val.app (.op ⊤) w)) at hn
  rw [hv, hw] at hn
  have ha : (J (d + m)).inv.val.app (.op ⊤)
      (atlasTwistedGlobalAction (nativePolynomialPullbackAtlas K n f) M d m v w) =
    atlasTwistedGlobalAction (L.tensorPower q).atlas M d m
      ((A d).inv.val.app (.op ⊤) v) ((J m).inv.val.app (.op ⊤) w) := by
    apply (Function.LeftInverse.injective
      (polarizedActionIso_inv_hom_apply (J (d + m)) ⊤))
    exact (polarizedActionIso_inv_hom_apply (J (d + m)).symm ⊤ _).trans hn.symm
  rw [nativePolarizedResiduePushforwardTensorTwistIso_inv_apply,
    nativePolarizedResiduePushforwardTensorTwistIso_inv_apply,
    nativePolynomialPullbackTwistIso_globalAction]
  change HEq (L.nativeResidueSection q (d + m) r
      ((J (d + m)).inv.val.app (.op ⊤)
        (atlasTwistedGlobalAction (nativePolynomialPullbackAtlas K n f) M d m v w)))
    (atlasPowerGlobalMul L.atlas (q * d) (q * m + r)
      (L.nativePowerSection q d ((A d).inv.val.app (.op ⊤) v))
      (L.nativeResidueSection q m r ((J m).inv.val.app (.op ⊤) w)))
  rw [ha]
  exact L.nativeResidueSection_action q d m r _ _

end
end SGPT.Foundations.Schemes
