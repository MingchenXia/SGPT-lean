import SGPT.Foundations.Schemes.NativePolarizedResidueActionComparison
import SGPT.Foundations.Schemes.NativePositiveProjectiveSectionExtension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (f : X ⟶ polynomialProj K n) (L : IntrinsicLineBundle X) (q : ℕ)
  (e : bundleTensorPower L.sheaf q ≅
    (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- The EXISTING polarized residue comparison followed by the ACTUAL
canonical projection is the original positive-power tensor transport. -/
theorem nativePolarizedResidueTensorTwist_hom_comp_projection (m r : ℕ) :
    (nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r).hom ≫
      nativeSchemeProjectionMap f (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m)
        (bundleTensorPower L.sheaf r) =
      (Scheme.Modules.pushforward f).map
        ((nativeLineTensorPowerAddIso L.atlas (q * m) r ≪≫
          bundleTensorIso (nativePositiveProjectivePowerIso K n f L q e m)
            (Iso.refl (bundleTensorPower L.sheaf r))).hom) := by
  let M := bundleTensorPower L.sheaf r
  let C := nativePolynomialPullbackPowerIso K n f m
  have ht {P Q R : X.Modules} (E : P ≅ Q) (F : Q ≅ R) :
      bundleTensorIso (E ≪≫ F) (Iso.refl M) =
        bundleTensorIso E (Iso.refl M) ≪≫ bundleTensorIso F (Iso.refl M) := by
    simpa only [Iso.refl_trans] using nativeBundleTensorIso_trans E F (Iso.refl M) (Iso.refl M)
  have hs {P Q : X.Modules} (E : P ≅ Q) :
      bundleTensorIso E.symm (Iso.refl M) = (bundleTensorIso E (Iso.refl M)).symm := by
    apply Iso.ext
    rfl
  have hC : nativeLineTensorPowerResidueIso L.atlas q m r ≪≫
      bundleTensorIso (nativeLineTensorPowerIso e m) (Iso.refl M) =
      (nativeLineTensorPowerAddIso L.atlas (q * m) r ≪≫
        bundleTensorIso (nativePositiveProjectivePowerIso K n f L q e m) (Iso.refl M)) ≪≫
          bundleTensorIso C (Iso.refl M) := by
    simp [nativeLineTensorPowerResidueIso_eq_add_mul, nativePositiveProjectivePowerIso,
      ht, hs, C, Iso.trans_assoc]
    rfl
  have := nativePolynomialTwistingTensorPowerProjectionMap_isIso K n f m M
  rw [nativePolarizedResiduePushforwardTensorTwistIso_eq_pullback, hC]
  simp [nativePolynomialPullbackTwistIso, Functor.mapIso_trans, Iso.trans_assoc, M]

/-- On EVERY subordinate projective open, the EXISTING residue inverse
retains the exact residual-module coefficient in the ORIGINAL positive-power
frame after genuine original additive-power regrouping. -/
theorem nativePolarizedResidueTensorTwist_inv_coefficients (m r : ℕ) (i : Fin (n + 1))
    (W : (polynomialProj K n).Opens) (h : W ⟶ polynomialProjCoordinateOpen K n i)
    (t : bundleSections (bundleTensor (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m)
      ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r))) W) :
    (nativePositiveProjectivePowerFrame K n f L q e m i).tensorModuleCoefficients
      (bundleTensorPower L.sheaf r) ((Opens.map f.base).map h)
      ((nativeLineTensorPowerAddIso L.atlas (q * m) r).hom.val.app (.op (f ⁻¹ᵁ W))
        ((nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r).inv.val.app (.op W) t)) =
      (((polynomialProjTwistingLine K n).atlas.frame i).tensorPower m).tensorModuleCoefficients
        ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) h t := by
  let M := bundleTensorPower L.sheaf r
  let A := nativeLineTensorPowerAddIso L.atlas (q * m) r
  let E := nativePositiveProjectivePowerIso K n f L q e m
  let R := nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r
  let s := R.inv.val.app (.op W) t
  have hi : R.hom.val.app (.op W) s = t :=
    congrArg (fun a ↦ a.val.app (.op W) t) R.inv_hom_id
  have hc := congrArg (fun a ↦ a.val.app (.op W) s)
    (nativePolarizedResidueTensorTwist_hom_comp_projection K n f L q e m r)
  change (nativeSchemeProjectionMap f (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m) M).val.app
      (.op W) (R.hom.val.app (.op W) s) =
    (bundleTensorIso E (Iso.refl M)).hom.val.app (.op (f ⁻¹ᵁ W))
      (A.hom.val.app (.op (f ⁻¹ᵁ W)) s) at hc
  rw [hi] at hc
  have ht := nativeTensorTwistIso_coefficients E
    (nativePositiveProjectivePowerFrame K n f L q e m i)
    (nativePolynomialPowerPullbackFrame K n f m i) (fun _ _ _ ↦ rfl)
    M ((Opens.map f.base).map h) (A.hom.val.app (.op (f ⁻¹ᵁ W)) s)
  rw [← hc] at ht
  have hp := nativeGeneratedLineProjectionMap_coefficients f
    (nativePolynomialPowerCoordinateHom K n m i) (polynomialProjCoordinateOpen K n i) M W h t
  rw [nativePolynomialPowerCoordinateHom_generatorFrame] at hp
  exact ht.symm.trans hp

/-- Genuine global sections under the SAME existing inverse have the
exact original positive-power coefficient readback on every original chart,
with actual restrictions and original unit powers retained. -/
theorem nativePolarizedResidueTensorTwist_inv_globalCoefficients (m r : ℕ) (i : Fin (n + 1))
    (t : bundleTwistedGlobalSections (polynomialProjTwistingLine K n).sheaf
      ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m) :
    (nativePositiveProjectivePowerFrame K n f L q e m i).tensorModuleCoefficients
      (bundleTensorPower L.sheaf r) (𝟙 _)
      ((nativeLineTensorPowerAddIso L.atlas (q * m) r).hom.val.app
        (.op (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i))
        ((bundleTensorPower L.sheaf (q * m + r)).val.map (homOfLE le_top).op
          ((nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r).inv.val.app (.op ⊤) t))) =
      atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
        ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m i t := by
  let U := polynomialProjCoordinateOpen K n i
  let P := bundleTensor (bundleTensorPower (polynomialProjTwistingLine K n).sheaf m)
    ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r))
  let Q := bundleTensorPower L.sheaf (q * m + r)
  let R := nativePolarizedResiduePushforwardTensorTwistIso L n f q e m r
  let w := R.inv.val.app (.op ⊤) t
  have hn := PresheafOfModules.naturality_apply R.inv.val U.leTop.op t
  change R.inv.val.app (.op U) (P.val.map U.leTop.op t) =
    Q.val.map (f ⁻¹ᵁ U).leTop.op w at hn
  have hc := nativePolarizedResidueTensorTwist_inv_coefficients K n f L q e m r i U (𝟙 _)
    (P.val.map U.leTop.op t)
  change (nativePositiveProjectivePowerFrame K n f L q e m i).tensorModuleCoefficients
    (bundleTensorPower L.sheaf r) (𝟙 _)
    ((nativeLineTensorPowerAddIso L.atlas (q * m) r).hom.val.app (.op (f ⁻¹ᵁ U))
      (R.inv.val.app (.op U) (P.val.map U.leTop.op t))) =
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
      ((Scheme.Modules.pushforward f).obj (bundleTensorPower L.sheaf r)) m i t at hc
  rw [hn] at hc
  exact hc

end
end SGPT.Foundations.Schemes
