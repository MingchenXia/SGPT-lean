import SGPT.Foundations.Schemes.NativePositiveProjectiveSectionExtension
import SGPT.Foundations.Schemes.NativeTensorPowerIsoFrames
import SGPT.Foundations.Schemes.NativeTensorPowerAnyFrame
/-!
# NativePositiveProjectiveFrameNormalization

The actual extension frame coefficient is the genuine positive coordinate-frame power coefficient after the original tensor regrouping. True inverse identities and actual tensor-power readbacks prove the normalization.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} (f : X ⟶ polynomialProj K n) (L : IntrinsicLineBundle X) (q : ℕ)
    (e : bundleTensorPower L.sheaf q ≅
      (Scheme.Modules.pullback f).obj (polynomialProjTwistingLine K n).sheaf)

/-- The actual positive coordinate frame on the original qth line power. -/
def nativePositiveProjectiveCoordinateFrame (i : Fin (n + 1)) :
    LocalBundleFrame (bundleTensorPower L.sheaf q) (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i) :=
  (SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)).mapIso e ≪≫
    (nativePolynomialPullbackAtlas K n f).frame i

/-- The extension frame is exactly normalized by the genuine positive coordinate frame and the original iterated-power comparison. -/
theorem nativePositiveProjectivePowerFrame_coefficients (d : ℕ) (i : Fin (n + 1))
    {W : X.Opens} (h : W ⟶ f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)
    (s : bundleSections (bundleTensorPower L.sheaf (q * d)) W) :
    (nativePositiveProjectivePowerFrame K n f L q e d i).coefficients h s =
      ((nativePositiveProjectiveCoordinateFrame K n f L q e i).tensorPower d).coefficients h
        ((nativeLineTensorPowerMulIso L.atlas q d).hom.val.app (.op W) s) := by
  let A := nativeLineTensorPowerMulIso L.atlas q d
  let B := nativeLineTensorPowerIso e d
  let C := nativePolynomialPullbackPowerIso K n f d
  let z := B.hom.val.app (.op W) (A.hom.val.app (.op W) s)
  have hc := nativePolynomialPullbackPowerIso_coefficients K n f d i h
    (C.inv.val.app (.op W) z)
  have hi := congrArg (fun a ↦ a.val.app (.op W) z) C.inv_hom_id
  change C.hom.val.app (.op W) (C.inv.val.app (.op W) z) = z at hi
  change (((nativePolynomialPullbackAtlas K n f).frame i).tensorPower d).coefficients h
      (C.hom.val.app (.op W) (C.inv.val.app (.op W) z)) =
    (nativePolynomialPowerPullbackFrame K n f d i).coefficients h (C.inv.val.app (.op W) z) at hc
  rw [hi] at hc
  have ht := nativeTensorPowerIso_frame_coefficients e
    (nativePositiveProjectiveCoordinateFrame K n f L q e i)
    ((nativePolynomialPullbackAtlas K n f).frame i) (fun _ _ _ ↦ rfl) d h
    (A.hom.val.app (.op W) s)
  change (nativePolynomialPowerPullbackFrame K n f d i).coefficients h
    (C.inv.val.app (.op W) z) = _
  exact hc.symm.trans ht

end
end SGPT.Foundations.Schemes
