import SGPT.Foundations.Schemes.NativeTensorTwistTransport
/-!
# NativeTensorPowerIsoFrames

Actual tensor isomorphisms preserve genuine framed coefficients; recursive actual tensor powers retain this readback. True local pure tensor reconstruction supplies the proof.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {X : Scheme.{u}}

/-- Any actual tensor section of two locally framed lines is recovered from its genuine scalar coefficient. -/
theorem nativeTensorFrame_reconstruct {P Q : X.Modules} {U W : X.Opens}
    (e : LocalBundleFrame P U) (d : LocalBundleFrame Q U) (h : W ⟶ U)
    (s : bundleSections (bundleTensor P Q) W) :
    tensorSection P Q W ((e.coefficients h).symm 1)
      ((d.coefficients h).symm ((e.tensor d).coefficients h s)) = s := by
  apply ((e.tensor d).coefficients h).injective
  rw [LocalBundleFrame.tensor_coefficients, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, one_mul]

/-- Genuine coefficient-preserving line isomorphisms remain coefficient-preserving after the literal sheafified tensor. -/
theorem nativeTensorIso_frame_coefficients {P P' Q Q' : X.Modules}
    (E : P ≅ P') (F : Q ≅ Q') {U : X.Opens}
    (e : LocalBundleFrame P U) (e' : LocalBundleFrame P' U)
    (d : LocalBundleFrame Q U) (d' : LocalBundleFrame Q' U)
    (hE : ∀ (W : X.Opens) (h : W ⟶ U) (s : bundleSections P W),
      e'.coefficients h (E.hom.val.app (.op W) s) = e.coefficients h s)
    (hF : ∀ (W : X.Opens) (h : W ⟶ U) (s : bundleSections Q W),
      d'.coefficients h (F.hom.val.app (.op W) s) = d.coefficients h s)
    {W : X.Opens} (h : W ⟶ U) (s : bundleSections (bundleTensor P Q) W) :
    (e'.tensor d').coefficients h ((bundleTensorIso E F).hom.val.app (.op W) s) =
      (e.tensor d).coefficients h s := by
  have hs := nativeTensorFrame_reconstruct e d h s
  conv_lhs => rw [← hs]
  rw [nativeBundleTensorIso_tensorSection, LocalBundleFrame.tensor_coefficients,
    hE, hF, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, one_mul]

/-- Tensor powers of an actual line isomorphism preserve the literal tensor-power frame coefficients on every subordinate open. -/
theorem nativeTensorPowerIso_frame_coefficients {P Q : X.Modules} (E : P ≅ Q)
    {U : X.Opens} (e : LocalBundleFrame P U) (d : LocalBundleFrame Q U)
    (hE : ∀ (W : X.Opens) (h : W ⟶ U) (s : bundleSections P W),
      d.coefficients h (E.hom.val.app (.op W) s) = e.coefficients h s)
    (m : ℕ) {W : X.Opens} (h : W ⟶ U) (s : bundleSections (bundleTensorPower P m) W) :
    (d.tensorPower m).coefficients h ((nativeLineTensorPowerIso E m).hom.val.app (.op W) s) =
      (e.tensorPower m).coefficients h s := by
  induction m generalizing W with
  | zero => rfl
  | succ m ih =>
      exact nativeTensorIso_frame_coefficients (nativeLineTensorPowerIso E m) E
        (e.tensorPower m) (d.tensorPower m) e d
        (fun W h s ↦ ih h s) hE h s

end
end SGPT.Foundations.Schemes
