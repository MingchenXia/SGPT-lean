import SGPT.Foundations.Schemes.NativeProjectiveCoordinateExtension
/-!
# NativeTensorTwistTransport

Literal sheaf isomorphisms transport actual module-twist sections and their true coefficients, using genuine pure tensor reconstruction and actual naturality.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {X : Scheme.{u}}

/-- An actual sheaf isomorphism preserving true line coefficients also preserves the actual arbitrary-module twist coefficients. -/
theorem nativeTensorTwistIso_coefficients {P Q : X.Modules} (E : P ≅ Q)
    {U : X.Opens} (e : LocalBundleFrame P U) (d : LocalBundleFrame Q U)
    (hE : ∀ (W : X.Opens) (h : W ⟶ U) (s : bundleSections P W),
      d.coefficients h (E.hom.val.app (.op W) s) = e.coefficients h s)
    (M : X.Modules) {W : X.Opens} (h : W ⟶ U)
    (s : bundleSections (bundleTensor P M) W) :
    d.tensorModuleCoefficients M h
      ((bundleTensorIso E (Iso.refl M)).hom.val.app (.op W) s) =
      e.tensorModuleCoefficients M h s := by
  have hs := e.tensorModuleCoefficients_reconstruct M h s
  conv_lhs => rw [← hs]
  rw [nativeBundleTensorIso_tensorSection, LocalBundleFrame.tensorModuleCoefficients_tmul,
    hE, LinearEquiv.apply_symm_apply, one_smul]
  rfl

/-- Transporting a true local frame along an actual sheaf isomorphism reads the literal mapped section coefficient. -/
theorem nativeTransportedFrame_coefficients {P Q : X.Modules} (E : P ≅ Q)
    {U W : X.Opens} (d : LocalBundleFrame Q U) (h : W ⟶ U)
    (s : bundleSections P W) :
    (show LocalBundleFrame P U from
      ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso E) ≪≫ d).coefficients h s =
      d.coefficients h (E.hom.val.app (.op W) s) := rfl

/-- Genuine global twist extensions transport through a literal sheaf isomorphism and retain their actual local module coefficient. -/
theorem nativeTensorTwistExtension_transport {P Q M : X.Modules} (E : P ≅ Q)
    {U : X.Opens} (d : LocalBundleFrame Q U) (s : bundleSections M U)
    (t : bundleSections (bundleTensor Q M) ⊤)
    (ht : d.tensorModuleCoefficients M (𝟙 U)
      ((bundleTensor Q M).val.map (homOfLE le_top).op t) = s) :
    ∃ w : bundleSections (bundleTensor P M) ⊤,
      (show LocalBundleFrame P U from
        ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso E) ≪≫ d).tensorModuleCoefficients
        M (𝟙 U) ((bundleTensor P M).val.map (homOfLE le_top).op w) = s := by
  let A := bundleTensorIso E (Iso.refl M)
  let w := A.inv.val.app (.op ⊤) t
  refine ⟨w, ?_⟩
  let e : LocalBundleFrame P U :=
    (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso E ≪≫ d
  have hc := nativeTensorTwistIso_coefficients E e d (fun _ _ _ ↦ rfl) M (𝟙 U)
    ((bundleTensor P M).val.map (homOfLE le_top).op w)
  have hn := PresheafOfModules.naturality_apply A.hom.val (homOfLE (show U ≤ ⊤ from le_top)).op w
  have hi := congrArg (fun a ↦ a.val.app (.op ⊤) t) A.inv_hom_id
  change A.hom.val.app (.op ⊤) w = t at hi
  change A.hom.val.app (.op U) ((bundleTensor P M).val.map (homOfLE le_top).op w) =
    (bundleTensor Q M).val.map (homOfLE le_top).op (A.hom.val.app (.op ⊤) w) at hn
  change d.tensorModuleCoefficients M (𝟙 U)
    (A.hom.val.app (.op U) ((bundleTensor P M).val.map (homOfLE le_top).op w)) = _ at hc
  rw [hn, hi, ht] at hc
  exact hc.symm

end
end SGPT.Foundations.Schemes
