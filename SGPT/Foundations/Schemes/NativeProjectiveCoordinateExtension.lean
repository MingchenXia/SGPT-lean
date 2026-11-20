import SGPT.Foundations.Schemes.NativeProjectivePowerCoordinateFrames
/-!
# NativeProjectiveCoordinateExtension

The true canonical projection map transports actual closed-projective coordinate-chart line sections to global pulled-back projective tensor twists with the original actual module coefficient.
-/

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable (K : Type) [Field K] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A genuine coordinate-chart line section extends to an actual pulled-back projective tensor twist, with its prescribed true coefficient. -/
theorem nativeClosedProjectiveCoordinateSection_pullbackExtension
    {X : Scheme} (f : X ⟶ polynomialProj K n) [IsClosedImmersion f]
    {M : X.Modules} (a : LineBundleAtlas M) (i : Fin (n + 1))
    (s : bundleSections M (f ⁻¹ᵁ polynomialProjCoordinateOpen K n i)) :
    ∃ (d : ℕ) (t : bundleSections (bundleTensor
      ((Scheme.Modules.pullback f).obj (bundleTensorPower (polynomialProjTwistingLine K n).sheaf d)) M) ⊤),
      (nativePolynomialPowerPullbackFrame K n f d i).tensorModuleCoefficients M (𝟙 _)
        ((bundleTensor ((Scheme.Modules.pullback f).obj
          (bundleTensorPower (polynomialProjTwistingLine K n).sheaf d)) M).val.map
            (homOfLE le_top).op t) = s := by
  obtain ⟨d, t, ht⟩ := closedPolynomialProjPushforwardCoordinateSection_twistedGlobalExtension
    K n f a i s
  let P := bundleTensorPower (polynomialProjTwistingLine K n).sheaf d
  let π := nativeSchemeProjectionMap f P M
  let w : bundleSections (bundleTensor ((Scheme.Modules.pullback f).obj P) M) ⊤ :=
    π.val.app (.op ⊤) t
  refine ⟨d, w, ?_⟩
  let U := polynomialProjCoordinateOpen K n i
  have hc := nativeGeneratedLineProjectionMap_coefficients f
    (nativePolynomialPowerCoordinateHom K n d i) U M U (𝟙 _)
    ((bundleTensor P ((Scheme.Modules.pushforward f).obj M)).val.map
      (homOfLE le_top).op t)
  have hn := PresheafOfModules.naturality_apply π.val
    (homOfLE (show U ≤ ⊤ from le_top)).op t
  change π.val.app (.op U)
      ((bundleTensor P ((Scheme.Modules.pushforward f).obj M)).val.map
        (homOfLE le_top).op t) =
    (bundleTensor ((Scheme.Modules.pullback f).obj P) M).val.map
      (homOfLE le_top).op w at hn
  change (nativePullbackGeneratorFrame f (nativePolynomialPowerCoordinateHom K n d i) U).tensorModuleCoefficients M
      ((Opens.map f.base).map (𝟙 U))
      (π.val.app (.op U) ((bundleTensor P ((Scheme.Modules.pushforward f).obj M)).val.map
        (homOfLE le_top).op t)) = _ at hc
  rw [hn, nativePolynomialPowerCoordinateHom_generatorFrame] at hc
  change (nativePolynomialPowerPullbackFrame K n f d i).tensorModuleCoefficients M (𝟙 _)
      ((bundleTensor ((Scheme.Modules.pullback f).obj P) M).val.map (homOfLE le_top).op w) =
    atlasTwistedGlobalCoefficients (polynomialProjTwistingLine K n).atlas
      ((Scheme.Modules.pushforward f).obj M) d i t at hc
  exact hc.trans ht

end
end SGPT.Foundations.Schemes
