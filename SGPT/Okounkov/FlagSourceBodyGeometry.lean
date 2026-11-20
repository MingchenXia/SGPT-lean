import SGPT.Okounkov.FlagBiholomorphicLifting
import SGPT.Okounkov.SourceSliceCorrection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Okounkov.ToricTransport
open Set
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH SGPT.PSH.VariableComplexAtlas

/-- The genuine source general body0 is its original perturbation/approximation
construction, with its proved actual carrier. -/
theorem sourceGeneralBody_zero_eq_univ (F : OriginalFlagGeometry.{u} 0)
    {θ : ClosedRealOneOneForm 0 F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) :
    SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩ = univ := by
  change ZeroSource.generalBody F θ φ hφ = univ
  rw [ZeroSource.generalBody_eq_partial, ZeroSource.partialOkounkovBody_eq_univ F hφ]

/-- The SAME actual source body is unchanged under genuine tensor geometric
equality on the SAME carrier, in every dimension and with PSH produced internally. -/
theorem sourceGeneralBody_geometricallyEq {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ η : ClosedRealOneOneForm n F.carrier} (hgeo : η.val.GeometricallyEq θ.val)
    {φ : F.carrier → EReal} (hφ : IsThetaPshPotential θ.val φ) :
    SourceTestCurveAllDimensions.generalBody F η ⟨φ,(hgeo.thetaPshPotential_iff φ).mpr hφ⟩ =
      SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩ := by
  cases n with
  | zero => rw [sourceGeneralBody_zero_eq_univ, sourceGeneralBody_zero_eq_univ]
  | succ m => exact SourceSlice.generalPartialBody_eq_of_geometricallyEq F hgeo hφ

/-- Actual native strong theta-PSH produces the original source QPSH,
with the SAME full native tensor, not a supplied local-potential certificate. -/
theorem sourceQPSH_of_native_thetaPsh {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ : ClosedRealOneOneForm n F.carrier} {φ : F.carrier → EReal}
    (hφ : IsThetaPshPotential θ.val φ) : (ofFixedModel n F.carrier).IsQPSH φ := by
  refine ⟨nativeClosedFormToAtlas θ, ?_⟩
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  have hr : atlasClosedFormToNative (nativeClosedFormToAtlas θ) = θ := by
    rcases θ with ⟨β,hβ⟩
    cases β
    rfl
  rw [hr]
  exact hφ

/-- Actual equality of the source form and potential preserves the SAME
source body, including its genuine0-dimensional construction. -/
theorem sourceGeneralBody_congr {n : ℕ} (F : OriginalFlagGeometry.{u} n)
    {θ η : ClosedRealOneOneForm n F.carrier} {φ ψ : F.carrier → EReal}
    (hθ : θ = η) (hφψ : φ = ψ)
    (hφ : IsThetaPshPotential θ.val φ) (hψ : IsThetaPshPotential η.val ψ) :
    SourceTestCurveAllDimensions.generalBody F θ ⟨φ,hφ⟩ =
      SourceTestCurveAllDimensions.generalBody F η ⟨ψ,hψ⟩ := by
  subst η
  subst ψ
  rfl

end SGPT.Okounkov.ToricTransport
