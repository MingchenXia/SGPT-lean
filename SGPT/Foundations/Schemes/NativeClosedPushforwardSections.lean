import SGPT.Foundations.Schemes.ProjectiveChartOverlap
import SGPT.Foundations.Schemes.NativeFanoAlgebraicFiniteness
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Native affine pushforward and actual closed-immersion sections

These producers use the true scheme-module pushforward and actual affine
preimages. Quasicoherence is obtained from the native tilde comparison;
finite modules are obtained from genuine line atlases and quotient rings.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopCat TopologicalSpace

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Genuine affine spectral pushforward preserves actual quasicoherence. -/
theorem specPushforward_isQuasicoherent {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward (Spec.map φ)).obj M).IsQuasicoherent := by
  apply (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr
  exact isIso_fromTildeΓ_pushforward φ M

/-- Actual affine pushforward restrictions are genuine module localizations. -/
theorem specPushforward_sectionRestriction_isLocalized {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (M : (Spec S).Modules) [M.IsQuasicoherent] (r : R) :
    IsLocalizedModule.Away r
      (affineSectionRestriction ((Scheme.Modules.pushforward (Spec.map φ)).obj M) r) := by
  let := specPushforward_isQuasicoherent φ M
  exact affineSectionRestriction_isLocalized _ r

/-- Actual affine inverse images under a genuine closed immersion are affine. -/
theorem closedImmersion_preimage_isAffine {X Y : Scheme.{u}} (i : X ⟶ Y)
    [IsClosedImmersion i] {U : Y.Opens} (hU : IsAffineOpen U) :
    IsAffineOpen (i ⁻¹ᵁ U) :=
  hU.preimage i

/-- A genuine line atlas gives finite actual inverse-image affine sections. -/
theorem closedImmersion_lineSections_finite_over_source {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] {L : X.Modules} (a : LineBundleAtlas L)
    {U : Y.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, i ⁻¹ᵁ U) Γ(L, i ⁻¹ᵁ U) :=
  a.affineOpenSections_finite (hU.preimage i)

/-- A genuine affine quotient ring is finite over the actual ambient affine ring. -/
theorem closedImmersion_affineSections_ringHom_finite {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] {U : Y.Opens} (hU : IsAffineOpen U) :
    (i.app U).hom.Finite :=
  RingHom.Finite.of_surjective _ (i.app_surjective U hU)

/-- Actual affine pushforward line sections are finite over their actual ambient ring. -/
theorem closedImmersion_pushforwardLineSections_finite {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] {L : X.Modules} (a : LineBundleAtlas L)
    {U : Y.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(Y, U) Γ((Scheme.Modules.pushforward i).obj L, U) := by
  let : Algebra Γ(Y, U) Γ(X, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  let : Module.Finite Γ(Y, U) Γ(X, i ⁻¹ᵁ U) :=
    closedImmersion_affineSections_ringHom_finite i hU
  let : Module Γ(X, i ⁻¹ᵁ U) Γ((Scheme.Modules.pushforward i).obj L, U) :=
    inferInstanceAs (Module Γ(X, i ⁻¹ᵁ U) Γ(L, i ⁻¹ᵁ U))
  let : Module.Finite Γ(X, i ⁻¹ᵁ U) Γ((Scheme.Modules.pushforward i).obj L, U) :=
    closedImmersion_lineSections_finite_over_source i a hU
  let : IsScalarTower Γ(Y, U) Γ(X, i ⁻¹ᵁ U)
      Γ((Scheme.Modules.pushforward i).obj L, U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact Module.Finite.trans Γ(X, i ⁻¹ᵁ U) Γ((Scheme.Modules.pushforward i).obj L, U)

end

end SGPT.Foundations.Schemes
