import SGPT.Foundations.Schemes.NativeLineTotalSpaceZeroDivisor
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-! # Normality of the actual native affine-line rings and stalks

All rings below are actual structure-sheaf rings. The only base normality
hypothesis is on the genuine affine base global ring; normality of the line
and of its actual stalks is produced by polynomial and localization theorems.
-/

open CategoryTheory AlgebraicGeometry

namespace SGPT.Foundations.Schemes

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual affine stalk is the native localization of the real global ring. -/
def nativeAffineStalkLocalizationEquiv (U : Scheme.{u}) [IsAffine U] (x : U) :
    Localization.AtPrime ((U.isoSpec.hom x).asIdeal) ≃+* U.presheaf.stalk x :=
  ((Spec.stalkIso (.of Γ(U, ⊤)) (U.isoSpec.hom x)).symm ≪≫
    asIso (U.isoSpec.hom.stalkMap x)).commRingCatIsoToRingEquiv

/-- Actual affine stalk domains are produced from the actual affine global domain. -/
theorem nativeAffineStalk_isDomain (U : Scheme.{u}) [IsAffine U]
    [IsDomain Γ(U, ⊤)] (x : U) : IsDomain (U.presheaf.stalk x) :=
  Function.Injective.isDomain (nativeAffineStalkLocalizationEquiv U x).symm
    (nativeAffineStalkLocalizationEquiv U x).symm.injective

/-- Actual affine stalks are integrally closed by genuine prime localization. -/
theorem nativeAffineStalk_isIntegrallyClosed (U : Scheme.{u}) [IsAffine U]
    [IsDomain Γ(U, ⊤)] [IsIntegrallyClosed Γ(U, ⊤)] (x : U) :
    IsIntegrallyClosed (U.presheaf.stalk x) := by
  let p := U.isoSpec.hom x
  have : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (nativeAffineStalkLocalizationEquiv U x)

/-- The genuine one-variable polynomial ring is the actual native affine-line global ring. -/
def nativeAffineLineSinglePolynomialEquiv (U : Scheme.{u}) [IsAffine U] :
    Polynomial Γ(U, ⊤) ≃+* Γ(nativeAffineLine U, ⊤) :=
  (MvPolynomial.uniqueAlgEquiv Γ(U, ⊤) PUnit.{u + 1}).symm.toRingEquiv.trans
    (nativeAffineLinePolynomialEquiv U)

/-- The actual affine-line global ring is a domain over a genuine affine global domain. -/
theorem nativeAffineLineGlobal_isDomain (U : Scheme.{u}) [IsAffine U]
    [IsDomain Γ(U, ⊤)] : IsDomain Γ(nativeAffineLine U, ⊤) :=
  Function.Injective.isDomain (nativeAffineLineSinglePolynomialEquiv U).symm
    (nativeAffineLineSinglePolynomialEquiv U).symm.injective

/-- Polynomial normality produces integral closure of actual affine-line global functions. -/
theorem nativeAffineLineGlobal_isIntegrallyClosed (U : Scheme.{u}) [IsAffine U]
    [IsDomain Γ(U, ⊤)] [IsIntegrallyClosed Γ(U, ⊤)] :
    IsIntegrallyClosed Γ(nativeAffineLine U, ⊤) :=
  IsIntegrallyClosed.of_equiv (nativeAffineLineSinglePolynomialEquiv U)

/-- Every actual native affine-line stalk is a domain under the genuine base hypothesis. -/
theorem nativeAffineLineStalk_isDomain (U : Scheme.{u}) [IsAffine U]
    [IsDomain Γ(U, ⊤)] (x : nativeAffineLine U) :
    IsDomain ((nativeAffineLine U).presheaf.stalk x) := by
  let := nativeAffineLineGlobal_isDomain U
  exact nativeAffineStalk_isDomain (nativeAffineLine U) x

/-- Every actual native affine-line stalk is integrally closed under genuine base normality. -/
theorem nativeAffineLineStalk_isIntegrallyClosed (U : Scheme.{u}) [IsAffine U]
    [IsDomain Γ(U, ⊤)] [IsIntegrallyClosed Γ(U, ⊤)] (x : nativeAffineLine U) :
    IsIntegrallyClosed ((nativeAffineLine U).presheaf.stalk x) := by
  let := nativeAffineLineGlobal_isDomain U
  let := nativeAffineLineGlobal_isIntegrallyClosed U
  exact nativeAffineStalk_isIntegrallyClosed (nativeAffineLine U) x

/-- Actual open-immersion stalk maps transfer the produced affine-line domains
to every real total-space point covered by a genuine affine framed chart. -/
theorem nativeDualLineStalk_isDomain {X : Scheme.{u}} {L : X.Modules}
    (a : LineBundleAtlas L)
    (hD : ∀ c : NativeFramedOpen a, IsAffine c.2.1.toScheme → Nonempty c.2.1.toScheme →
      IsDomain Γ(c.2.1.toScheme, ⊤)) (x : nativeDualLineTotalSpace a) :
    IsDomain ((nativeDualLineTotalSpace a).presheaf.stalk x) := by
  obtain ⟨c, hc, y, rfl⟩ := nativeDualLine_affineFramedChart_cover a x
  let : IsAffine c.2.1.toScheme := hc
  have hn : Nonempty c.2.1.toScheme := ⟨nativeAffineLineProjection c.2.1.toScheme y⟩
  let := hD c hc hn
  let := nativeAffineLineStalk_isDomain c.2.1.toScheme y
  let e := (asIso ((nativeFramedChart a c).stalkMap y)).commRingCatIsoToRingEquiv
  exact Function.Injective.isDomain e e.injective

/-- Actual total-space stalk integral closure is derived from real affine base
normality, actual polynomial normality and native open-immersion stalk maps. -/
theorem nativeDualLineStalk_isIntegrallyClosed {X : Scheme.{u}} {L : X.Modules}
    (a : LineBundleAtlas L)
    (hD : ∀ c : NativeFramedOpen a, IsAffine c.2.1.toScheme → Nonempty c.2.1.toScheme →
      IsDomain Γ(c.2.1.toScheme, ⊤))
    (hN : ∀ c : NativeFramedOpen a, IsAffine c.2.1.toScheme → Nonempty c.2.1.toScheme →
      IsIntegrallyClosed Γ(c.2.1.toScheme, ⊤)) (x : nativeDualLineTotalSpace a) :
    IsIntegrallyClosed ((nativeDualLineTotalSpace a).presheaf.stalk x) := by
  obtain ⟨c, hc, y, rfl⟩ := nativeDualLine_affineFramedChart_cover a x
  let : IsAffine c.2.1.toScheme := hc
  have hn : Nonempty c.2.1.toScheme := ⟨nativeAffineLineProjection c.2.1.toScheme y⟩
  let := hD c hc hn
  let := hN c hc hn
  let := nativeAffineLineStalk_isIntegrallyClosed c.2.1.toScheme y
  exact IsIntegrallyClosed.of_equiv
    (asIso ((nativeFramedChart a c).stalkMap y)).symm.commRingCatIsoToRingEquiv

end

end SGPT.Foundations.Schemes
