import SGPT.NAPotential.DHFlagAllDimensions
import SGPT.NAPotential.BimeroRepresentative

/-! # The Duistermaat–Heckman measure does not depend on the representative of the class

Source `rmk:NApotential:L47` (`chapter_NApotential.tex`), closing sentence (*the constructions
below are independent of the choice of `θ` within its cohomology class*), for the
Duistermaat–Heckman measure `DH(Γ)` of `def:DHm`: if `θ'` is cohomologous to `θ` and
`Γ ∈ PSH^NA(X, θ)_{>0}`, the image `Γ'` of `Γ` in `PSH^NA(X, θ')_{>0}` (the bijection of
`prop:Imodeltestcurveindeptheta`) has `DH(Γ') = DH(Γ)`.

The proof compares slice masses: the flag measure equals the intrinsic measure
`DH.naIntrinsicDuistermaatHeckman`, the Stieltjes measure of `τ ↦ -∫ θ_{Γ_τ}^n`
(`DHSource.naDuistermaatHeckman_eq_intrinsic`, `thm:DHindep`), and the change of representative
preserves every slice mass (`SourceTestCurve.changeRepresentative_realMass`).

## Main results

* `DH.naDHStieltjes_changeRepresentative`, `DH.naIntrinsicDuistermaatHeckman_changeRepresentative`.
* `DHSource.naDuistermaatHeckman_changeRepresentative`: `DH(Γ') = DH(Γ)` for the flag
  definition `def:DHm`, in every dimension.
* `sourcePositiveTestCurveToNA_changeRepresentative`: the identification of
  `PSH^NA(X, θ)_{>0}` with positive `𝓘`-model test curves commutes with the change of
  representative.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.NAPotential

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Okounkov

section Intrinsic

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [ConnectedSpace M] {θ η : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The slice-mass Stieltjes function is unchanged by the change of representative. -/
theorem DH.naDHStieltjes_changeRepresentative (omega omega' : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourcePositiveIModelTestCurve θ) :
    DH.naDHStieltjes omega (sourceIModelTestCurveRepresentativeEquiv omega' hc Γ) =
      DH.naDHStieltjes omega Γ := by
  ext t
  change -sourceTestCurveRealMassAt omega (Γ.val.changeRepresentative omega' hc) t =
    -sourceTestCurveRealMassAt omega Γ.val t
  rw [show sourceTestCurveRealMassAt omega (Γ.val.changeRepresentative omega' hc) =
      sourceTestCurveRealMassAt omega Γ.val from
    Γ.val.changeRepresentative_realMass omega' hc]

/-- The intrinsic Duistermaat–Heckman measure is unchanged by the change of representative. -/
theorem DH.naIntrinsicDuistermaatHeckman_changeRepresentative
    (omega omega' : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourcePositiveIModelTestCurve θ) :
    DH.naIntrinsicDuistermaatHeckman omega (sourceIModelTestCurveRepresentativeEquiv omega' hc Γ) =
      DH.naIntrinsicDuistermaatHeckman omega Γ := by
  unfold DH.naIntrinsicDuistermaatHeckman
  rw [DH.naDHStieltjes_changeRepresentative omega omega' hc Γ]

/-- The identification of `PSH^NA(X, θ)_{>0}` with positive `𝓘`-model test curves commutes with
the change of representative of `rmk:NApotential:L47`. -/
theorem sourcePositiveTestCurveToNA_changeRepresentative (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (Γ : SourcePositiveIModelTestCurve θ) :
    sourcePositiveTestCurveToNA (sourceIModelTestCurveRepresentativeEquiv omega hc Γ) =
      (sourcePositiveTestCurveToNA Γ).changeRepresentative hc := by
  let κ := sourceKahlerFormOfBackground omega
  have hN := (sourcePositiveTestCurveToNA Γ).changeRepresentative_POrder_equivalent omega hc
  have hA := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent
    (sourceIModelTestCurveRepresentativeEquiv omega hc Γ) omega
  have hB := sourcePositiveTestCurveToNA_realizedComponent_POrder_equivalent Γ omega
  have hC := Γ.val.changeRepresentative_POrder_equivalent omega hc
  have hX : SourceNAPOrder (sourcePositiveTestCurveToNA (sourceIModelTestCurveRepresentativeEquiv
      omega hc Γ)) (sourcePositiveTestCurveToNA Γ) := by
    apply (sourceNAPOrder_iff_realizedComponents _ _ omega omega).mpr
    exact SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hA.1 hC.2) hB.2
  have hY : SourceNAPOrder (sourcePositiveTestCurveToNA Γ)
      (sourcePositiveTestCurveToNA (sourceIModelTestCurveRepresentativeEquiv omega hc Γ)) := by
    apply (sourceNAPOrder_iff_realizedComponents _ _ omega omega).mpr
    exact SourceTestCurvePOrder.trans omega (SourceTestCurvePOrder.trans omega hB.1 hC.1) hA.2
  exact SourceNAPOrder.antisymm (hX.trans hN.1) (hN.2.trans hY)

end Intrinsic

section Flag

variable {n : ℕ} (F : OriginalFlagGeometry.{u} n)
  [MeasurableSpace F.carrier] [BorelSpace F.carrier]
  {θ η : AtlasClosedRealOneOneForm (ofFixedModel n F.carrier)}

/-- Source `rmk:NApotential:L47` for `def:DHm`: the Duistermaat–Heckman measure of
`Γ ∈ PSH^NA(X, θ)_{>0}` equals that of its image in `PSH^NA(X, θ')_{>0}` for every cohomologous
representative `θ'` (in every dimension, for the flag definition). -/
theorem DHSource.naDuistermaatHeckman_changeRepresentative (omega : KahlerBackground n F.carrier)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative η))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (Γ : SourcePositiveIModelTestCurve θ) :
    DHSource.naDuistermaatHeckman F (hc ▸ hbig)
        (sourceIModelTestCurveRepresentativeEquiv omega hc Γ) =
      DHSource.naDuistermaatHeckman F hbig Γ := by
  rw [DHSource.naDuistermaatHeckman_eq_intrinsic F omega,
    DHSource.naDuistermaatHeckman_eq_intrinsic F omega]
  exact DH.naIntrinsicDuistermaatHeckman_changeRepresentative omega omega hc Γ

end Flag

end SGPT.NAPotential

end
