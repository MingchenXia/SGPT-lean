import SGPT.Blowup.ContDH
import SGPT.NAPotential.DHGeneralRepresentative
import SGPT.NAPotential.BimeroRepresentative
import SGPT.PSH.SourceNASumAlgebra

/-! # Background change and the flagless Duistermaat–Heckman measure under a change of
representative

Source `rmk:NApotential:L47` (`chapter_NApotential.tex`), closing sentence: *the constructions
below are independent of the choice of `θ` within its cohomology class*. This file treats two
further constructions:

* the general background change `P_{θ+ω}[•]_𝓘 : PSH^NA(X, θ) → PSH^NA(X, θ + ω)` of
  `def:PSHNAtrangeneral` (`SourceNAPotential.backgroundChange`, `ω` a closed smooth semipositive
  form): `backgroundChange_changeRepresentative`, `P_{θ'+ω}[Γ']_𝓘 = (P_{θ+ω}[Γ]_𝓘)'`;
* the Duistermaat–Heckman measure `eq:DHmgeneral` of `X` without a flag
  (`SGPT.Blowup.naDuistermaatHeckmanGeneral`, read on the chosen flag-bearing modification):
  `naDuistermaatHeckmanGeneral_changeRepresentative`, `DH(Γ') = DH(Γ)`.

Here `'` denotes the canonical bijection `PSH^NA(X, θ) ≃ PSH^NA(X, θ')` of the remark
(`SourceNAPotential.changeRepresentative`, on `PSH^NA(X, θ)_{>0}` the bijection
`sourceIModelTestCurveRepresentativeEquiv` of `prop:Imodeltestcurveindeptheta`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.RIsoB

open Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.PSH.VariableComplexAtlas

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Source `rmk:NApotential:L47` for `def:PSHNAtrangeneral`: the background change
`P_{θ+ω}[•]_𝓘` commutes with the change of representative,
`P_{θ'+ω}[Γ']_𝓘 = (P_{θ+ω}[Γ]_𝓘)'` in `PSH^NA(X, θ' + ω)` (with `{θ + ω} = {θ' + ω}`). -/
theorem backgroundChange_changeRepresentative (omega : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))
    (Γ : SourceNAPotential θ) (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    (Γ.changeRepresentative hc).backgroundChange η hη =
      (Γ.backgroundChange η hη).changeRepresentative (sourceNASumBackground_class hc rfl) := by
  have h1 := (Γ.changeRepresentative hc).backgroundChange_POrder_equivalent omega η hη
  have h2 := Γ.changeRepresentative_POrder_equivalent omega hc
  have h3 := Γ.backgroundChange_POrder_equivalent omega η hη
  have h4 := (Γ.backgroundChange η hη).changeRepresentative_POrder_equivalent omega
    (sourceNASumBackground_class hc rfl)
  exact SourceNAPOrder.antisymm
    (h1.2.trans (h2.2.trans (h3.1.trans h4.1)))
    (h4.2.trans (h3.2.trans (h2.1.trans h1.1)))

/-- Source `rmk:NApotential:L47` for `eq:DHmgeneral` (the Duistermaat–Heckman measure of `X`
without a flag, `DH(Γ) = DH(π^*Γ)` on a flag-bearing modification `π`): for
`Γ ∈ PSH^NA(X, θ)_{>0}` and its image `Γ'` in `PSH^NA(X, θ')_{>0}`, `DH(Γ') = DH(Γ)`. -/
theorem naDuistermaatHeckmanGeneral_changeRepresentative (omega omega' : KahlerBackground n M)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))
    (Γ : SourcePositiveIModelTestCurve θ) :
    SGPT.Blowup.naDuistermaatHeckmanGeneral omega
        (sourceIModelTestCurveRepresentativeEquiv omega' hc Γ) =
      SGPT.Blowup.naDuistermaatHeckmanGeneral omega Γ := by
  rw [SGPT.Blowup.naDuistermaatHeckmanGeneral_eq_intrinsic,
    SGPT.Blowup.naDuistermaatHeckmanGeneral_eq_intrinsic]
  exact DH.naIntrinsicDuistermaatHeckman_changeRepresentative omega omega' hc Γ

end SGPT.NAPotential.RIsoB

end
