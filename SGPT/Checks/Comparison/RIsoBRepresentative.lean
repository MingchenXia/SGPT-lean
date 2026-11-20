import SGPT.Checks.Comparison.BJExistConsequences
import SGPT.NAPotential.AnTransBimero

/-! # The Boucksom–Jonsson comparison map and the change of representative

Source `rmk:NApotential:L47` (`chapter_NApotential.tex`), closing sentence (*the constructions
below are independent of the choice of `θ` within its cohomology class*), for the comparison map
`eq:analymap`, `PSH^NA(X, θ) → PSH(L^An)`, `Γ ↦ Γ^An` (`SGPT.NAPotential.BJ.Exist.naAnalytification`,
`cor:testcurvegivepshme`): if `θ` and `θ'` are two representatives of `c₁(L)` (given by two smooth
metrics on `L`), the map for `θ'` sends the image `Γ'` of `Γ` under the canonical bijection
`PSH^NA(X, θ) ≃ PSH^NA(X, θ')` to the same psh metric `Γ^An ∈ PSH(L^An)`:
`naAnalytification_changeRepresentative`. Consequently the two comparison maps differ exactly by
the canonical bijection (`naAnalytification_comp_changeRepresentative`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.NAPotential.RIsoB

open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.NAPotential.Berkovich SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.NAPotential.BJ.Exist
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]

local instance rIsoBProper : IsProper f :=
  (ProjectiveFactorizationRingIso.of_isProjective f).isProper

local instance rIsoBPointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance rIsoBPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance rIsoBPointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) {m : ℕ} (hm : 0 < m)

/-- Source `rmk:NApotential:L47` for the comparison map `eq:analymap`: for two smooth metrics on
`L` with curvature representatives `θ`, `θ'` (`{θ} = {θ'}`), the comparison map of `θ'` sends the
image `Γ'` of `Γ ∈ PSH^NA(X, θ)` under the canonical bijection to the same element
`Γ^An ∈ PSH(L^An)` as the comparison map of `θ` sends `Γ`. -/
theorem naAnalytification_changeRepresentative (omega : KahlerBackground n (SchemeComplexPoint f))
    (HM HM' : SchemeLineBundleMetric f n E M)
    {θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    (hθ' : (atlasClosedFormToNative θ').val.GeometricallyEq (((m : ℝ)⁻¹) • HM'.curvature b).val)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) (Γ : SourceNAPotential θ) :
    naAnalytification f n E b HM' hm hθ' ω (Γ.changeRepresentative hc) =
      naAnalytification f n E b HM hm hθ ω Γ := by
  apply Subtype.ext
  funext v
  rw [naAnalytification_apply, naAnalytification_apply]
  exact naPotentialAnAt_changeRepresentative n E omega hc Γ ω v

/-- The comparison maps of two representatives differ by the canonical bijection
`PSH^NA(X, θ) ≃ PSH^NA(X, θ')` of `rmk:NApotential:L47`. -/
theorem naAnalytification_comp_changeRepresentative
    (omega : KahlerBackground n (SchemeComplexPoint f)) (HM HM' : SchemeLineBundleMetric f n E M)
    {θ θ' : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
    (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
    (hθ' : (atlasClosedFormToNative θ').val.GeometricallyEq (((m : ℝ)⁻¹) • HM'.curvature b).val)
    (hc : RealBottChern.ofRepresentative (atlasClosedFormToNative θ) =
      RealBottChern.ofRepresentative (atlasClosedFormToNative θ'))
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    (naAnalytification f n E b HM' hm hθ' ω) ∘ sourceNARepresentativeEquiv hc =
      naAnalytification f n E b HM hm hθ ω :=
  funext fun Γ => naAnalytification_changeRepresentative f n E b hm omega HM HM' hθ hθ' hc ω Γ

end SGPT.NAPotential.RIsoB

end
