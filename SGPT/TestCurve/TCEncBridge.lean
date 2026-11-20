import SGPT.TestCurve.TCEncZFiltration
import SGPT.NAPotential.NANSTestConfigWeak

/-!
# `rmk:PhongSturm` and `rmk:NApotential:L862` for test configurations

The results `SGPT.TestCurve.GlobalSkoda.phongSturmRemark` (`rmk:PhongSturm`) and
`SGPT.NAPotential.NANS.TestConfig.testConfig_rescaledJumpMeasure_tendsto`,
`testConfig_normalized_tendsto` (`rmk:NApotential:L862`) are stated for finitely generated
normalized `ℤ`-filtrations of `R(X, L)`. Here they are applied to the filtration
`TestConfiguration.zFiltration` induced by a test configuration in the sense of
`SGPT.TestCurve.TCEnc.TestConfiguration` (a flat proper `𝔾_m`-equivariant model over `𝔸¹`),
under the finite-generation hypothesis `FiltrationFinitelyGenerated` (for ample test
configurations, [BHJ17, Prop. 2.15]; not proved here).

## Main results

* `phongSturm_testConfiguration`: for `L` ample with a smooth metric of Kähler curvature and a
  test configuration `(𝓧, 𝓛)` whose filtration is finitely generated, the geodesic ray `Γ^{𝓕*}`
  of the induced filtration is the Phong–Sturm ray: `Γ^{𝓕*}_t = Φ(t)` for `t > 0`.
* `phongSturmRemark_smoothAmple`: the statement of `rmk:PhongSturm` quantified over smooth ample
  equivariant test configurations, with the input not formalized here (finite generation of the
  filtration, [BHJ17, Prop. 2.15]) as a hypothesis.
* `testConfiguration_rescaledJumpMeasure_tendsto`, `testConfiguration_normalized_tendsto`: the
  Duistermaat–Heckman comparison of `rmk:NApotential:L862` for test configurations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.TestCurve.TCEnc

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set Metric SGPT.Okounkov
open SGPT.LineBundle
open SGPT.TestCurve.TestConfig SGPT.TestCurve.GlobalSkoda SGPT.TestCurve.SkodaRWN MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

/-! ### `rmk:PhongSturm` -/

section PhongSturm

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance tcEncPSTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance tcEncPSCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance tcEncPSMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance tcEncPSBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

local instance tcEncPSManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-- **`rmk:PhongSturm` for a test configuration**: let `L` be ample on the integral smooth
projective `X`, `h` a smooth metric with Kähler curvature, `μ = (dd^c φ)^n`, and `(𝓧, 𝓛)` a
test configuration of `(X, L)` whose induced filtration `𝓕` is finitely generated. Then
the geodesic ray `Γ^{𝓕*}` is the Phong–Sturm ray of `(𝓧, 𝓛)` ([RWN14, §9, (9.1)]):
`Γ^{𝓕*}_t = Φ(t)` for all `t > 0` and every choice of adapted orthonormal bases. -/
theorem phongSturm_testConfiguration [IsSeparated f] [QuasiCompact f] [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (T : TestConfiguration f a) (hfg : T.FiltrationFinitelyGenerated E) :
    PhongSturmClaim H (curvatureVolume H a hK) (T.inducedFiltration E hfg) :=
  phongSturmRemark H a P hK (T.zFiltration E) hfg (T.zFiltration_piece_zero_zero E)

/-- **Source `rmk:PhongSturm`, quantified over test configurations**: for `L` ample and `h` with
Kähler curvature, for every smooth ample `𝔾_m`-equivariant test configuration `(𝓧, 𝓛)` of
`(X, L)` with finitely generated induced filtration `𝓕` (finite generation holds for every ample
test configuration by [BHJ17, Prop. 2.15], not proved here), the geodesic ray `Γ^{𝓕*}` is the
Phong–Sturm ray. The equivariance, ampleness and smoothness hypotheses are not used by the
proof. -/
theorem phongSturmRemark_smoothAmple [IsSeparated f] [QuasiCompact f] [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (T : TestConfiguration f a) (_hEq : T.IsGmEquivariant) (_hAmple : T.IsAmple)
    (_hSmooth : T.IsSmooth) (hfg : T.FiltrationFinitelyGenerated E) :
    PhongSturmClaim H (curvatureVolume H a hK) (T.inducedFiltration E hfg) :=
  phongSturm_testConfiguration H a P hK T hfg

end PhongSturm

/-! ### `rmk:NApotential:L862` -/

section DH

open SGPT.NAPotential.NANS.TestConfig
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.PSH.VariableComplexAtlas

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance tcEncDHTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance tcEncDHCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance tcEncDHManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance tcEncDHMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance tcEncDHBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L}
  (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **`rmk:NApotential:L862` for a test configuration**: for a test configuration `(𝓧, 𝓛)` of
`(X, L)` with finitely generated induced filtration `𝓕`, `θ = c₁(L, h)` Kähler (a
Hodge class) and `X` with a smooth flag, the rescaled weight measures `(n!/kⁿ) ν_k` of `𝓕`
converge weakly to the book's Duistermaat–Heckman measure `DH(Γ^𝓕)` of the induced test curve. -/
theorem testConfiguration_rescaledJumpMeasure_tendsto (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j) atTop
      (𝓝 (filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig)) :=
  testConfig_rescaledJumpMeasure_tendsto H Y hY (T.zFiltration E) hfg
    (T.zFiltration_piece_zero_zero E) hK hbig

/-- **`rmk:NApotential:L862` for a test configuration, normalized form**: the normalized rescaled
weight measures `N_k⁻¹ ν_k` (the Duistermaat–Heckman approximations of [BHJ17, §3.2]) converge
weakly to `DH(Γ^𝓕) / DH(Γ^𝓕)(ℝ)`, and the masses `n! N_k / kⁿ` converge to `DH(Γ^𝓕)(ℝ)`. -/
theorem testConfiguration_normalized_tendsto (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => (rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j).normalize)
        atTop (𝓝 (filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig).normalize) ∧
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j).mass)
        atTop (𝓝 (filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig).mass) :=
  testConfig_normalized_tendsto H Y hY (T.zFiltration E) hfg
    (T.zFiltration_piece_zero_zero E) hK hbig

end DH

end SGPT.TestCurve.TCEnc
