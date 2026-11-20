import SGPT.TestCurve.TCLinAmple

/-!
# `rmk:PhongSturm` and `rmk:NApotential:L862` for ample linearized test configurations

Source: `rmk:PhongSturm` (chapter *Test curves*: *"Suppose that `L` is ample and `𝓕` is the
filtration induced by a smooth test configuration `(𝓧, 𝓛)` of `(X, L)`. Then the geodesic ray
`Γ^{𝓕*}` is exactly the Phong–Sturm geodesic ray associated with `(𝓧, 𝓛)`."*) and
`rmk:NApotential:L862` (chapter *Non-Archimedean pluripotential theory*: *"When `{θ}` is a Hodge
class and `Γ` is induced by a test configuration as in `ex:RWN` and `rmk:PhongSturm`, our
Duistermaat–Heckman measure coincides with the more traditional definition of [BHJ17, §3.2]."*).

Lane TC-ENC proved both statements for test configurations whose induced filtration is finitely
generated; lane FG-REL discharged finite generation for test configurations given in Donaldson's
equivariant-coordinates form. Here the test configurations are those of [BHJ17, Def. 2.1–2.3]:
`LinearizedTestConfiguration` (a test configuration with its `𝔾_m`-action and a
`𝔾_m`-linearization of `𝓛`) which is ample (`TCEnc.TestConfiguration.IsAmple`: a power `𝓛^r` is
relatively very ample, `𝓛^r ≅ ι^* 𝒪(1)` with `(ι, π) : 𝓧 ↪ ℙᴺ × 𝔸¹` a closed immersion). Finite
generation is `LinearizedTestConfiguration.filtrationFinitelyGenerated` ([BHJ17, Prop. 2.15]).

## Main results

* `phongSturm_linearized`, `phongSturmRemark_linearized`: `rmk:PhongSturm`.
* `linearized_rescaledJumpMeasure_tendsto`, `linearized_normalized_tendsto`:
  `rmk:NApotential:L862`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.TCLin

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Opposite
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TCEnc

/-! ### `rmk:PhongSturm` -/

section PhongSturm

open Filter Set Metric SGPT.Okounkov MeasureTheory
open SGPT.TestCurve.GlobalSkoda SGPT.TestCurve.SkodaRWN
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance tcLinPSTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance tcLinPSCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance tcLinPSMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance tcLinPSBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

local instance tcLinPSManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-- **`rmk:PhongSturm` for ample test configurations** ([BHJ17, Def. 2.1–2.3]): for `L` ample on
the integral smooth projective `X`, `h` with Kähler curvature, `μ = (dd^c φ)^n` and `(𝓧, 𝓛)` an
ample test configuration of `(X, L)` with a `𝔾_m`-linearized `𝓛`, the geodesic ray `Γ^{𝓕*}` of
the induced filtration is the Phong–Sturm ray of [RWN14, (9.1)]: `Γ^{𝓕*}_t = Φ(t)` for all
`t > 0` and every choice of adapted orthonormal bases. -/
theorem phongSturm_linearized [IsSeparated f] [QuasiCompact f] [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (T : LinearizedTestConfiguration f a) (hA : T.IsAmple) :
    PhongSturmClaim H (curvatureVolume H a hK)
      (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) :=
  phongSturm_testConfiguration H a P hK T.toTestConfiguration _

/-- **Source `rmk:PhongSturm`, quantified over smooth ample test configurations**: for `L` ample
and `h` with Kähler curvature, for every smooth ample test configuration `(𝓧, 𝓛)` of `(X, L)` in
the sense of [BHJ17, Def. 2.1–2.3] (`𝔾_m`-action, `𝔾_m`-linearized `𝓛`), the geodesic ray
`Γ^{𝓕*}` of the induced filtration `𝓕` is the Phong–Sturm ray. Smoothness of `𝓧` is not used by
the proof. -/
theorem phongSturmRemark_linearized [IsSeparated f] [QuasiCompact f] [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (T : LinearizedTestConfiguration f a) (hA : T.IsAmple) (_hSmooth : T.IsSmooth) :
    PhongSturmClaim H (curvatureVolume H a hK)
      (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) :=
  phongSturm_linearized H a P hK T hA

end PhongSturm

/-! ### `rmk:NApotential:L862` -/

section DH

open Filter Set Metric SGPT.Okounkov MeasureTheory
open SGPT.TestCurve.GlobalSkoda SGPT.TestCurve.SkodaRWN
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology
open SGPT.NAPotential.NANS.TestConfig
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.PSH.VariableComplexAtlas

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance tcLinDHTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance tcLinDHCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance tcLinDHManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance tcLinDHMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance tcLinDHBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L}
  (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **`rmk:NApotential:L862` for ample test configurations** ([BHJ17, Def. 2.1–2.3]): for an
ample test configuration `(𝓧, 𝓛)` of `(X, L)` with a `𝔾_m`-linearized `𝓛`, `θ = c₁(L, h)` Kähler
(a Hodge class) and `X` with a smooth flag, the rescaled weight measures `(n!/kⁿ) ν_k` of the
induced filtration converge weakly to the book's Duistermaat–Heckman measure `DH(Γ^𝓕)`. -/
theorem linearized_rescaledJumpMeasure_tendsto (T : LinearizedTestConfiguration f a)
    (hA : T.IsAmple)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => rescaledFiniteMeasure
        (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) (m + 1) j) atTop
      (𝓝 (filtrationDHFinite (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
        H Y hY hbig)) :=
  testConfiguration_rescaledJumpMeasure_tendsto H Y hY T.toTestConfiguration _ hK hbig

/-- **`rmk:NApotential:L862` for ample test configurations, normalized form**: the normalized
weight measures `N_k⁻¹ ν_k` of [BHJ17, §3.2] converge weakly to `DH(Γ^𝓕) / DH(Γ^𝓕)(ℝ)`, and the
masses `n! N_k / kⁿ` converge to `DH(Γ^𝓕)(ℝ)`. -/
theorem linearized_normalized_tendsto (T : LinearizedTestConfiguration f a) (hA : T.IsAmple)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => (rescaledFiniteMeasure
        (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) (m + 1) j).normalize) atTop
      (𝓝 (filtrationDHFinite (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
        H Y hY hbig).normalize) ∧
    Tendsto (fun j : ℕ => (rescaledFiniteMeasure
        (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) (m + 1) j).mass) atTop
      (𝓝 (filtrationDHFinite (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
        H Y hY hbig).mass) :=
  testConfiguration_normalized_tendsto H Y hY T.toTestConfiguration _ hK hbig

end DH

end SGPT.TestCurve.TCLin
