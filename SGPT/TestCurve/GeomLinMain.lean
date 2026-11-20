import SGPT.TestCurve.GeomLinSheaf
import SGPT.TestCurve.TCLinMain
import SGPT.TestCurve.TCOkoCentral
import SGPT.Okounkov.TCOkoBody

/-!
# `rmk:PhongSturm`, `rmk:Okounkov:L2335`, `rmk:NApotential:L862` for geometrically linearized
# test configurations

Source: `rmk:PhongSturm` (chapter *Test curves*), `rmk:Okounkov:L2335` (chapter *Okounkov
bodies*) and `rmk:NApotential:L862` (chapter *Non-Archimedean pluripotential theory*). The three
remarks concern the filtration induced by a (smooth, ample) test configuration `(𝓧, 𝓛)` of
`(X, L)` in the sense of [BHJ17, Def. 2.1–2.3]: a `𝔾_m`-equivariant flat proper `π : 𝓧 → 𝔸¹` with
a **`𝔾_m`-linearized** line bundle `𝓛`, the linearization being an isomorphism
`Φ : σ^* 𝓛 ≅ pr₂^* 𝓛` with the cocycle condition (`GeomLinearizedTestConfiguration`, lane
GEOM-LIN).

Lanes TC-LIN and TC-OKO proved the three remarks for `TCLin.LinearizedTestConfiguration`, whose
linearization is recorded by the `𝔾_m`-representation it induces on the sections
(`SectionLinearization`). A geometric linearization induces that representation
(`GeomLinearizedTestConfiguration.toLinearized`, `GeomLinSection`), so the statements below,
for the [BHJ17] test configurations with the geometric linearization, follow. A linearization
given as an isomorphism of sheaves of modules between framed models of `σ^* 𝓛` and `pr₂^* 𝓛`
(`SheafLinearization`, `GeomLinSheaf`) is a geometric linearization
(`GeomLinearizedTestConfiguration.ofSheaf`), so the statements apply to it as well.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.GeomLin

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Opposite
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TCEnc SGPT.TestCurve.TCLin

/-- **[BHJ17, Prop. 2.15]**: the filtration induced by an ample test configuration with a
geometric `𝔾_m`-linearization is finitely generated (`X` integral projective). -/
theorem GeomLinearizedTestConfiguration.filtrationFinitelyGenerated {X : Scheme.{0}}
    {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L} [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (T : GeomLinearizedTestConfiguration f a)
    (hA : T.IsAmple) : T.FiltrationFinitelyGenerated E :=
  (T.toLinearized E).filtrationFinitelyGenerated E hA

/-! ### `rmk:PhongSturm` -/

section PhongSturm

open Filter Set Metric SGPT.Okounkov MeasureTheory
open SGPT.TestCurve.GlobalSkoda SGPT.TestCurve.SkodaRWN
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance geomLinPSTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance geomLinPSCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance geomLinPSMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance geomLinPSBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

local instance geomLinPSManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-- **Source `rmk:PhongSturm`**: for `L` ample on the integral smooth projective `X`, `h` with
Kähler curvature, `μ = (dd^c φ)^n`, and every smooth ample test configuration `(𝓧, 𝓛)` of `(X, L)`
in the sense of [BHJ17, Def. 2.1–2.3] (a `𝔾_m`-action and a geometric `𝔾_m`-linearization
`σ^* 𝓛 ≅ pr₂^* 𝓛` with the cocycle condition), the geodesic ray `Γ^{𝓕*}` of the induced
filtration `𝓕` is the Phong–Sturm ray of [RWN14, (9.1)]: `Γ^{𝓕*}_t = Φ(t)` for all `t > 0` and
every choice of adapted orthonormal bases. Smoothness of `𝓧` is not used by the proof. -/
theorem phongSturm_geomLinearized [IsSeparated f] [QuasiCompact f] [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (T : GeomLinearizedTestConfiguration f a) (hA : T.IsAmple) (_hSmooth : T.IsSmooth) :
    PhongSturmClaim H (curvatureVolume H a hK)
      (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) :=
  phongSturm_linearized H a P hK (T.toLinearized E) hA

end PhongSturm

/-! ### `rmk:NApotential:L862` -/

section DH

open Filter Set Metric SGPT.Okounkov MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology ENNReal
open SGPT.NAPotential.NANS.TestConfig SGPT.TestCurve.TCOko
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.PSH.VariableComplexAtlas

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance geomLinDHTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance geomLinDHCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance geomLinDHManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance geomLinDHMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance geomLinDHBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L}
  (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **Source `rmk:NApotential:L862`**: for an ample test configuration `(𝓧, 𝓛)` of `(X, L)`
with a geometric `𝔾_m`-linearization of `𝓛` ([BHJ17, Def. 2.1–2.3]), `θ = c₁(L, h)` Kähler (a
Hodge class) and `X` with a smooth flag:

* the linearization makes `H⁰(𝓧, k𝓛) / t H⁰(𝓧, k𝓛)` a `ℂ^*`-representation (weight
  decomposition), and its weight measure is the jumping measure of the induced filtration;
* the rescaled weight measures `(n!/kⁿ) ∑_λ dim (H⁰(𝓧, k𝓛)/t)_λ δ_{λ/k}` (`k = j + 1`) are the
  measures `rescaledFiniteMeasure` of the induced filtration, and they converge weakly to the
  book's Duistermaat–Heckman measure `DH(Γ^𝓕)`. -/
theorem geomLinearized_centralWeight_tendsto (T : GeomLinearizedTestConfiguration f a)
    (hA : T.IsAmple)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    (∀ k : ℕ, DirectSum.IsInternal (centralWeight T.toTestConfiguration k)) ∧
    (∀ j : ℕ, ((rescaledFiniteMeasure (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
        (m + 1) j : FiniteMeasure ℝ) : Measure ℝ) =
        (((m + 1).factorial : ℝ≥0∞) / ((j + 1 : ℕ) : ℝ≥0∞) ^ (m + 1)) •
          centralWeightMeasure T.toTestConfiguration (j + 1)) ∧
    Tendsto (fun j : ℕ => rescaledFiniteMeasure
        (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) (m + 1) j) atTop
      (𝓝 (filtrationDHFinite (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
        H Y hY hbig)) :=
  ⟨fun k => (linearized_centralWeight (E := E) (T.toLinearized E) hA k).1,
    linearized_centralWeight_tendsto H Y hY (T.toLinearized E) hA hK hbig⟩

/-- **`rmk:NApotential:L862`, normalized form**: the normalized weight measures `N_k⁻¹ ν_k` of
[BHJ17, §3.2] converge weakly to `DH(Γ^𝓕) / DH(Γ^𝓕)(ℝ)`, and the masses `n! N_k / kⁿ` converge to
`DH(Γ^𝓕)(ℝ)`. -/
theorem geomLinearized_normalized_tendsto (T : GeomLinearizedTestConfiguration f a)
    (hA : T.IsAmple)
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
  linearized_normalized_tendsto H Y hY (T.toLinearized E) hA hK hbig

end DH

/-! ### `rmk:Okounkov:L2335` -/

section Okounkov

open Filter Set Metric SGPT.Okounkov MeasureTheory SGPT.Okounkov.TCOko
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {E : ClosedProjectiveEmbedding f}
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance geomLinOkoTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance geomLinOkoCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance geomLinOkoManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance geomLinOkoMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance geomLinOkoBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)
  {L : X.Modules} {a : LineBundleAtlas L} (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **Source `rmk:Okounkov:L2335`**: let `(𝓧, 𝓛)` be an ample test configuration of `(X, L)` in
the sense of [BHJ17, Def. 2.1–2.3] (`𝔾_m`-action, geometric `𝔾_m`-linearization of `𝓛`, `𝓛`
relatively ample), `𝓕` the induced filtration (finitely generated, [BHJ17, Prop. 2.15]), `h` a
smooth metric on `L` with `{c₁(L, h)}` a Hodge class, `Γ = Γ^𝓕` the test curve of `ex:RWN` and
`Y•` a smooth flag. Then for every `τ < Γ_max = τ(𝓕)`, `Δ_{Y•}(θ, Γ_τ)` is the Okounkov body of
the graded linear series `⊕_k 𝓕^{kτ}_k`. -/
theorem geomLinearized_seriesBody_eq (T : GeomLinearizedTestConfiguration f a) (hA : T.IsAmple)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    {τ : ℝ} (hτ : (τ : EReal) <
      (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)).slope) :
    letI := E.isSeparated
    letI := E.quasiCompact
    seriesBody f (m + 1) E Y hY
        (filtrationSeries (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) τ) =
      PartialBody.generalPartialBody (schemeFubiniStudyOriginalFlagGeometry f (m + 1) E Y hY)
        (H.curvature a)
        ((T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)).testCurvePotential H τ) :=
  linearized_seriesBody_eq Y hY H (T.toLinearized E) hA hHodge hτ

end Okounkov

end SGPT.TestCurve.GeomLin
