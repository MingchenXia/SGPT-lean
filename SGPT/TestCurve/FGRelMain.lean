import SGPT.TestCurve.FGRelTCChart
import SGPT.TestCurve.TCEncBridge

/-!
# Finite generation of the filtration of an ample test configuration

Source: the first half of [BHJ17, Prop. 2.15], used by `rmk:PhongSturm` (chapter *Test
curves*) and `rmk:NApotential:L862` (chapter *Non-Archimedean pluripotential theory*), where it is
the hypothesis `TestConfiguration.FiltrationFinitelyGenerated` of the statements.

## Equivariant coordinates

A test configuration in the sense of [BHJ17, Def. 2.1] carries a `𝔾_m`-*linearized* line bundle
`𝓛`; an *ample* test configuration has `𝓛` relatively ample, and then (for `r` divisible enough)
`(𝓧, r𝓛)` embeds `𝔾_m`-equivariantly into `ℙᴺ × 𝔸¹` with a diagonal `𝔾_m`-action on `ℙᴺ` — this
is Donaldson's original definition of a test configuration, used by Phong–Sturm [PS07] and
[RWN14, §8–9]. In the encoding of `SGPT.TestCurve.TCEnc.TestConfiguration` (where the
identification `𝓧 ∖ 𝓧₀ ≅ X × 𝔾_m`, `𝓛|_{𝓧 ∖ 𝓧₀} ≅ q^* L` is recorded but no linearization of `𝓛`),
such an embedding is recorded by `EquivariantCoordinates T`:

* sections `ξ_0, …, ξ_N ∈ H⁰(𝓧, 𝓛^r)` which are weight vectors: `ξ_i` extends `t^{-w_i} q^* y_i`
  with `y_i ∈ H⁰(X, L^r)` (`isWeightVector`; i.e. the `𝔾_m`-action on `ℙᴺ` is `diag(t^{-w_i})` and
  `y` is the embedding of `X = 𝓧_1`);
* without common zeros (`noCommonZero`: the morphism `(ξ, π) : 𝓧 → ℙᴺ × 𝔸¹` is defined);
* the chart condition of a closed embedding in its `𝔾_m`-graded form (`chart`,
  `FGRel.WeightChartCondition`): on `{ξ_i ≠ 0}` every weight vector of `H⁰(𝓧, 𝓛^{rk})` is,
  after multiplication by a power of `ξ_i`, a linear combination of monomials `t^a ξ^β` of the
  same weight.

## Main results

* `filtrationFinitelyGenerated_of_equivariantCoordinates`: **the filtration induced by a test
  configuration with equivariant coordinates is finitely generated** ([BHJ17, Prop. 2.15]).
  The proof (`FGRel.isFinitelyGenerated_of_polarization`) reduces modulo `t` to the central fibre
  `𝓧₀ = V(J) ⊆ ℙᴺ_ℂ` and uses Serre's theorem over the field `ℂ` (from `SGPT.Foundations.Schemes`'s Čech
  theory of finite graded modules over `ℂ[X_0, …, X_N]`), the saturation property of sections of
  `𝓛` (`FGRel.saturation_of_weightSections`), graded Nakayama in the power of `t`, finiteness of
  each degree, and a Veronese argument for degrees prime to `r`.
* `phongSturm_equivariantCoordinates`, `phongSturmRemark_equivariantCoordinates`: `rmk:PhongSturm`
  for such test configurations without the finite generation hypothesis.
* `equivariantCoordinates_rescaledJumpMeasure_tendsto`,
  `equivariantCoordinates_normalized_tendsto`: `rmk:NApotential:L862` likewise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.TestCurve.FGRel

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Opposite
open SGPT.TestCurve.TestConfig SGPT.TestCurve.TestConfig.LaurentSecRing SGPT.TestCurve.TCEnc

/-- **Equivariant coordinates of an ample test configuration** (see the module docstring):
weight sections `ξ_i ∈ H⁰(𝓧, 𝓛^r)` extending `t^{-w_i} q^* y_i`, without common zeros, satisfying
the weight chart condition of a closed embedding `𝓧 ↪ ℙᴺ × 𝔸¹`. -/
structure EquivariantCoordinates {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules}
    {a : LineBundleAtlas L} (T : TestConfiguration f a) where
  /-- The power `𝓛^r` giving the embedding. -/
  r : ℕ
  r_pos : 0 < r
  /-- The dimension of the projective space. -/
  N : ℕ
  /-- The weights of the diagonal `𝔾_m`-action on `ℙᴺ`. -/
  w : Fin (N + 1) → ℤ
  /-- The coordinate sections of `L^r` on `X = 𝓧_1`. -/
  y : Fin (N + 1) → SectionSpace f L r
  /-- The coordinate sections of `𝓛^r` on `𝓧`. -/
  ξ : Fin (N + 1) → SectionSpace T.structureMap T.line r
  /-- `ξ_i` is the weight vector extending `t^{-w_i} q^* y_i`. -/
  isWeightVector : ∀ i, T.Extends (w i) r (y i) (ξ i)
  /-- The `ξ_i` have no common zeros. -/
  noCommonZero : ∀ c : T.extAtlas.I, T.extAtlas.opens c ≤
    ⨆ i, T.space.basicOpen (atlasPowerGlobalCoefficients T.extAtlas r c (ξ i))
  /-- The chart condition of the closed embedding `(ξ, π)`, in its `𝔾_m`-graded form. -/
  chart : WeightChartCondition T w ξ

/-- **[BHJ17, Prop. 2.15], first half: the filtration induced by an ample test configuration
(with its equivariant coordinates) is finitely generated.** -/
theorem filtrationFinitelyGenerated_of_equivariantCoordinates {X : Scheme.{0}}
    {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L} [IsIntegral X]
    (E : ClosedProjectiveEmbedding f) (T : TestConfiguration f a)
    (P : EquivariantCoordinates T) : T.FiltrationFinitelyGenerated E :=
  isFinitelyGenerated_of_polarization E (T.zFiltration E) (T.zFiltration_piece_zero_zero E)
    P.r_pos P.w P.y (fun i => T.mem_piece.mpr ⟨P.ξ i, P.isWeightVector i⟩)
    (fun k j s hs => chart_of_weightChartCondition T P.w P.ξ P.y P.isWeightVector P.chart k j s hs)
    (fun k j s h => saturation_of_weightSections E T P.w P.y P.ξ P.isWeightVector
      P.noCommonZero k j s h)

/-! ### `rmk:PhongSturm` -/

section PhongSturm

open Filter Set Metric SGPT.Okounkov MeasureTheory
open SGPT.TestCurve.GlobalSkoda SGPT.TestCurve.SkodaRWN
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance fgRelPSTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance fgRelPSCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance fgRelPSMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance fgRelPSBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

local instance fgRelPSManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-- **`rmk:PhongSturm` for an ample test configuration**, with no finite generation hypothesis:
for `L` ample on the integral smooth projective `X`, `h` with Kähler curvature,
`μ = (dd^c φ)^n` and `(𝓧, 𝓛)` a test configuration of `(X, L)` with equivariant coordinates,
the geodesic ray `Γ^{𝓕*}` of the induced filtration is the Phong–Sturm ray of [RWN14, (9.1)]:
`Γ^{𝓕*}_t = Φ(t)` for all `t > 0` and every choice of adapted orthonormal bases. -/
theorem phongSturm_equivariantCoordinates [IsSeparated f] [QuasiCompact f] [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (T : TestConfiguration f a) (C : EquivariantCoordinates T) :
    PhongSturmClaim H (curvatureVolume H a hK)
      (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C)) :=
  phongSturm_testConfiguration H a P hK T _

/-- **Source `rmk:PhongSturm`, quantified over smooth ample test configurations**: for `L` ample
and `h` with Kähler curvature, for every smooth `𝔾_m`-equivariant test configuration `(𝓧, 𝓛)` of
`(X, L)` with equivariant coordinates (an ample test configuration with its linearization, in
Donaldson's form), the geodesic ray `Γ^{𝓕*}` of the induced filtration `𝓕` is the Phong–Sturm
ray. The equivariance and smoothness hypotheses are not used by the proof. -/
theorem phongSturmRemark_equivariantCoordinates [IsSeparated f] [QuasiCompact f] [IsIntegral X]
    [Nonempty (SchemeComplexPoint f)] [CompactSpace (SchemeComplexPoint f)]
    (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (T : TestConfiguration f a) (_hEq : T.IsGmEquivariant) (C : EquivariantCoordinates T)
    (_hSmooth : T.IsSmooth) :
    PhongSturmClaim H (curvatureVolume H a hK)
      (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C)) :=
  phongSturm_equivariantCoordinates H a P hK T C

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

local instance fgRelDHTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance fgRelDHCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance fgRelDHManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance fgRelDHMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance fgRelDHBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L}
  (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

/-- **`rmk:NApotential:L862` for an ample test configuration**, with no finite generation
hypothesis: the rescaled weight measures `(n!/kⁿ) ν_k` of the induced filtration converge weakly
to the book's Duistermaat–Heckman measure `DH(Γ^𝓕)`. -/
theorem equivariantCoordinates_rescaledJumpMeasure_tendsto (T : TestConfiguration f a)
    (C : EquivariantCoordinates T)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => rescaledFiniteMeasure
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        (m + 1) j) atTop
      (𝓝 (filtrationDHFinite
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        H Y hY hbig)) :=
  testConfiguration_rescaledJumpMeasure_tendsto H Y hY T _ hK hbig

/-- **`rmk:NApotential:L862` for an ample test configuration, normalized form**: the normalized
weight measures `N_k⁻¹ ν_k` of [BHJ17, §3.2] converge weakly to `DH(Γ^𝓕) / DH(Γ^𝓕)(ℝ)`, and the
masses `n! N_k / kⁿ` converge to `DH(Γ^𝓕)(ℝ)`. -/
theorem equivariantCoordinates_normalized_tendsto (T : TestConfiguration f a)
    (C : EquivariantCoordinates T)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    Tendsto (fun j : ℕ => (rescaledFiniteMeasure
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        (m + 1) j).normalize) atTop
      (𝓝 (filtrationDHFinite
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        H Y hY hbig).normalize) ∧
    Tendsto (fun j : ℕ => (rescaledFiniteMeasure
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        (m + 1) j).mass) atTop
      (𝓝 (filtrationDHFinite
        (T.inducedFiltration E (filtrationFinitelyGenerated_of_equivariantCoordinates E T C))
        H Y hY hbig).mass) :=
  testConfiguration_normalized_tendsto H Y hY T _ hK hbig

end DH

end SGPT.TestCurve.FGRel
