import SGPT.TestCurve.MiscMArbitraryMetric
import SGPT.TestCurve.GeomLinMain
import SGPT.LineBundle.IntersectionAmple

/-!
# The mass factor of `rmk:NApotential:L862` (snapshot `c88c7ff4`)

Source `rmk:NApotential:L862` (chapter *Non-Archimedean pluripotential theory*,
`author/chapter_NApotential.tex:866–868` of `c88c7ff4`; ERRATA I04, corrected upstream):

> Let `Γ` be induced by a test configuration `(𝓧, 𝓛)` of `(X, L)` with `L` ample, as in
> `ex:RWN`, `rmk:PhongSturm`. The Duistermaat–Heckman measure of [BHJ17, §3.2] is normalized to
> have total mass one. By `eq:momentDHmtc2`, our measure has total mass `vol Γ = (Lⁿ)`, since
> `Γ_{-∞} = V_θ`. Thus `DH(Γ)` is `(Lⁿ)` times their measure.

The existing results (lanes NA-NS, TC-ENC, FG-REL, QW-NA, MISC-M, GEOM-LIN) prove, for the
filtration `𝓕` induced by a test configuration with finitely generated filtration (every ample
test configuration with a `𝔾_m`-linearization), `θ = c₁(L, h)` with `{θ}` a Hodge class: the
normalized weight measures `N_k⁻¹ ν_k` of [BHJ17] converge weakly to `DH(Γ^𝓕)/DH(Γ^𝓕)(ℝ)`, and
`n! N_k / kⁿ → DH(Γ^𝓕)(ℝ)`, `N_k = h⁰(X, L^k)`. Combined with asymptotic Riemann–Roch for the
ample `L` (`AmplePolarization.tendsto_h0_selfIntersection`: `n! h⁰(X, L^k)/kⁿ → (Lⁿ)`, `(Lⁿ)` the
Snapper–Kleiman self-intersection number), this gives the remark's mass factor:

* `rescaledFiniteMeasure_mass_coe`: the mass of `(n!/kⁿ) ν_k` is `n! h⁰(X, L^k)/kⁿ`;
* `testConfiguration_DH_mass_eq_selfIntersection`: `DH(Γ^𝓕)(ℝ) = (Lⁿ)`;
* `testConfiguration_DH_eq_selfIntersection_smul`: the BHJ measure, i.e. the weak limit `ν` of the
  probability measures `N_k⁻¹ ν_k`, exists and `DH(Γ^𝓕) = (Lⁿ) • ν`;
* `geomLinearized_DH_eq_selfIntersection_smul`: the same for every ample test configuration with a
  geometric `𝔾_m`-linearization ([BHJ17, Def. 2.1–2.3]).

The weights `ν_k` here are those of `H⁰(𝓧, k𝓛)/t H⁰(𝓧, k𝓛)`; their identification
with the weights of `H⁰(𝓧₀, k𝓛₀)` used in [BHJ17, §3.2] (cohomology and base change along the
central fibre) is not formalized and stays open in the ledger.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.TestCurve.SrcRev

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle
open Filter Set SGPT.Okounkov MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.TestCurve.TCEnc SGPT.NAPotential.NANS.TestConfig SGPT.TestCurve.MiscM
open scoped Topology ENNReal Nat

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f}

local instance srcRevDHTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance srcRevDHCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance srcRevDHManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance srcRevDHMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance srcRevDHBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

omit [SmoothOfRelativeDimension (m + 1) f] in
/-- The total mass of the rescaled jumping measure `(n!/kⁿ) ν_k` (`k = j + 1`) is
`n! h⁰(X, L^k) / kⁿ`. -/
theorem rescaledFiniteMeasure_mass_coe {L : X.Modules} {a : LineBundleAtlas L}
    (F : SectionFiltration f a) (n j : ℕ) :
    ((rescaledFiniteMeasure F n j).mass : ℝ) =
      (n ! : ℝ) * (h0 f L (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ n := by
  have h1 : ((rescaledFiniteMeasure F n j).mass : ℝ≥0∞) = rescaledJumpMeasure F n j univ :=
    FiniteMeasure.ennreal_mass
  rw [rescaledJumpMeasure_apply, F.jumpMeasure_univ] at h1
  have h2 := congrArg ENNReal.toReal h1
  rw [ENNReal.coe_toReal] at h2
  rw [h2, h0, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]

variable [IsIntegral X] {L : X.Modules} {a : LineBundleAtlas L}
  (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **`rmk:NApotential:L862`, the total mass**: for a test configuration of `(X, L)`, `L` ample,
with finitely generated induced filtration `𝓕`, and `θ = c₁(L, h)` with `{θ}` a Hodge class, the
Duistermaat–Heckman measure `DH(Γ^𝓕)` (computed with any smooth flag) has total mass `(Lⁿ)`. -/
theorem testConfiguration_DH_mass_eq_selfIntersection (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E) (P : AmplePolarization f L)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
      ((filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig).mass : ℝ) =
        P.selfIntersection (m + 1) := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) :=
    SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  intro Y hY
  obtain ⟨μ, -, hmass, hμ⟩ := testConfiguration_normalized_tendsto_hodge H T hfg hHodge hbig
  rw [← hμ Y hY]
  have hR : Tendsto (fun j : ℕ =>
      ((rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j).mass : ℝ)) atTop
      (𝓝 (μ.mass : ℝ)) := (NNReal.continuous_coe.tendsto _).comp hmass
  have hRR : Tendsto (fun j : ℕ =>
      ((m + 1) ! : ℝ) * (h0 f L (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (m + 1)) atTop
      (𝓝 (P.selfIntersection (m + 1))) :=
    (P.tendsto_h0_selfIntersection (m + 1) a).comp (tendsto_add_atTop_nat 1)
  refine tendsto_nhds_unique hR (hRR.congr fun j => ?_)
  exact (rescaledFiniteMeasure_mass_coe (T.inducedFiltration E hfg) (m + 1) j).symm

/-- **`rmk:NApotential:L862`, the comparison with [BHJ17, §3.2]**: under the hypotheses of
`testConfiguration_DH_mass_eq_selfIntersection`, the normalized weight measures `N_k⁻¹ ν_k`
(probability measures; `normalize_rescaledFiniteMeasure`) converge weakly to a probability
measure `ν`, and `DH(Γ^𝓕) = (Lⁿ) • ν`. -/
theorem testConfiguration_DH_eq_selfIntersection_smul (T : TestConfiguration f a)
    (hfg : T.FiltrationFinitelyGenerated E) (P : AmplePolarization f L)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
      ∃ ν : ProbabilityMeasure ℝ,
        Tendsto (fun j : ℕ =>
          (rescaledFiniteMeasure (T.inducedFiltration E hfg) (m + 1) j).normalize) atTop (𝓝 ν) ∧
        filtrationDHFinite (T.inducedFiltration E hfg) H Y hY hbig =
          (P.selfIntersection (m + 1)).toNNReal • ν.toFiniteMeasure := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  have : Nonempty (SchemeComplexPoint f) :=
    SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  have : ConnectedSpace (SchemeComplexPoint f) :=
    SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
  intro Y hY
  obtain ⟨μ, hnorm, -, hμ⟩ := testConfiguration_normalized_tendsto_hodge H T hfg hHodge hbig
  have hm := testConfiguration_DH_mass_eq_selfIntersection H T hfg P hHodge hbig Y hY
  refine ⟨μ.normalize, hnorm, ?_⟩
  rw [← hμ Y hY] at hm ⊢
  conv_lhs => rw [μ.self_eq_mass_smul_normalize]
  rw [← hm, Real.toNNReal_coe]

/-- **`rmk:NApotential:L862` for the test configurations of [BHJ17, Def. 2.1–2.3]**: for an ample
test configuration `(𝓧, 𝓛)` of `(X, L)`, `L` ample, with a geometric `𝔾_m`-linearization of `𝓛`,
and `θ = c₁(L, h)` with `{θ}` a Hodge class: `DH(Γ^𝓕)(ℝ) = (Lⁿ)`, the normalized weight measures
`N_k⁻¹ ν_k` converge weakly to a probability measure `ν`, and `DH(Γ^𝓕) = (Lⁿ) • ν`. -/
theorem geomLinearized_DH_eq_selfIntersection_smul
    (T : SGPT.TestCurve.GeomLin.GeomLinearizedTestConfiguration f a) (hA : T.IsAmple)
    (P : AmplePolarization f L)
    (hHodge : letI := E.isSeparated; letI := E.quasiCompact;
      ∃ ω : ClosedRealOneOneForm (m + 1) (SchemeComplexPoint f), ω.val.IsKahler ∧
        RealBottChern.ofRepresentative ω = RealBottChern.ofRepresentative (H.curvature a))
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : Nonempty (SchemeComplexPoint f) :=
      SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    ∀ (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
      ((filtrationDHFinite (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
          H Y hY hbig).mass : ℝ) = P.selfIntersection (m + 1) ∧
      ∃ ν : ProbabilityMeasure ℝ,
        Tendsto (fun j : ℕ => (rescaledFiniteMeasure
          (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)) (m + 1) j).normalize)
          atTop (𝓝 ν) ∧
        filtrationDHFinite (T.inducedFiltration E (T.filtrationFinitelyGenerated E hA))
            H Y hY hbig = (P.selfIntersection (m + 1)).toNNReal • ν.toFiniteMeasure :=
  fun Y hY =>
    ⟨testConfiguration_DH_mass_eq_selfIntersection H T.toTestConfiguration
        (T.filtrationFinitelyGenerated E hA) P hHodge hbig Y hY,
      testConfiguration_DH_eq_selfIntersection_smul H T.toTestConfiguration
        (T.filtrationFinitelyGenerated E hA) P hHodge hbig Y hY⟩

end SGPT.TestCurve.SrcRev

end
