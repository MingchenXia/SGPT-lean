import SGPT.GAGA.SmoothFlagsScheme
import SGPT.GAGA.H0LOkounkov
import SGPT.GAGA.H0LTestCurve

/-!
# `cor:volbigL`, `ex:RWN` and `rmk:max_filt` without a smooth flag


The projective forms of `cor:volbigL`, `ex:RWN` and `rmk:max_filt` (lanes H0-GAGA3, RWN, TESTCONF)
were proved on an integral smooth projective complex scheme `X` *carrying a smooth flag* (the
upper bound of `thm:DXmain1` uses flag valuations). Since every such `X` with `X(ℂ) ≠ ∅` carries
a smooth flag (`SGPT.GAGA.SmoothFlags.smoothFlagsExist`), the flag hypothesis is removed:

* `smoothFlag f E`, `isSmoothFlag_smoothFlag`: a chosen smooth flag on `X(ℂ)`;
* `tendsto_normalized_h0` (**`cor:volbigL`**): `lim_k n! h⁰(X, Lᵏ)/kⁿ = ∫_X θ_{V_θ}ⁿ` for every
  pseudo-effective `L` with a smooth metric;
* `volume_pos`, `rwnMinimalClause`, `rwnIModelClause`, `filtrationTestCurve_mem_iModel_and_isBounded`
  (**`ex:RWN`**, `{θ}` big): `vol L > 0`, clauses (b) and (a), and the conclusion (`Γ^𝓕` is a
  bounded `𝓘`-model test curve based at `V_θ`);
* `filtrationRay_mem_maximal` (**`rmk:max_filt`**): the ray `Γ^{𝓕*}` is a maximal geodesic ray
  emanating from `V_θ`, for every Kähler background of `X(ℂ)`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.GAGA.SmoothFlags

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.NAPotential.GAGAMult SGPT.TestCurve.TestConfig
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus SGPT.Foundations.Analysis.Pending.DiagonalMass
open scoped Topology ENNReal

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (E : ClosedProjectiveEmbedding f)
  [IsIntegral X] {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]

local instance smoothFlagsTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance smoothFlagsCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance smoothFlagsManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)

/-! ### A chosen smooth flag -/

/-- A smooth flag on `X(ℂ)` (`X` integral smooth projective, `X(ℂ) ≠ ∅`), chosen by
`smoothFlagsExist`. -/
def smoothFlag [Nonempty (SchemeComplexPoint f)] : Fin (m + 1 + 1) → Set (SchemeComplexPoint f) :=
  Classical.choose (smoothFlagsExist X f E m)

theorem isSmoothFlag_smoothFlag [Nonempty (SchemeComplexPoint f)] :
    IsSmoothFlag (smoothFlag f E (m := m)) :=
  Classical.choose_spec (smoothFlagsExist X f E m)

/-! ### `cor:volbigL` -/

/-- **Source `cor:volbigL`** (projective setting, every integral smooth projective `X`, no flag
hypothesis): for a pseudo-effective line bundle `L` (`V_θ ∈ PSH(X, θ)`) with a smooth metric `H`,
`θ = c₁(L, H)`, `lim_k n! h⁰(X, Lᵏ)/kⁿ = ∫_X θ_{V_θ}ⁿ`. -/
theorem tendsto_normalized_h0 [Nonempty (SchemeComplexPoint f)] {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (m + 1) E L)
    (hV : letI := E.isSeparated; letI := E.quasiCompact;
      IsThetaPshPotential (H.curvature a).val (thetaPshSupremum (H.curvature a).val)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    letI : MeasurableSpace (SchemeComplexPoint f) := borel _
    haveI : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    Tendsto (fun k : ℕ => (((m + 1).factorial : ℝ≥0∞) * (h0 f L k : ℝ≥0∞)) / (k : ℝ≥0∞) ^ (m + 1))
      atTop (𝓝 (diagonalPotentialMass (H.curvature a)
        (thetaPshSupremum (H.curvature a).val) hV)) :=
  SGPT.GAGA.H0L.tendsto_normalized_h0 f E (smoothFlag f E) (isSmoothFlag_smoothFlag f E) a H hV

/-! ### `ex:RWN` and `rmk:max_filt` -/

section RWN

local instance smoothFlagsMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance smoothFlagsBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {f E} {L : X.Modules} {a : LineBundleAtlas L}
  (F : SGPT.LineBundle.SectionFiltration f a) (H : SchemeLineBundleMetric f (m + 1) E L)

/-- **`vol L > 0` for `{c₁(L, h)}` big**, on every integral smooth projective `X` with
`X(ℂ) ≠ ∅`. -/
theorem volume_pos [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    0 < SGPT.LineBundle.volume f L (m + 1) :=
  SGPT.GAGA.H0L.volume_pos H (smoothFlag f E) (isSmoothFlag_smoothFlag f E) hbig

/-- **Clause (b) of `ex:RWN`** (`eq:Gammatautheta`), no flag hypothesis: for `{θ}` big,
`Γ^𝓕_τ = V_θ` for all `τ ≤ -C`. -/
theorem rwnMinimalClause [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNMinimalClause F H :=
  SGPT.GAGA.H0L.rwnMinimalClause F H (smoothFlag f E) (isSmoothFlag_smoothFlag f E) hbig

/-- **Clause (a) of `ex:RWN`**, no flag hypothesis: for `{θ}` big, every `Γ^𝓕_τ`, `τ < τ(𝓕)`, is
`𝓘`-model. -/
theorem rwnIModelClause [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNIModelClause F H :=
  SGPT.GAGA.H0L.rwnIModelClause F H (smoothFlag f E) (isSmoothFlag_smoothFlag f E) hbig

/-- **Conclusion of `ex:RWN`**, no flag hypothesis: for `L` with `{θ}` big and every filtration
`𝓕` of `R(X, L)`, the family `Γ^𝓕 = (Γ^𝓕_τ)_{τ < τ(𝓕)}` is a bounded `𝓘`-model test curve based at
`V_θ` (`Γ^𝓕 ∈ 𝓔^{NA}(X, θ)`, bounded). -/
theorem filtrationTestCurve_mem_iModel_and_isBounded [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    SGPT.TestCurve.TestConf.filtrationTestCurve F H hbig (rwnIModelClause F H hbig)
        (rwnMinimalClause F H hbig) ∈
      SourceIModelTestCurves (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H)
        (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
        (SGPT.TestCurve.TestConf.sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) ∧
    SourceTestCurveIsBounded
      (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
      (SGPT.TestCurve.TestConf.filtrationTestCurve F H hbig (rwnIModelClause F H hbig)
        (rwnMinimalClause F H hbig)) :=
  SGPT.GAGA.H0L.filtrationTestCurve_mem_iModel_and_isBounded F H (smoothFlag f E)
    (isSmoothFlag_smoothFlag f E) hbig

/-- **Source `rmk:max_filt`**, no flag hypothesis: for `L` with `{θ}` big and every filtration `𝓕`
of `R(X, L)`, the ray `Γ^{𝓕*}` (the Legendre transform of `Γ^𝓕`) is a maximal geodesic ray
emanating from `V_θ`, for every Kähler background `ω` of `X(ℂ)`. -/
theorem filtrationRay_mem_maximal [Nonempty (SchemeComplexPoint f)]
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (omega : letI := E.isSeparated; letI := E.quasiCompact;
      KahlerBackground (m + 1) (SchemeComplexPoint f)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) :=
      SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m + 1)
    sourceTestCurveLegendreRay (SGPT.TestCurve.TestConf.filtrationTestCurvePredata F H hbig
        (rwnIModelClause F H hbig) (rwnMinimalClause F H hbig)) ∈
      sourceMaximalGeodesicRays omega (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H)
        (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
        (SGPT.TestCurve.TestConf.sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) :=
  SGPT.GAGA.H0L.filtrationRay_mem_maximal F H (smoothFlag f E) (isSmoothFlag_smoothFlag f E) hbig
    omega

end RWN

end SGPT.GAGA.SmoothFlags
