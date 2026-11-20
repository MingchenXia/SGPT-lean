import SGPT.GAGA.H0LDXMain
import SGPT.TestCurve.SkodaIncMain
import SGPT.TestCurve.RWNClauses

/-!
# `ex:RWN`, `rmk:max_filt` and `rmk:PhongSturm` with GAGA


GAGA for the sections of an arbitrary line bundle (`SGPT.GAGA.H0L.schemeSectionsAlgebraic`) and
the lower bound of `thm:DXmain1` (`SGPT.GAGA.H0L.dxMainLowerBound`) discharge the corresponding
hypotheses of the test-curve chapter:

* `eventually_schemeSectionsAlgebraic`: the `SchemeSectionsAlgebraic` (`j ≫ 0`) in the
  form taken by the consumers, for every line bundle with an atlas and a smooth metric;
* `schemePointExtension`: the uniform `L²` point extension for *algebraic* sections of `L^k`
  (`SGPT.TestCurve.SkodaRWN.SchemePointExtension`, first input of [RWN14, Prop. 7.11]);
* `rwnMinimalClause_of_isKahler`: clause (b) of `ex:RWN` (`Γ^𝓕_τ = V_θ` for `τ ≤ -C`) for a
  positively curved metric, from the point extension (no flag needed);
* `rwnSkodaClause_of_globalSkodaDivision`, `phongSturmRemark_of_globalSkodaDivision`:
  [RWN14, Prop. 7.11] and `rmk:PhongSturm` for `μ = (dd^c φ)ⁿ`, conditional only on Skoda's
  division theorem `GlobalSkodaDivision`;
* on `X` with a smooth flag and `{θ}` big: `volume_pos` (`vol L > 0`), `rwnMinimalClause` and
  `rwnIModelClause` (clauses (b) and (a) of `ex:RWN`), `filtrationTestCurve_mem_iModel_and_isBounded`
  (the conclusion of `ex:RWN`) and `filtrationRay_mem_maximal` (`rmk:max_filt`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.GAGA.H0L

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set SGPT.Okounkov SGPT.LineBundle
open MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.NAPotential.GAGAMult SGPT.TestCurve.TestConfig SGPT.TestCurve.SkodaRWN
  SGPT.TestCurve.SkodaInc
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis.FirstPass.IEnvelope SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.POrder SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.SingularGlobalPOrder
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open scoped Topology ENNReal

/-! ### GAGA and the point extension -/

section PointExtension

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {n : ℕ} [SmoothOfRelativeDimension n f]
  {E : ClosedProjectiveEmbedding f}

local instance h0lTCTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0lTCCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance h0lTCManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance h0lTCMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance h0lTCBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} (H : SchemeLineBundleMetric f n E L) (a : LineBundleAtlas L)

/-- **GAGA for the sections of `L^j`** in the form of the consumers (`letI` instances from the
closed projective embedding). -/
theorem eventually_schemeSectionsAlgebraic :
    letI := E.isSeparated
    letI := E.quasiCompact
    ∀ᶠ j in atTop, SchemeSectionsAlgebraic f n E a H j := by
  let := E.isSeparated
  let := E.quasiCompact
  have : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  exact Eventually.of_forall fun j => schemeSectionsAlgebraic a H j

/-- **The uniform `L²` extension from a point for the algebraic sections of `L^k`**
(`SchemePointExtension`), for every smooth positive volume `μ` and every Kähler form `ω`. -/
theorem schemePointExtension (μ : Measure (SchemeComplexPoint f))
    (hμ : letI := E.isSeparated; letI := E.quasiCompact; IsSmoothPositiveVolume (n := n) μ)
    (omega : letI := E.isSeparated; letI := E.quasiCompact;
      KahlerBackground n (SchemeComplexPoint f)) :
    SchemePointExtension H a μ omega :=
  schemePointExtension_of_sectionsAlgebraic H a μ hμ omega
    (eventually_schemeSectionsAlgebraic H a)

variable [IsIntegral X]

/-- **Clause (b) of `ex:RWN` (`eq:Gammatautheta`) for a positively curved metric**
(`θ = c₁(L, h)` Kähler, e.g. `L` ample as in the footnote to `ex:RWN`): `Γ^𝓕_τ = V_θ` for
`τ ≤ -C`, for every filtration `𝓕` of `R(X, L)`. -/
theorem rwnMinimalClause_of_isKahler (F : SectionFiltration f a)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNMinimalClause F H :=
  rwnMinimalClause_of_pointExtension F H (curvatureVolume H a hK)
    (isBernsteinMarkov_curvatureVolume H a H a hK) hK
    (schemePointExtension H a (curvatureVolume H a hK)
      (isSmoothPositiveVolume_curvatureVolume H a hK) (curvatureKahlerBackground H a hK))

/-- **[RWN14, Proposition 7.11] for ample test configurations from Skoda's division theorem**:
for a positively curved metric, `GlobalSkodaDivision` gives `P_θ[ψ_τ] = ψ_τ` for `τ < τ(𝓕)`, for
every normalized finitely generated `ℤ`-filtration `𝓕`. -/
theorem rwnSkodaClause_of_globalSkodaDivision [Nonempty (SchemeComplexPoint f)]
    (G : SectionZFiltration f a) (hG : G.IsFinitelyGenerated) (h0 : G.piece 0 0 = ⊤)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hSk : GlobalSkodaDivision H a) :
    RWNSkodaClause H (G.fgFiltration hG h0) :=
  rwnSkodaClause_of_sectionsAlgebraic_of_globalSkodaDivision G hG h0 H hK
    (eventually_schemeSectionsAlgebraic H a) hSk

/-- **`rmk:PhongSturm` from Skoda's division theorem**: let `L` be ample on the smooth projective
`X`, `h = e^{-φ}` a positively curved smooth metric and `μ = (dd^c φ)ⁿ`. If Skoda's `L²` division
theorem holds (`GlobalSkodaDivision`), then for every ample test configuration the geodesic ray
of `ex:RWN` is the Phong–Sturm ray. -/
theorem phongSturmRemark_of_globalSkodaDivision [Nonempty (SchemeComplexPoint f)]
    [CompactSpace (SchemeComplexPoint f)] (P : AmplePolarization f L)
    (hK : letI := E.isSeparated; letI := E.quasiCompact; (H.curvature a).val.IsKahler)
    (hSk : GlobalSkodaDivision H a) :
    PhongSturmRemark H a (curvatureVolume H a hK) :=
  phongSturmRemark_of_sectionsAlgebraic_of_globalSkodaDivision H P hK
    (eventually_schemeSectionsAlgebraic H a) hSk

end PointExtension

/-! ### `ex:RWN` and `rmk:max_filt` on `X` with a smooth flag -/

section Flag

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {m : ℕ} [SmoothOfRelativeDimension (m + 1) f]
  {E : ClosedProjectiveEmbedding f} [IsIntegral X]

local instance h0lRWNTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance h0lRWNCharts : ChartedSpace (ComplexModel (m + 1)) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f (m + 1)
local instance h0lRWNManifold [IsSeparated f] [QuasiCompact f] :
    IsComplexManifold (m + 1) (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f (m + 1)
local instance h0lRWNMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance h0lRWNBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable {L : X.Modules} {a : LineBundleAtlas L}
  (F : SGPT.LineBundle.SectionFiltration f a) (H : SchemeLineBundleMetric f (m + 1) E L)
  (Y : Fin (m + 1 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y)

omit [IsIntegral X] in
include Y hY in
/-- A smooth flag makes `X(ℂ)` nonempty. -/
theorem nonempty_of_smoothFlag : Nonempty (SchemeComplexPoint f) := by
  obtain ⟨x, -⟩ := (hY.level_closed_connected 0).2.nonempty
  exact ⟨x⟩

omit [IsIntegral X] in
include Y hY in
/-- The lower bound of `thm:DXmain1` at `V_θ` (`{θ}` big), on `X` with a smooth flag. -/
theorem dxMainLowerBound_thetaPshSupremum
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    haveI : Nonempty (SchemeComplexPoint f) := nonempty_of_smoothFlag Y hY
    SGPT.IGood.DXMain.DXMainLowerBound f E a H
      (letI := E.isSeparated; letI := E.quasiCompact;
        haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact;
        MinimalSingularityLelongVanishing.isThetaPshPotential_thetaPshSupremum (H.curvature a)
          hbig) := by
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  have : Nonempty (SchemeComplexPoint f) := nonempty_of_smoothFlag Y hY
  exact dxMainLowerBound a H _

include Y hY in
/-- **`vol L > 0` for `{c₁(L, h)}` big** (the book's bigness), on `X` with a smooth flag. -/
theorem volume_pos
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    0 < SGPT.LineBundle.volume f L (m + 1) := by
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  exact SGPT.TestCurve.RWN.volume_pos_of_lowerBound H hbig
    (dxMainLowerBound_thetaPshSupremum H Y hY hbig)

include Y hY in
/-- **Clause (b) of `ex:RWN`** (`eq:Gammatautheta`): on `X` with a smooth flag and `{θ}` big,
`Γ^𝓕_τ = V_θ` for all `τ ≤ -C`. -/
theorem rwnMinimalClause
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNMinimalClause F H := by
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  exact SGPT.TestCurve.RWN.rwnMinimalClause_of_lowerBound F H Y hY hbig
    (dxMainLowerBound_thetaPshSupremum H Y hY hbig)

include Y hY in
/-- **Clause (a) of `ex:RWN`**: on `X` with a smooth flag and `{θ}` big, every `Γ^𝓕_τ`,
`τ < τ(𝓕)`, is `𝓘`-model. -/
theorem rwnIModelClause
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    SGPT.TestCurve.TestConf.RWNIModelClause F H := by
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  exact SGPT.TestCurve.RWN.rwnIModelClause_of_lowerBound F H Y hY hbig
    (dxMainLowerBound_thetaPshSupremum H Y hY hbig)

include Y hY in
/-- **Conclusion of `ex:RWN`**: on `X` with a smooth flag and `{θ}` big, the family
`Γ^𝓕 = (Γ^𝓕_τ)_{τ < τ(𝓕)}` is a bounded `𝓘`-model test curve based at `V_θ`. -/
theorem filtrationTestCurve_mem_iModel_and_isBounded
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a))) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    SGPT.TestCurve.TestConf.filtrationTestCurve F H hbig (rwnIModelClause F H Y hY hbig)
        (rwnMinimalClause F H Y hY hbig) ∈
      SourceIModelTestCurves (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H)
        (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
        (SGPT.TestCurve.TestConf.sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) ∧
    SourceTestCurveIsBounded
      (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
      (SGPT.TestCurve.TestConf.filtrationTestCurve F H hbig (rwnIModelClause F H Y hY hbig)
        (rwnMinimalClause F H Y hY hbig)) := by
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  exact SGPT.TestCurve.RWN.filtrationTestCurve_mem_iModel_and_isBounded_of_lowerBound F H Y hY hbig
    (dxMainLowerBound_thetaPshSupremum H Y hY hbig)

include Y hY in
/-- **Source `rmk:max_filt`**: on `X` with a smooth flag and `{θ}` big, the ray `Γ^{𝓕*}` induced
by a filtration `𝓕` (the Legendre transform of `Γ^𝓕`) is a maximal geodesic ray emanating from
`V_θ`, for every Kähler background `ω` of `X^{an}`. -/
theorem filtrationRay_mem_maximal
    (hbig : letI := E.isSeparated; letI := E.quasiCompact;
      IsBigClass (RealBottChern.ofRepresentative (H.curvature a)))
    (omega : letI := E.isSeparated; letI := E.quasiCompact;
      KahlerBackground (m + 1) (SchemeComplexPoint f)) :
    letI := E.isSeparated
    letI := E.quasiCompact
    haveI : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    haveI : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
    sourceTestCurveLegendreRay (SGPT.TestCurve.TestConf.filtrationTestCurvePredata F H hbig
        (rwnIModelClause F H Y hY hbig) (rwnMinimalClause F H Y hY hbig)) ∈
      sourceMaximalGeodesicRays omega (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H)
        (sourceMinimalEnvelope (SGPT.TestCurve.TestConf.curvatureAtlasForm (a := a) H))
        (SGPT.TestCurve.TestConf.sourceMinimalEnvelope_curvatureAtlasForm_model H hbig) := by
  have : ConnectedSpace (SchemeComplexPoint f) := schemeSmoothFlag_connectedSpace f (m + 1) Y hY
  exact SGPT.TestCurve.RWN.filtrationRay_mem_maximal_of_lowerBound F H Y hY hbig
    (dxMainLowerBound_thetaPshSupremum H Y hY hbig) omega

end Flag

end SGPT.GAGA.H0L
