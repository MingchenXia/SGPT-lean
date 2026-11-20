import SGPT.TestCurve.TCZeroFiltrationCurve
import SGPT.NAPotential.DHFlagZero

/-! Actual original zero-dimensional filtration source pushforward and its weight normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.ZeroSource
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Okounkov SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.NANS.TestConfig
open scoped Topology ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  [IsIntegral X] [SmoothOfRelativeDimension 0 f] (E : ClosedProjectiveEmbedding f)
local instance zeroDHTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance zeroDHCharts : ChartedSpace (ComplexModel 0) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f 0
local instance zeroDHManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold 0 (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f 0
local instance zeroDHMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance zeroDHBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

variable (F : SectionFiltration f a) (H : SchemeLineBundleMetric f 0 E L)

omit [IsIntegral X] in
/-- Actual bigness of the literal original atlas form, with no class certificate input. -/
theorem filtrationSourceCurve_atlas_big (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  IsBigClass (RealBottChern.ofRepresentative
    (atlasClosedFormToNative (TestConf.curvatureAtlasForm (a := a) H))) := by
  let := E.isSeparated
  let := E.quasiCompact
  dsimp only
  rw [TestConf.curvatureAtlasForm_native]
  exact filtration_curvature_big E H P

/-- The original source concave-transform pushforward of the actual original filtration curve. -/
def filtrationSourceDH (P : AmplePolarization f L)
    (Y : Fin (0 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) : Measure ℝ := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  let : MeasurableSpace (schemeFubiniStudyOriginalFlagGeometry f 0 E Y hY).carrier := borel _
  let : BorelSpace (schemeFubiniStudyOriginalFlagGeometry f 0 E Y hY).carrier := ⟨rfl⟩
  exact SGPT.NAPotential.DHSource.naDuistermaatHeckman
    (schemeFubiniStudyOriginalFlagGeometry f 0 E Y hY)
    (filtrationSourceCurve_atlas_big E H P) (filtrationSourceCurve E F H P)

/-- Actual original pushforward calculation; every actual original flag yields the same measure. -/
theorem filtrationSourceDH_eq_dirac (P : AmplePolarization f L)
    (Y : Fin (0 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y) :
    filtrationSourceDH E F H P Y hY = Measure.dirac F.slope.toReal := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
  let : MeasurableSpace (schemeFubiniStudyOriginalFlagGeometry f 0 E Y hY).carrier := borel _
  let : BorelSpace (schemeFubiniStudyOriginalFlagGeometry f 0 E Y hY).carrier := ⟨rfl⟩
  change SGPT.NAPotential.DHSource.naDuistermaatHeckman
    (schemeFubiniStudyOriginalFlagGeometry f 0 E Y hY)
    (filtrationSourceCurve_atlas_big E H P) (filtrationSourceCurve E F H P) = _
  rw [SGPT.NAPotential.DHSource.Zero.naDuistermaatHeckman_eq_dirac,
    filtrationSourceCurve_max]

/-- The genuine original zero-dimensional source DH reader, requiring only original F, H, P.
The measure is constructed from an internally produced original flag; all flags read back it. -/
theorem filtration_source_DH_normalization (P : AmplePolarization f L) :
    ∃ μ : FiniteMeasure ℝ,
      (μ : Measure ℝ) = Measure.dirac F.slope.toReal ∧
      μ.mass = 1 ∧ P.selfIntersection 0 = 1 ∧
      Tendsto (fun j : ℕ => (rescaledFiniteMeasure F 0 j).normalize) atTop (𝓝 μ.normalize) ∧
      μ = (P.selfIntersection 0).toNNReal • μ.normalize.toFiniteMeasure ∧
      ∀ (Y : Fin (0 + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
        filtrationSourceDH E F H P Y hY = (μ : Measure ℝ) := by
  let := E.isSeparated
  let := E.quasiCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  obtain ⟨Y, hY⟩ := SGPT.Okounkov.OriginalBook.exists_original_smoothFlag_allDimensions f 0 E
  have hf : IsFiniteMeasure (filtrationSourceDH E F H P Y hY) := by
    rw [filtrationSourceDH_eq_dirac E F H P Y hY]
    infer_instance
  let μ : FiniteMeasure ℝ := ⟨filtrationSourceDH E F H P Y hY, hf⟩
  have hμ : (μ : Measure ℝ) = Measure.dirac F.slope.toReal :=
    filtrationSourceDH_eq_dirac E F H P Y hY
  have hμp : μ = (diracProba F.slope.toReal).toFiniteMeasure :=
    FiniteMeasure.toMeasure_injective hμ
  have hnorm : μ.normalize = diracProba F.slope.toReal := by
    rw [hμp, ProbabilityMeasure.toFiniteMeasure_normalize_eq_self]
  have hmass : μ.mass = 1 := by rw [hμp, ProbabilityMeasure.mass_toFiniteMeasure]
  have hP := ZeroDH.original_selfIntersection_eq_one E P a
  refine ⟨μ, hμ, hmass, hP, ?_, ?_, ?_⟩
  · rw [hnorm]
    exact ZeroDH.normalized_weights_tendsto_dirac_slope E F
  · rw [hP, Real.toNNReal_one, one_smul, hnorm, hμp]
  · intro Y' hY'
    exact (filtrationSourceDH_eq_dirac E F H P Y' hY').trans hμ.symm

end SGPT.TestCurve.ZeroSource
