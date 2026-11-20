import SGPT.TestCurve.TCZeroSourceDH
import SGPT.TestCurve.TCAmpleDHGeometry
import SGPT.TestCurve.TCActualCentralWeightMeasure

/-! Entire original rmk:NApotential:L862: genuine source DH and genuine central geometric weights,
all dimensions including zero, from original ample geometric test-configuration data alone. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.TestCurve.OriginalBookDH
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes SGPT.LineBundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Okounkov SGPT.PSH.VariableComplexAtlas
open SGPT.NAPotential.NANS.TestConfig SGPT.TestCurve.GeomLin SGPT.TestCurve.TCEnc
open scoped Topology ENNReal NNReal

private theorem normalize_pos_smul (μ : FiniteMeasure ℝ) (c : ℝ≥0) (hc : c ≠ 0) :
    (c • μ).normalize = μ.normalize := by
  by_cases hμ : μ = 0
  · simp only [hμ, smul_zero]
  have hs : c • μ ≠ 0 := smul_ne_zero hc hμ
  have hm : (c • μ).mass = c * μ.mass := by
    simp only [FiniteMeasure.mass, FiniteMeasure.smul_apply, smul_eq_mul]
  apply ProbabilityMeasure.toMeasure_injective
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hs, hm,
    FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ hμ,
    smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hc, mul_one]

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
  [IsIntegral X] {n : ℕ} [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
local instance originalDHTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance originalDHCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance originalDHManifold [IsSeparated f] [QuasiCompact f] : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
local instance originalDHMeasurable : MeasurableSpace (SchemeComplexPoint f) := borel _
local instance originalDHBorel : BorelSpace (SchemeComplexPoint f) := ⟨rfl⟩

/-- The literal original source pushforward in ALL dimensions, including its actual zero curve.
The original curve and big Chern class are manufactured from the same original ample line. -/
def originalFiltrationDH (F : SectionFiltration f a) (H : SchemeLineBundleMetric f n E L)
    (P : AmplePolarization f L) (Y : Fin (n + 1) → Set (SchemeComplexPoint f))
    (hY : IsSmoothFlag Y) : Measure ℝ := by
  cases n with
  | zero => exact ZeroSource.filtrationSourceDH E F H P Y hY
  | succ m =>
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m+1)
    exact filtrationDH F H Y hY (AmpleChern.originalAmple_curvature_domain f (m+1) E P a H).2

/-- The actual source measure, original normalized jumping limit, original mass and all flags,
with no supplied class, curve, flag, cutoff, mass or weak-limit certificate. -/
theorem original_source_DH_limit (H : SchemeLineBundleMetric f n E L)
    (T : GeomLinearizedTestConfiguration f a) (hA : T.IsAmple) (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let F := T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)
  ∃ μ : FiniteMeasure ℝ,
    (μ.mass : ℝ) = P.selfIntersection n ∧
    Tendsto (fun j : ℕ => (rescaledFiniteMeasure F n j).normalize) atTop (𝓝 μ.normalize) ∧
    μ = (P.selfIntersection n).toNNReal • μ.normalize.toFiniteMeasure ∧
    ∀ (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
      (μ : Measure ℝ) = originalFiltrationDH E F H P Y hY := by
  cases n with
  | zero =>
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E 0
    let F := T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)
    obtain ⟨μ, -, hm, hP, hlim, hscale, hall⟩ :=
      ZeroSource.filtration_source_DH_normalization E F H P
    refine ⟨μ, ?_, hlim, hscale, ?_⟩
    · rw [hm, hP]; rfl
    · intro Y hY
      exact (hall Y hY).symm
  | succ m =>
    let := E.isSeparated
    let := E.quasiCompact
    let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
    let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
    let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E (m+1)
    obtain ⟨hbig, μ, hm, hlim, hscale, hall⟩ :=
      SrcRev.geomLinearized_ample_DH_without_class_or_flag_input H T hA P
    refine ⟨μ, hm, hlim, hscale, ?_⟩
    intro Y hY
    exact congrArg FiniteMeasure.toMeasure (hall Y hY)

/-- Entire original rmk:NApotential:L862. The BHJ measures are the actual geometric central H0
weight measures on a genuine cofinal tail of ALL original degrees; the source measure is the
literal original pushforward for EVERY actual original flag. No desired output is an input. -/
theorem geomLinearized_book_DH (H : SchemeLineBundleMetric f n E L)
    (T : GeomLinearizedTestConfiguration f a) (hA : T.IsAmple) (P : AmplePolarization f L) :
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let F := T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)
  ∃ (μ : FiniteMeasure ℝ) (ν : ProbabilityMeasure ℝ) (B : ℕ) (W : ℕ → FiniteMeasure ℝ),
    (∀ j, (W j : Measure ℝ) = CentralFiber.geometricCentralWeightMeasure
      T.toTestConfiguration T.linearization (B+j+1)) ∧
    (∀ j, (W j).mass = (h0 f L (B+j+1) : ℝ≥0)) ∧
    Tendsto (fun j => (W j).normalize) atTop (𝓝 ν) ∧
    (μ.mass : ℝ) = P.selfIntersection n ∧
    μ = (P.selfIntersection n).toNNReal • ν.toFiniteMeasure ∧
    ∀ (Y : Fin (n + 1) → Set (SchemeComplexPoint f)) (hY : IsSmoothFlag Y),
      (μ : Measure ℝ) = originalFiltrationDH E F H P Y hY := by
  let := E.isSeparated
  let := E.quasiCompact
  let : CompactSpace (SchemeComplexPoint f) := E.analyticCompact
  let : Nonempty (SchemeComplexPoint f) := SGPT.TestCurve.QwNA.nonempty_schemeComplexPoint_of_isIntegral E
  let : ConnectedSpace (SchemeComplexPoint f) := SGPT.GAGA.OkoClose.connectedSpace_of_isIntegral f E n
  let F := T.inducedFiltration E (T.filtrationFinitelyGenerated E hA)
  obtain ⟨μ, hm, hlim, hscale, hall⟩ := original_source_DH_limit E H T hA P
  obtain ⟨B, hB⟩ := CentralFiber.exists_eventual_geometricCentralWeightMeasure
    T.toTestConfiguration T.linearization E hA
  have hgeo (j : ℕ) : CentralFiber.geometricCentralWeightMeasure
      T.toTestConfiguration T.linearization (B+j+1) = F.jumpMeasure (B+j+1) :=
    (hB (B+j+1) (by omega)).2 (by omega)
  have hfinite (j : ℕ) : IsFiniteMeasure (CentralFiber.geometricCentralWeightMeasure
      T.toTestConfiguration T.linearization (B+j+1)) := by
    rw [hgeo j]
    refine ⟨?_⟩
    rw [F.jumpMeasure_univ]
    exact ENNReal.natCast_lt_top _
  let W (j : ℕ) : FiniteMeasure ℝ := ⟨CentralFiber.geometricCentralWeightMeasure
    T.toTestConfiguration T.linearization (B+j+1), hfinite j⟩
  have hnorm (j : ℕ) : (rescaledFiniteMeasure F n (B+j)).normalize = (W j).normalize := by
    let c : ℝ≥0 := (n.factorial : ℝ≥0) / (B+j+1 : ℝ≥0)^n
    have hk : (B+j+1 : ℝ≥0) ≠ 0 := by positivity
    have hc : c ≠ 0 := div_ne_zero (by exact_mod_cast (Nat.factorial_pos n).ne') (pow_ne_zero n hk)
    have hs : rescaledFiniteMeasure F n (B+j) = c • W j := by
      apply FiniteMeasure.toMeasure_injective
      change ((n.factorial : ℝ≥0∞) / ((B+j+1 : ℕ) : ℝ≥0∞)^n) • F.jumpMeasure (B+j+1) =
        (c : ℝ≥0∞) • CentralFiber.geometricCentralWeightMeasure
          T.toTestConfiguration T.linearization (B+j+1)
      rw [hgeo j]
      congr 1
      simp only [c, ENNReal.coe_div (pow_ne_zero n hk), ENNReal.coe_pow,
        ENNReal.coe_natCast, ENNReal.coe_add, ENNReal.coe_one, Nat.cast_add, Nat.cast_one]
    rw [hs]
    exact normalize_pos_smul (W j) c hc
  refine ⟨μ, μ.normalize, B, W, fun _ => rfl, ?_, ?_, hm, hscale, hall⟩
  · intro j
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_mass]
    change CentralFiber.geometricCentralWeightMeasure T.toTestConfiguration T.linearization
      (B+j+1) univ = _
    rw [hgeo j, F.jumpMeasure_univ]
    simp only [h0, ENNReal.coe_natCast]
  · have ht := hlim.comp (tendsto_add_atTop_nat B)
    apply ht.congr
    intro j
    simpa only [Function.comp_apply, F, Nat.add_comm] using hnorm j

end SGPT.TestCurve.OriginalBookDH
