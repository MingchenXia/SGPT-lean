import SGPT.Foundations.Analysis.Pending.NaturalHermitianCompleteChartLocalization
import SGPT.Foundations.Analysis.Pending.NaturalChartScalarNativeCutoffs

/-! # Internally finite original chart cutoffs on the whole energy graph -/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff BigOperators Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianFiniteChartLocalizers

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses NaturalHermitianSmoothFormMetric
  NaturalHermitianMetricCoefficients NaturalHermitianOrthonormalFormBasis
  NaturalHermitianFrozenCoefficientSobolev NaturalCoefficientSobolevRellich
  NaturalHermitianGraphEnergy NaturalHermitianCompleteChartLocalization
  NaturalChartScalarNativeCutoffs NaturalChartCutoffCoefficientTests
  ChartPartition XiaoChartLocalization ProductTestForms

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

local instance formNormedAddCommGroup (q : ℕ) : NormedAddCommGroup (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedAddCommGroup

local instance formNormedSpace (q : ℕ) : NormedSpace ℝ (FormCoefficients n q) :=
  ContinuousAlternatingMap.instNormedSpace

local instance graphNormedAddCommGroup (w : KahlerBackground n M) (q : ℕ) :
    NormedAddCommGroup (GraphEnergy w q) :=
  Submodule.normedAddCommGroup (graphEnergySubmodule w q)

local instance graphInnerProductSpace (w : KahlerBackground n M) (q : ℕ) :
    InnerProductSpace ℝ (GraphEnergy w q) :=
  Submodule.innerProductSpace (graphEnergySubmodule w q)

/-- The actual local geometry and readback output of the original local Gårding construction. -/
structure ChartBallLocalizer (w : KahlerBackground n M) (q : ℕ) where
  chart : ComplexChart n M
  center : ComplexModel n
  center_mem : center ∈ chart.val.target
  basis : Module.Basis (Fin (n * 2)) ℝ (ComplexModel n)
  orthonormal : ∀ i j,
    associatedMetricCLM (w.form.val.coeff chart center) (basis i) (basis j) =
      if i = j then 1 else 0
  positive_orientation : basis.orientation = (coordinateRealBasis n).orientation
  radius : ℝ
  radius_pos : 0 < radius
  ball_target : Metric.ball center radius ⊆ chart.val.target
  readback : ∀ (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ Metric.ball center radius)
    (φ : 𝓓_{K}(ComplexModel n, ℝ)) (α : SmoothRealForm n M q),
    completeChartValueCLM w chart q center center_mem basis K (hK.trans ball_target) φ
      (smoothEnergyLinear w q α) =
    fixedFormValueCLM basis q volume K (fixedFormCoefficientJet
      (w.form.val.coeff chart center) (w.isKahler.1 chart center center_mem).1
      (w.isKahler.1 chart center center_mem).2 basis q volume K
      (chartCutoffTest chart K (hK.trans ball_target) φ α))

/-- The literal inverse-chart image of the good ball, with no total-map off-source values. -/
def chartBallOpen {w : KahlerBackground n M} {q : ℕ} (d : ChartBallLocalizer w q) : Opens M :=
  ⟨d.chart.val.symm '' Metric.ball d.center d.radius,
    d.chart.val.isOpen_image_symm_of_subset_target Metric.isOpen_ball d.ball_target⟩

theorem chartBallOpen_subset_source {w : KahlerBackground n M} {q : ℕ}
    (d : ChartBallLocalizer w q) : (chartBallOpen d : Set M) ⊆ d.chart.val.source := by
  rintro _ ⟨y, hy, rfl⟩
  exact d.chart.val.map_target (d.ball_target hy)

theorem chartBallOpen_subset_preimage_ball {w : KahlerBackground n M} {q : ℕ}
    (d : ChartBallLocalizer w q) :
    (chartBallOpen d : Set M) ⊆ d.chart.val ⁻¹' Metric.ball d.center d.radius := by
  rintro _ ⟨y, hy, rfl⟩
  change d.chart.val (d.chart.val.symm y) ∈ Metric.ball d.center d.radius
  rw [d.chart.val.right_inv (d.ball_target hy)]
  exact hy

/-- Every original point is covered by geometry internally produced from the actual background. -/
theorem exists_chartBallLocalizer_at (w : KahlerBackground n M) (q : ℕ) (x : M) :
    ∃ d : ChartBallLocalizer w q, x ∈ chartBallOpen d := by
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨b, hb, ho, r, hr, hball, hlocal⟩ :=
    exists_compact_complete_chart_localization w e q (e.val x) hz
  let d : ChartBallLocalizer w q :=
    ⟨e, e.val x, hz, b, hb, ho, r, hr, hball, fun K hK φ => (hlocal K hK φ).2⟩
  refine ⟨d, ?_⟩
  change x ∈ e.val.symm '' Metric.ball (e.val x) r
  exact ⟨e.val x, Metric.mem_ball_self hr, e.val.left_inv hx⟩

/-- A genuinely finite original partition with its original good chart geometry. -/
structure FiniteChartLocalization (w : KahlerBackground n M) (q : ℕ) where
  card : ℕ
  localizer : Fin card → ChartBallLocalizer w q
  cutoff : Fin card → M → ℝ
  smooth : ∀ i, ChartSmooth (n := n) (cutoff i)
  nonneg : ∀ i x, 0 ≤ cutoff i x
  support_ball : ∀ i, tsupport (cutoff i) ⊆ (chartBallOpen (localizer i) : Set M)
  support_compact : ∀ i, IsCompact (tsupport (cutoff i))
  sum_one : ∀ x, ∑ i, cutoff i x = 1

/-- The original good-ball cover and original partition theorem internally produce the finite data. -/
theorem exists_finiteChartLocalization (w : KahlerBackground n M) (q : ℕ) :
    Nonempty (FiniteChartLocalization w q) := by
  classical
  choose d hd using exists_chartBallLocalizer_at w q
  obtain ⟨m, χ, idx, hsm, hn, hs, hc, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) (fun x => chartBallOpen (d x))
      (fun x => ⟨x, hd x⟩)
  exact ⟨⟨m, fun i => d (idx i), χ, hsm, hn, hs, hc, hsum⟩⟩

/-- The literal original chart image of the compact scalar topological support. -/
def finiteChartCompact {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (i : Fin D.card) : Compacts (ComplexModel n) :=
  transportedScalarCompact (D.localizer i).chart (D.cutoff i) (D.support_compact i)
    ((D.support_ball i).trans (chartBallOpen_subset_source (D.localizer i)))

theorem finiteChartCompact_subset_ball {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (i : Fin D.card) :
    (finiteChartCompact D i : Set (ComplexModel n)) ⊆
      Metric.ball (D.localizer i).center (D.localizer i).radius :=
  transportedScalarCompact_subset_ball (D.localizer i).chart (D.cutoff i)
    (D.support_compact i) ((D.support_ball i).trans (chartBallOpen_subset_source (D.localizer i)))
    (D.localizer i).center (D.localizer i).radius
    ((D.support_ball i).trans (chartBallOpen_subset_preimage_ball (D.localizer i)))

theorem finiteChartCompact_subset_target {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (i : Fin D.card) :
    (finiteChartCompact D i : Set (ComplexModel n)) ⊆ (D.localizer i).chart.val.target :=
  (finiteChartCompact_subset_ball D i).trans (D.localizer i).ball_target

/-- The genuine native scalar cutoff on its internally transported original compact. -/
def finiteNativeCutoff {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (i : Fin D.card) :
    𝓓_{finiteChartCompact D i}(ComplexModel n, ℝ) :=
  nativeScalarChartCutoff (D.localizer i).chart (D.cutoff i) (D.smooth i)
    (D.support_compact i) ((D.support_ball i).trans (chartBallOpen_subset_source (D.localizer i)))

theorem finiteNativeCutoff_reextension {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (i : Fin D.card) :
    chartExtend (D.localizer i).chart (finiteNativeCutoff D i) = D.cutoff i :=
  chartExtend_nativeScalarChartCutoff (D.localizer i).chart (D.cutoff i) (D.smooth i)
    (D.support_compact i) ((D.support_ball i).trans (chartBallOpen_subset_source (D.localizer i)))

theorem sum_finiteNativeCutoff_reextension {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (x : M) :
    ∑ i, chartExtend (D.localizer i).chart (finiteNativeCutoff D i) x = 1 := by
  simp only [finiteNativeCutoff_reextension]
  exact D.sum_one x

theorem finite_native_cutoff_product_eq_localizedCoeff {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (i : Fin D.card) (α : SmoothRealForm n M q) :
    (chartCutoffTest (D.localizer i).chart (finiteChartCompact D i)
      (finiteChartCompact_subset_target D i) (finiteNativeCutoff D i) α :
        ComplexModel n → StronglyPositiveForms.RealForm n q) =
      localizedCoeff (D.localizer i).chart (D.cutoff i) α :=
  native_cutoff_product_eq_localizedCoeff (D.localizer i).chart (D.cutoff i) (D.smooth i)
    (D.support_compact i) ((D.support_ball i).trans (chartBallOpen_subset_source (D.localizer i))) q α

/-- The actual full-graph compact chart value map of an internally selected finite member. -/
def finiteChartValueCLM {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (i : Fin D.card) :
    GraphEnergy w q →L[ℝ] CoefficientL2 (volume : Measure (ComplexModel n)) (FormIndex n q) :=
  completeChartValueCLM w (D.localizer i).chart q (D.localizer i).center
    (D.localizer i).center_mem (D.localizer i).basis (finiteChartCompact D i)
    (finiteChartCompact_subset_target D i) (finiteNativeCutoff D i)

theorem finiteChartValueCLM_isCompactOperator {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (i : Fin D.card) :
    IsCompactOperator (finiteChartValueCLM D i) :=
  completeChartValueCLM_isCompactOperator w (D.localizer i).chart q (D.localizer i).center
    (D.localizer i).center_mem (D.localizer i).basis (finiteChartCompact D i)
    (finiteChartCompact_subset_target D i) (finiteNativeCutoff D i)

theorem finiteChartValueCLM_smooth_readback {w : KahlerBackground n M} {q : ℕ}
    (D : FiniteChartLocalization w q) (i : Fin D.card) (α : SmoothRealForm n M q) :
    finiteChartValueCLM D i (smoothEnergyLinear w q α) =
      fixedFormValueCLM (D.localizer i).basis q volume (finiteChartCompact D i)
        (fixedFormCoefficientJet (w.form.val.coeff (D.localizer i).chart (D.localizer i).center)
          (w.isKahler.1 (D.localizer i).chart (D.localizer i).center (D.localizer i).center_mem).1
          (w.isKahler.1 (D.localizer i).chart (D.localizer i).center (D.localizer i).center_mem).2
          (D.localizer i).basis q volume (finiteChartCompact D i)
          (chartCutoffTest (D.localizer i).chart (finiteChartCompact D i)
            (finiteChartCompact_subset_target D i) (finiteNativeCutoff D i) α)) :=
  (D.localizer i).readback (finiteChartCompact D i) (finiteChartCompact_subset_ball D i)
    (finiteNativeCutoff D i) α

/-- Only the original background and degree are supplied: the finite family and all its compact readbacks are internal outputs. -/
theorem exists_finite_compact_chart_localizers (w : KahlerBackground n M) (q : ℕ) :
    ∃ D : FiniteChartLocalization w q, ∀ i : Fin D.card,
      IsCompactOperator (finiteChartValueCLM D i) ∧
      (∀ α : SmoothRealForm n M q,
        finiteChartValueCLM D i (smoothEnergyLinear w q α) =
          fixedFormValueCLM (D.localizer i).basis q volume (finiteChartCompact D i)
            (fixedFormCoefficientJet (w.form.val.coeff (D.localizer i).chart (D.localizer i).center)
              (w.isKahler.1 (D.localizer i).chart (D.localizer i).center (D.localizer i).center_mem).1
              (w.isKahler.1 (D.localizer i).chart (D.localizer i).center (D.localizer i).center_mem).2
              (D.localizer i).basis q volume (finiteChartCompact D i)
              (chartCutoffTest (D.localizer i).chart (finiteChartCompact D i)
                (finiteChartCompact_subset_target D i) (finiteNativeCutoff D i) α))) := by
  obtain ⟨D⟩ := exists_finiteChartLocalization w q
  exact ⟨D, fun i => ⟨finiteChartValueCLM_isCompactOperator D i,
    finiteChartValueCLM_smooth_readback D i⟩⟩

end SGPT.Foundations.Analysis.Pending.NaturalHermitianFiniteChartLocalizers
