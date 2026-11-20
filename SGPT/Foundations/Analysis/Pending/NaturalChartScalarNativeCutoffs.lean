import SGPT.Foundations.Analysis.Pending.NaturalChartCutoffCoefficientTests
import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.XiaoChartLocalization

/-! # Actual global scalar cutoffs transported to whole native chart tests -/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.NaturalChartScalarNativeCutoffs

open FirstPass ProductTestForms ChartPartition NaturalChartCutoffCoefficientTests XiaoChartLocalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal original scalar chart restriction, with its actual zero branch. -/
def scalarChartRestriction (e : ComplexChart n M) (f : M → ℝ) : ComplexModel n → ℝ :=
  e.val.target.indicator fun y => f (e.val.symm y)

omit [IsComplexManifold n M] in
theorem scalarChartRestriction_of_mem (e : ComplexChart n M) (f : M → ℝ)
    (y : ComplexModel n) (hy : y ∈ e.val.target) :
    scalarChartRestriction e f y = f (e.val.symm y) := indicator_of_mem hy _

omit [IsComplexManifold n M] in
theorem scalarChartRestriction_of_notMem (e : ComplexChart n M) (f : M → ℝ)
    (y : ComplexModel n) (hy : y ∉ e.val.target) :
    scalarChartRestriction e f y = 0 := indicator_of_notMem hy _

omit [IsComplexManifold n M] in
/-- The whole scalar is zero outside the literal image of the original topological support. -/
theorem scalarChartRestriction_zero_of_notMem_image (e : ComplexChart n M) (f : M → ℝ)
    (y : ComplexModel n) (hy : y ∉ e.val '' tsupport f) :
    scalarChartRestriction e f y = 0 := by
  by_cases hyt : y ∈ e.val.target
  · rw [scalarChartRestriction_of_mem e f y hyt]
    by_contra hne
    exact hy ⟨e.val.symm y, subset_tsupport f hne, e.val.right_inv hyt⟩
  · exact scalarChartRestriction_of_notMem e f y hyt

/-- Target smoothness and the genuine compact zero germ internally give whole native scalar smoothness. -/
theorem scalarChartRestriction_smooth_support (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) :
    ContDiff ℝ (⊤ : ℕ∞) (scalarChartRestriction e f) ∧
      HasCompactSupport (scalarChartRestriction e f) ∧
      tsupport (scalarChartRestriction e f) ⊆ e.val '' tsupport f := by
  let K : Set (ComplexModel n) := e.val '' tsupport f
  have hKc : IsCompact K := hc.image_of_continuousOn (e.val.continuousOn.mono hs)
  have hKt : K ⊆ e.val.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.val.map_source (hs hx)
  have hsupport : Function.support (scalarChartRestriction e f) ⊆ K := by
    intro y hy
    by_contra h
    exact hy (scalarChartRestriction_zero_of_notMem_image e f y h)
  refine ⟨contDiff_iff_contDiffAt.2 (fun y => ?_),
    HasCompactSupport.of_support_subset_isCompact hKc hsupport,
    closure_minimal hsupport hKc.isClosed⟩
  by_cases hyt : y ∈ e.val.target
  · have heq : scalarChartRestriction e f =ᶠ[𝓝 y] fun z => f (e.val.symm z) := by
      filter_upwards [e.val.open_target.mem_nhds hyt] with z hz
      exact scalarChartRestriction_of_mem e f z hz
    exact ((hf e).contDiffAt (e.val.open_target.mem_nhds hyt)).congr_of_eventuallyEq heq
  · have hyK : y ∉ K := fun h => hyt (hKt h)
    have heq : scalarChartRestriction e f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hyK] with z hz
      exact scalarChartRestriction_zero_of_notMem_image e f z hz
    exact contDiffAt_const.congr_of_eventuallyEq heq

omit [IsComplexManifold n M] in
/-- The actual compact image of the original scalar topological support. -/
def transportedScalarCompact (e : ComplexChart n M) (f : M → ℝ)
    (hc : IsCompact (tsupport f)) (hs : tsupport f ⊆ e.val.source) :
    Compacts (ComplexModel n) :=
  ⟨e.val '' tsupport f, hc.image_of_continuousOn (e.val.continuousOn.mono hs)⟩

omit [IsComplexManifold n M] in
theorem transportedScalarCompact_coe (e : ComplexChart n M) (f : M → ℝ)
    (hc : IsCompact (tsupport f)) (hs : tsupport f ⊆ e.val.source) :
    (transportedScalarCompact e f hc hs : Set (ComplexModel n)) = e.val '' tsupport f := rfl

omit [IsComplexManifold n M] in
theorem transportedScalarCompact_subset_target (e : ComplexChart n M) (f : M → ℝ)
    (hc : IsCompact (tsupport f)) (hs : tsupport f ⊆ e.val.source) :
    (transportedScalarCompact e f hc hs : Set (ComplexModel n)) ⊆ e.val.target := by
  rintro _ ⟨x, hx, rfl⟩
  exact e.val.map_source (hs hx)

/-- Genuine original infinitely smooth scalar test on its internally transported actual compact. -/
def nativeScalarChartCutoff (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) :
    𝓓_{transportedScalarCompact e f hc hs}(ComplexModel n, ℝ) :=
  ⟨scalarChartRestriction e f, (scalarChartRestriction_smooth_support e f hf hc hs).1,
    fun y hy => scalarChartRestriction_zero_of_notMem_image e f y hy⟩

theorem nativeScalarChartCutoff_apply (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) (y : ComplexModel n) :
    nativeScalarChartCutoff e f hf hc hs y = scalarChartRestriction e f y := rfl

theorem nativeScalarChartCutoff_of_mem (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) (y : ComplexModel n) (hy : y ∈ e.val.target) :
    nativeScalarChartCutoff e f hf hc hs y = f (e.val.symm y) :=
  scalarChartRestriction_of_mem e f y hy

theorem nativeScalarChartCutoff_of_notMem (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) (y : ComplexModel n) (hy : y ∉ e.val.target) :
    nativeScalarChartCutoff e f hf hc hs y = 0 :=
  scalarChartRestriction_of_notMem e f y hy

theorem nativeScalarChartCutoff_tsupport_subset (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) :
    tsupport (nativeScalarChartCutoff e f hf hc hs : ComplexModel n → ℝ) ⊆
      transportedScalarCompact e f hc hs :=
  (nativeScalarChartCutoff e f hf hc hs).tsupport_subset

/-- The original scalar is literally recovered at every manifold point by its original chart extension. -/
theorem chartExtend_nativeScalarChartCutoff (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) :
    chartExtend e (nativeScalarChartCutoff e f hf hc hs) = f := by
  funext x
  by_cases hx : x ∈ e.val.source
  · rw [chartExtend_of_mem hx,
      nativeScalarChartCutoff_of_mem e f hf hc hs (e.val x) (e.val.map_source hx), e.val.left_inv hx]
  · rw [chartExtend_of_notMem hx]
    symm
    by_contra hne
    exact hx (hs (subset_tsupport f hne))

omit [IsComplexManifold n M] in
/-- Original subordination gives literal ball containment of the actual transported compact. -/
theorem transportedScalarCompact_subset_ball (e : ComplexChart n M) (f : M → ℝ)
    (hc : IsCompact (tsupport f)) (hs : tsupport f ⊆ e.val.source)
    (z : ComplexModel n) (r : ℝ) (hball : tsupport f ⊆ e.val ⁻¹' Metric.ball z r) :
    (transportedScalarCompact e f hc hs : Set (ComplexModel n)) ⊆ Metric.ball z r := by
  rintro _ ⟨x, hx, rfl⟩
  exact hball hx

/-- Entire original native vector cutoff equals the actual earlier indicator localization, with every off-target value read back. -/
theorem native_cutoff_product_eq_localizedCoeff (e : ComplexChart n M) (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (hc : IsCompact (tsupport f))
    (hs : tsupport f ⊆ e.val.source) (q : ℕ) (α : SmoothRealForm n M q) :
    (chartCutoffTest e (transportedScalarCompact e f hc hs)
      (transportedScalarCompact_subset_target e f hc hs) (nativeScalarChartCutoff e f hf hc hs) α :
      ComplexModel n → StronglyPositiveForms.RealForm n q) = localizedCoeff e f α := by
  funext y
  rw [chartCutoffTest_apply]
  by_cases hy : y ∈ e.val.target
  · rw [nativeScalarChartCutoff_of_mem e f hf hc hs y hy, localizedCoeff, indicator_of_mem hy]
  · rw [nativeScalarChartCutoff_of_notMem e f hf hc hs y hy, localizedCoeff, indicator_of_notMem hy,
      zero_smul]

end SGPT.Foundations.Analysis.Pending.NaturalChartScalarNativeCutoffs
