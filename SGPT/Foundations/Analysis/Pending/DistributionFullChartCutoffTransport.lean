import SGPT.Foundations.Analysis.Pending.DistributionChartPullback
import SGPT.Foundations.Analysis.Pending.DistributionCutoffExtension
import SGPT.Foundations.Analysis.Pending.ChartPartition

set_option autoImplicit false

/-! Actual LF transport from every full chart, with an internally constructed
chart-supported weight. ENTIRE BP proofs precede this file. Chart directions
are f-coordinates to e-coordinates: F=e after inverse f. No global BC claim. -/

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.DistributionFullChartCutoffTransport
open FirstPass ThetaPshChartLimitGluing DistributionChartPullback DistributionCutoffExtension

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem chartWeight_data (f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) :
    let g := f.val.target.indicator (fun z => χ (f.val.symm z))
    ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ f.val.target := by
  let K : Set (ComplexModel n) := f.val '' tsupport χ
  have hKc : IsCompact K := hc.image_of_continuousOn (f.val.continuousOn.mono hs)
  have hKt : K ⊆ f.val.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact f.val.map_source (hs hx)
  let g := f.val.target.indicator (fun z => χ (f.val.symm z))
  have hgK : tsupport g ⊆ K := by
    refine closure_minimal (fun z hz => ?_) hKc.isClosed
    have hzt : z ∈ f.val.target := by
      by_contra h
      exact hz (indicator_of_notMem h _)
    have hn : χ (f.val.symm z) ≠ 0 := by
      intro h
      exact hz (by simp [g, indicator_of_mem hzt, h])
    exact ⟨f.val.symm z, subset_tsupport _ hn, f.val.right_inv hzt⟩
  have hgt := hgK.trans hKt
  have hgo : ContDiffOn ℝ ∞ g f.val.target :=
    (hχ f).congr fun z hz => indicator_of_mem hz _
  refine ⟨?_, hKc.of_isClosed_subset (isClosed_tsupport g) hgK, hgt⟩
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ f.val.target
  · exact hgo.contDiffAt (f.val.open_target.mem_nhds hz)
  · have hzs : z ∉ tsupport g := fun h => hz (hgt h)
    have he : g =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hzs] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact contDiffAt_const.congr_of_eventuallyEq he

/-- Original globally smooth compact chart test, with no chosen cutoff input. -/
def chartWeightTest (f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) : 𝓓(chartTarget f, ℝ) :=
  let h := chartWeight_data f χ hχ hc hs
  ⟨f.val.target.indicator (fun z => χ (f.val.symm z)), h.1, h.2.1, h.2.2⟩

private theorem exists_overlap_cutoff (e f : ComplexChart n M) (χ : M → ℝ)
    (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ f.val.source)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target) :
    ∃ θ : 𝓓(overlapTarget f e, ℝ), ∀ z ∈ (chartTransition f e).source,
      χ (f.val.symm z) ≠ 0 → (chartTransition f e) z ∈ K →
        θ ((chartTransition f e) z) = 1 := by
  let A : Set M := e.val.symm '' (K : Set (ComplexModel n))
  have hAc : IsCompact A := K.isCompact.image_of_continuousOn (e.val.symm.continuousOn.mono hK)
  have hAs : A ⊆ e.val.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact e.val.map_target (hK hz)
  let I : Set M := A ∩ tsupport χ
  have hIc : IsCompact I := hAc.inter hc
  have hIe : I ⊆ e.val.source := inter_subset_left.trans hAs
  have hIf : I ⊆ f.val.source := inter_subset_right.trans hs
  have hJc : IsCompact (e.val '' I) := hIc.image_of_continuousOn (e.val.continuousOn.mono hIe)
  have hJ : e.val '' I ⊆ overlapTarget f e := by
    rintro _ ⟨y, hy, rfl⟩
    change e.val y ∈ e.val.target ∩ e.val.symm ⁻¹' f.val.source
    refine ⟨e.val.map_source (hIe hy), ?_⟩
    change e.val.symm (e.val y) ∈ f.val.source
    rw [e.val.left_inv (hIe hy)]
    exact hIf hy
  obtain ⟨θ, hθ, _⟩ := exists_testFunction_eq_one_nhds_compact hJc hJ
  refine ⟨θ, fun z hz hn hk => hθ.self_of_nhdsSet _ ?_⟩
  refine ⟨f.val.symm z, ⟨?_, subset_tsupport _ hn⟩, rfl⟩
  refine ⟨(chartTransition f e) z, hk, ?_⟩
  change e.val.symm (e.val (f.val.symm z)) = f.val.symm z
  exact e.val.left_inv hz.2

private def overlapCutoff (e f : ComplexChart n M) (χ : M → ℝ)
    (hc : IsCompact (tsupport χ)) (hs : tsupport χ ⊆ f.val.source)
    (K : Compacts (ComplexModel n)) (hK : (K : Set (ComplexModel n)) ⊆ e.val.target) :
    𝓓(overlapTarget f e, ℝ) := (exists_overlap_cutoff e f χ hc hs K hK).choose

private def fixedMap (e f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target) :
    𝓓(chartTarget e, ℝ) →L[ℝ] 𝓓(chartTarget f, ℝ) :=
  (cutoffTestCLM (Ω := overlapSource f e) (chartWeightTest f χ hχ hc hs)).comp
    ((weightedTestCLM f e).comp
      (cutoffTestCLM (Ω := chartTarget e) (overlapCutoff e f χ hc hs K hK)))

private theorem fixedMap_value (e f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) (K : Compacts (ComplexModel n))
    (hK : (K : Set (ComplexModel n)) ⊆ e.val.target)
    (φ : 𝓓(chartTarget e, ℝ)) (hφ : tsupport φ ⊆ K) (z : ComplexModel n) :
    fixedMap e f χ hχ hc hs K hK φ z =
      pullFun f e φ z * chartWeightTest f χ hχ hc hs z := by
  change pullFun f e (cutoffTestCLM (overlapCutoff e f χ hc hs K hK) φ) z *
      chartWeightTest f χ hχ hc hs z = _
  by_cases hz : z ∈ (chartTransition f e).source
  · rw [pullFun_of_mem f e _ hz, pullFun_of_mem f e _ hz]
    change transitionJac f e z * (φ ((chartTransition f e) z) *
      overlapCutoff e f χ hc hs K hK ((chartTransition f e) z)) * _ = _
    by_cases hp : φ ((chartTransition f e) z) = 0
    · simp [hp]
    by_cases hn : χ (f.val.symm z) = 0
    · have hw : chartWeightTest f χ hχ hc hs z = 0 := by
        change f.val.target.indicator (fun y => χ (f.val.symm y)) z = 0
        have hzt : z ∈ f.val.target := hz.1
        rw [indicator_of_mem hzt, hn]
      simp [hw]
    have hθ := (exists_overlap_cutoff e f χ hc hs K hK).choose_spec z hz hn
      (hφ (subset_tsupport _ hp))
    rw [show overlapCutoff e f χ hc hs K hK ((chartTransition f e) z) = 1 from hθ,
      mul_one]
  · rw [pullFun_of_notMem f e _ hz, pullFun_of_notMem f e _ hz]

private def fullTest (e f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) (φ : 𝓓(chartTarget e, ℝ)) :
    𝓓(chartTarget f, ℝ) :=
  fixedMap e f χ hχ hc hs ⟨tsupport φ, φ.hasCompactSupport⟩ φ.tsupport_subset φ

private theorem fullTest_value (e f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) (φ : 𝓓(chartTarget e, ℝ)) (z : ComplexModel n) :
    fullTest e f χ hχ hc hs φ z = pullFun f e φ z * chartWeightTest f χ hχ hc hs z :=
  fixedMap_value e f χ hχ hc hs _ _ φ Subset.rfl z

/-- Genuine continuous LF transport of all full-chart tests; internal compact
cutoffs produce continuity, and the displayed value is independent of them. -/
def fullChartTestCLM (e f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) :
    𝓓(chartTarget e, ℝ) →L[ℝ] 𝓓(chartTarget f, ℝ) :=
  TestFunction.limitCLM ℝ (fullTest e f χ hχ hc hs)
    (fun K hK => (fixedMap e f χ hχ hc hs K hK).comp
      (TestFunction.ofSupportedInCLM ℝ hK))
    (fun K hK φ => by
      apply TestFunction.ext
      intro z
      rw [fullTest_value]
      exact (fixedMap_value e f χ hχ hc hs K hK
        (TestFunction.ofSupportedIn hK φ) φ.tsupport_subset z).symm)

open Classical in
/-- Literal formula, in the actual f-to-e coordinate direction, for every full
input test. There is no incoming overlap-support hypothesis. -/
theorem fullChartTestCLM_value (e f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) (φ : 𝓓(chartTarget e, ℝ)) (z : ComplexModel n) :
    fullChartTestCLM e f χ hχ hc hs φ z =
      if z ∈ (chartTransition f e).source then
        χ (f.val.symm z) * transitionJac f e z * φ ((chartTransition f e) z) else 0 := by
  change fullTest e f χ hχ hc hs φ z = _
  rw [fullTest_value]
  by_cases hz : z ∈ (chartTransition f e).source
  · rw [if_pos hz, pullFun_of_mem f e _ hz]
    change transitionJac f e z * φ ((chartTransition f e) z) *
      f.val.target.indicator (fun y => χ (f.val.symm y)) z = _
    have hzt : z ∈ f.val.target := hz.1
    rw [indicator_of_mem hzt]
    ring
  · rw [if_neg hz, pullFun_of_notMem f e _ hz, zero_mul]

/-- Actual signed full-chart distribution, not a chosen density representation. -/
def weightedChartDistribution (e f : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (hc : IsCompact (tsupport χ))
    (hs : tsupport χ ⊆ f.val.source) (R : 𝓓'(chartTarget f, ℝ)) :
    𝓓'(chartTarget e, ℝ) := R.comp (fullChartTestCLM e f χ hχ hc hs)

end SGPT.Foundations.Analysis.Pending.DistributionFullChartCutoffTransport
