import SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentOverlap
import SGPT.Foundations.Analysis.FirstPass.FiniteMeasureGluing

set_option autoImplicit false

/-! # Genuine atlas-independent AC top measure of full positive global currents

The entire owned blueprint statement/proofs precede implementation.  The
measure is constructed, not assumed, and its total mass may be infinite.
-/

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions

namespace SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure
open FirstPass GlobalCurrents GlobalCurrentPotentials
  _root_.SGPT.Foundations.Analysis.LocalCurrents LocalProductCurrents
  LocalBedfordTaylorLocality LocalCurrentPullback
  ActualAnalyticCurrentLocalDensity GlobalPositiveCurrentACRestriction
  GlobalPositiveCurrentOverlap PositiveCurrentACTopMeasure

section Transport
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M]

private def invChart (e : ComplexChart n M) : e.val.target → M :=
  fun z => ((e.val.toHomeomorphSourceTarget).symm z : M)

private theorem measurableEmbedding_invChart (e : ComplexChart n M) :
    MeasurableEmbedding (invChart e) :=
  (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).comp
    (e.val.toHomeomorphSourceTarget).symm.measurableEmbedding

private def chartTransport (e : ComplexChart n M)
    (μ : Measure (ComplexModel n)) : Measure M :=
  (μ.comap (Subtype.val : e.val.target → ComplexModel n)).map (invChart e)

private theorem chartTransport_apply (e : ComplexChart n M)
    (μ : Measure (ComplexModel n)) (s : Set M) :
    chartTransport e μ s = μ (e.val.target ∩ e.val.symm ⁻¹' s) := by
  have hsub : MeasurableEmbedding (Subtype.val : e.val.target → ComplexModel n) :=
    MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet
  rw [chartTransport, (measurableEmbedding_invChart e).map_apply, hsub.comap_apply]
  congr 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hz, hzs⟩
    exact ⟨⟨z, hz⟩, hzs, rfl⟩

private theorem chartTransport_source_compl (e : ComplexChart n M)
    (μ : Measure (ComplexModel n)) :
    chartTransport e μ e.val.sourceᶜ = 0 := by
  rw [chartTransport_apply]
  have hset : e.val.target ∩ e.val.symm ⁻¹' e.val.sourceᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.2 (e.val.map_target hz.1)
  rw [hset, measure_empty]

private theorem chartTransport_restrict_source (e : ComplexChart n M)
    (μ : Measure (ComplexModel n)) :
    (chartTransport e μ).restrict e.val.source = chartTransport e μ :=
  Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (chartTransport_source_compl e μ))

private theorem measurable_inverse_preimage (e : ComplexChart n M)
    {U : Opens (ComplexModel n)} (hU : U ≤ chartTarget e)
    {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet ((U : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' s) := by
  have hf : ContinuousOn e.val.symm U := e.val.continuousOn_symm.mono hU
  have hemb := MeasurableEmbedding.subtype_coe U.isOpen.measurableSet
  have hm : Measurable ((U : Set (ComplexModel n)).domRestrict e.val.symm) :=
    (continuousOn_iff_continuous_domRestrict.mp hf).measurable
  have ht := hemb.measurableSet_image.mpr (hm hs)
  convert ht using 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists,
    exists_and_right, exists_eq_right]
  tauto

variable [IsComplexManifold n M]

private theorem chartTransport_overlap (e f : ComplexChart n M)
    {μ ν : Measure (ComplexModel n)}
    (hcov : μ.restrict (overlapSource e f) =
      (ν.restrict (overlapTarget e f)).map
        (onOpen (overlapTarget e f) (chartTransition e f).symm)) :
    (chartTransport e μ).restrict (e.val.source ∩ f.val.source) =
      (chartTransport f ν).restrict (e.val.source ∩ f.val.source) := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    chartTransport_apply, chartTransport_apply]
  let A := overlapSource e f
  let B := overlapTarget e f
  let F := chartTransition e f
  let t := (A : Set (ComplexModel n)) ∩ e.val.symm ⁻¹' s
  have ht : MeasurableSet t := measurable_inverse_preimage e (overlapSource_le e f) hs
  have hLt : e.val.target ∩ e.val.symm ⁻¹' (s ∩ (e.val.source ∩ f.val.source)) = t := by
    ext z
    change (z ∈ e.val.target ∧ e.val.symm z ∈ s ∩ (e.val.source ∩ f.val.source)) ↔
      ((z ∈ e.val.target ∧ e.val.symm z ∈ f.val.source) ∧ e.val.symm z ∈ s)
    constructor
    · rintro ⟨hz, hs', -, hf⟩
      exact ⟨⟨hz, hf⟩, hs'⟩
    · rintro ⟨⟨hz, hf⟩, hs'⟩
      exact ⟨hz, hs', e.val.map_target hz, hf⟩
  have hRt : onOpen B F.symm ⁻¹' t ∩ B =
      f.val.target ∩ f.val.symm ⁻¹' (s ∩ (e.val.source ∩ f.val.source)) := by
    ext w
    constructor
    · rintro ⟨hwt, hw⟩
      rw [mem_preimage, onOpen_of_mem hw] at hwt
      have hw' : w ∈ f.val.target ∧ f.val.symm w ∈ e.val.source := hw
      have hback : e.val.symm (F.symm w) = f.val.symm w :=
        e.val.left_inv hw'.2
      rw [mem_inter_iff, mem_preimage, hback] at hwt
      exact ⟨hw'.1, hwt.2, hw'.2, f.val.map_target hw'.1⟩
    · rintro ⟨hw, hs', he, -⟩
      have hwB : w ∈ B := ⟨hw, he⟩
      refine ⟨?_, hwB⟩
      rw [mem_preimage, onOpen_of_mem hwB]
      refine ⟨(isBiholomorphicPair_chartTransition e f).mapsTo_inv hwB, ?_⟩
      have hback : e.val.symm (F.symm w) = f.val.symm w := e.val.left_inv he
      rwa [mem_preimage, hback]
  rw [hLt, ← hRt, ← Measure.restrict_apply' B.isOpen.measurableSet,
    ← Measure.map_apply (measurable_onOpen_inv (isBiholomorphicPair_chartTransition e f)) ht,
    ← hcov, Measure.restrict_apply' A.isOpen.measurableSet,
    inter_eq_left.mpr inter_subset_left]
end Transport

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The original chart's canonical coefficientwise AC top measure, transported
only through its actual target subtype.  Infinite mass is allowed. -/
def chartACMeasure
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e : ComplexChart (m + 1) M) : Measure M :=
  chartTransport e (acTopMeasure (isPositive_chartSpanCurrent T hT e))

private theorem acTopMeasure_congr {U : Opens (ComplexModel (m + 1))}
    {S R : LocalProductCurrent (m + 1) U m}
    (hS : IsPositive S) (hR : IsPositive R) (h : S = R) :
    acTopMeasure hS = acTopMeasure hR := by
  subst R
  rfl

/-- Actual pullback/restriction internally produces every chart overlap. -/
theorem chartACMeasure_overlap
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e f : ComplexChart (m + 1) M) :
    (chartACMeasure T hT e).restrict (e.val.source ∩ f.val.source) =
      (chartACMeasure T hT f).restrict (e.val.source ∩ f.val.source) := by
  apply chartTransport_overlap
  have hc := map_acTopMeasure_eq (isBiholomorphicPair_chartTransition e f)
    (isPositive_restrict (isPositive_chartSpanCurrent T hT f) (overlapTarget_le e f))
  have heq := acTopMeasure_congr
    (isPositive_pullback (isBiholomorphicPair_chartTransition e f)
      (isPositive_restrict (isPositive_chartSpanCurrent T hT f) (overlapTarget_le e f)))
    (isPositive_restrict (isPositive_chartSpanCurrent T hT e) (overlapSource_le e f))
    (pullback_chartSpanCurrent_eq_restrict T hT e f)
  rw [acTopMeasure_restrict (isPositive_chartSpanCurrent T hT e) (overlapSource_le e f)]
    at heq
  rw [acTopMeasure_restrict (isPositive_chartSpanCurrent T hT f) (overlapTarget_le e f)]
    at hc
  exact heq.symm.trans hc.symm

private theorem chartACMeasure_restrict_source
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e : ComplexChart (m + 1) M) :
    (chartACMeasure T hT e).restrict e.val.source = chartACMeasure T hT e :=
  chartTransport_restrict_source e _

omit [MeasurableSpace M] [BorelSpace M] [IsComplexManifold (m + 1) M] in
private theorem exists_finite_original_charts [CompactSpace M] :
    ∃ k : ℕ, ∃ E : Fin k → ComplexChart (m + 1) M,
      ∀ x : M, ∃ i, x ∈ (E i).val.source := by
  classical
  let U : M → Set M := fun x => (complexChartAt (n := m + 1) x).val.source
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U
    (fun x => (complexChartAt (n := m + 1) x).val.open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_complexChartAt_source x⟩)
  let a := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun i => complexChartAt (a i).val, fun x => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  refine ⟨a.symm ⟨y, hyt⟩, ?_⟩
  simpa only [Equiv.apply_symm_apply] using hxy

/-- The natural compact manifold and original positive current produce the
unique global measure; no atlas or compatibility witness is an input. -/
theorem existsUnique_globalACtopMeasure [CompactSpace M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) :
    ∃! μ : Measure M, ∀ e : ComplexChart (m + 1) M,
      μ.restrict e.val.source = chartACMeasure T hT e := by
  classical
  obtain ⟨k, E, hE⟩ := exists_finite_original_charts (m := m) (M := M)
  let U : Fin k → Set M := fun i => (E i).val.source
  let μ := FiniteMeasureGluing.glue U (fun i => chartACMeasure T hT (E i))
  have hU : ∀ i, MeasurableSet (U i) := fun i => (E i).val.open_source.measurableSet
  have hcover : ⋃ i, U i = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨i, hi⟩ := hE x
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hμ : ∀ e : ComplexChart (m + 1) M,
      μ.restrict e.val.source = chartACMeasure T hT e := by
    intro e
    have hsub : e.val.source ⊆ ⋃ i, U i := by rw [hcover]; exact subset_univ _
    exact (FiniteMeasureGluing.glue_restrict U _ hU e.val.open_source.measurableSet
      hsub _ (fun i => chartACMeasure_overlap T hT (E i) e)).trans
        (chartACMeasure_restrict_source T hT e)
  refine ⟨μ, hμ, fun ν hν => ?_⟩
  apply FiniteMeasureGluing.ext_of_restrict_eq U hU hcover
  intro i
  exact (hν (E i)).trans (hμ (E i)).symm

/-- The constructed atlas-independent measure; no finite-mass instance is
claimed, and closedness is not used. -/
def globalACtopMeasure [CompactSpace M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) : Measure M :=
  (existsUnique_globalACtopMeasure T hT).exists.choose

/-- Every original chart, including one outside the internally chosen cover,
recovers its original AC top measure on ALL measurable sets. -/
theorem globalACtopMeasure_restrict_chart [CompactSpace M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (e : ComplexChart (m + 1) M) :
    (globalACtopMeasure T hT).restrict e.val.source = chartACMeasure T hT e :=
  (existsUnique_globalACtopMeasure T hT).exists.choose_spec e

/-- Uniqueness is a consumer of the already internally constructed measure. -/
theorem globalACtopMeasure_unique [CompactSpace M]
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (hT : IsFullPositive T) (ν : Measure M)
    (hν : ∀ e : ComplexChart (m + 1) M,
      ν.restrict e.val.source = chartACMeasure T hT e) :
    ν = globalACtopMeasure T hT :=
  (existsUnique_globalACtopMeasure T hT).unique hν
    (globalACtopMeasure_restrict_chart T hT)

end SGPT.Foundations.Analysis.Pending.GlobalPositiveCurrentACTopMeasure
