import SGPT.Foundations.Analysis.Pending.NaturalHermitianHodgeStar
import SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false

/-! # The actual global measure of original Hermitian metric unit volume

The entire mathematical blueprint predates this SOURCE. Original chart
densities and genuine chart transport construct the global measure internally.
No global volume measure, atlas, compatibility or existence certificate is an
input. Closedness, connectedness and positive dimension are not assumed.
-/

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.NaturalHermitianVolumeMeasure

open FirstPass NaturalHermitianHodgeStar NaturalHermitianTopFormOrientation
  TopDegreeDensity ChartwiseGlobalL1

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The literal target-supported density of the actual original metric unit volume. -/
def chartDensityMeasure (w : SmoothRealForm n M 2) (e : ComplexChart n M) :
    Measure (ComplexModel n) :=
  (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (metricVolumeDensity w e z))

/-- The original chart volume, transported through the actual inverse chart. -/
def chartVolumeMeasure (w : SmoothRealForm n M 2) (e : ComplexChart n M) : Measure M :=
  (chartDensityMeasure w e).map e.val.symm

omit [MeasurableSpace M] [BorelSpace M] in
/-- The actual full volume tensor law gives its precise real Jacobian density. -/
theorem metricVolumeDensity_transport (w : SmoothRealForm n M 2)
    (e f : ComplexChart n M) (z : ComplexModel n)
    (hz : z ∈ (chartTransition e f).source) :
    metricVolumeDensity w e z =
      LinearMap.det (chartTransitionDerivative e f z : ComplexModel n →ₗ[ℝ] ComplexModel n) *
        metricVolumeDensity w f (chartTransition e f z) := by
  unfold metricVolumeDensity
  rw [metricVolumeCoefficients_transport w e f z hz, topDensity_compContinuousLinearMap]

private theorem inverse_chart_aemeasurable (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) : AEMeasurable e.val.symm (chartDensityMeasure w e) :=
  (e.val.continuousOn_symm.aemeasurable e.val.open_target.measurableSet).mono_ac
    (withDensity_absolutelyContinuous _ _)

/-- Exact genuine measurable-set evaluation of the actual inverse-chart pushforward. -/
theorem chartVolumeMeasure_apply (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) {s : Set M} (hs : MeasurableSet s) :
    chartVolumeMeasure w e s =
      ∫⁻ z in e.val.target ∩ e.val.symm ⁻¹' s, ENNReal.ofReal (metricVolumeDensity w e z) := by
  rw [chartVolumeMeasure, Measure.map_apply_of_aemeasurable (inverse_chart_aemeasurable w e) hs,
    chartDensityMeasure, withDensity_apply' _ _,
    Measure.restrict_restrict' e.val.open_target.measurableSet, inter_comm]

private theorem chartVolumeMeasure_source_compl (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) : chartVolumeMeasure w e e.val.sourceᶜ = 0 := by
  rw [chartVolumeMeasure_apply w e e.val.open_source.measurableSet.compl]
  have hset : e.val.target ∩ e.val.symm ⁻¹' e.val.sourceᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.2 (e.val.map_target hz.1)
  rw [hset, Measure.restrict_empty, lintegral_zero_measure]

/-- The actual original chart volume is entirely supported on its genuine chart source. -/
theorem chartVolumeMeasure_restrict_source (w : SmoothRealForm n M 2)
    (e : ComplexChart n M) :
    (chartVolumeMeasure w e).restrict e.val.source = chartVolumeMeasure w e :=
  Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr (chartVolumeMeasure_source_compl w e))

omit [IsComplexManifold n M] in
private theorem measurable_inverse_preimage (e : ComplexChart n M)
    {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet (e.val.target ∩ e.val.symm ⁻¹' s) := by
  have hm : Measurable (e.val.target.domRestrict e.val.symm) :=
    e.val.continuousOn_symm.domRestrict.measurable
  have ht := (MeasurableEmbedding.subtype_coe e.val.open_target.measurableSet).measurableSet_image.mpr
    (hm hs)
  convert ht using 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists,
    exists_and_right, exists_eq_right]
  tauto

/-- Actual original differentiability and tensor transport internally produce full chart overlap. -/
theorem chartVolumeMeasure_overlap (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e f : ComplexChart n M) :
    (chartVolumeMeasure w e).restrict (e.val.source ∩ f.val.source) =
      (chartVolumeMeasure w f).restrict (e.val.source ∩ f.val.source) := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  have hsm := hs.inter (e.val.open_source.measurableSet.inter f.val.open_source.measurableSet)
  rw [chartVolumeMeasure_apply w e hsm, chartVolumeMeasure_apply w f hsm]
  let F := chartTransition e f
  let A := e.val.target ∩ e.val.symm ⁻¹' (s ∩ (e.val.source ∩ f.val.source))
  let B := f.val.target ∩ f.val.symm ⁻¹' (s ∩ (e.val.source ∩ f.val.source))
  have hA : MeasurableSet A := measurable_inverse_preimage e hsm
  have hAsub : A ⊆ F.source := fun z hz => ⟨hz.1, hz.2.2.2⟩
  have himage : F '' A = B := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzF := hAsub hz
      refine ⟨f.val.map_source hzF.2, ?_⟩
      change f.val.symm (f.val (e.val.symm z)) ∈ s ∩ (e.val.source ∩ f.val.source)
      rw [f.val.left_inv hz.2.2.2]
      exact hz.2
    · intro hy
      have hyF : y ∈ F.target := ⟨hy.1, hy.2.2.1⟩
      refine ⟨F.symm y, ?_, F.right_inv hyF⟩
      refine ⟨(F.map_target hyF).1, ?_⟩
      change e.val.symm (e.val (f.val.symm y)) ∈ s ∩ (e.val.source ∩ f.val.source)
      rw [e.val.left_inv hy.2.2.1]
      exact hy.2
  have hderiv : ∀ z ∈ A, HasFDerivWithinAt F (chartTransitionDerivative e f z) A z := by
    intro z hz
    exact ((HolomorphicMaps.chartTransition_contDiffAt_real e f (hAsub hz)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hderiv
    (F.injOn.mono hAsub) (fun z => ENNReal.ofReal (metricVolumeDensity w f z))
  change (∫⁻ z in A, ENNReal.ofReal (metricVolumeDensity w e z)) =
    ∫⁻ z in B, ENNReal.ofReal (metricVolumeDensity w f z)
  rw [← himage, hcov]
  refine setLIntegral_congr_fun hA fun z hz => ?_
  have hd := chartTransition_det_pos w hw e f z (hAsub hz)
  rw [metricVolumeDensity_transport w e f z (hAsub hz), ENNReal.ofReal_mul hd.le]
  congr 1
  rw [abs_of_pos hd]

private def countableGlue {X : Type*} [MeasurableSpace X]
    (U : ℕ → Set X) (μ : ℕ → Measure X) : Measure X :=
  Measure.sum (fun i => (μ i).restrict (disjointed U i))

private theorem countableGlue_restrict {X : Type*} [MeasurableSpace X]
    (U : ℕ → Set X) (μ : ℕ → Measure X) (hU : ∀ i, MeasurableSet (U i))
    {W : Set X} (hW : MeasurableSet W) (hcover : W ⊆ ⋃ i, U i) (ν : Measure X)
    (hcompat : ∀ i, (μ i).restrict (U i ∩ W) = ν.restrict (U i ∩ W)) :
    (countableGlue U μ).restrict W = ν.restrict W := by
  have hD : ∀ i, MeasurableSet (disjointed U i) := MeasurableSet.disjointed hU
  have hpiece (i : ℕ) :
      ((μ i).restrict (disjointed U i)).restrict W = ν.restrict (W ∩ disjointed U i) := by
    rw [Measure.restrict_restrict hW]
    have hsub : W ∩ disjointed U i ⊆ U i ∩ W :=
      fun _ hx => ⟨disjointed_subset U i hx.2, hx.1⟩
    have h := congrArg (fun κ : Measure X => κ.restrict (W ∩ disjointed U i)) (hcompat i)
    simpa only [Measure.restrict_restrict_of_subset hsub] using h
  have hd : Pairwise (fun i j => Disjoint (W ∩ disjointed U i) (W ∩ disjointed U j)) := by
    intro i j hij
    exact (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  rw [countableGlue, Measure.restrict_sum _ hW]
  simp_rw [hpiece]
  rw [← Measure.restrict_iUnion hd (fun i => hW.inter (hD i))]
  congr 1
  rw [← inter_iUnion, iUnion_disjointed]
  exact inter_eq_left.mpr hcover

private theorem countable_ext_of_restrict_eq {X : Type*} [MeasurableSpace X]
    (U : ℕ → Set X) (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    {μ ν : Measure X} (h : ∀ i, μ.restrict (U i) = ν.restrict (U i)) : μ = ν := by
  have hμ := countableGlue_restrict U (fun _ => μ) hU MeasurableSet.univ
    (by rw [hcover]) μ (fun _ => rfl)
  have hν := countableGlue_restrict U (fun _ => μ) hU MeasurableSet.univ
    (by rw [hcover]) ν (by simpa only [inter_univ] using h)
  exact (by simpa only [Measure.restrict_univ] using hμ.symm.trans hν)

omit [MeasurableSpace M] [BorelSpace M] in
private theorem exists_countable_original_charts [Nonempty M] :
    ∃ E : ℕ → ComplexChart n M, ∀ x : M, ∃ i, x ∈ (E i).val.source := by
  classical
  let U : M → Set M := fun x => (complexChartAt (n := n) x).val.source
  obtain ⟨t, ht, hcover⟩ := TopologicalSpace.countable_cover_nhds (fun x : M =>
    (complexChartAt (n := n) x).val.open_source.mem_nhds (mem_complexChartAt_source x))
  have hne : t.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty M›
    have hx : x ∈ ⋃ y ∈ t, U y := by rw [hcover]; exact mem_univ x
    obtain ⟨y, hyt, -⟩ := mem_iUnion₂.mp hx
    exact ⟨y, hyt⟩
  obtain ⟨a, ha⟩ := ht.exists_eq_range hne
  refine ⟨fun i => complexChartAt (a i), fun x => ?_⟩
  have hx : x ∈ ⋃ y ∈ t, U y := by rw [hcover]; exact mem_univ x
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp hx
  rw [ha] at hyt
  obtain ⟨i, rfl⟩ := hyt
  exact ⟨i, hxy⟩

/-- Original Hermitian data genuinely produces a unique global measure in every dimension,
including arbitrary noncompact, disconnected and empty original manifolds. -/
theorem existsUnique_hermitianVolumeMeasure (w : SmoothRealForm n M 2) (hw : w.IsHermitian) :
    ∃! μ : Measure M, ∀ e : ComplexChart n M,
      μ.restrict e.val.source = chartVolumeMeasure w e := by
  classical
  cases isEmpty_or_nonempty M with
  | inl h =>
    have : IsEmpty M := h
    have hall (μ ν : Measure M) : μ = ν := by
      ext s hs
      have hzero : s = ∅ := by ext x; exact isEmptyElim x
      rw [hzero, measure_empty, measure_empty]
    exact ⟨0, fun _ => hall _ _, fun ν _ => hall ν 0⟩
  | inr h =>
    have : Nonempty M := h
    obtain ⟨E, hE⟩ := exists_countable_original_charts (n := n) (M := M)
    let U : ℕ → Set M := fun i => (E i).val.source
    let μ := countableGlue U (fun i => chartVolumeMeasure w (E i))
    have hU : ∀ i, MeasurableSet (U i) := fun i => (E i).val.open_source.measurableSet
    have hcover : ⋃ i, U i = univ := by
      apply eq_univ_iff_forall.mpr
      intro x
      obtain ⟨i, hi⟩ := hE x
      exact mem_iUnion.mpr ⟨i, hi⟩
    have hμ : ∀ e : ComplexChart n M, μ.restrict e.val.source = chartVolumeMeasure w e := by
      intro e
      have hsub : e.val.source ⊆ ⋃ i, U i := by rw [hcover]; exact subset_univ _
      exact (countableGlue_restrict U _ hU e.val.open_source.measurableSet hsub _
        (fun i => chartVolumeMeasure_overlap w hw (E i) e)).trans
          (chartVolumeMeasure_restrict_source w e)
    refine ⟨μ, hμ, fun ν hν => ?_⟩
    apply countable_ext_of_restrict_eq U hU hcover
    intro i
    exact (hν (E i)).trans (hμ (E i)).symm

/-- The actual global metric-unit volume, chosen only from the internally proved unique producer. -/
def hermitianVolumeMeasure (w : SmoothRealForm n M 2) (hw : w.IsHermitian) : Measure M :=
  (existsUnique_hermitianVolumeMeasure w hw).exists.choose

/-- Exact genuine restriction to every original chart, including charts outside the internal cover. -/
theorem hermitianVolumeMeasure_restrict_chart (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) :
    (hermitianVolumeMeasure w hw).restrict e.val.source = chartVolumeMeasure w e :=
  (existsUnique_hermitianVolumeMeasure w hw).exists.choose_spec e

/-- The forward original chart reads back exactly the literal original metric volume density. -/
theorem hermitianVolumeMeasure_map_chart (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) :
    Measure.map e.val ((hermitianVolumeMeasure w hw).restrict e.val.source) =
      chartDensityMeasure w e := by
  have hforward : AEMeasurable e.val (chartVolumeMeasure w e) := by
    rw [← hermitianVolumeMeasure_restrict_chart w hw e]
    exact e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  rw [hermitianVolumeMeasure_restrict_chart, chartVolumeMeasure,
    hforward.map_map_of_aemeasurable (inverse_chart_aemeasurable w e)]
  have hac : chartDensityMeasure w e ≪ volume.restrict e.val.target :=
    withDensity_absolutelyContinuous _ _
  have hid : (e.val ∘ e.val.symm) =ᵐ[chartDensityMeasure w e] id :=
    hac.ae_le ((ae_restrict_mem e.val.open_target.measurableSet).mono
      fun z hz => e.val.right_inv hz)
  rw [Measure.map_congr hid, Measure.map_id]

/-- The internally constructed actual Hermitian measure has the existing smooth-positive
volume predicate, with the literal metric-unit density in every original chart. -/
theorem isSmoothPositiveVolume_hermitianVolumeMeasure (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) : IsSmoothPositiveVolume (n := n) (hermitianVolumeMeasure w hw) := by
  intro e
  exact ⟨metricVolumeDensity w e, metricVolumeDensity_smooth w e,
    metricVolumeDensity_positive w hw e, hermitianVolumeMeasure_map_chart w hw e⟩

omit [IsComplexManifold n M] in
private theorem measurable_source_preimage (e : ComplexChart n M)
    {K : Set (ComplexModel n)} (hK : MeasurableSet K) :
    MeasurableSet (e.val.source ∩ e.val ⁻¹' K) := by
  have hm : Measurable (e.val.source.domRestrict e.val) :=
    e.val.continuousOn.domRestrict.measurable
  have ht := (MeasurableEmbedding.subtype_coe e.val.open_source.measurableSet).measurableSet_image.mpr
    (hm hK)
  convert ht using 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_image, Subtype.exists,
    exists_and_right, exists_eq_right]
  tauto

/-- Exact original chart-image mass for every measurable set in the actual target. -/
theorem hermitianVolumeMeasure_source_preimage (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) {K : Set (ComplexModel n)} (hK : MeasurableSet K)
    (hKt : K ⊆ e.val.target) :
    hermitianVolumeMeasure w hw (e.val.source ∩ e.val ⁻¹' K) =
      ∫⁻ z in K, ENNReal.ofReal (metricVolumeDensity w e z) := by
  have hm := e.val.continuousOn.aemeasurable
    (μ := hermitianVolumeMeasure w hw) e.val.open_source.measurableSet
  have h := congrArg (fun ν : Measure (ComplexModel n) => ν K)
    (hermitianVolumeMeasure_map_chart w hw e)
  rw [Measure.map_apply_of_aemeasurable hm hK,
    Measure.restrict_apply' e.val.open_source.measurableSet,
    chartDensityMeasure, withDensity_apply' _ _,
    Measure.restrict_restrict hK, inter_eq_left.mpr hKt] at h
  simpa only [inter_comm] using h

/-- The literal inverse-chart image has the exact original metric-density integral. -/
theorem hermitianVolumeMeasure_inverse_image (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    (e : ComplexChart n M) {K : Set (ComplexModel n)} (hK : MeasurableSet K)
    (hKt : K ⊆ e.val.target) :
    hermitianVolumeMeasure w hw (e.val.symm '' K) =
      ∫⁻ z in K, ENNReal.ofReal (metricVolumeDensity w e z) := by
  rw [e.val.symm_image_eq_source_inter_preimage hKt]
  exact hermitianVolumeMeasure_source_preimage w hw e hK hKt

private theorem hermitianVolumeMeasure_closedBall_lt_top
    (w : SmoothRealForm n M 2) (hw : w.IsHermitian) (e : ComplexChart n M)
    (z : ComplexModel n) (r : ℝ) (hKt : closedBall z r ⊆ e.val.target) :
    hermitianVolumeMeasure w hw (e.val.symm '' closedBall z r) < ⊤ := by
  have hK : IsCompact (closedBall z r) := isCompact_closedBall z r
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((metricVolumeDensity_smooth w e).continuousOn.mono hKt)
  rw [hermitianVolumeMeasure_inverse_image w hw e isClosed_closedBall.measurableSet hKt]
  calc
    (∫⁻ y in closedBall z r, ENNReal.ofReal (metricVolumeDensity w e y))
        ≤ ∫⁻ _ in closedBall z r, ENNReal.ofReal C := by
      refine lintegral_mono_ae ((ae_restrict_mem isClosed_closedBall.measurableSet).mono
        fun y hy => ENNReal.ofReal_le_ofReal ?_)
      exact (le_abs_self _).trans (hC y hy)
    _ = ENNReal.ofReal C * volume (closedBall z r) := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

/-- The genuine global Hermitian volume is locally finite without compactness or positive dimension. -/
theorem isLocallyFiniteMeasure_hermitianVolumeMeasure (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) : IsLocallyFiniteMeasure (hermitianVolumeMeasure w hw) := by
  refine ⟨fun x => ?_⟩
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨r, hr, hrt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (e.val.open_target.mem_nhds hz)
  have hball : ball (e.val x) r ⊆ e.val.target := ball_subset_closedBall.trans hrt
  have hU : IsOpen (e.val.symm '' ball (e.val x) r) :=
    e.val.isOpen_image_symm_of_subset_target isOpen_ball hball
  have hxU : x ∈ e.val.symm '' ball (e.val x) r :=
    ⟨e.val x, mem_ball_self hr, e.val.left_inv hx⟩
  refine ⟨e.val.symm '' ball (e.val x) r, hU.mem_nhds hxU, ?_⟩
  exact (measure_mono (image_mono ball_subset_closedBall)).trans_lt
    (hermitianVolumeMeasure_closedBall_lt_top w hw e (e.val x) r hrt)

/-- Every actual nonempty original open set has strictly positive Hermitian volume. -/
theorem hermitianVolumeMeasure_open_pos (w : SmoothRealForm n M 2) (hw : w.IsHermitian)
    {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < hermitianVolumeMeasure w hw U := by
  obtain ⟨x, hxU⟩ := hne
  let e := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  let c : ℝ := metricVolumeDensity w e (e.val x) / 2
  have hc : 0 < c := half_pos (metricVolumeDensity_positive w hw e (e.val x) hz)
  have hlow : IsOpen (e.val.target ∩ metricVolumeDensity w e ⁻¹' Ioi c) :=
    (metricVolumeDensity_smooth w e).continuousOn.isOpen_inter_preimage
      e.val.open_target isOpen_Ioi
  have hzone : IsOpen ((e.val.target ∩ metricVolumeDensity w e ⁻¹' Ioi c) ∩
      (e.val '' (e.val.source ∩ U))) :=
    hlow.inter (e.val.isOpen_image_source_inter hU)
  have hzlow : e.val x ∈ e.val.target ∩ metricVolumeDensity w e ⁻¹' Ioi c :=
    ⟨hz, half_lt_self (metricVolumeDensity_positive w hw e (e.val x) hz)⟩
  have hzonez : e.val x ∈ (e.val.target ∩ metricVolumeDensity w e ⁻¹' Ioi c) ∩
      (e.val '' (e.val.source ∩ U)) := ⟨hzlow, ⟨x, ⟨hx, hxU⟩, rfl⟩⟩
  obtain ⟨r, hr, hrzone⟩ := Metric.mem_nhds_iff.mp (hzone.mem_nhds hzonez)
  have hrt : ball (e.val x) r ⊆ e.val.target := fun _ hy => (hrzone hy).1.1
  have hsub : e.val.symm '' ball (e.val x) r ⊆ U := by
    rintro y ⟨z, hzball, rfl⟩
    obtain ⟨y, hy, hye⟩ := (hrzone hzball).2
    rw [← hye, e.val.left_inv hy.1]
    exact hy.2
  apply lt_of_lt_of_le _ (measure_mono hsub)
  rw [hermitianVolumeMeasure_inverse_image w hw e isOpen_ball.measurableSet hrt]
  have hp : 0 < ENNReal.ofReal c * volume (ball (e.val x) r) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hc).ne'
      (measure_ball_pos volume (e.val x) hr).ne'
  calc
    0 < ENNReal.ofReal c * volume (ball (e.val x) r) := hp
    _ = ∫⁻ _ in ball (e.val x) r, ENNReal.ofReal c := by simp
    _ ≤ ∫⁻ z in ball (e.val x) r, ENNReal.ofReal (metricVolumeDensity w e z) := by
      refine lintegral_mono_ae ((ae_restrict_mem isOpen_ball.measurableSet).mono fun z hzball => ?_)
      exact ENNReal.ofReal_le_ofReal (hrzone hzball).1.2.le

/-- The actual all-dimensional Hermitian measure has full original topological support. -/
theorem isOpenPosMeasure_hermitianVolumeMeasure (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) : Measure.IsOpenPosMeasure (hermitianVolumeMeasure w hw) :=
  ⟨fun _ hU hne => (hermitianVolumeMeasure_open_pos w hw hU hne).ne'⟩

/-- Compactness gives actual finite total Hermitian volume, including empty manifolds. -/
theorem isFiniteMeasure_hermitianVolumeMeasure [CompactSpace M] (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) : IsFiniteMeasure (hermitianVolumeMeasure w hw) := by
  have : IsLocallyFiniteMeasure (hermitianVolumeMeasure w hw) :=
    isLocallyFiniteMeasure_hermitianVolumeMeasure w hw
  infer_instance

/-- Strict total-volume positivity has exactly the necessary original nonempty hypothesis. -/
theorem hermitianVolumeMeasure_univ_pos [Nonempty M] (w : SmoothRealForm n M 2)
    (hw : w.IsHermitian) : 0 < hermitianVolumeMeasure w hw univ :=
  hermitianVolumeMeasure_open_pos w hw isOpen_univ univ_nonempty

end SGPT.Foundations.Analysis.Pending.NaturalHermitianVolumeMeasure
