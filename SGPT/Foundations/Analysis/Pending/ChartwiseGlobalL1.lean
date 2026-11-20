import SGPT.Foundations.Analysis.FirstPass.PotentialL1
import SGPT.Foundations.Analysis.FirstPass.ERealChordUSC

set_option autoImplicit false

/-!
# Chartwise local `L¹` convergence is global `L¹` convergence

Blueprint `trace:chartwise-global-l1`.  On a compact complex manifold `M`, fix a *smooth positive
volume* `μ`: a Borel measure which, read in every atlas chart, is a smooth positive density times
Lebesgue measure on the chart target (`IsSmoothPositiveVolume`).  For measurable extended-real
functions — in particular for quasi-plurisubharmonic ones, which are upper semicontinuous — the
chartwise local `L¹` convergence `ManifoldL1LocallyTendsto` of the first pass is equivalent to
convergence of the global `L¹(μ)` distance `∫ |u_i - v| dμ` to `0`
(`manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance`).  Consequently the global topology
does not depend on the smooth positive volume (`tendsto_globalL1EDistance_iff`).

The absolute difference is the first pass's `canonicalERealAbsDiff` (zero on the common pole set),
and the integrals are lower Lebesgue integrals, so no integrability hypothesis is needed: the two
sides are compared by the density bounds on compact chart sets, and a finite cover of `M` by such
sets bounds the global integral by finitely many chartwise ones.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1

open FirstPass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [MeasurableSpace M] [BorelSpace M]

/-- A **smooth positive volume** on `M`: in every atlas chart `e`, the pushforward of `μ`
restricted to the chart source is `ρ_e(z) dz` on the chart target, for a smooth function `ρ_e`
that is positive on the target. -/
def IsSmoothPositiveVolume (μ : Measure M) : Prop :=
  ∀ e : ComplexChart n M, ∃ ρ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ ρ e.val.target ∧
    (∀ z ∈ e.val.target, 0 < ρ z) ∧
    Measure.map e.val (μ.restrict e.val.source) =
      (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (ρ z))

/-- The global extended `L¹(μ)` distance of two extended-real functions, with the canonical
absolute difference (zero on the common pole set).  It may be `⊤`. -/
def globalL1EDistance (μ : Measure M) (u v : M → EReal) : ℝ≥0∞ :=
  ∫⁻ x, canonicalERealAbsDiff (u x) (v x) ∂μ

omit [ChartedSpace (ComplexModel n) M] in
/-- The set of points of a chart source mapped into a closed set is Borel. -/
theorem measurableSet_source_inter_preimage (e : OpenPartialHomeomorph M (ComplexModel n))
    {K : Set (ComplexModel n)} (hK : IsClosed K) :
    MeasurableSet (e.source ∩ e ⁻¹' K) := by
  have hopen : IsOpen (e.source ∩ e ⁻¹' Kᶜ) :=
    e.continuousOn.isOpen_inter_preimage e.open_source hK.isOpen_compl
  have heq : e.source ∩ e ⁻¹' K = e.source \ (e.source ∩ e ⁻¹' Kᶜ) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_compl_iff]
    tauto
  rw [heq]
  exact e.open_source.measurableSet.diff hopen.measurableSet

/-- **Reading a set integral in a chart.**  If `μ` is `ρ(z) dz` in the chart `e`, then for a
measurable `f ≥ 0` and a compact `K` inside the chart target,
`∫_{e⁻¹(K)} f dμ = ∫_K ρ(z) f(e⁻¹ z) dz`. -/
theorem setLIntegral_source_inter_preimage {μ : Measure M} (e : ComplexChart n M)
    {ρ : ComplexModel n → ℝ} (hρc : ContinuousOn ρ e.val.target)
    (hmap : Measure.map e.val (μ.restrict e.val.source) =
      (volume.restrict e.val.target).withDensity (fun z => ENNReal.ofReal (ρ z)))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKt : K ⊆ e.val.target)
    {f : M → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in e.val.source ∩ e.val ⁻¹' K, f x ∂μ =
      ∫⁻ z in K, ENNReal.ofReal (ρ z) * f (e.val.symm z) := by
  set ν := μ.restrict e.val.source with hν
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have he : AEMeasurable e.val ν :=
    e.val.continuousOn.aemeasurable e.val.open_source.measurableSet
  have hmapK : Measure.map e.val (ν.restrict (e.val ⁻¹' K)) =
      (volume.restrict K).withDensity (fun z => ENNReal.ofReal (ρ z)) := by
    rw [← Measure.restrict_map_of_aemeasurable he hKm, hmap, restrict_withDensity hKm,
      Measure.restrict_restrict hKm, inter_eq_left.mpr hKt]
  have hF : AEMeasurable (fun z => f (e.val.symm z)) (volume.restrict K) :=
    hf.comp_aemeasurable ((e.val.continuousOn_symm.mono hKt).aemeasurable hKm)
  have hρ : AEMeasurable (fun z => ENNReal.ofReal (ρ z)) (volume.restrict K) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (hρc.mono hKt)).aemeasurable hKm
  have hS := measurableSet_source_inter_preimage e.val hK.isClosed
  calc ∫⁻ x in e.val.source ∩ e.val ⁻¹' K, f x ∂μ
      = ∫⁻ x in e.val.source ∩ e.val ⁻¹' K, f (e.val.symm (e.val x)) ∂μ :=
        setLIntegral_congr_fun hS fun x hx => by rw [e.val.left_inv hx.1]
    _ = ∫⁻ x, f (e.val.symm (e.val x)) ∂(ν.restrict (e.val ⁻¹' K)) := by
        rw [hν, Measure.restrict_restrict' e.val.open_source.measurableSet, inter_comm]
    _ = ∫⁻ z, f (e.val.symm z) ∂(Measure.map e.val (ν.restrict (e.val ⁻¹' K))) := by
        refine (lintegral_map' (f := fun z => f (e.val.symm z)) ?_ he.restrict).symm
        rw [hmapK]
        exact hF.mono_ac (withDensity_absolutelyContinuous _ _)
    _ = ∫⁻ z in K, ENNReal.ofReal (ρ z) * f (e.val.symm z) := by
        rw [hmapK, lintegral_withDensity_eq_lintegral_mul₀ hρ hF]
        rfl

omit [MeasurableSpace M] [BorelSpace M] in
/-- The chartwise distance is the chart reading of the pointwise absolute difference. -/
theorem chartL1EDistance_eq (u v : M → EReal) (e : ComplexChart n M) (K : Set (ComplexModel n)) :
    chartL1EDistance u v e K =
      ∫⁻ z in K, (fun x => canonicalERealAbsDiff (u x) (v x)) (e.val.symm z) := rfl

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [BorelSpace M] in
/-- The absolute difference of two measurable functions is measurable. -/
theorem measurable_canonicalERealAbsDiff_comp {u v : M → EReal} (hu : Measurable u)
    (hv : Measurable v) : Measurable fun x => canonicalERealAbsDiff (u x) (v x) :=
  measurable_canonicalERealAbsDiff.comp (hu.prodMk hv)

/-- **Global controls local.**  For a chart `e` and a compact `K` inside its target there is a
finite constant `C` with `d_{e,K}(u, v) ≤ C ∫ |u - v| dμ` for all measurable `u, v`. -/
theorem exists_chartL1EDistance_le_globalL1EDistance {μ : Measure M}
    (hμ : IsSmoothPositiveVolume (n := n) μ) (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u v : M → EReal, Measurable u → Measurable v →
      chartL1EDistance u v e K ≤ C * globalL1EDistance μ u v := by
  obtain ⟨ρ, hρs, hρpos, hmap⟩ := hμ e
  have hρc : ContinuousOn ρ e.val.target := hρs.continuousOn
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, ENNReal.zero_ne_top, fun u v _ _ => by simp⟩
  obtain ⟨z₀, hz₀K, hmin⟩ := hK.exists_isMinOn hne (hρc.mono hKt)
  have hc : 0 < ρ z₀ := hρpos z₀ (hKt hz₀K)
  refine ⟨ENNReal.ofReal (ρ z₀)⁻¹, ENNReal.ofReal_ne_top, fun u v hu hv => ?_⟩
  set f : M → ℝ≥0∞ := fun x => canonicalERealAbsDiff (u x) (v x) with hfdef
  have hf : Measurable f := measurable_canonicalERealAbsDiff_comp hu hv
  rw [chartL1EDistance_eq]
  calc ∫⁻ z in K, f (e.val.symm z)
      ≤ ∫⁻ z in K, ENNReal.ofReal (ρ z₀)⁻¹ * (ENNReal.ofReal (ρ z) * f (e.val.symm z)) := by
        refine lintegral_mono_ae ((ae_restrict_mem hK.isClosed.measurableSet).mono fun z hz => ?_)
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
        refine le_mul_of_one_le_left zero_le ?_
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]
        exact hmin hz
    _ = ENNReal.ofReal (ρ z₀)⁻¹ * ∫⁻ z in K, ENNReal.ofReal (ρ z) * f (e.val.symm z) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (ρ z₀)⁻¹ * ∫⁻ x in e.val.source ∩ e.val ⁻¹' K, f x ∂μ := by
        rw [setLIntegral_source_inter_preimage e hρc hmap hK hKt hf]
    _ ≤ ENNReal.ofReal (ρ z₀)⁻¹ * globalL1EDistance μ u v := by
        gcongr
        exact setLIntegral_le_lintegral _ _

/-- **Local controls global, on one chart set.**  For a chart `e` and a compact `K` inside its
target there is a finite constant `C` with `∫_{e⁻¹(K)} |u - v| dμ ≤ C d_{e,K}(u, v)`. -/
theorem exists_setLIntegral_le_chartL1EDistance {μ : Measure M}
    (hμ : IsSmoothPositiveVolume (n := n) μ) (e : ComplexChart n M) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKt : K ⊆ e.val.target) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u v : M → EReal, Measurable u → Measurable v →
      ∫⁻ x in e.val.source ∩ e.val ⁻¹' K, canonicalERealAbsDiff (u x) (v x) ∂μ ≤
        C * chartL1EDistance u v e K := by
  obtain ⟨ρ, hρs, -, hmap⟩ := hμ e
  have hρc : ContinuousOn ρ e.val.target := hρs.continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hρc.mono hKt)
  refine ⟨ENNReal.ofReal B, ENNReal.ofReal_ne_top, fun u v hu hv => ?_⟩
  rw [setLIntegral_source_inter_preimage e hρc hmap hK hKt
    (measurable_canonicalERealAbsDiff_comp hu hv), chartL1EDistance_eq,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ((ae_restrict_mem hK.isClosed.measurableSet).mono fun z hz => ?_)
  gcongr
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hB z hz))

omit [MeasurableSpace M] [BorelSpace M] in
/-- A finite cover of a compact manifold by compact chart sets: closed coordinate balls around
the points of a finite set, each inside the target of the preferred chart at its centre. -/
theorem exists_finite_chart_cover [CompactSpace M] :
    ∃ (t : Finset M) (r : M → ℝ), (∀ x, 0 < r x) ∧
      (∀ x, Metric.closedBall ((complexChartAt (n := n) x).val x) (r x) ⊆
        (complexChartAt (n := n) x).val.target) ∧
      ∀ y : M, ∃ x ∈ t, y ∈ (complexChartAt (n := n) x).val.source ∩
        (complexChartAt (n := n) x).val ⁻¹'
          Metric.closedBall ((complexChartAt (n := n) x).val x) (r x) := by
  have hball : ∀ x : M, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall ((complexChartAt (n := n) x).val x) r ⊆
        (complexChartAt (n := n) x).val.target := by
    intro x
    set e := complexChartAt (n := n) x
    have hx : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp e.val.open_target _ hx
    exact ⟨r / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hsub⟩
  choose r hr hrsub using hball
  set W : M → Set M := fun x => (complexChartAt (n := n) x).val.source ∩
    (complexChartAt (n := n) x).val ⁻¹' Metric.ball ((complexChartAt (n := n) x).val x) (r x)
  have hWopen : ∀ x, IsOpen (W x) := fun x =>
    (complexChartAt (n := n) x).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) x).val.open_source Metric.isOpen_ball
  have hWmem : ∀ x, x ∈ W x := fun x =>
    ⟨mem_complexChartAt_source x, Metric.mem_ball_self (hr x)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWopen
    (fun y _ => mem_iUnion.mpr ⟨y, hWmem y⟩)
  refine ⟨t, r, hr, hrsub, fun y => ?_⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  exact ⟨x, hx, hyx.1, Metric.ball_subset_closedBall hyx.2⟩

/-- **Chartwise local `L¹` convergence is global `L¹(μ)` convergence** (blueprint
`trace:chartwise-global-l1`).  On a compact complex manifold with a smooth positive volume `μ`,
for measurable extended-real functions `u_i`, `v`,
`u_i → v` chartwise locally in `L¹` if and only if `∫ |u_i - v| dμ → 0`. -/
theorem manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance [CompactSpace M]
    {μ : Measure M} (hμ : IsSmoothPositiveVolume (n := n) μ) {α : Type*} {l : Filter α}
    {u : α → M → EReal} {v : M → EReal} (hu : ∀ i, Measurable (u i)) (hv : Measurable v) :
    ManifoldL1LocallyTendsto (n := n) u l v ↔
      Tendsto (fun i => globalL1EDistance μ (u i) v) l (𝓝 0) := by
  constructor
  · intro hloc
    obtain ⟨t, r, hr, hrsub, hcover⟩ := exists_finite_chart_cover (n := n) (M := M)
    have hC : ∀ x : M, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u v : M → EReal, Measurable u → Measurable v →
        ∫⁻ y in (complexChartAt (n := n) x).val.source ∩ (complexChartAt (n := n) x).val ⁻¹'
          Metric.closedBall ((complexChartAt (n := n) x).val x) (r x),
            canonicalERealAbsDiff (u y) (v y) ∂μ ≤
          C * chartL1EDistance u v (complexChartAt (n := n) x)
            (Metric.closedBall ((complexChartAt (n := n) x).val x) (r x)) := fun x =>
      exists_setLIntegral_le_chartL1EDistance hμ _ (isCompact_closedBall _ _) (hrsub x)
    choose C hCtop hCle using hC
    set S : M → Set M := fun x => (complexChartAt (n := n) x).val.source ∩
      (complexChartAt (n := n) x).val ⁻¹'
        Metric.closedBall ((complexChartAt (n := n) x).val x) (r x) with hSdef
    have hSm : ∀ x, MeasurableSet (S x) := fun x =>
      measurableSet_source_inter_preimage _ Metric.isClosed_closedBall
    have hbound : ∀ i, globalL1EDistance μ (u i) v ≤
        ∑ x ∈ t, C x * chartL1EDistance (u i) v (complexChartAt (n := n) x)
          (Metric.closedBall ((complexChartAt (n := n) x).val x) (r x)) := by
      intro i
      set f : M → ℝ≥0∞ := fun y => canonicalERealAbsDiff (u i y) (v y) with hfdef
      have hf : Measurable f := measurable_canonicalERealAbsDiff_comp (hu i) hv
      calc globalL1EDistance μ (u i) v = ∫⁻ y, f y ∂μ := rfl
        _ ≤ ∫⁻ y, ∑ x ∈ t, (S x).indicator f y ∂μ := by
            refine lintegral_mono fun y => ?_
            obtain ⟨x, hx, hyx⟩ := hcover y
            calc f y = (S x).indicator f y := (indicator_of_mem hyx f).symm
              _ ≤ ∑ x ∈ t, (S x).indicator f y :=
                Finset.single_le_sum (f := fun x => (S x).indicator f y)
                  (fun _ _ => zero_le) hx
        _ = ∑ x ∈ t, ∫⁻ y in S x, f y ∂μ := by
            rw [lintegral_finsetSum _ fun x _ => hf.indicator (hSm x)]
            exact Finset.sum_congr rfl fun x _ => lintegral_indicator (hSm x) f
        _ ≤ _ := Finset.sum_le_sum fun x _ => hCle x (u i) v (hu i) hv
    have hlim : Tendsto (fun i => ∑ x ∈ t, C x * chartL1EDistance (u i) v
        (complexChartAt (n := n) x)
          (Metric.closedBall ((complexChartAt (n := n) x).val x) (r x))) l (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ∑ x ∈ t, C x * 0 by simp]
      refine tendsto_finsetSum _ fun x _ => ENNReal.Tendsto.const_mul ?_ (Or.inr (hCtop x))
      exact hloc _ _ (isCompact_closedBall _ _) (hrsub x)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) hbound
  · intro hglob e K hK hKt
    obtain ⟨C, hCtop, hCle⟩ := exists_chartL1EDistance_le_globalL1EDistance hμ e hK hKt
    have hlim : Tendsto (fun i => C * globalL1EDistance μ (u i) v) l (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hglob (Or.inr hCtop)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun i => hCle (u i) v (hu i) hv

/-- **The global `L¹` topology does not depend on the smooth positive volume.** -/
theorem tendsto_globalL1EDistance_iff [CompactSpace M] {μ ν : Measure M}
    (hμ : IsSmoothPositiveVolume (n := n) μ) (hν : IsSmoothPositiveVolume (n := n) ν)
    {α : Type*} {l : Filter α} {u : α → M → EReal} {v : M → EReal}
    (hu : ∀ i, Measurable (u i)) (hv : Measurable v) :
    Tendsto (fun i => globalL1EDistance μ (u i) v) l (𝓝 0) ↔
      Tendsto (fun i => globalL1EDistance ν (u i) v) l (𝓝 0) :=
  (manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance hμ hu hv).symm.trans
    (manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance hν hu hv)

/-- **Chartwise and global `L¹` convergence of quasi-plurisubharmonic potentials** (blueprint
`trace:chartwise-global-l1`, as stated): for quasi-psh `u_i`, `v` on a compact complex manifold
with a smooth positive volume `μ`, chartwise local `L¹` convergence is equivalent to
`∫ |u_i - v| dμ → 0`. -/
theorem manifoldL1LocallyTendsto_iff_of_manifoldQuasiPlurisubharmonic [IsComplexManifold n M]
    [CompactSpace M] {μ : Measure M} (hμ : IsSmoothPositiveVolume (n := n) μ) {α : Type*}
    {l : Filter α} {u : α → M → EReal} {v : M → EReal}
    (hu : ∀ i, ManifoldQuasiPlurisubharmonic (n := n) (u i))
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v) :
    ManifoldL1LocallyTendsto (n := n) u l v ↔
      Tendsto (fun i => globalL1EDistance μ (u i) v) l (𝓝 0) :=
  manifoldL1LocallyTendsto_iff_tendsto_globalL1EDistance hμ
    (fun i => (hu i).upperSemicontinuous.measurable) hv.upperSemicontinuous.measurable

end

end SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
