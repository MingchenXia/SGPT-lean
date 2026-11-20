import SGPT.Foundations.Analysis.Pending.ActualChartTruncatedQuasiContinuousWeightedContinuity
import SGPT.Foundations.Analysis.Pending.ActualLocalNonPluripolarCutoffIntegrals
import SGPT.Foundations.Analysis.Pending.BedfordTaylorMaxObstacle

set_option autoImplicit false

/-! # Actual moving singular chart cutoff limits

Original capacity limits internally produce a single tail before every
level and test. Actual compact BT integrability and strict NP locality
transfer the produced real weighted limits to genuine finite nonnegative
integrals of the original singular tuples. The unweighted local singular
mass need not be finite. Full moving-family mass liminf remains separate.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualSingularChartQuasiContinuousCutoffWeightedLimits

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.MixedMongeAmpere FirstPass.MixedNonPluripolar
  GlobalSlotStokes BedfordTaylor MixedMongeAmpere MixedNonPluripolar ThetaCapacity
  ActualLocalNonPluripolarCutoffIntegrals CapacityWeightedConvergence

noncomputable section

variable {n : ℕ}

private theorem integrable_truncated_cutoff_test
    {D : Opens (ComplexModel n)} {w : Fin n → ComplexModel n → EReal}
    (hw : ∀ i, PlurisubharmonicOn (w i) D) (k : ℕ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (ht : tsupport h ⊆ K) :
    Integrable (fun z => h z * cutoff k (fun i => mixedTruncationReal w k i z))
      (canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal w k)
        (mixedTruncationReal_isLocallyBounded hw k)) := by
  have hzero : ∀ z, z ∉ K → h z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun hs => hz (ht hs))
  have hrep : (fun z => h z * cutoff k (fun i => mixedTruncationReal w k i z)) =
      (fun z => h z * cutoff k (fun i => (D : Set (ComplexModel n)).indicator
        (mixedTruncationReal w k i) z)) := by
    funext z
    by_cases hz : z ∈ D
    · simp only [indicator_of_mem hz]
    · rw [hzero z (fun hzK => hz (hKD hzK))]
      simp only [zero_mul]
  have hm : Measurable (fun z => h z * cutoff k (fun i => mixedTruncationReal w k i z)) := by
    rw [hrep]
    exact hc.measurable.mul ((cutoff_properties k).1.continuous.measurable.comp
      (measurable_pi_lambda _ fun i =>
        LocalBedfordTaylorProducts.measurable_indicator_of_isLocallyBoundedPshOn
          (mixedTruncationReal_isLocallyBounded hw k i)))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∀ z, |h z * cutoff k (fun i => mixedTruncationReal w k i z)| ≤ max C 0 := by
    intro z
    have hH : |h z| ≤ max C 0 := by
      by_cases hz : z ∈ K
      · have hr : |h z| ≤ C := by simpa only [Real.norm_eq_abs] using hC z hz
        exact hr.trans (le_max_left _ _)
      · rw [hzero z hz, abs_zero]
        exact le_max_right _ _
    rw [abs_mul, abs_of_nonneg ((cutoff_properties k).2 _).1.1]
    calc
      _ ≤ max C 0 * 1 := mul_le_mul hH ((cutoff_properties k).2 _).1.2
        ((cutoff_properties k).2 _).1.1 (le_max_right _ _)
      _ = max C 0 := mul_one _
  exact integrable_of_bounded_of_support hK.measurableSet
    (canonicalMixedBedfordTaylorMeasure_finiteOnCompacts
      (mixedTruncationReal_isLocallyBounded hw k) hK hKD)
    hm.stronglyMeasurable hb (fun z hz => by rw [hzero z hz, zero_mul])

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

omit [IsComplexManifold n M] [CompactSpace M] in
private theorem integrable_weighted_truncated_cutoff_test (e : ComplexChart n M)
    {D : Opens (ComplexModel n)} (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {w : Fin n → ComplexModel n → EReal}
    (hw : ∀ i, PlurisubharmonicOn (w i) D) (k : ℕ)
    {χ : M → ℝ} {C : ℝ} (hC : 0 ≤ C) (hχC : ∀ x, |χ x| ≤ C) (hχm : Measurable χ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {h : ComplexModel n → ℝ} (hc : Continuous h) (ht : tsupport h ⊆ K) :
    Integrable (fun y => χ (e.val.symm y) * h y *
      cutoff k (fun i => mixedTruncationReal w k i y))
      (canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal w k)
        (mixedTruncationReal_isLocallyBounded hw k)) := by
  classical
  let read : ComplexModel n → ℝ := e.val.target.indicator (fun y => χ (e.val.symm y))
  have hm : Measurable read := by
    apply measurable_of_restrict_of_restrict_compl e.val.open_target.measurableSet
    · have hi : Measurable (e.val.target.domRestrict e.val.symm) :=
        (continuousOn_iff_continuous_domRestrict.mp e.val.symm.continuousOn).measurable
      have heq : e.val.target.domRestrict read = fun y : e.val.target => χ (e.val.symm y) := by
        funext y
        exact indicator_of_mem y.property (fun z => χ (e.val.symm z))
      rw [heq]
      exact hχm.comp hi
    · have heq : e.val.targetᶜ.domRestrict read = fun _ => (0 : ℝ) := by
        funext y
        exact indicator_of_notMem y.property (fun z => χ (e.val.symm z))
      rw [heq]
      exact measurable_const
  have hb : ∀ y, ‖read y‖ ≤ C := by
    intro y
    by_cases hy : y ∈ e.val.target
    · simpa only [read, indicator_of_mem hy, Real.norm_eq_abs] using hχC (e.val.symm y)
    · simpa only [read, indicator_of_notMem hy, norm_zero] using hC
  have hi := (integrable_truncated_cutoff_test hw k hK hKD hc ht).bdd_mul
    hm.aestronglyMeasurable (Eventually.of_forall hb)
  have heq : (fun y => χ (e.val.symm y) * h y * cutoff k
      (fun i => mixedTruncationReal w k i y)) =
      fun y => read y * (h y * cutoff k (fun i => mixedTruncationReal w k i y)) := by
    funext y
    by_cases hy : y ∈ e.val.target
    · simp only [read, indicator_of_mem hy, mul_assoc]
    · have hz : h y = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hy (hDt (hKD (ht hh))))
      simp only [read, indicator_of_notMem hy, hz, mul_zero, zero_mul]
  rw [heq]
  exact hi

/-- True finite moving non-pluripolar cutoff integrals, with the tail,
corrected PSH and bounded-BT integrability produced internally. -/
theorem exists_tail_quasiContinuous_cutoff_lintegral_limits (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    (J : SlotChart θ omega.form) {D : Opens (ComplexModel n)}
    (hcompact : IsCompact (closure (D : Set (ComplexModel n))))
    (hclosure : closure (D : Set (ComplexModel n)) ⊆ J.domain)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    let corr (f : Fin n → M → EReal) : Fin n → ComplexModel n → EReal :=
      fun i z => f i (J.chart.val.symm z) + (J.potential i z : EReal)
    ∃ N : ℕ,
      ∃ hU : ∀ j i, PlurisubharmonicOn (corr (u (j + N)) i) D,
      ∃ hV : ∀ i, PlurisubharmonicOn (corr v i) D,
      ∀ k : ℕ, ∀ (χ : M → ℝ) (C : ℝ), 0 ≤ C →
        (∀ x, 0 ≤ χ x ∧ |χ x| ≤ C) → Measurable χ →
        QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) χ → ∀ h : ComplexModel n → ℝ,
        Continuous h → (∀ z, 0 ≤ h z) → tsupport h ⊆ K →
      (∀ j, (∫⁻ z, ENNReal.ofReal ((χ (J.chart.val.symm z) * h z)) * ENNReal.ofReal
        (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
        ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) < ⊤) ∧
      ((∫⁻ z, ENNReal.ofReal ((χ (J.chart.val.symm z) * h z)) * ENNReal.ofReal
        (cutoff k (fun i => mixedTruncationReal (corr v) k i z))
        ∂mixedTruncationLimitMeasure D (corr v) hV) < ⊤) ∧
      Tendsto (fun j => ∫⁻ z, ENNReal.ofReal ((χ (J.chart.val.symm z) * h z)) * ENNReal.ofReal
        (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
        ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) atTop
        (𝓝 (∫⁻ z, ENNReal.ofReal ((χ (J.chart.val.symm z) * h z)) * ENNReal.ofReal
          (cutoff k (fun i => mixedTruncationReal (corr v) k i z))
          ∂mixedTruncationLimitMeasure D (corr v) hV)) := by
  dsimp only
  let corr (f : Fin n → M → EReal) : Fin n → ComplexModel n → EReal :=
    fun i z => f i (J.chart.val.symm z) + (J.potential i z : EReal)
  have hDJ : D ≤ J.domain := fun z hz => hclosure (subset_closure hz)
  have hCorr (f : Fin n → M → EReal) (hf : ∀ i, IsThetaPshPotential (θ i).val (f i)) :
      ∀ i, PlurisubharmonicOn (corr f i) D := fun i =>
    (BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
      (hf i).1 J.chart (J.localPotential i)).mono hDJ
  obtain ⟨N, hN⟩ := ActualChartTruncatedQuasiContinuousWeightedContinuity.exists_tail_weighted_limits
    omega hu hv hcap J hcompact hclosure hK hKD
  refine ⟨N, (fun j => hCorr (u (j + N)) (hu (j + N))), hCorr v hv, ?_⟩
  intro k χ C hC hχC hχm hχ h hc hn ht
  have hzD : ∀ z, z ∉ D → h z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun hs => hz (hKD (ht hs)))
  have hnn (w : Fin n → ComplexModel n → EReal) :
      ∀ z, 0 ≤ (χ (J.chart.val.symm z) * h z) * cutoff k (fun i => mixedTruncationReal w k i z) :=
    fun z => mul_nonneg (mul_nonneg (hχC _).1 (hn z)) ((cutoff_properties k).2 _).1.1
  have hEq (w : Fin n → ComplexModel n → EReal)
      (hw : ∀ i, PlurisubharmonicOn (w i) D) :
      (∫⁻ z, ENNReal.ofReal ((χ (J.chart.val.symm z) * h z)) * ENNReal.ofReal
        (cutoff k (fun i => mixedTruncationReal w k i z))
        ∂mixedTruncationLimitMeasure D w hw) =
      ENNReal.ofReal (∫ z, (χ (J.chart.val.symm z) * h z) * cutoff k (fun i => mixedTruncationReal w k i z)
        ∂canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal w k)
          (mixedTruncationReal_isLocallyBounded hw k)) := by
    calc
      _ = ∫⁻ z, ENNReal.ofReal ((χ (J.chart.val.symm z) * h z)) * ENNReal.ofReal
          (cutoff k (fun i => mixedTruncationReal w k i z))
          ∂canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal w k)
            (mixedTruncationReal_isLocallyBounded hw k) :=
        (lintegral_cutoff_eq_le hw k (fun z hz => by rw [hzD z hz, mul_zero, ENNReal.ofReal_zero])).1.symm
      _ = ∫⁻ z, ENNReal.ofReal ((χ (J.chart.val.symm z) * h z) * cutoff k (fun i => mixedTruncationReal w k i z))
          ∂canonicalMixedBedfordTaylorMeasure D (mixedTruncationReal w k)
            (mixedTruncationReal_isLocallyBounded hw k) :=
        lintegral_congr fun z => (ENNReal.ofReal_mul (mul_nonneg (hχC _).1 (hn z))).symm
      _ = _ := (ofReal_integral_eq_lintegral_ofReal
        (integrable_weighted_truncated_cutoff_test J.chart
          (fun y hy => J.domain_le_target (hDJ hy)) hw k hC (fun x => (hχC x).2) hχm
          hK hKD hc ht) (Eventually.of_forall (hnn w))).symm
  refine ⟨fun j => ?_, ?_, ?_⟩
  · rw [hEq]
    exact ENNReal.ofReal_lt_top
  · rw [hEq]
    exact ENNReal.ofReal_lt_top
  · obtain ⟨hTU, hTV, hlim⟩ := hN k
    have hcompactH : HasCompactSupport h := hK.of_isClosed_subset (isClosed_tsupport _) ht
    have hreal := hlim (cutoff k) 1 (cutoff_properties k).1 χ C hC (fun x => (hχC x).2) hχm hχ h hc hcompactH ht
    have hh := (ENNReal.continuous_ofReal.tendsto _).comp hreal
    simpa only [hEq, Function.comp_def, corr] using hh

end
end SGPT.Foundations.Analysis.Pending.ActualSingularChartQuasiContinuousCutoffWeightedLimits
