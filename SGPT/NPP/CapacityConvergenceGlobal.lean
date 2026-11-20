import SGPT.NPP.CapacityConvergenceChart

/-!
# Semicontinuity of non-pluripolar products with moving quasi-continuous weights

Global form, on a compact Kähler manifold, of the semicontinuity theorem of non-pluripolar
products under convergence in capacity, with moving weights (source `thm:semicon`, chapter
`chapter_npp.tex`; Xia, *Foundations of pluripotential theory*,
`thm:nonpluripolar-capacity-lower-limit`; Darvas–Di Nezza–Lu, survey, Theorem 2.6).

For closed real `(1,1)`-forms `θ_1, …, θ_n`, `θ_i`-psh potentials `u_j^i → v^i` in Kähler
capacity, and uniformly bounded nonnegative Borel weights `χ_j → χ` in Kähler capacity with
`χ` quasi-continuous:

* `lintegral_le_liminf_moving`: `∫ χ f ⟨θ_v⟩ ≤ liminf_j ∫ χ_j f ⟨θ_{u_j}⟩` for every continuous
  `f ≥ 0` (the chart step `chart_moving_test_liminf` is summed over a finite precompact slot
  chart partition of unity);
* `tendsto_integral_moving`: if moreover the total masses converge, then
  `∫ g χ_j ⟨θ_{u_j}⟩ → ∫ g χ ⟨θ_v⟩` for every continuous `g`, i.e. `χ_j ⟨θ_{u_j}⟩ → χ ⟨θ_v⟩`
  weakly as measures.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.NPP.CapacityConvergence

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open GlobalSlotStokes GlobalNonPluripolar ThetaCapacity ChartPartition
  CapacityWeightedConvergence FiniteGeodesicStripCharts

/-- Fatou's lemma for finite sums. -/
theorem finite_sum_liminf_le {m : ℕ} (f : ℕ → Fin m → ℝ≥0∞) :
    (∑ a, liminf (fun j => f j a) atTop) ≤
      liminf (fun j => ∑ a, f j a) atTop := by
  have h := lintegral_liminf_le (μ := Measure.count) (u := atTop)
    (fun j => measurable_of_finite (f j))
  simpa only [lintegral_fintype, Measure.count_singleton, mul_one] using h

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

theorem continuous_chartRead_of_continuous {e : ComplexChart n M} {f : M → ℝ}
    (hf : Continuous f) (hfc : IsCompact (tsupport f))
    (hfs : tsupport f ⊆ e.val.source) : Continuous (chartRead e f) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ e.val.target
  · have hc : ContinuousOn (fun y => f (e.val.symm y)) e.val.target :=
      hf.continuousOn.comp e.val.symm.continuousOn (fun _ _ => mem_univ _)
    have hread : ContinuousOn (chartRead e f) e.val.target :=
      hc.congr (fun y hy => chartRead_of_mem hy)
    exact hread.continuousAt (e.val.open_target.mem_nhds hz)
  · have hzK : z ∉ e.val '' tsupport f := fun h => hz (image_tsupport_subset_target hfs h)
    have hev : chartRead e f =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [(isCompact_image_tsupport hfc hfs).isClosed.isOpen_compl.mem_nhds hzK]
        with y hy
      by_contra h
      exact hy (support_chartRead_subset e f h)
    exact continuousAt_const.congr_of_eventuallyEq hev

theorem chartExtend_read_eq (e : ComplexChart n M) (f : M → ℝ)
    (hfs : tsupport f ⊆ e.val.source) : chartExtend e (chartRead e f) = f := by
  funext x
  by_cases hx : x ∈ e.val.source
  · rw [chartExtend_of_mem hx, chartRead_of_mem (e.val.map_source hx), e.val.left_inv hx]
  · rw [chartExtend_of_notMem hx,
      image_eq_zero_of_notMem_tsupport (fun hs => hx (hfs hs))]

variable [MeasurableSpace M] [BorelSpace M]

omit [TopologicalSpace M] [BorelSpace M] in
theorem sum_lintegrals_ofReal {m : ℕ} (f : Fin m → M → ℝ)
    (hm : ∀ a, Measurable (f a)) (h0 : ∀ a x, 0 ≤ f a x) (μ : Measure M) :
    (∑ a, ∫⁻ x, ENNReal.ofReal (f a x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (∑ a, f a x) ∂μ := by
  have hadd := lintegral_finsetSum (μ := μ) Finset.univ
    (fun a _ => (hm a).ennreal_ofReal)
  refine hadd.symm.trans (lintegral_congr ?_)
  intro x
  exact (ENNReal.ofReal_sum_of_nonneg (fun a _ => h0 a x)).symm

variable [IsComplexManifold n M] [CompactSpace M]

/-- **Moving-weight lower semicontinuity of non-pluripolar products** (`thm:semicon`,
`eq:semicon1`, in native form). -/
theorem lintegral_le_liminf_moving (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hχ0 : ∀ j x, 0 ≤ χ j x) (hχ₀C : ∀ x, 0 ≤ χ₀ x ∧ |χ₀ x| ≤ C)
    (hχm : ∀ j, Measurable (χ j)) (hχ₀m : Measurable χ₀)
    (hχ₀ : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) χ₀)
    (hχcap : ∀ c : ℝ, 0 < c → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | c < |χ j x - χ₀ x|}) atTop (𝓝 0))
    {f : M → ℝ} (hf : Continuous f) (hn : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (χ₀ x * f x) ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ j x * f x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := by
  classical
  obtain ⟨m, part, J, D, hsm, h0, hcompact, hclosure, hsupp, hcpt, h1⟩ :=
    ActualPrecompactSlotChartPartition.exists_precompact_chart_partition θ omega.form
  let g : Fin m → M → ℝ := fun a x => f x * part a x
  have hgc (a : Fin m) : Continuous (g a) :=
    hf.mul (GlobalSlotStokes.ChartSmooth.continuous (hsm a))
  have hg0 (a : Fin m) (x : M) : 0 ≤ g a x := mul_nonneg (hn x) (h0 a x)
  have hgs (a : Fin m) : tsupport (g a) ⊆ tsupport (part a) := tsupport_mul_subset_right
  have hsum : (fun x => ∑ a, g a x) = f := by
    funext x
    simp only [g, ← Finset.mul_sum, h1 x, mul_one]
  have htotal (w : M → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (μ : Measure M) :
      (∑ a, ∫⁻ x, ENNReal.ofReal (w x * g a x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (w x * f x) ∂μ := by
    have h := sum_lintegrals_ofReal (fun a x => w x * g a x)
      (fun a => hw.mul (hgc a).measurable) (fun a x => mul_nonneg (hw0 x) (hg0 a x)) μ
    exact h.trans (lintegral_congr (fun x => congrArg ENNReal.ofReal
      (by rw [← Finset.mul_sum, congrFun hsum x])))
  have hlocal (a : Fin m) :
      (∫⁻ x, ENNReal.ofReal (χ₀ x * g a x) ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ j x * g a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := by
    have hsource : tsupport (g a) ⊆ (J a).chart.val.source :=
      fun x hx => (hsupp a (hgs a hx)).1
    have hgcpt : IsCompact (tsupport (g a)) :=
      (hcpt a).of_isClosed_subset (isClosed_tsupport _) (hgs a)
    let K : Set (ComplexModel n) := (J a).chart.val '' tsupport (g a)
    have hK : IsCompact K := isCompact_image_tsupport hgcpt hsource
    have hKD : K ⊆ D a := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hsupp a (hgs a hx)).2
    have hread0 : ∀ z, 0 ≤ chartRead (J a).chart (g a) z := by
      intro z
      by_cases hz : z ∈ (J a).chart.val.target
      · rw [chartRead_of_mem hz]; exact hg0 a _
      · rw [chartRead_of_notMem hz]
    have h := chart_moving_test_liminf omega hu hv hcap (J a) (hcompact a) (hclosure a) hK hKD
      hC hχ0 hχ₀C hχm hχ₀m hχ₀ hχcap
      (continuous_chartRead_of_continuous (hgc a) hgcpt hsource) hread0
      (tsupport_chartRead_subset hgcpt hsource)
    rwa [chartExtend_read_eq (J a).chart (g a) hsource] at h
  calc
    _ = ∑ a, ∫⁻ x, ENNReal.ofReal (χ₀ x * g a x)
        ∂globalMixedMeasure θ v (fun i => (hv i).1) :=
      (htotal χ₀ hχ₀m (fun x => (hχ₀C x).1) _).symm
    _ ≤ ∑ a, liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ j x * g a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop :=
      Finset.sum_le_sum (fun a _ => hlocal a)
    _ ≤ liminf (fun j => ∑ a, ∫⁻ x, ENNReal.ofReal (χ j x * g a x)
        ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := finite_sum_liminf_le _
    _ = _ := congrArg (fun q : ℕ → ℝ≥0∞ => liminf q atTop)
      (funext fun j => htotal (χ j) (hχm j) (hχ0 j) _)

omit [TopologicalSpace M] [BorelSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] in
/-- A moving liminf inequality of integrals of bounded nonnegative Borel functions against
finite measures gives eventual real lower bounds. -/
theorem eventually_integral_gt_moving
    {μ : ℕ → Measure M} {ν : Measure M}
    [∀ j, IsFiniteMeasure (μ j)] [IsFiniteMeasure ν]
    {g : ℕ → M → ℝ} {g₀ : M → ℝ} {B : ℝ}
    (hm : ∀ j, Measurable (g j)) (hm₀ : Measurable g₀)
    (hb : ∀ j x, |g j x| ≤ B) (hb₀ : ∀ x, |g₀ x| ≤ B)
    (hn : ∀ j x, 0 ≤ g j x) (hn₀ : ∀ x, 0 ≤ g₀ x)
    (hliminf : (∫⁻ x, ENNReal.ofReal (g₀ x) ∂ν) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal (g j x) ∂μ j) atTop)
    {a : ℝ} (ha : a < ∫ x, g₀ x ∂ν) :
    ∀ᶠ j in atTop, a < ∫ x, g j x ∂μ j := by
  have heq (j : ℕ) :
      ENNReal.ofReal (∫ x, g j x ∂μ j) = ∫⁻ x, ENNReal.ofReal (g j x) ∂μ j :=
    ofReal_integral_eq_lintegral_ofReal (integrable_of_bounded (hm j) (hb j))
      (Eventually.of_forall (hn j))
  have heq₀ : ENNReal.ofReal (∫ x, g₀ x ∂ν) = ∫⁻ x, ENNReal.ofReal (g₀ x) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal (integrable_of_bounded hm₀ hb₀)
      (Eventually.of_forall hn₀)
  by_cases ha0 : a < 0
  · exact Eventually.of_forall (fun j => ha0.trans_le (integral_nonneg (hn j)))
  · have ha0' : 0 ≤ a := not_lt.mp ha0
    have hp : 0 < ∫ x, g₀ x ∂ν := ha0'.trans_lt ha
    have hENN : ENNReal.ofReal a < liminf (fun j => ∫⁻ x,
        ENNReal.ofReal (g j x) ∂μ j) atTop :=
      ((ENNReal.ofReal_lt_ofReal_iff hp).mpr ha).trans_le (heq₀.trans_le hliminf)
    filter_upwards [eventually_lt_of_lt_liminf hENN] with j hj
    rw [← heq j] at hj
    exact (ENNReal.ofReal_lt_ofReal_iff').mp hj |>.1

/-- **Weak convergence of the weighted non-pluripolar products under mass convergence**
(`thm:semicon`, second part, in native form): `χ_j ⟨θ_{u_j}⟩ → χ₀ ⟨θ_v⟩` against every
continuous function. -/
theorem tendsto_integral_moving (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j i, IsThetaPshPotential (θ i).val (u j i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (hcap : ∀ i a, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j i x ≠ ⊥ ∧ v i x ≠ ⊥ ∧ a < |(u j i x).toReal - (v i x).toReal|})
      atTop (𝓝 0))
    (hmass : Tendsto (fun j => globalMixedMeasure θ (u j) (fun i => (hu j i).1) univ) atTop
      (𝓝 (globalMixedMeasure θ v (fun i => (hv i).1) univ)))
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hχC : ∀ j x, 0 ≤ χ j x ∧ χ j x ≤ C) (hχ₀C : ∀ x, 0 ≤ χ₀ x ∧ χ₀ x ≤ C)
    (hχm : ∀ j, Measurable (χ j)) (hχ₀m : Measurable χ₀)
    (hχ₀ : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) χ₀)
    (hχcap : ∀ c : ℝ, 0 < c → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | c < |χ j x - χ₀ x|}) atTop (𝓝 0))
    (g : C(M, ℝ)) :
    Tendsto (fun j => ∫ x, g x * χ j x ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1))
      atTop (𝓝 (∫ x, g x * χ₀ x ∂globalMixedMeasure θ v (fun i => (hv i).1))) := by
  classical
  let μ (j : ℕ) : Measure M := globalMixedMeasure θ (u j) (fun i => (hu j i).1)
  let ν : Measure M := globalMixedMeasure θ v (fun i => (hv i).1)
  let : ∀ j, IsFiniteMeasure (μ j) := fun j => globalMixedMeasure_isFiniteMeasure omega _
  let : IsFiniteMeasure ν := globalMixedMeasure_isFiniteMeasure omega _
  obtain ⟨G₀, hG₀⟩ := isCompact_univ.exists_bound_of_continuousOn g.continuous.continuousOn
  let G : ℝ := max G₀ 0 + 1
  have hG : 0 < G := by positivity
  have hgG (x : M) : |g x| ≤ G := by
    have h := hG₀ x (mem_univ x)
    rw [Real.norm_eq_abs] at h
    exact h.trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  let B : ℝ := G * C
  have hB : 0 ≤ B := mul_nonneg hG.le hC
  -- the weights `B ± g χ`
  have habsχ (j : ℕ) (x : M) : |g x * χ j x| ≤ B := by
    rw [abs_mul, abs_of_nonneg (hχC j x).1]
    exact mul_le_mul (hgG x) (hχC j x).2 (hχC j x).1 hG.le
  have habsχ₀ (x : M) : |g x * χ₀ x| ≤ B := by
    rw [abs_mul, abs_of_nonneg (hχ₀C x).1]
    exact mul_le_mul (hgG x) (hχ₀C x).2 (hχ₀C x).1 hG.le
  have hpos (s : ℝ) (hs : s = 1 ∨ s = -1) (j : ℕ) (x : M) : 0 ≤ B + s * (g x * χ j x) := by
    rcases hs with rfl | rfl
    · linarith [(abs_le.mp (habsχ j x)).1]
    · linarith [(abs_le.mp (habsχ j x)).2]
  have hpos₀ (s : ℝ) (hs : s = 1 ∨ s = -1) (x : M) : 0 ≤ B + s * (g x * χ₀ x) := by
    rcases hs with rfl | rfl
    · linarith [(abs_le.mp (habsχ₀ x)).1]
    · linarith [(abs_le.mp (habsχ₀ x)).2]
  have hlower (s : ℝ) (hs : s = 1 ∨ s = -1) :
      (∫⁻ x, ENNReal.ofReal (B + s * (g x * χ₀ x)) ∂ν) ≤
        liminf (fun j => ∫⁻ x, ENNReal.ofReal (B + s * (g x * χ j x)) ∂μ j) atTop := by
    have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    have hQC : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0))
        (fun x => B + s * (g x * χ₀ x)) := by
      intro eta heta
      obtain ⟨O, hO, hOc, hcont⟩ := hχ₀ eta heta
      exact ⟨O, hO, hOc, continuousOn_const.add (continuousOn_const.mul
        (g.continuous.continuousOn.mul hcont))⟩
    have hcapw : ∀ c : ℝ, 0 < c → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
        {x | c < |(B + s * (g x * χ j x)) - (B + s * (g x * χ₀ x))|}) atTop (𝓝 0) := by
      intro c hc
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hχcap (c / G) (div_pos hc hG)) (fun _ => zero_le) (fun j => thetaCapacity_mono ?_)
      intro x hx
      change c < |(B + s * (g x * χ j x)) - (B + s * (g x * χ₀ x))| at hx
      change c / G < |χ j x - χ₀ x|
      have he : (B + s * (g x * χ j x)) - (B + s * (g x * χ₀ x)) =
          s * g x * (χ j x - χ₀ x) := by ring
      rw [he, abs_mul, abs_mul, hs1, one_mul] at hx
      rw [div_lt_iff₀ hG]
      calc c < |g x| * |χ j x - χ₀ x| := hx
        _ ≤ G * |χ j x - χ₀ x| := mul_le_mul_of_nonneg_right (hgG x) (abs_nonneg _)
        _ = |χ j x - χ₀ x| * G := mul_comm _ _
    have h := lintegral_le_liminf_moving omega hu hv hcap
      (χ := fun j x => B + s * (g x * χ j x)) (χ₀ := fun x => B + s * (g x * χ₀ x))
      (C := 2 * B) (by positivity) (fun j x => hpos s hs j x)
      (fun x => ⟨hpos₀ s hs x, by
        rw [abs_of_nonneg (hpos₀ s hs x)]
        have : |s * (g x * χ₀ x)| ≤ B := by rw [abs_mul, hs1, one_mul]; exact habsχ₀ x
        linarith [(abs_le.mp this).2]⟩)
      (fun j => measurable_const.add (measurable_const.mul (g.continuous.measurable.mul (hχm j))))
      (measurable_const.add (measurable_const.mul (g.continuous.measurable.mul hχ₀m)))
      hQC hcapw continuous_const (fun _ => zero_le_one)
    simpa only [mul_one] using h
  -- integrability of all tests
  have hintχ (j : ℕ) : Integrable (fun x => g x * χ j x) (μ j) :=
    integrable_of_bounded (g.continuous.measurable.mul (hχm j)) (habsχ j)
  have hintχ₀ : Integrable (fun x => g x * χ₀ x) ν :=
    integrable_of_bounded (g.continuous.measurable.mul hχ₀m) habsχ₀
  have hsplit (τ : Measure M) [IsFiniteMeasure τ] (w : M → ℝ) (hw : Integrable w τ) (s : ℝ) :
      (∫ x, B + s * w x ∂τ) = B * τ.real univ + s * ∫ x, w x ∂τ := by
    rw [integral_add (integrable_const B) (hw.const_mul s), integral_const, integral_const_mul,
      smul_eq_mul, mul_comm]
  have hreal : Tendsto (fun j => (μ j).real univ) atTop (𝓝 (ν.real univ)) := by
    have h := (ENNReal.tendsto_toReal (measure_ne_top ν univ)).comp hmass
    simpa only [Function.comp_def, measureReal_def] using h
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hplus := eventually_integral_gt_moving
    (μ := μ) (ν := ν) (g := fun j x => B + 1 * (g x * χ j x))
    (g₀ := fun x => B + 1 * (g x * χ₀ x)) (B := 2 * B)
    (fun j => measurable_const.add (measurable_const.mul (g.continuous.measurable.mul (hχm j))))
    (measurable_const.add (measurable_const.mul (g.continuous.measurable.mul hχ₀m)))
    (fun j x => by
      rw [abs_of_nonneg (hpos 1 (Or.inl rfl) j x), one_mul]
      linarith [(abs_le.mp (habsχ j x)).2])
    (fun x => by
      rw [abs_of_nonneg (hpos₀ 1 (Or.inl rfl) x), one_mul]
      linarith [(abs_le.mp (habsχ₀ x)).2])
    (hpos 1 (Or.inl rfl)) (hpos₀ 1 (Or.inl rfl)) (hlower 1 (Or.inl rfl))
    (show (∫ x, B + 1 * (g x * χ₀ x) ∂ν) - ε / 3 < ∫ x, B + 1 * (g x * χ₀ x) ∂ν by linarith)
  have hminus := eventually_integral_gt_moving
    (μ := μ) (ν := ν) (g := fun j x => B + -1 * (g x * χ j x))
    (g₀ := fun x => B + -1 * (g x * χ₀ x)) (B := 2 * B)
    (fun j => measurable_const.add (measurable_const.mul (g.continuous.measurable.mul (hχm j))))
    (measurable_const.add (measurable_const.mul (g.continuous.measurable.mul hχ₀m)))
    (fun j x => by
      rw [abs_of_nonneg (hpos (-1) (Or.inr rfl) j x)]
      linarith [(abs_le.mp (habsχ j x)).1])
    (fun x => by
      rw [abs_of_nonneg (hpos₀ (-1) (Or.inr rfl) x)]
      linarith [(abs_le.mp (habsχ₀ x)).1])
    (hpos (-1) (Or.inr rfl)) (hpos₀ (-1) (Or.inr rfl)) (hlower (-1) (Or.inr rfl))
    (show (∫ x, B + -1 * (g x * χ₀ x) ∂ν) - ε / 3 < ∫ x, B + -1 * (g x * χ₀ x) ∂ν by linarith)
  have hnear := Metric.tendsto_nhds.mp (hreal.const_mul B) (ε / 3) hε3
  filter_upwards [hplus, hminus, hnear] with j hjp hjn hjmass
  rw [hsplit ν _ hintχ₀, hsplit (μ j) _ (hintχ j)] at hjp hjn
  rw [Real.dist_eq, abs_lt] at hjmass ⊢
  constructor <;> linarith [hjmass.1, hjmass.2]

end SGPT.NPP.CapacityConvergence
