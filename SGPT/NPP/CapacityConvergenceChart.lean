import SGPT.NPP.CapacityModulus
import SGPT.Foundations.Analysis.Pending.ActualMixedCapacityQuasiContinuousLiminf
import SGPT.Foundations.Analysis.Pending.ActualChartCapacityReverse
import SGPT.Foundations.Analysis.Pending.BedfordTaylorFixedWeight
import SGPT.Foundations.Analysis.Pending.ActualCapacityUpperBound

/-!
# Moving quasi-continuous weights in a slot chart

This file proves the chart-level step of the semicontinuity theorem of non-pluripolar
products with *moving* weights (source `thm:semicon`, chapter `chapter_npp.tex`; Xia,
*Foundations of pluripotential theory*, `thm:nonpluripolar-capacity-lower-limit` and
`lem:nonpluripolar-cutoff-weights`).

Let `u_j → v` in Kähler capacity (the gap sets
`{u_j ≠ -∞, v ≠ -∞, |u_j - v| > a}` have capacity tending to zero), and let `χ_j → χ` be
uniformly bounded nonnegative Borel weights converging in Kähler capacity, `χ`
quasi-continuous. In a precompact slot chart `D`, for a nonnegative continuous test `h`
with compact support,

`∫ χ h ⟨θ_v⟩ ≤ liminf_j ∫ χ_j h ⟨θ_{u_j}⟩`.

Proof. At truncation level `k`, the cutoff weight `a_k ∈ [0,1]` of
`lem:nonpluripolar-cutoff-weights` turns the non-pluripolar products into Bedford–Taylor
products `λ_j` of the truncations, and the fixed-weight limit
`∫ χ h a_k dλ_j → ∫ χ h a_k dλ` is the existing
`exists_tail_quasiContinuous_cutoff_lintegral_limits`. The truncations lie in a fixed box on
`D` for large `j`, so `λ_j(E) ≤ c_k Cap_D(E)` (`IsBTLimit.le_relCapacity_of_abs_le`), and the
relative capacity of subsets of a compact set is dominated by the Kähler capacity
(`exists_compact_capacity_reverse`). Hence replacing `χ` by `χ_j` costs at most
`H (c λ_j(K) + C λ_j({|χ_j - χ| > c} ∩ K))`, which tends to `H c λ_j(K)`, and `c > 0` is
arbitrary. Letting `k → ∞` (`tendsto_lintegral_cutoff`) gives the inequality.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators ENNReal

namespace SGPT.NPP.CapacityConvergence

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.FirstPass.MixedNonPluripolar
open SGPT.Foundations.Analysis.FirstPass.GlobalPotentialPatches
open GlobalSlotStokes GlobalNonPluripolar MixedNonPluripolar MixedMongeAmpere ThetaCapacity
open ActualLocalNonPluripolarCutoffIntegrals ChartPartition CapacityWeightedConvergence
open BedfordTaylor

/-- If `a_j → A` and eventually `a_j ≤ b_j + e + δ_j` with `δ_j → 0`, then
`A ≤ liminf b + e`. -/
theorem le_liminf_add_of_tendsto {a b δ : ℕ → ℝ≥0∞} {A e : ℝ≥0∞}
    (ha : Tendsto a atTop (𝓝 A)) (hδ : Tendsto δ atTop (𝓝 0))
    (hle : ∀ᶠ j in atTop, a j ≤ b j + e + δ j) : A ≤ liminf b atTop + e := by
  have h1 : liminf a atTop ≤ liminf ((fun j => b j + e) + δ) atTop :=
    liminf_le_liminf hle
  have h2 : liminf ((fun j => b j + e) + δ) atTop = liminf (fun j => b j + e) atTop :=
    ENNReal.liminf_add_of_right_tendsto_zero hδ _
  have h3 : liminf (fun j => b j + e) atTop = liminf b atTop + e :=
    liminf_add_const atTop b e (by isBoundedDefault) (by isBoundedDefault)
  rw [← ha.liminf_eq]
  exact h1.trans (h2.trans h3).le

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- A chart read of a Borel function, cut off by a continuous test supported in the
coordinate domain, is Borel. -/
theorem measurable_supported_read (e : ComplexChart n M)
    {D : Opens (ComplexModel n)} (hDt : (D : Set (ComplexModel n)) ⊆ e.val.target)
    {χ : M → ℝ} (hχ : Measurable χ) {h : ComplexModel n → ℝ} (hc : Continuous h)
    (hz : ∀ z, z ∉ D → h z = 0) :
    Measurable (fun z => χ (e.val.symm z) * h z) := by
  apply measurable_of_restrict_of_restrict_compl e.val.open_target.measurableSet
  · have hi : Measurable (e.val.target.domRestrict e.val.symm) :=
      (continuousOn_iff_continuous_domRestrict.mp e.val.symm.continuousOn).measurable
    exact (hχ.comp hi).mul (hc.measurable.comp measurable_subtype_coe)
  · have heq : e.val.targetᶜ.domRestrict (fun z => χ (e.val.symm z) * h z) =
        fun _ => (0 : ℝ) := by
      funext z
      exact mul_eq_zero_of_right _ (hz _ (fun hh => z.property (hDt hh)))
    rw [heq]
    exact measurable_const

/-- The chart read of a Borel function, extended by zero off the chart target, is Borel. -/
theorem measurable_indicator_read (e : ComplexChart n M) {χ : M → ℝ} (hχ : Measurable χ) :
    Measurable (e.val.target.indicator (fun z => χ (e.val.symm z))) := by
  apply measurable_of_restrict_of_restrict_compl e.val.open_target.measurableSet
  · have hi : Measurable (e.val.target.domRestrict e.val.symm) :=
      (continuousOn_iff_continuous_domRestrict.mp e.val.symm.continuousOn).measurable
    have heq : e.val.target.domRestrict (e.val.target.indicator (fun z => χ (e.val.symm z))) =
        fun z => χ (e.val.target.domRestrict e.val.symm z) := by
      funext z
      exact indicator_of_mem z.property _
    rw [heq]
    exact hχ.comp hi
  · have heq : e.val.targetᶜ.domRestrict (e.val.target.indicator (fun z => χ (e.val.symm z))) =
        fun _ => (0 : ℝ) := by
      funext z
      exact indicator_of_notMem z.property _
    rw [heq]
    exact measurable_const

variable [IsComplexManifold n M] [CompactSpace M]

/-- A global test supported in a slot-chart domain integrates against the global
non-pluripolar product as its chart read against the local non-pluripolar product. -/
theorem global_chart_test_eq
    {θ : Fin n → ClosedRealOneOneForm n M} {κ : ClosedRealOneOneForm n M}
    (J : SlotChart θ κ) {D : Opens (ComplexModel n)} (hD : D ≤ J.domain)
    {u : Fin n → M → EReal} (hu : ∀ i, ThetaPlurisubharmonic (θ i).val (u i))
    (hcorr : ∀ i, PlurisubharmonicOn
      (fun z => u i (J.chart.val.symm z) + (J.potential i z : EReal)) D)
    {χ : M → ℝ} {h : ComplexModel n → ℝ} (hzero : ∀ z, z ∉ D → h z = 0) :
    (∫⁻ x, ENNReal.ofReal (χ x * chartExtend J.chart h x) ∂globalMixedMeasure θ u hu) =
    ∫⁻ z, ENNReal.ofReal (χ (J.chart.val.symm z) * h z) ∂mixedTruncationLimitMeasure D
      (fun i z => u i (J.chart.val.symm z) + (J.potential i z : EReal)) hcorr := by
  let P : Patch θ u := {
    chart := J.chart
    domain := D
    domain_le_target := fun z hz => J.domain_le_target (hD hz)
    potential := J.potential
    localPotential := fun i => (J.localPotential i).mono D.isOpen hD
    plurisubharmonic := hcorr }
  have hs : Function.support (fun x => ENNReal.ofReal (χ x * chartExtend J.chart h x)) ⊆
      (P.source : Set M) := by
    intro x hx
    by_contra hbad
    apply hx
    change ENNReal.ofReal (χ x * chartExtend J.chart h x) = 0
    by_cases hxs : x ∈ J.chart.val.source
    · rw [chartExtend_of_mem hxs, hzero _ (fun hxD => hbad ⟨hxs, hxD⟩), mul_zero,
        ENNReal.ofReal_zero]
    · rw [chartExtend_of_notMem hxs, mul_zero, ENNReal.ofReal_zero]
  have hcomp : (mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic)
      (P.domain : Set (ComplexModel n))ᶜ = 0 :=
    mixedTruncationLimitMeasure_compl P.plurisubharmonic
  calc
    _ = ∫⁻ x in P.source, ENNReal.ofReal (χ x * chartExtend J.chart h x)
        ∂globalMixedMeasure θ u hu := (setLIntegral_eq_of_support_subset hs).symm
    _ = ∫⁻ z, ENNReal.ofReal (χ (J.chart.val.symm z) *
          chartExtend J.chart h (J.chart.val.symm z))
        ∂mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic := by
      rw [globalMixedMeasure_restrict_patch hu P, patchMeasure,
        ActualSingularChartMassLiminf.lintegral_pushMeasure P hcomp]
    _ = _ := by
      apply lintegral_congr_ae
      have hae : ∀ᵐ z ∂mixedTruncationLimitMeasure P.domain P.corrected P.plurisubharmonic,
          z ∈ P.domain := ae_iff.mpr hcomp
      filter_upwards [hae] with z hz
      rw [chartExtend_of_mem (J.chart.val.map_target (P.domain_le_target hz)),
        J.chart.val.right_inv (P.domain_le_target hz)]

/-- **Chart step of `thm:semicon` with moving weights.** For capacity-convergent potentials,
moving bounded nonnegative Borel weights `χ_j → χ₀` in Kähler capacity with `χ₀`
quasi-continuous, and a nonnegative continuous test `h` supported in a compact subset of a
precompact slot-chart domain, the weighted non-pluripolar integrals satisfy the liminf
inequality. -/
theorem chart_moving_test_liminf (omega : KahlerBackground n M)
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
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D)
    {χ : ℕ → M → ℝ} {χ₀ : M → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hχ0 : ∀ j x, 0 ≤ χ j x) (hχ₀C : ∀ x, 0 ≤ χ₀ x ∧ |χ₀ x| ≤ C)
    (hχm : ∀ j, Measurable (χ j)) (hχ₀m : Measurable χ₀)
    (hχ₀ : QuasiContinuousFor (thetaCapacity omega.form (fun _ => 0)) χ₀)
    (hχcap : ∀ c : ℝ, 0 < c → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | c < |χ j x - χ₀ x|}) atTop (𝓝 0))
    {h : ComplexModel n → ℝ} (hc : Continuous h) (hn : ∀ z, 0 ≤ h z)
    (ht : tsupport h ⊆ K) :
    (∫⁻ x, ENNReal.ofReal (χ₀ x * chartExtend J.chart h x)
      ∂globalMixedMeasure θ v (fun i => (hv i).1)) ≤
    liminf (fun j => ∫⁻ x, ENNReal.ofReal (χ j x * chartExtend J.chart h x)
      ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)) atTop := by
  classical
  let corr (f : Fin n → M → EReal) : Fin n → ComplexModel n → EReal :=
    fun i z => f i (J.chart.val.symm z) + (J.potential i z : EReal)
  have hDJ : D ≤ J.domain := fun z hz => hclosure (subset_closure hz)
  have hDt : (D : Set (ComplexModel n)) ⊆ J.chart.val.target :=
    fun z hz => J.domain_le_target (hDJ hz)
  have hCorr (f : Fin n → M → EReal) (hf : ∀ i, IsThetaPshPotential (θ i).val (f i)) :
      ∀ i, PlurisubharmonicOn (corr f i) D := fun i =>
    (BoundedGlobalProduct.ThetaPlurisubharmonic.corrected_plurisubharmonicOn
      (hf i).1 J.chart (J.localPotential i)).mono hDJ
  have hzK : ∀ z, z ∉ K → h z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun hs => hz (ht hs))
  have hzD : ∀ z, z ∉ D → h z = 0 := fun z hz => hzK z (fun hzK => hz (hKD hzK))
  obtain ⟨N, hU, hV, hlimits⟩ :=
    ActualSingularChartQuasiContinuousCutoffWeightedLimits.exists_tail_quasiContinuous_cutoff_lintegral_limits
      omega hu hv hcap J hcompact hclosure hK hKD
  let b (j : ℕ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (χ j x * chartExtend J.chart h x)
    ∂globalMixedMeasure θ (u j) (fun i => (hu j i).1)
  -- an eventual box bound for the corrected potentials on `D`
  obtain ⟨B, hB, hBev⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ j in atTop, ∀ i, ∀ y ∈ D,
      corr (u (j + N)) i y ≤ (B : EReal) := by
    choose H hH using fun i : Fin n =>
      ActualCapacityUpperBound.exists_eventual_upper_bound omega (fun j => hu j i) (hv i)
        (hcap i)
    choose R hR using fun i : Fin n => hcompact.exists_bound_of_continuousOn
      ((J.localPotential i).2.2.1.continuousOn.mono hclosure)
    refine ⟨∑ i, (|H i| + |R i|), Finset.sum_nonneg fun i _ => by positivity, ?_⟩
    have hall : ∀ᶠ j in atTop, ∀ i, ∀ x, u j i x ≤ (H i : EReal) := eventually_all.mpr hH
    filter_upwards [(tendsto_add_atTop_nat N).eventually hall] with j hj i y hy
    have hr : |J.potential i y| ≤ R i := by
      simpa only [Real.norm_eq_abs] using hR i y (subset_closure hy)
    have hsingle : |H i| + |R i| ≤ ∑ i, (|H i| + |R i|) :=
      Finset.single_le_sum (f := fun i : Fin n => |H i| + |R i|) (fun i _ => by positivity)
        (Finset.mem_univ i)
    calc corr (u (j + N)) i y ≤ ((H i + J.potential i y : ℝ) : EReal) := by
          change u (j + N) i (J.chart.val.symm y) + (J.potential i y : EReal) ≤ _
          rw [EReal.coe_add]
          exact add_le_add (hj i _) le_rfl
      _ ≤ _ := EReal.coe_le_coe_iff.mpr (by
          have h1 := le_abs_self (H i)
          have h2 := le_abs_self (J.potential i y)
          have h3 := le_abs_self (R i)
          linarith)
  -- comparison of relative and Kähler capacity on `K`
  obtain ⟨Crev, hCrev, hrev⟩ :=
    ActualChartCapacityReverse.exists_compact_capacity_reverse omega J.chart hDt
      (J.kahlerLocal.mono D.isOpen hDJ) hK hKD
  have hKcap : relCapacity D K < ⊤ := by
    refine (hrev K le_rfl).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    have h := SGPT.NPP.sourceThetaCapacity_lt_top omega
      (SGPT.PSH.VariableComplexAtlas.nativeClosedFormToAtlas omega.form) (J.chart.val.symm '' K)
    rwa [SGPT.NPP.sourceThetaCapacity_kahler] at h
  -- a bound for the test
  obtain ⟨Hh, hHh⟩ : ∃ Hh : ℝ, ∀ z, h z ≤ Hh := by
    obtain ⟨R, hR⟩ := hc.bounded_above_of_compact_support
      (hK.of_isClosed_subset (isClosed_tsupport _) ht)
    exact ⟨R, fun z => (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hR z)⟩
  have hHh0 : 0 ≤ Hh := (hn 0).trans (hHh 0)
  -- the chart reads of the weights
  let r (w : M → ℝ) : ComplexModel n → ℝ :=
    J.chart.val.target.indicator (fun z => w (J.chart.val.symm z))
  have hr_eq (w : M → ℝ) {z : ComplexModel n} (hz : z ∈ K) :
      r w z = w (J.chart.val.symm z) := indicator_of_mem (hDt (hKD hz)) _
  -- the level-wise bound
  have hbound (k : ℕ) :
      (∫⁻ z, ENNReal.ofReal (χ₀ (J.chart.val.symm z) * h z) * ENNReal.ofReal
        (cutoff k (fun i => mixedTruncationReal (corr v) k i z))
        ∂mixedTruncationLimitMeasure D (corr v) hV) ≤ liminf b atTop := by
    have hlim := (hlimits k χ₀ C hC hχ₀C hχ₀m hχ₀ h hc hn ht).2.2
    let Mk : ℝ≥0∞ := ENNReal.ofReal ((n * (2 * (B + k + 1))) ^ n)
    -- the truncated BT measures
    let lam (j : ℕ) : Measure (ComplexModel n) := canonicalMixedBedfordTaylorMeasure D
      (mixedTruncationReal (corr (u (j + N))) k) (mixedTruncationReal_isLocallyBounded (hU j) k)
    have hdom : ∀ᶠ j in atTop, ∀ E : Set (ComplexModel n), E ⊆ D →
        lam j E ≤ Mk * relCapacity D E := by
      filter_upwards [hBev] with j hj E hE
      have hlimit : IsBTLimit D (mixedTruncationReal (corr (u (j + N))) k) (lam j) :=
        IsLocalMixedBedfordTaylorMeasure.isBTLimit
          (canonicalMixedBedfordTaylorMeasure_spec D _ _)
      refine hlimit.le_relCapacity_of_abs_le (mixedTruncationReal_isLocallyBounded (hU j) k)
        le_rfl (by positivity) (fun i y hy => ?_) hE
      have hcoe := coe_mixedTruncationReal (hU j) k i hy
      have hlo : -(k : ℝ) ≤ mixedTruncationReal (corr (u (j + N))) k i y := by
        apply EReal.coe_le_coe_iff.mp
        rw [hcoe]
        exact truncation_lower_bound _ k y
      have hhi : mixedTruncationReal (corr (u (j + N))) k i y ≤ B := by
        apply EReal.coe_le_coe_iff.mp
        rw [hcoe]
        exact max_le (hj i y hy) (EReal.coe_le_coe_iff.mpr (by
          have := Nat.cast_nonneg (α := ℝ) k
          linarith))
      rw [abs_le]
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) k]
    -- the measurable cutoff
    let cutD (w : Fin n → ComplexModel n → EReal) (z : ComplexModel n) : ℝ≥0∞ :=
      ENNReal.ofReal (cutoff k (fun i => (D : Set (ComplexModel n)).indicator
        (mixedTruncationReal w k i) z))
    have hcutD (w : Fin n → ComplexModel n → EReal) (hw : ∀ i, PlurisubharmonicOn (w i) D) :
        Measurable (cutD w) := by
      refine ENNReal.measurable_ofReal.comp ((cutoff_properties k).1.continuous.measurable.comp
        (measurable_pi_lambda _ fun i => ?_))
      exact LocalBedfordTaylorProducts.measurable_indicator_of_isLocallyBoundedPshOn
        (mixedTruncationReal_isLocallyBounded hw k i)
    have hcut_le (w : Fin n → ComplexModel n → EReal) (z : ComplexModel n) :
        ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal w k i z)) ≤ 1 :=
      ENNReal.ofReal_le_one.mpr ((cutoff_properties k).2 _).1.2
    have hfinal (c : ℝ) (hc0 : 0 < c) :
        (∫⁻ z, ENNReal.ofReal (χ₀ (J.chart.val.symm z) * h z) * ENNReal.ofReal
          (cutoff k (fun i => mixedTruncationReal (corr v) k i z))
          ∂mixedTruncationLimitMeasure D (corr v) hV) ≤
          liminf b atTop + ENNReal.ofReal (Hh * c) * (Mk * relCapacity D K) := by
      let E (j : ℕ) : Set (ComplexModel n) :=
        {z | z ∈ K ∧ c < |r (χ (j + N)) z - r χ₀ z|}
      have hEm (j : ℕ) : MeasurableSet (E j) :=
        hK.measurableSet.inter (measurableSet_lt measurable_const
          (continuous_abs.measurable.comp ((measurable_indicator_read J.chart (hχm (j + N))).sub
            (measurable_indicator_read J.chart hχ₀m))))
      let G (j : ℕ) (z : ComplexModel n) : ℝ≥0∞ :=
        ENNReal.ofReal (Hh * c) * K.indicator 1 z + ENNReal.ofReal (Hh * C) * (E j).indicator 1 z
      have hGm (j : ℕ) : Measurable (G j) :=
        (measurable_const.mul (measurable_one.indicator hK.measurableSet)).add
          (measurable_const.mul (measurable_one.indicator (hEm j)))
      have hG0 (j : ℕ) (z : ComplexModel n) (hz : z ∉ D) : G j z = 0 := by
        have hzK' : z ∉ K := fun h' => hz (hKD h')
        have hzE : z ∉ E j := fun h' => hzK' h'.1
        simp only [G, indicator_of_notMem hzK', indicator_of_notMem hzE, mul_zero, add_zero]
      -- pointwise comparison of the weights
      have hpt (j : ℕ) (z : ComplexModel n) :
          ENNReal.ofReal (χ₀ (J.chart.val.symm z) * h z) ≤
            ENNReal.ofReal (χ (j + N) (J.chart.val.symm z) * h z) + G j z := by
        by_cases hzK' : z ∈ K
        · have hχ₀z := hχ₀C (J.chart.val.symm z)
          have hχz := hχ0 (j + N) (J.chart.val.symm z)
          have hhz := hHh z
          have hnz := hn z
          by_cases hzE : z ∈ E j
          · have hG : ENNReal.ofReal (Hh * C) ≤ G j z := by
              simp only [G, indicator_of_mem hzE, Pi.one_apply, mul_one]
              exact le_add_self
            refine le_trans ?_ (add_le_add le_rfl hG)
            rw [← ENNReal.ofReal_add (mul_nonneg hχz hnz) (mul_nonneg hHh0 hC)]
            apply ENNReal.ofReal_le_ofReal
            have : χ₀ (J.chart.val.symm z) * h z ≤ C * Hh := by
              have habs := (le_abs_self (χ₀ (J.chart.val.symm z))).trans hχ₀z.2
              exact mul_le_mul habs hhz hnz hC
            nlinarith [mul_nonneg hχz hnz]
          · have hgap : |χ (j + N) (J.chart.val.symm z) - χ₀ (J.chart.val.symm z)| ≤ c := by
              have : ¬ c < |r (χ (j + N)) z - r χ₀ z| := fun h' => hzE ⟨hzK', h'⟩
              rw [hr_eq _ hzK', hr_eq _ hzK'] at this
              exact le_of_not_gt this
            have hG : ENNReal.ofReal (Hh * c) ≤ G j z := by
              simp only [G, indicator_of_mem hzK', Pi.one_apply, mul_one]
              exact le_self_add
            refine le_trans ?_ (add_le_add le_rfl hG)
            rw [← ENNReal.ofReal_add (mul_nonneg hχz hnz) (mul_nonneg hHh0 hc0.le)]
            apply ENNReal.ofReal_le_ofReal
            have hle : χ₀ (J.chart.val.symm z) ≤ χ (j + N) (J.chart.val.symm z) + c := by
              have := neg_abs_le (χ (j + N) (J.chart.val.symm z) - χ₀ (J.chart.val.symm z))
              linarith
            have h1 : χ₀ (J.chart.val.symm z) * h z ≤
                (χ (j + N) (J.chart.val.symm z) + c) * h z :=
              mul_le_mul_of_nonneg_right hle hnz
            have h2 : c * h z ≤ Hh * c := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hhz hc0.le
            nlinarith
        · rw [hzK z hzK', mul_zero, ENNReal.ofReal_zero]
          exact zero_le
      -- integrated comparison
      have hint (j : ℕ) :
          (∫⁻ z, ENNReal.ofReal (χ₀ (J.chart.val.symm z) * h z) * ENNReal.ofReal
            (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
            ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) ≤
          (∫⁻ z, ENNReal.ofReal (χ (j + N) (J.chart.val.symm z) * h z) * ENNReal.ofReal
            (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
            ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) +
          ∫⁻ z, G j z ∂lam j := by
        have hGcut : (fun z => G j z * ENNReal.ofReal
            (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))) =
            fun z => G j z * cutD (corr (u (j + N))) z := by
          funext z
          by_cases hz : z ∈ D
          · simp only [cutD, indicator_of_mem hz]
          · rw [hG0 j z hz, zero_mul, zero_mul]
        calc _ ≤ ∫⁻ z, (ENNReal.ofReal (χ (j + N) (J.chart.val.symm z) * h z) * ENNReal.ofReal
              (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z)) +
              G j z * ENNReal.ofReal
              (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z)))
              ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j) := by
              apply lintegral_mono
              intro z
              change _ ≤ _ * _ + _ * _
              rw [← add_mul]
              exact mul_le_mul_left (hpt j z) _
          _ = (∫⁻ z, ENNReal.ofReal (χ (j + N) (J.chart.val.symm z) * h z) * ENNReal.ofReal
              (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
              ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) +
              ∫⁻ z, G j z * ENNReal.ofReal
              (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
              ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j) := by
              rw [lintegral_add_right _ (by rw [hGcut]; exact (hGm j).mul (hcutD _ (hU j)))]
          _ ≤ _ := by
              refine add_le_add le_rfl ?_
              rw [← (lintegral_cutoff_eq_le (hU j) k (h := G j) (hG0 j)).1]
              exact lintegral_mono fun z => mul_le_of_le_one_right zero_le (hcut_le _ z)
      -- the error integrals
      have herr : ∀ᶠ j in atTop, (∫⁻ z, G j z ∂lam j) ≤
          ENNReal.ofReal (Hh * c) * (Mk * relCapacity D K) +
            ENNReal.ofReal (Hh * C) * (Mk * (ENNReal.ofReal Crev *
              thetaCapacity omega.form (fun _ => 0) {x | c < |χ (j + N) x - χ₀ x|})) := by
        filter_upwards [hdom] with j hj
        have hKm : Measurable (fun z => ENNReal.ofReal (Hh * c) * K.indicator 1 z) :=
          measurable_const.mul (measurable_one.indicator hK.measurableSet)
        rw [lintegral_add_left hKm, lintegral_const_mul _ (measurable_one.indicator hK.measurableSet),
          lintegral_const_mul _ (measurable_one.indicator (hEm j)),
          lintegral_indicator_one hK.measurableSet, lintegral_indicator_one (hEm j)]
        refine add_le_add (mul_le_mul_right (hj K hKD) _) (mul_le_mul_right ?_ _)
        refine (hj (E j) (fun z hz => hKD hz.1)).trans (mul_le_mul_right ?_ _)
        refine (hrev (E j) (fun z hz => hz.1)).trans (mul_le_mul_right ?_ _)
        apply thetaCapacity_mono
        rintro _ ⟨z, hz, rfl⟩
        have := hz.2
        rw [hr_eq _ hz.1, hr_eq _ hz.1] at this
        exact this
      have hδ : Tendsto (fun j => ENNReal.ofReal (Hh * C) * (Mk * (ENNReal.ofReal Crev *
          thetaCapacity omega.form (fun _ => 0) {x | c < |χ (j + N) x - χ₀ x|}))) atTop (𝓝 0) := by
        have h0 := (hχcap c hc0).comp (tendsto_add_atTop_nat N)
        have h1 := ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.ofReal_ne_top (r := Crev)))
        have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (ENNReal.ofReal_ne_top
          (r := (n * (2 * (B + k + 1))) ^ n)))
        have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.ofReal_ne_top (r := Hh * C)))
        simpa only [mul_zero, Function.comp_def] using h3
      have hmain := le_liminf_add_of_tendsto hlim hδ (by
        filter_upwards [herr] with j hj
        refine (hint j).trans ?_
        rw [add_assoc]
        exact add_le_add le_rfl hj)
      refine hmain.trans (add_le_add ?_ le_rfl)
      calc liminf (fun j => ∫⁻ z, ENNReal.ofReal (χ (j + N) (J.chart.val.symm z) * h z) *
              ENNReal.ofReal (cutoff k (fun i => mixedTruncationReal (corr (u (j + N))) k i z))
              ∂mixedTruncationLimitMeasure D (corr (u (j + N))) (hU j)) atTop
          ≤ liminf (fun j => b (j + N)) atTop := by
            refine liminf_le_liminf (Eventually.of_forall fun j => ?_)
            refine (lintegral_cutoff_eq_le (hU j) k (fun z hz => by
              rw [hzD z hz, mul_zero, ENNReal.ofReal_zero])).2.trans_eq ?_
            exact (global_chart_test_eq (χ := χ (j + N)) J hDJ (fun i => (hu (j + N) i).1)
              (hU j) hzD).symm
        _ = liminf b atTop := liminf_nat_add b N
    -- let `c → 0`
    have hlimc : Tendsto (fun c : ℝ => liminf b atTop +
        ENNReal.ofReal (Hh * c) * (Mk * relCapacity D K)) (𝓝[>] 0)
        (𝓝 (liminf b atTop + 0)) := by
      refine tendsto_const_nhds.add ?_
      have h1 : Tendsto (fun c : ℝ => ENNReal.ofReal (Hh * c)) (𝓝[>] 0) (𝓝 0) := by
        have := ((ENNReal.continuous_ofReal.comp (continuous_const_mul Hh)).tendsto' 0 0
          (by simp)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa only [Function.comp_def] using this
      have hfin : Mk * relCapacity D K ≠ ⊤ :=
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKcap).ne
      have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hfin)
      simpa only [zero_mul] using h2
    rw [add_zero] at hlimc
    exact ge_of_tendsto hlimc (eventually_nhdsWithin_of_forall fun c hc0 => hfinal c hc0)
  have htarget := tendsto_lintegral_cutoff hV
    (measurable_supported_read J.chart hDt hχ₀m hc hzD).ennreal_ofReal
    (fun z hz => by rw [hzD z hz, mul_zero, ENNReal.ofReal_zero])
  rw [global_chart_test_eq (χ := χ₀) J hDJ (fun i => (hv i).1) (hCorr v hv) hzD]
  exact le_of_tendsto htarget (Eventually.of_forall hbound)

end SGPT.NPP.CapacityConvergence
