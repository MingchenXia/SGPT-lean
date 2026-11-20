import SGPT.Okounkov.TranscendentalWNLegendreSmooth
import SGPT.Foundations.Analysis.Pending.BedfordTaylorDecreasingLimit
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
import SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorDecreasing

/-!
# Measure-theoretic tools for the locally bounded case (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:bounded-case` (auxiliary statements).

* `tendsto_lintegral_truncationLimitMeasure_of_antitone`: **Bedford–Taylor decreasing
  continuity** for TN's non-pluripolar measures of locally bounded psh functions, tested against
  a continuous compactly supported `φ ≥ 0` and written with lower Lebesgue integrals
  (from `BedfordTaylor.tendsto_integral_of_antitone_isBTLimit`);
* `exists_cutoff_seq`: for a bounded open set `V`, continuous compactly supported functions
  `0 ≤ φ_j ≤ 1` with `tsupport φ_j ⊆ V` increasing to `1_V`;
* `truncationLimitMeasure_apply_of_subset`: the non-pluripolar measure of a set `E ⊆ V` is the
  same on `V` and on a larger open set (locality).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending

variable {n : ℕ}

/-! ### Integrals of compactly supported test functions -/

theorem integrable_of_continuous_of_measure_tsupport_lt_top {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {φ : X → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hμ : μ (tsupport φ) < ⊤) :
    Integrable φ μ := by
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  have hon : IntegrableOn φ (tsupport φ) μ :=
    Measure.integrableOn_of_bounded (M := M) hμ.ne hφ.aestronglyMeasurable
      (Eventually.of_forall fun x => hM x)
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport φ)).mp hon

/-- `∫⁻ ofReal φ = ofReal ∫ φ` for a continuous compactly supported `φ ≥ 0`. -/
theorem lintegral_ofReal_eq_ofReal_integral {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} {φ : X → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hμ : μ (tsupport φ) < ⊤)
    (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫⁻ x, ENNReal.ofReal (φ x) ∂μ = ENNReal.ofReal (∫ x, φ x ∂μ) :=
  (ofReal_integral_eq_lintegral_ofReal
    (integrable_of_continuous_of_measure_tsupport_lt_top hφ hφc hμ)
    (Eventually.of_forall hφ0)).symm

/-! ### Local boundedness -/

/-- A psh function dominated by a continuous function is locally bounded. -/
theorem isLocallyBoundedPshOn_of_abs_le_continuousOn {U : Opens (ComplexModel n)}
    {f g : ComplexModel n → ℝ} (hp : PlurisubharmonicOn (fun z => (f z : EReal)) U)
    (hg : ContinuousOn g U) (hfg : ∀ z ∈ U, |f z| ≤ g z) : IsLocallyBoundedPshOn U f := by
  refine ⟨hp, fun z hz => ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen z hz
  have hcb : closedBall z (r / 2) ⊆ (U : Set (ComplexModel n)) :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨C, hC⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn (hg.mono hcb)
  refine ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by linarith),
    fun w hw => hcb (ball_subset_closedBall hw), C, fun w hw => ?_⟩
  have hw' : w ∈ closedBall z (r / 2) := ball_subset_closedBall hw
  exact (hfg w (hcb hw')).trans ((le_abs_self _).trans (by simpa using hC w hw'))

/-! ### Bedford–Taylor decreasing continuity -/

/-- **Bedford–Taylor decreasing continuity** for the non-pluripolar measures of locally bounded
psh functions, in lower-integral form. -/
theorem tendsto_lintegral_truncationLimitMeasure_of_antitone {Ω : Opens (ComplexModel n)}
    {w : ℕ → ComplexModel n → ℝ} {v : ComplexModel n → ℝ}
    (hw : ∀ k, IsLocallyBoundedPshOn Ω (w k)) (hv : IsLocallyBoundedPshOn Ω v)
    (hanti : ∀ z ∈ Ω, Antitone fun k => w k z)
    (hlim : ∀ z ∈ Ω, Tendsto (fun k => w k z) atTop (𝓝 (v z)))
    {φ : ComplexModel n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) (hφ0 : ∀ z, 0 ≤ φ z) :
    Tendsto (fun k => ∫⁻ z, ENNReal.ofReal (φ z) ∂(MongeAmpere.truncationLimitMeasure Ω
        (fun z => (w k z : EReal)) (hw k).1)) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (φ z) ∂(MongeAmpere.truncationLimitMeasure Ω
        (fun z => (v z : EReal)) hv.1))) := by
  have hBT := BedfordTaylor.tendsto_integral_of_antitone_isBTLimit hw hv hanti hlim
    (fun k => BedfordTaylor.isBTLimit_canonicalBedfordTaylorMeasure (hw k))
    (BedfordTaylor.isBTLimit_canonicalBedfordTaylorMeasure hv) hφ hφc hφΩ
  have hfin : ∀ {f : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f),
      MongeAmpere.canonicalBedfordTaylorMeasure Ω f hf (tsupport φ) < ⊤ := fun hf =>
    MongeAmpere.canonicalBedfordTaylorMeasure_finiteOnCompacts hf hφc hφΩ
  have e : ∀ {f : ComplexModel n → ℝ} (hf : IsLocallyBoundedPshOn Ω f),
      ∫⁻ z, ENNReal.ofReal (φ z) ∂(MongeAmpere.truncationLimitMeasure Ω
        (fun z => (f z : EReal)) hf.1) =
      ENNReal.ofReal (∫ z, φ z ∂(MongeAmpere.canonicalBedfordTaylorMeasure Ω f hf)) := by
    intro f hf
    rw [MongeAmpere.truncationLimitMeasure_eq_canonical hf]
    exact lintegral_ofReal_eq_ofReal_integral hφ hφc (hfin hf) hφ0
  rw [e hv]
  exact ((ENNReal.continuous_ofReal.tendsto _).comp hBT).congr fun k => (e (hw k)).symm

/-! ### Locality -/

/-- For `E ⊆ V ≤ Ω`, the non-pluripolar measure of `E` is the same on `V` and on `Ω`. -/
theorem truncationLimitMeasure_apply_of_subset {Ω V : Opens (ComplexModel n)} (hVΩ : V ≤ Ω)
    {f : ComplexModel n → EReal} (hf : PlurisubharmonicOn f Ω) (hfV : PlurisubharmonicOn f V)
    {E : Set (ComplexModel n)} (hE : E ⊆ V) :
    MongeAmpere.truncationLimitMeasure Ω f hf E = MongeAmpere.truncationLimitMeasure V f hfV E := by
  rw [← MongeAmpere.truncationLimitMeasure_restrict_open hVΩ hf hfV,
    Measure.restrict_apply' V.isOpen.measurableSet, inter_eq_left.mpr hE]

/-! ### Cutoff sequences for bounded open sets -/

/-- Continuous compactly supported `0 ≤ φ_j ≤ 1`, `tsupport φ_j ⊆ V`, increasing to `1_V`. -/
theorem exists_cutoff_seq {X : Type*} [MetricSpace X] [ProperSpace X] {V : Set X}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) :
    ∃ φ : ℕ → X → ℝ, (∀ j, Continuous (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ V) ∧ (∀ j x, 0 ≤ φ j x ∧ φ j x ≤ 1) ∧
      (∀ x, Monotone fun j => φ j x) ∧
      (∀ x, Tendsto (fun j => φ j x) atTop (𝓝 (V.indicator (fun _ => (1 : ℝ)) x))) := by
  by_cases hne : (Vᶜ).Nonempty
  · set φ : ℕ → X → ℝ := fun j x => max 0 (min 1 ((j + 1 : ℝ) * infDist x Vᶜ - 1)) with hφ
    have hcont : ∀ j, Continuous (φ j) := fun j =>
      continuous_const.max (continuous_const.min
        ((continuous_const.mul (continuous_infDist_pt _)).sub continuous_const))
    have hts : ∀ j, tsupport (φ j) ⊆ {x | 0 ≤ (j + 1 : ℝ) * infDist x Vᶜ - 1} := by
      intro j
      refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const
        ((continuous_const.mul (continuous_infDist_pt _)).sub continuous_const))
      rw [Function.mem_support] at hx
      by_contra hlt
      simp only [mem_ofPred_eq, not_le] at hlt
      apply hx
      simp only [hφ]
      rw [min_eq_right (by linarith), max_eq_left hlt.le]
    have hsub : ∀ j, tsupport (φ j) ⊆ V := by
      intro j x hx
      by_contra hxV
      have h0 : infDist x Vᶜ = 0 := infDist_zero_of_mem hxV
      have := hts j hx
      simp only [mem_ofPred_eq, h0, mul_zero, zero_sub] at this
      linarith
    refine ⟨φ, hcont, fun j => ?_, hsub, fun j x => ⟨le_max_left _ _, ?_⟩, fun x j l hjl => ?_,
      fun x => ?_⟩
    · exact (hVb.isCompact_closure).of_isClosed_subset (isClosed_tsupport _)
        ((hsub j).trans subset_closure)
    · exact max_le zero_le_one (min_le_left _ _)
    · have hd := infDist_nonneg (x := x) (s := Vᶜ)
      have : ((j : ℝ) + 1) * infDist x Vᶜ ≤ ((l : ℝ) + 1) * infDist x Vᶜ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ hjl) hd
      simp only [hφ]
      exact max_le_max le_rfl (min_le_min le_rfl (by linarith))
    · by_cases hx : x ∈ V
      · rw [indicator_of_mem hx]
        have hpos : 0 < infDist x Vᶜ :=
          (hV.isClosed_compl.notMem_iff_infDist_pos hne).mp (fun h => h hx)
        obtain ⟨J, hJ⟩ := exists_nat_gt (2 / infDist x Vᶜ)
        refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨J, fun j hj => ?_⟩)
        have hj : (2 / infDist x Vᶜ) < (j : ℝ) + 1 := by
          have : (J : ℝ) ≤ j := by exact_mod_cast hj
          linarith
        have h2 : 2 ≤ ((j : ℝ) + 1) * infDist x Vᶜ := by
          rw [div_lt_iff₀ hpos] at hj
          linarith
        simp only [hφ]
        rw [min_eq_left (by linarith), max_eq_right zero_le_one]
      · rw [indicator_of_notMem hx]
        have h0 : infDist x Vᶜ = 0 := infDist_zero_of_mem hx
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun j => ?_)
        simp only [hφ, h0, mul_zero, zero_sub]
        rw [min_eq_right (by norm_num), max_eq_left (by norm_num)]
  · have hV' : V = univ := by
      rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
      exact hne
    subst hV'
    refine ⟨fun _ _ => 1, fun _ => continuous_const, fun _ => ?_, fun _ => subset_univ _,
      fun _ _ => ⟨zero_le_one, le_rfl⟩, fun _ _ _ _ => le_rfl, fun x => ?_⟩
    · exact (hVb.isCompact_closure).of_isClosed_subset (isClosed_tsupport _)
        (by rw [closure_univ]; exact subset_univ _)
    · rw [indicator_of_mem (mem_univ x)]
      exact tendsto_const_nhds

end SGPT.Okounkov.TranscendentalWN
