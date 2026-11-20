import SGPT.PSH.LocalL1
import SGPT.Foundations.Analysis.PSHD.DiscRecovery
import SGPT.Foundations.Analysis.FirstPass.PotentialL1

set_option autoImplicit false

noncomputable section
namespace SGPT.PSH.LocalL1Recovery
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Finite lower truncation retains original poles before taking a real value. -/
def lowerTrunc (L : ℝ) (u : E → EReal) : E → ℝ :=
  fun x => (max (u x) (L : EReal)).toReal

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
/-- The actual lower truncation is genuinely disc PSH, including at original poles. -/
theorem discPshOn_lowerTrunc {u : E → EReal} {U : Set E}
    (hu : DiscPshOn u U) (L : ℝ) :
    DiscPshOn (fun x => (lowerTrunc L u x : EReal)) U := by
  apply (hu.max (discPshOn_const (L : EReal) (EReal.coe_ne_top L) U)).congr
  intro x hx
  exact (EReal.coe_toReal
    (ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (hu.ne_top x hx))
      (EReal.coe_lt_top L)))
    (ne_of_gt ((EReal.bot_lt_coe L).trans_le (le_max_right _ _)))).symm

/-- Genuine finite clipping is contractive for the original canonical distance.
The assertion includes both infinities; no finiteness certificate is supplied. -/
theorem lowerTrunc_enorm_sub_le (a b : EReal) (L : ℝ) :
    ‖(max a (L : EReal)).toReal - (max b (L : EReal)).toReal‖ₑ ≤
      canonicalERealAbsDiff a b := by
  have hmax (s : ℝ) : max (s : EReal) (L : EReal) = ((max s L : ℝ) : EReal) := by
    by_cases hs : s ≤ L
    · rw [max_eq_right (EReal.coe_le_coe hs), max_eq_right hs]
    · rw [max_eq_left (EReal.coe_le_coe (le_of_not_ge hs)),
        max_eq_left (le_of_not_ge hs)]
  cases a <;> cases b <;>
    simp [canonicalERealAbsDiff, poleModifiedERealAbsDiff, EReal.abs_def,
      hmax, ← EReal.coe_sub, Real.enorm_eq_ofReal_abs]
  exact abs_max_sub_max_le_abs _ _ L

/-- Local canonical L1 convergence gives actual convergence of every clipped
ball mean. Integrability comes from genuine PSH ball estimates. -/
theorem tendsto_integral_lowerTrunc_ball
    {u : ℕ → E → EReal} {v : E → EReal} {U : Set E}
    (hu : ∀ j, DiscPshOn (u j) U) (hv : DiscPshOn v U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (p : E) {r : ℝ} (hr : 0 < r) (hB : closedBall p r ⊆ U) (L : ℝ)
    (hlim : Tendsto (fun j => ∫⁻ x in closedBall p r,
      canonicalERealAbsDiff (u j x) (v x) ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x in ball p r, lowerTrunc L (u j) x ∂μ)
      atTop (𝓝 (∫ x in ball p r, lowerTrunc L v x ∂μ)) := by
  have hi (f : E → EReal) (hf : DiscPshOn f U) :
      IntegrableOn (lowerTrunc L f) (ball p r) μ := by
    have hclip := discPshOn_lowerTrunc hf L
    simpa using (hclip.ae_finite_and_integrableOn_ball μ p hr hB
      (EReal.coe_ne_bot _)).2.1
  apply tendsto_integral_of_L1 (lowerTrunc L v) (hi v hv).aestronglyMeasurable
    (Eventually.of_forall fun j => hi (u j) (hu j))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le)
  intro j
  exact (lintegral_mono fun x => lowerTrunc_enorm_sub_le (u j x) (v x) L).trans
    (lintegral_mono_set ball_subset_closedBall)

/-- Original local canonical L1 convergence forces the true point values
eventually below every finite number above the source limit. -/
theorem eventually_lt_of_localL1
    {u : ℕ → E → EReal} {v : E → EReal} {U : Set E}
    (hu : ∀ j, DiscPshOn (u j) U) (hv : DiscPshOn v U) (hU : IsOpen U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hlim : ∀ K : Set E, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫⁻ x in K, canonicalERealAbsDiff (u j x) (v x) ∂μ)
        atTop (𝓝 0))
    {p : E} (hp : p ∈ U) {a : ℝ} (ha : v p < (a : EReal)) :
    ∀ᶠ j in atTop, u j p < (a : EReal) := by
  obtain ⟨b, hb, hba⟩ := EReal.exists_between_coe_real ha
  have hupper : ∀ᶠ x in 𝓝 p, x ∈ U ∧ v x < (b : EReal) := by
    have hh := hv.upperSemicontinuousOn p hp (b : EReal) hb
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hp)] at hh
    exact (show ∀ᶠ x in 𝓝 p, x ∈ U from hU.mem_nhds hp).and hh
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hupper
  let r := δ / 2
  have hr : 0 < r := half_pos hδ
  have hB : closedBall p r ⊆ U := by
    intro x hx
    exact (hbound ((mem_closedBall.mp hx).trans_lt (half_lt_self hδ))).1
  let L := b - 1
  have hconv := tendsto_integral_lowerTrunc_ball hu hv μ p hr hB L
    (hlim (closedBall p r) (isCompact_closedBall p r) hB)
  have hint : IntegrableOn (lowerTrunc L v) (ball p r) μ := by
    simpa using ((discPshOn_lowerTrunc hv L).ae_finite_and_integrableOn_ball
      μ p hr hB (EReal.coe_ne_bot _)).2.1
  have hm : 0 < (μ (ball p r)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos μ p hr)) measure_ball_lt_top.ne
  let : IsFiniteMeasure (μ.restrict (ball p r)) :=
    ⟨by simpa using measure_ball_lt_top (μ := μ) (x := p) (r := r)⟩
  have hmean : (∫ x in ball p r, lowerTrunc L v x ∂μ) /
      (μ (ball p r)).toReal ≤ b := by
    apply (div_le_iff₀ hm).mpr
    have hle : (∫ x in ball p r, lowerTrunc L v x ∂μ) ≤
        ∫ _x in ball p r, b ∂μ := by
      apply integral_mono_ae hint (integrable_const b)
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hvx := (hbound ((mem_ball.mp hx).trans (half_lt_self hδ))).2.le
      have hmax : max (v x) (L : EReal) ≤ (b : EReal) :=
        max_le hvx (EReal.coe_le_coe (by dsimp [L]; linarith))
      exact EReal.toReal_le_toReal hmax
        (ne_of_gt ((EReal.bot_lt_coe L).trans_le (le_max_right _ _)))
        (EReal.coe_ne_top b)
    simpa [integral_const, Measure.real, smul_eq_mul, mul_comm] using hle
  have hbA : b < a := EReal.coe_lt_coe_iff.mp hba
  have hev := (hconv.div_const (μ (ball p r)).toReal).eventually
    (gt_mem_nhds (hmean.trans_lt hbA))
  filter_upwards [hev] with j hj
  have hsub := PSHD.le_real_ball_average (discPshOn_lowerTrunc (hu j) L) μ p hr hB
  have hpclip : max (u j p) (L : EReal) ≠ ⊤ :=
    ne_of_lt (max_lt (lt_top_iff_ne_top.mpr ((hu j).ne_top p hp))
      (EReal.coe_lt_top L))
  exact ((le_max_left (u j p) (L : EReal)).trans
    (EReal.le_coe_toReal hpclip)).trans_lt
      (EReal.coe_lt_coe_iff.mpr (hsub.trans_lt hj))

/-- Every original point has the full extended upper-limsup inequality,
including negative-infinite limit values. -/
theorem limsup_le_of_localL1
    {u : ℕ → E → EReal} {v : E → EReal} {U : Set E}
    (hu : ∀ j, DiscPshOn (u j) U) (hv : DiscPshOn v U) (hU : IsOpen U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hlim : ∀ K : Set E, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫⁻ x in K, canonicalERealAbsDiff (u j x) (v x) ∂μ)
        atTop (𝓝 0)) :
    ∀ p ∈ U, limsup (fun j => u j p) atTop ≤ v p := by
  intro p hp
  apply (limsup_le_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
  intro c hc
  obtain ⟨a, ha, hac⟩ := EReal.exists_between_coe_real hc
  exact (eventually_lt_of_localL1 hu hv hU μ hlim hp ha).mono
    (fun j hj => hj.trans hac)

/-- Actual local canonical L1 convergence internally gives a uniform upper
bound for the entire original family on a neighborhood of every point. -/
theorem exists_local_uniform_upper_bound_of_localL1
    {u : ℕ → E → EReal} {v : E → EReal} {U : Set E}
    (hu : ∀ j, DiscPshOn (u j) U) (hv : DiscPshOn v U) (hU : IsOpen U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hlim : ∀ K : Set E, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫⁻ x in K, canonicalERealAbsDiff (u j x) (v x) ∂μ)
        atTop (𝓝 0))
    {p : E} (hp : p ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧
      ∃ C : ℝ, ∀ j : ℕ, ∀ x ∈ ball p r, u j x ≤ (C : EReal) := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU p hp
  let s := R / 2
  have hs : 0 < s := half_pos hR
  have hBs : closedBall p s ⊆ U :=
    (closedBall_subset_ball (half_lt_self hR)).trans hRU
  have hconv := tendsto_integral_lowerTrunc_ball hu hv μ p hs hBs 0
    (hlim (closedBall p s) (isCompact_closedBall p s) hBs)
  obtain ⟨B, hB⟩ := hconv.bddAbove_range
  let r := s / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r < s := by dsimp [r]; linarith
  have hm : 0 < (μ (ball (0 : E) r)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos μ 0 hr)) measure_ball_lt_top.ne
  refine ⟨r, hr, (ball_subset_ball hrs.le).trans (ball_subset_closedBall.trans hBs),
    B / (μ (ball (0 : E) r)).toReal, ?_⟩
  intro j x hx
  have hsmall : closedBall x r ⊆ ball p s := by
    intro y hy
    have hd := dist_triangle y x p
    have hyx := mem_closedBall.mp hy
    have hxp := mem_ball.mp hx
    apply mem_ball.mpr
    dsimp [r] at hyx hxp
    linarith
  have hi : IntegrableOn (lowerTrunc 0 (u j)) (ball p s) μ := by
    simpa using ((discPshOn_lowerTrunc (hu j) 0).ae_finite_and_integrableOn_ball
      μ p hs hBs (EReal.coe_ne_bot _)).2.1
  have hnonneg : ∀ y : E, 0 ≤ lowerTrunc 0 (u j) y :=
    fun y => EReal.toReal_nonneg (by simp)
  have hmono := setIntegral_mono_set hi (Eventually.of_forall hnonneg)
    (Eventually.of_forall (show ball x r ⊆ ball p s from ball_subset_closedBall.trans hsmall))
  have hmass : μ (ball x r) = μ (ball (0 : E) r) := by
    simpa using (lintegral_ball_add μ (fun _ => (1 : ℝ≥0∞)) x r).symm
  have hsub := PSHD.le_real_ball_average (discPshOn_lowerTrunc (hu j) 0)
    μ x hr (hsmall.trans (ball_subset_closedBall.trans hBs))
  rw [hmass] at hsub
  have hvalue : lowerTrunc 0 (u j) x ≤ B / (μ (ball (0 : E) r)).toReal :=
    hsub.trans (div_le_div_of_nonneg_right
      (hmono.trans (hB (mem_range_self j))) hm.le)
  have hpclip : max (u j x) (0 : EReal) ≠ ⊤ :=
    ne_of_lt (max_lt (lt_top_iff_ne_top.mpr
      ((hu j).ne_top x (hBs (ball_subset_closedBall (ball_subset_ball hrs.le hx)))))
      (EReal.coe_lt_top 0))
  exact ((le_max_left (u j x) (0 : EReal)).trans
    (EReal.le_coe_toReal hpclip)).trans (EReal.coe_le_coe hvalue)

end SGPT.PSH.LocalL1Recovery
