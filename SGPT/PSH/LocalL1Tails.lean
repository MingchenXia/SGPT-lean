import SGPT.PSH.LocalL1Recovery
import SGPT.PSH.Supremum
import SGPT.Foundations.Analysis.FirstPass.PotentialL1AESubsequence
import SGPT.Foundations.Analysis.PlurisubharmonicAE

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.LocalL1Recovery
open Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Actual original local L1 convergence gives uniform eventual upper
recovery on a genuine neighborhood of each original point. -/
theorem eventually_locally_lt_of_localL1
    {u : ℕ → E → EReal} {v : E → EReal} {U : Set E}
    (hu : ∀ j, DiscPshOn (u j) U) (hv : DiscPshOn v U) (hU : IsOpen U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hlim : ∀ K : Set E, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫⁻ x in K, canonicalERealAbsDiff (u j x) (v x) ∂μ)
        atTop (𝓝 0))
    {p : E} (hp : p ∈ U) {a : ℝ} (ha : v p < (a : EReal)) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧
      ∀ᶠ j in atTop, ∀ x ∈ ball p r, u j x < (a : EReal) := by
  obtain ⟨b, hb, hba⟩ := EReal.exists_between_coe_real ha
  have hbaR : b < a := EReal.coe_lt_coe_iff.mp hba
  have hupper : ∀ᶠ x in 𝓝 p, x ∈ U ∧ v x < (b : EReal) := by
    have hh := hv.upperSemicontinuousOn p hp (b : EReal) hb
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hp)] at hh
    exact (show ∀ᶠ x in 𝓝 p, x ∈ U from hU.mem_nhds hp).and hh
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hupper
  let s := δ / 2
  have hs : 0 < s := half_pos hδ
  have hBs : closedBall p s ⊆ U := by
    intro x hx
    exact (hbound ((mem_closedBall.mp hx).trans_lt (half_lt_self hδ))).1
  let r := s / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r < s := by dsimp [r]; linarith
  let A := (μ (ball p s)).toReal
  let D := (μ (ball (0 : E) r)).toReal
  have hA : 0 ≤ A := ENNReal.toReal_nonneg
  have hD : 0 < D :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos μ 0 hr)) measure_ball_lt_top.ne
  let M := A / D
  have hM : 0 ≤ M := div_nonneg hA hD.le
  let ε := (a - b) / (2 * (M + 1))
  have hε : 0 < ε := div_pos (sub_pos.mpr hbaR) (by positivity)
  have hεM : ε * M < a - b := by
    dsimp only [ε]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < 2 * (M + 1))]
    nlinarith
  let L := b - ε
  have hconv := tendsto_integral_lowerTrunc_ball hu hv μ p hs hBs L
    (hlim (closedBall p s) (isCompact_closedBall p s) hBs)
  have hi (f : E → EReal) (hf : DiscPshOn f U) :
      IntegrableOn (lowerTrunc L f) (ball p s) μ := by
    simpa using ((discPshOn_lowerTrunc hf L).ae_finite_and_integrableOn_ball
      μ p hs hBs (EReal.coe_ne_bot _)).2.1
  let : IsFiniteMeasure (μ.restrict (ball p s)) :=
    ⟨by simpa using measure_ball_lt_top (μ := μ) (x := p) (r := s)⟩
  have hIv : (∫ x in ball p s, lowerTrunc L v x ∂μ) ≤ A * b := by
    have hh : (∫ x in ball p s, lowerTrunc L v x ∂μ) ≤
        ∫ _x in ball p s, b ∂μ := by
      apply integral_mono_ae (hi v hv) (integrable_const b)
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hvx := (hbound ((mem_ball.mp hx).trans (half_lt_self hδ))).2.le
      exact EReal.toReal_le_toReal (max_le hvx
        (EReal.coe_le_coe (by dsimp [L]; linarith)))
        (ne_of_gt ((EReal.bot_lt_coe L).trans_le (le_max_right _ _))) (EReal.coe_ne_top b)
    simpa [A, integral_const, Measure.real, smul_eq_mul] using hh
  have hlimit : ((∫ x in ball p s, lowerTrunc L v x ∂μ) - A * L) / D + L < a := by
    have hmul : M * D = A := div_mul_cancel₀ A hD.ne'
    apply (lt_sub_iff_add_lt).mp
    apply (div_lt_iff₀ hD).mpr
    dsimp [L] at *
    nlinarith [hεM]
  have hevent := (((hconv.sub_const (A * L)).div_const D).add_const L).eventually
    (gt_mem_nhds hlimit)
  refine ⟨r, hr, (ball_subset_ball hrs.le).trans (ball_subset_closedBall.trans hBs), ?_⟩
  filter_upwards [hevent] with j hj
  intro x hx
  have hsmall : closedBall x r ⊆ ball p s := by
    intro y hy
    have hd := dist_triangle y x p
    have hyx := mem_closedBall.mp hy
    have hxp := mem_ball.mp hx
    apply mem_ball.mpr
    dsimp [r] at hyx hxp
    linarith
  have hsmallU := hsmall.trans (ball_subset_closedBall.trans hBs)
  have hm : μ (ball x r) = μ (ball (0 : E) r) := by
    simpa using (lintegral_ball_add μ (fun _ => (1 : ℝ≥0∞)) x r).symm
  let : IsFiniteMeasure (μ.restrict (ball x r)) :=
    ⟨by simpa using measure_ball_lt_top (μ := μ) (x := x) (r := r)⟩
  have hIx : IntegrableOn (lowerTrunc L (u j)) (ball x r) μ := by
    simpa using ((discPshOn_lowerTrunc (hu j) L).ae_finite_and_integrableOn_ball
      μ x hr hsmallU (EReal.coe_ne_bot _)).2.1
  have hpositive : ∀ᵐ y ∂μ.restrict (ball p s), 0 ≤ lowerTrunc L (u j) y - L := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have htop := (hu j).ne_top y (hBs (ball_subset_closedBall hy))
    have h := EReal.toReal_le_toReal (le_max_right (u j y) (L : EReal))
      (EReal.coe_ne_bot L) (ne_of_lt (max_lt (lt_top_iff_ne_top.mpr htop) (EReal.coe_lt_top L)))
    exact sub_nonneg.mpr (by simpa [lowerTrunc] using h)
  have hmono := setIntegral_mono_set ((hi (u j) (hu j)).sub (integrable_const L)) hpositive
    (Eventually.of_forall (show ball x r ⊆ ball p s from ball_subset_closedBall.trans hsmall))
  change (∫ y in ball x r, lowerTrunc L (u j) y - L ∂μ) ≤
    (∫ y in ball p s, lowerTrunc L (u j) y - L ∂μ) at hmono
  rw [integral_sub hIx (integrable_const L), integral_sub (hi (u j) (hu j))
    (integrable_const L), integral_const, integral_const] at hmono
  have hmono' : (∫ y in ball x r, lowerTrunc L (u j) y ∂μ) - D * L ≤
      (∫ y in ball p s, lowerTrunc L (u j) y ∂μ) - A * L := by
    simpa [Measure.real, smul_eq_mul, hm, D, A] using hmono
  have hsub := PSHD.le_real_ball_average (discPshOn_lowerTrunc (hu j) L) μ x hr hsmallU
  rw [hm] at hsub
  have hvalue : lowerTrunc L (u j) x < a := by
    apply lt_of_le_of_lt hsub
    change (∫ y in ball x r, lowerTrunc L (u j) y ∂μ) / D < a
    apply (div_lt_iff₀ hD).mpr
    have hj' := (div_lt_iff₀ hD).mp ((lt_sub_iff_add_lt).mpr hj)
    linarith
  have hpclip : max (u j x) (L : EReal) ≠ ⊤ :=
    ne_of_lt (max_lt (lt_top_iff_ne_top.mpr ((hu j).ne_top x
      (hBs (ball_subset_closedBall (ball_subset_ball hrs.le hx))))) (EReal.coe_lt_top L))
  exact ((le_max_left (u j x) (L : EReal)).trans (EReal.le_coe_toReal hpclip)).trans_lt
    (EReal.coe_lt_coe_iff.mpr hvalue)

/-- The infimum of the actual upper-regularized original tails is bounded
above by the original local L1 limit at every point, including poles. -/
theorem iInf_uscSup_tail_le_of_localL1
    {u : ℕ → E → EReal} {v : E → EReal} {U : Set E}
    (hu : ∀ j, DiscPshOn (u j) U) (hv : DiscPshOn v U) (hU : IsOpen U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hlim : ∀ K : Set E, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫⁻ x in K, canonicalERealAbsDiff (u j x) (v x) ∂μ)
        atTop (𝓝 0)) :
    ∀ p ∈ U, (⨅ N : ℕ, uscSup (fun j => u (j + N)) p) ≤ v p := by
  intro p hp
  apply le_of_forall_gt
  intro c hc
  obtain ⟨a, ha, hac⟩ := EReal.exists_between_coe_real hc
  obtain ⟨r, hr, _hBU, hevent⟩ := eventually_locally_lt_of_localL1 hu hv hU μ hlim hp ha
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  have hlocal : uscSup (fun j => u (j + N)) p ≤ (a : EReal) := by
    apply (uscRegularization_le_localSup (fun x => ⨆ j, u (j + N) x)
      (isOpen_ball.mem_nhds (mem_ball_self hr))).trans
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact iSup_le fun j => (hN (j + N) (by omega) y hy).le
  exact ((iInf_le (fun M => uscSup (fun j => u (j + M)) p) N).trans hlocal).trans_lt hac

/-- Any genuine PSH majorant of every original sequence member also majorizes
the actual local L1 limit. Finite lower truncations produce the measurable
representatives internally, so original negative-infinite values are retained. -/
theorem le_of_localL1_of_le
    {u : ℕ → E → EReal} {v w : E → EReal} {U : Set E}
    (hu : ∀ j, DiscPshOn (u j) U) (hv : DiscPshOn v U)
    (hw : DiscPshOn w U) (hU : IsOpen U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hlim : ∀ K : Set E, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫⁻ x in K, canonicalERealAbsDiff (u j x) (v x) ∂μ)
        atTop (𝓝 0))
    (huw : ∀ j, ∀ x ∈ U, u j x ≤ w x) :
    ∀ p ∈ U, v p ≤ w p := by
  intro p hp
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU p hp
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hBU : closedBall p r ⊆ U :=
    (closedBall_subset_ball (half_lt_self hR)).trans hRU
  have hclip (L : ℝ) : lowerTrunc L v p ≤ lowerTrunc L w p := by
    have hi (f : E → EReal) (hf : DiscPshOn f U) :
        IntegrableOn (lowerTrunc L f) (ball p r) μ := by
      simpa using ((discPshOn_lowerTrunc hf L).ae_finite_and_integrableOn_ball
        μ p hr hBU (EReal.coe_ne_bot _)).2.1
    have hm (f : E → EReal) (hf : DiscPshOn f U) :
        AEMeasurable (fun x => (lowerTrunc L f x : EReal)) (μ.restrict (ball p r)) :=
      continuous_coe_real_ereal.measurable.comp_aemeasurable
        (hi f hf).aestronglyMeasurable.aemeasurable
    have hL1 : Tendsto (fun j => ∫⁻ x in ball p r,
        canonicalERealAbsDiff (lowerTrunc L (u j) x : EReal)
          (lowerTrunc L v x : EReal) ∂μ) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hlim (closedBall p r) (isCompact_closedBall p r) hBU) (fun _ => zero_le)
      intro j
      apply (lintegral_mono ?_).trans (lintegral_mono_set ball_subset_closedBall)
      intro x
      simpa [canonicalERealAbsDiff, poleModifiedERealAbsDiff,
        ← EReal.coe_sub, EReal.abs_def, Real.enorm_eq_ofReal_abs, lowerTrunc]
        using lowerTrunc_enorm_sub_le (u j x) (v x) L
    obtain ⟨ns, _hns, hae⟩ :=
      exists_strictMono_tendsto_ae_toReal_of_lintegral_canonicalERealAbsDiff
        (fun j => hm (u j) (hu j)) (hm v hv) hL1
    have horder : ∀ᵐ x ∂μ.restrict (ball p r),
        (lowerTrunc L v x : EReal) ≤ (lowerTrunc L w x : EReal) := by
      filter_upwards [hae, ae_restrict_mem measurableSet_ball] with x hx hxB
      apply EReal.coe_le_coe
      apply le_of_tendsto_of_tendsto (by simpa using hx) tendsto_const_nhds
      apply Eventually.of_forall
      intro j
      apply EReal.toReal_le_toReal
        (max_le_max (huw (ns j) x (hBU (ball_subset_closedBall hxB))) le_rfl)
        (ne_of_gt ((EReal.bot_lt_coe L).trans_le (le_max_right _ _)))
        (ne_of_lt (max_lt (lt_top_iff_ne_top.mpr
          (hw.ne_top x (hBU (ball_subset_closedBall hxB)))) (EReal.coe_lt_top L)))
    have hpoint := ((discPshOn_lowerTrunc hv L).plurisubharmonicOn hU).mono
      (ball_subset_closedBall.trans hBU) |>.le_of_ae_le isOpen_ball
        (((discPshOn_lowerTrunc hw L).plurisubharmonicOn hU).mono
          (ball_subset_closedBall.trans hBU)).upperSemicontinuousOn μ horder
    exact EReal.coe_le_coe_iff.mp (hpoint p (mem_ball_self hr))
  by_contra hnot
  obtain ⟨L, hwL, hLv⟩ := EReal.exists_between_coe_real (lt_of_not_ge hnot)
  have hwclip : lowerTrunc L w p = L := by
    simp [lowerTrunc, max_eq_right hwL.le]
  have hvclip : v p ≤ (lowerTrunc L v p : EReal) :=
    (le_max_left _ _).trans (EReal.le_coe_toReal
      (ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (hv.ne_top p hp))
        (EReal.coe_lt_top L))))
  have hle := hclip L
  rw [hwclip] at hle
  exact (not_lt_of_ge (hvclip.trans (EReal.coe_le_coe hle))) hLv

/-- The true infimum of all original upper-regularized tails is exactly
the source local L1 limit. Both inequalities are internally produced. -/
theorem iInf_uscSup_tail_eq_of_localL1
    {u : ℕ → E → EReal} {v : E → EReal} {U : Set E}
    (hu : ∀ j, DiscPshOn (u j) U) (hv : DiscPshOn v U) (hU : IsOpen U)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hlim : ∀ K : Set E, IsCompact K → K ⊆ U →
      Tendsto (fun j => ∫⁻ x in K, canonicalERealAbsDiff (u j x) (v x) ∂μ)
        atTop (𝓝 0)) :
    EqOn (fun p => ⨅ N : ℕ, uscSup (fun j => u (j + N)) p) v U := by
  have hb : SGPT.PSH.LocallyUniformlyBoundedAbove u U := by
    intro p hp
    obtain ⟨r, hr, _hBU, C, hC⟩ :=
      exists_local_uniform_upper_bound_of_localL1 hu hv hU μ hlim hp
    exact ⟨ball p r, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)),
      C, fun j x hx => hC j x hx.1⟩
  have htail (N : ℕ) : DiscPshOn (uscSup (fun j => u (j + N))) U := by
    have hpsh : ∀ f ∈ range (fun j => u (j + N)), PlurisubharmonicOn f U := by
      rintro f ⟨j, rfl⟩
      exact (hu (j + N)).plurisubharmonicOn hU
    have hbound : SGPT.PSH.LocallyUniformlyBoundedAbove (fun j => u (j + N)) U := by
      intro p hp
      obtain ⟨V, hV, C, hC⟩ := hb p hp
      exact ⟨V, hV, C, fun j => hC (j + N)⟩
    have hg := plurisubharmonicOn_uscRegularization_sSup hU
      (range_nonempty (fun j => u (j + N))) hpsh
      (locallyUniformlyBoundedAbove_range_iff.mpr hbound)
    rw [sSup_range_eq] at hg
    exact hg.discPshOn
  intro p hp
  apply le_antisymm (iInf_uscSup_tail_le_of_localL1 hu hv hU μ hlim p hp)
  apply le_iInf
  intro N
  exact le_of_localL1_of_le (fun j => hu (j + N)) hv (htail N) hU μ
    (fun K hK hKU => (hlim K hK hKU).comp (tendsto_add_atTop_nat N))
    (fun j x _ => le_uscSup (fun k => u (k + N)) j x) p hp

end SGPT.PSH.LocalL1Recovery
