import SGPT.NPP.BoundedPshAverages

/-!
# Actual joint radial PSH on genuinely bounded patches

Complete blueprint: `blueprint/src/dnt-big-bounded-joint-radial.tex`, written
first. The actual integral is unchanged. The proof constructs the actual
measurable zero extension and finite compact kernel parameter measure,
derives each PSH integrand and the numerical bound, and applies actual Fubini
averaging with the previously proved joint continuity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace SGPT.NPP.DNTBig

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.PshRadialRegularization

variable {n : ℕ}

/-- Openness follows from the actual positive radius buffer. -/
theorem isOpen_radialJointDomain (W : Set (ComplexModel n)) :
    IsOpen (radialJointDomain W) := by
  rw [isOpen_iff_mem_nhds]
  rintro p ⟨d, hrd, hdW⟩
  have hV : {q : ComplexModel n × ℂ | dist q.1 p.1 + Real.exp q.2.re < d} ∈ 𝓝 p :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hrd)
  filter_upwards [hV] with q hq
  refine ⟨d - dist q.1 p.1, by linarith, ?_⟩
  intro x hx
  apply hdW
  rw [mem_ball] at hx ⊢
  exact (dist_triangle x q.1 p.1).trans_lt (by linarith)

private theorem measurable_indicator_toReal {W : Set (ComplexModel n)}
    (hW : IsOpen W) {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u W) :
    Measurable (W.indicator (fun x => (u x).toReal)) := by
  classical
  have hsc : UpperSemicontinuous (fun x : W => u x) :=
    upperSemicontinuousOn_iff_restrict.mpr hu.upperSemicontinuousOn
  have hm : Measurable (fun x : W => (u x).toReal) := hsc.measurable.ereal_toReal
  refine measurable_of_restrict_of_restrict_compl hW.measurableSet ?_ ?_
  · convert hm using 1
    funext x
    simp [Set.domRestrict, x.property]
  · have heq : Wᶜ.domRestrict (W.indicator (fun x => (u x).toReal)) =
        fun _ : (Wᶜ : Set (ComplexModel n)) => (0 : ℝ) := by
      funext x
      exact Set.indicator_of_notMem x.property _
    rw [heq]
    exact measurable_const

/-- Joint PSH of the literal actual radial integral, proved from genuine
finite patch bounds by compact parameter localization and disc/Fubini. -/
theorem plurisubharmonicOn_boundedJointRadialRegularization
    {ρ : ComplexModel n → ℝ} (hρ : IsRadialKernel ρ)
    {W : Set (ComplexModel n)} (hW : IsOpen W)
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u W)
    {C : ℝ} (hC : 0 ≤ C)
    (hub : ∀ z ∈ W, ((-C : ℝ) : EReal) ≤ u z ∧ u z ≤ (C : EReal)) :
    PlurisubharmonicOn
      (fun p : ComplexModel n × ℂ =>
        ((radialRegularization ρ u (Real.exp p.2.re) p.1 : ℝ) : EReal))
      (radialJointDomain W) := by
  classical
  let f : ComplexModel n → ℝ := W.indicator (fun z => (u z).toReal)
  have hfmeas : Measurable f := measurable_indicator_toReal hW hu
  have hfinite (z) (hz : z ∈ W) : u z ≠ ⊤ ∧ u z ≠ ⊥ :=
    ⟨ne_top_of_le_ne_top (EReal.coe_ne_top C) (hub z hz).2,
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot (-C)) (hub z hz).1⟩
  have hf_eq (z) (hz : z ∈ W) : f z = (u z).toReal := Set.indicator_of_mem hz _
  have hcoe (z) (hz : z ∈ W) : (f z : EReal) = u z := by
    rw [hf_eq z hz]
    exact EReal.coe_toReal (hfinite z hz).1 (hfinite z hz).2
  have hfb : ∀ z, ‖f z‖ ≤ C := by
    intro z
    by_cases hz : z ∈ W
    · rw [Real.norm_eq_abs, abs_le]
      have hh := hub z hz
      rw [← hcoe z hz, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff] at hh
      exact hh
    · simp only [f, Set.indicator_of_notMem hz, norm_zero]
      exact hC
  have hfp : PlurisubharmonicOn (fun z => (f z : EReal)) W := by
    intro z hz
    apply (hu z hz).congr
    filter_upwards [hW.mem_nhds hz] with y hy
    exact (hcoe y hy).symm
  have huL : LocallyIntegrableOn (fun z => (u z).toReal) W volume := by
    have hfL := locallyIntegrableOn_of_plurisubharmonicOn_real (Ω := ⟨W, hW⟩) hfp
    refine LocallyIntegrableOn.congr ?_ hfL
    filter_upwards [ae_restrict_mem hW.measurableSet] with z hz
    exact hf_eq z hz
  let K : Set (ComplexModel n) := closedBall 0 1
  let μ : Measure (ComplexModel n) := volume.restrict K
  let _ : IsFiniteMeasure μ := ⟨by
    change (volume.restrict K) univ < ⊤
    simpa only [Measure.restrict_apply_univ] using
      (isCompact_closedBall (0 : ComplexModel n) 1).measure_lt_top (μ := volume)⟩
  let F : (ComplexModel n × ℂ) × ComplexModel n → ℝ := fun q =>
    if q.2 ∈ K then f (q.1.1 + Complex.exp q.1.2 • q.2) * ρ q.2 else 0
  have hF : Measurable F := by
    exact Measurable.ite (measurableSet_closedBall.preimage measurable_snd)
      ((hfmeas.comp (by fun_prop : Measurable (fun q : (ComplexModel n × ℂ) ×
        ComplexModel n => q.1.1 + Complex.exp q.1.2 • q.2))).mul
        (hρ.continuous.measurable.comp measurable_snd)) measurable_const
  have hpsh : ∀ a, PlurisubharmonicOn (fun p => (F (p, a) : EReal))
      (radialJointDomain W) := by
    intro a
    by_cases ha : a ∈ K
    · have hp := plurisubharmonicOn_complexRadiusPullback hW hfp a
        (mem_closedBall_zero_iff.mp ha)
      by_cases hzero : ρ a = 0
      · simpa only [F, if_pos ha, hzero, mul_zero, EReal.coe_zero] using
          (discPshOn_const (0 : EReal) (by simp) (radialJointDomain W)).plurisubharmonicOn
            (isOpen_radialJointDomain W)
      · have hpos : 0 < ρ a := lt_of_le_of_ne (hρ.nonneg a) (Ne.symm hzero)
        simpa only [F, if_pos ha, EReal.coe_mul, mul_comm] using hp.const_mul hpos
    · simpa only [F, if_neg ha, EReal.coe_zero] using
        (discPshOn_const (0 : EReal) (by simp) (radialJointDomain W)).plurisubharmonicOn
          (isOpen_radialJointDomain W)
  obtain ⟨B₀, hB₀⟩ := hρ.continuous.bounded_above_of_compact_support hρ.hasCompactSupport
  let B : ℝ := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hρB (a) : ‖ρ a‖ ≤ B := (hB₀ a).trans (le_max_left _ _)
  have hFb : ∀ p ∈ radialJointDomain W, ∀ a, ‖F (p, a)‖ ≤ C * B := by
    intro p _ a
    by_cases ha : a ∈ K
    · simp only [F, if_pos ha, norm_mul]
      exact mul_le_mul (hfb _) (hρB a) (norm_nonneg _) hC
    · simp only [F, if_neg ha, norm_zero]
      exact mul_nonneg hC hB
  have harg {p : ComplexModel n × ℂ} (hp : p ∈ radialJointDomain W)
      {a : ComplexModel n} (ha : a ∈ K) : p.1 + Complex.exp p.2 • a ∈ W := by
    obtain ⟨d, hrd, hdW⟩ := hp
    apply hdW
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_exp]
    exact (mul_le_of_le_one_right (Real.exp_pos _).le
      (mem_closedBall_zero_iff.mp ha)).trans_lt hrd
  have havg {p : ComplexModel n × ℂ} (hp : p ∈ radialJointDomain W) :
      (∫ a, F (p, a) ∂μ) = radialRegularization ρ u (Real.exp p.2.re) p.1 := by
    rw [radialRegularization_exp_re_eq_complexIntegral hρ]
    change (∫ a in K, F (p, a)) = _
    rw [← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    filter_upwards [] with a
    change K.indicator (fun a => F (p, a)) a =
      (u (p.1 + Complex.exp p.2 • a)).toReal * ρ a
    by_cases ha : a ∈ K
    · simp only [Set.indicator_of_mem ha, F, if_pos ha, hf_eq _ (harg hp ha)]
    · have hρ0 : ρ a = 0 := hρ.eq_zero_of_one_lt_norm
        (lt_of_not_ge (by simpa only [K, mem_closedBall_zero_iff] using ha))
      simp only [Set.indicator_of_notMem ha, hρ0, mul_zero]
  have hcont : ContinuousOn (fun p => ∫ a, F (p, a) ∂μ) (radialJointDomain W) := by
    intro p hp
    have hloc := continuousAt_radialRegularization_joint hρ huL
      (p := (p.1, Real.exp p.2.re)) (Real.exp_pos p.2.re) hp
    have hmap : ContinuousAt (fun q : ComplexModel n × ℂ => (q.1, Real.exp q.2.re)) p :=
      by fun_prop
    have hh := ContinuousAt.comp' (f := fun q : ComplexModel n × ℂ =>
      (q.1, Real.exp q.2.re)) hloc hmap
    exact hh.continuousWithinAt.congr (fun q hq => havg hq) (havg hp)
  have h := plurisubharmonicOn_boundedParameterAverage μ (isOpen_radialJointDomain W)
    hF hpsh (mul_nonneg hC hB) hFb hcont
  intro p hp
  apply (h p hp).congr
  filter_upwards [(isOpen_radialJointDomain W).mem_nhds hp] with q hq
  exact congrArg (fun t : ℝ => (t : EReal)) (havg hq)

end SGPT.NPP.DNTBig
