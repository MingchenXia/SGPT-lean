import SGPT.Trace.OTExt2LocalCalc
import SGPT.Trace.OTMarginPole

/-!
# One step of the local critical-gain extension (smooth weight, fixed `ε`)

Blueprint `claude-ot-ext2.tex`, node `claude-ot-ext2:local-step`.  Xia, *Foundations of
pluripotential theory*, proof of `lem:local-critical-gain-extension`, paragraphs *The twisted
form* and *The correction*.

In `ℂ^{m+d} = ℂ^m × ℂ^d` with `R = |w|²`, `D = {|z'| < r', |w| < r''}` (`r''² < e^{-4}`) and
`U = D \ {w = 0}`, let `P` be smooth near `D̄` with `Levi(P)(v) ≥ π |v|²` and `f` holomorphic near
`B̄(0, r')`.  For `0 < ε < e^{-4}`:

* the weight `φ = P + d log R` and the twist `a = μ_ε(ψ_ε)`, `b = (2 - ψ_ε)²` (`ψ_ε = log(ε + R)`)
  have twisted curvature `H ≥ π|v|² + (ε/R)|∂ψ_ε(v)|² > 0` on `U`
  (`twistedCurvature_normal_pole_ge`);
* the cut-off extension `G = f(z') χ(R/ε)` has data density `4 M² |f|² 1_{ε/2 ≤ R ≤ ε}`;
* the twisted estimate on `U` (`euclideanTwistedCorrection`, with the complete metric of
  `hasCompleteCutoffs_kahlerPot`) gives `S` holomorphic on `U`; `S` is square integrable near
  `{w = 0}` and extends holomorphically to `F` on `D` (`euclideanRemovable`); `F - f(z')` is
  holomorphic near `{w = 0}` with `∫ |F - f|² |w|^{-2d} < ∞`, so `F(z', 0) = f(z')`
  (`eq_zero_of_lintegral_normalWeight`);
* `∫_D |F - G|² e^{-P} (ε + R)^{-d} ψ_ε^{-2} ≤ 5 ∫_D 4M² |f|² 1_{ε/2 ≤ R ≤ ε} e^{-P} R^{-d}`
  (`exists_local_step`), using `a + b ≤ 5 ψ_ε²` (`twist_sum_le_five_sq`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.OTExt2

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Trace.TwistedL2
open SGPT.Trace.OTMargin (normalWeight normalWeight_nonneg normalWeight_eq_zero_iff
  eq_zero_of_lintegral_normalWeight ae_normalWeight_pos)

variable {m d : ℕ}

/-! ### The coordinate plane is locally analytically null -/

theorem isLocallyAnalyticNull_normalWeight_eq_zero (hd : 1 ≤ d) :
    IsLocallyAnalyticNull (n := m + d)
      {z : ComplexModel (m + d) | normalWeight (m + d) m z = 0} := by
  set i₀ : Fin (m + d) := ⟨m, by omega⟩
  intro x
  refine ⟨chart0, univ, fun z => z i₀, trivial, isOpen_univ, trivial, fun _ _ => trivial,
    ?_, ?_, ?_⟩
  · exact ((EuclideanSpace.proj i₀ : ComplexModel (m + d) →L[ℂ] ℂ).differentiable).differentiableOn
  · intro W' _ hW' ⟨z₀, hz₀⟩
    by_cases h0 : z₀ i₀ = 0
    · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hW' z₀ hz₀
      set w : ComplexModel (m + d) := z₀ + EuclideanSpace.single i₀ ((δ / 2 : ℝ) : ℂ)
      refine ⟨w, hball ?_, ?_⟩
      · rw [mem_ball, dist_eq_norm]
        simp only [w, add_sub_cancel_left, PiLp.norm_single, Complex.norm_real,
          Real.norm_eq_abs]
        rw [abs_of_pos (by positivity)]
        linarith
      · simp only [w, PiLp.add_apply, PiLp.single_apply, h0, zero_add, if_true]
        exact_mod_cast (by positivity : (δ / 2 : ℝ) ≠ 0)
    · exact ⟨z₀, hz₀, h0⟩
  · intro z _ hz
    have := (normalWeight_eq_zero_iff z).mp hz
    exact this i₀ (by simp [i₀])

/-! ### Elementary identities -/

theorem exp_neg_weight {P R : ℝ} (hR : 0 < R) (k : ℕ) :
    Real.exp (-(P + (k : ℝ) * Real.log R)) = Real.exp (-P) * (R ^ k)⁻¹ := by
  rw [neg_add, Real.exp_add, Real.exp_neg ((k : ℝ) * Real.log R), Real.exp_nat_mul,
    Real.exp_log hR]

theorem coordinateProjection_mem_ball {m n : ℕ} (hmn : m ≤ n) {r' : ℝ} {z : ComplexModel n}
    (hz : tanWeight n m z < r' ^ 2) (hr' : 0 < r') : coordinateProjection n m z ∈ ball 0 r' := by
  rw [mem_ball_zero_iff]
  rw [tanWeight_eq_norm_proj hmn] at hz
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr'.le two_ne_zero).mp hz

theorem localDom_subset_ball {n m : ℕ} {r' r'' : ℝ} (hr' : 0 < r') (hr'' : 0 < r'') :
    localDom n m r' r'' ⊆ ball 0 (r' + r'') := by
  intro z hz
  rw [mem_ball_zero_iff]
  have h1 := tanWeight_add_normalWeight m z
  have h2 : ‖z‖ ^ 2 < (r' + r'') ^ 2 := by nlinarith [hz.1, hz.2]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

theorem isCompact_closure_localDom {n m : ℕ} {r' r'' : ℝ} (hr' : 0 < r') (hr'' : 0 < r'') :
    IsCompact (closure (localDom n m r' r'')) :=
  (isCompact_closedBall (0 : ComplexModel n) (r' + r'')).of_isClosed_subset isClosed_closure
    (closure_minimal ((localDom_subset_ball hr' hr'').trans ball_subset_closedBall)
      isClosed_closedBall)

theorem volume_localDom_lt_top {n m : ℕ} {r' r'' : ℝ} (hr' : 0 < r') (hr'' : 0 < r'') :
    volume (localDom n m r' r'') < ⊤ :=
  (measure_mono (localDom_subset_ball hr' hr'')).trans_lt measure_ball_lt_top

theorem ae_restrict_localPunct {r' r'' : ℝ} (hd : 1 ≤ d) :
    ∀ᵐ z ∂(volume.restrict (localDom (m + d) m r' r'')), z ∈ localPunct (m + d) m r' r'' := by
  filter_upwards [ae_restrict_mem (isOpen_localDom m r' r'').measurableSet,
    ae_restrict_of_ae (ae_normalWeight_pos (n := m + d) (m := m) (by omega))] with z hz h0
  exact ⟨hz.1, hz.2, h0⟩

theorem restrict_localPunct_eq {r' r'' : ℝ} (hd : 1 ≤ d) :
    (volume.restrict (localPunct (m + d) m r' r'') : Measure (ComplexModel (m + d))) =
      volume.restrict (localDom (m + d) m r' r'') := by
  refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
  · rw [sdiff_eq_empty.mpr (localPunct_subset m r' r''), measure_empty]
  · have h0 : volume {z : ComplexModel (m + d) | ¬ 0 < normalWeight (m + d) m z} = 0 :=
      ae_iff.mp (ae_normalWeight_pos (by omega))
    refine measure_mono_null (fun z hz => ?_) h0
    obtain ⟨hzD, hzU⟩ := hz
    exact fun hpos => hzU ⟨hzD.1, hzD.2, hpos⟩

/-! ### One step -/

/-- The weight `w_ε = e^{-P} (ε + R)^{-d} (log (ε + R))^{-2}`. -/
def stepWeight (d : ℕ) (P R ε : ℝ) : ℝ :=
  Real.exp (-P) * ((ε + R) ^ d)⁻¹ * (Real.log (ε + R) ^ 2)⁻¹

/-- The indicator of the shell `ε/2 ≤ R ≤ ε`. -/
def shellInd (ε R : ℝ) : ℝ := if ε / 2 ≤ R ∧ R ≤ ε then 1 else 0

theorem shellInd_nonneg (ε R : ℝ) : 0 ≤ shellInd ε R := by
  unfold shellInd; split_ifs <;> norm_num

theorem shellInd_le_one (ε R : ℝ) : shellInd ε R ≤ 1 := by
  unfold shellInd; split_ifs <;> norm_num

theorem inv_pow_le_of_shell {ε R : ℝ} (hε : 0 < ε) (h : shellInd ε R ≠ 0) (k : ℕ) :
    (R ^ k)⁻¹ ≤ (2 / ε) ^ k := by
  unfold shellInd at h
  split_ifs at h with hs
  · have h1 : 0 < ε / 2 := by positivity
    rw [← inv_pow]
    refine pow_le_pow_left₀ (inv_pos.mpr (by linarith [hs.1])).le ?_ k
    calc R⁻¹ ≤ (ε / 2)⁻¹ := inv_anti₀ h1 hs.1
      _ = 2 / ε := by rw [inv_div]
  · exact absurd rfl h

theorem shell_mul_inv_pow_le {ε R x : ℝ} (hε : 0 < ε) (hx : 0 ≤ x) (k : ℕ) :
    x * shellInd ε R * (R ^ k)⁻¹ ≤ x * (2 / ε) ^ k := by
  by_cases h : shellInd ε R = 0
  · rw [h, mul_zero, zero_mul]; exact mul_nonneg hx (by positivity)
  · have h1 : shellInd ε R = 1 := by
      unfold shellInd at h ⊢; split_ifs at h ⊢ <;> simp_all
    rw [h1, mul_one]
    exact mul_le_mul_of_nonneg_left (inv_pow_le_of_shell hε h k) hx

/-- **One step of the local critical-gain extension** (FPT, proof of
`lem:local-critical-gain-extension`, smooth weight, fixed `ε`). -/
theorem exists_local_step (hd : 1 ≤ d) {r' r'' : ℝ} (hr' : 0 < r') (hr'' : 0 < r'')
    (hr''e : r'' ^ 2 < Real.exp (-4))
    {O : Set (ComplexModel (m + d))} (hO : IsOpen O)
    (hDO : closure (localDom (m + d) m r' r'') ⊆ O)
    {P : ComplexModel (m + d) → ℝ} (hP : ContDiffOn ℝ ∞ P O)
    (hPL : ∀ z ∈ O, ∀ v : ComplexModel (m + d), Real.pi * ‖v‖ ^ 2 ≤ leviForm P z v)
    {O' : Set (ComplexModel m)} (hO' : IsOpen O') (hBO' : closedBall 0 r' ⊆ O')
    {f : ComplexModel m → ℂ} (hf : DifferentiableOn ℂ f O')
    {M : ℝ} (hM : ∀ x, |deriv chenCutoff x| ≤ M)
    {ε : ℝ} (hε : 0 < ε) (hεe : ε < Real.exp (-4)) :
    ∃ F : ComplexModel (m + d) → ℂ, DifferentiableOn ℂ F (localDom (m + d) m r' r'') ∧
      (∀ z' ∈ ball (0 : ComplexModel m) r', F (coordinateInclusion (m + d) m z') = f z') ∧
      ∫⁻ z in localDom (m + d) m r' r'', ENNReal.ofReal
          (‖F z - f (coordinateProjection (m + d) m z) *
            (chenCutoff (normalWeight (m + d) m z / ε) : ℂ)‖ ^ 2 *
            stepWeight d (P z) (normalWeight (m + d) m z) ε) ≤
        5 * ∫⁻ z in localDom (m + d) m r' r'', ENNReal.ofReal
          (4 * M ^ 2 * ‖f (coordinateProjection (m + d) m z)‖ ^ 2 *
            shellInd ε (normalWeight (m + d) m z) *
            (Real.exp (-P z) * (normalWeight (m + d) m z ^ d)⁻¹)) := by
  classical
  set D := localDom (m + d) m r' r'' with hDdef
  set U := localPunct (m + d) m r' r'' with hUdef
  set R := normalWeight (m + d) m with hRdef
  set proj := coordinateProjection (m + d) m with hproj
  set fP : ComplexModel (m + d) → ℂ := fun z => f (proj z) with hfP
  set G : ComplexModel (m + d) → ℂ := fun z => fP z * (chenCutoff (R z / ε) : ℂ) with hG
  have hmn : m ≤ m + d := by omega
  have hUo : IsOpen U := isOpen_localPunct m r' r''
  have hDo : IsOpen D := isOpen_localDom m r' r''
  have hUD : U ⊆ D := localPunct_subset m r' r''
  have hDO' : D ⊆ O := subset_closure.trans hDO
  have hUO : U ⊆ O := hUD.trans hDO'
  have hRpos : ∀ z ∈ U, 0 < R z := fun z hz => hz.2.2
  have hR4 : ∀ z ∈ D, R z < Real.exp (-4) := fun z hz => lt_trans hz.2 hr''e
  have hR1 : ∀ z ∈ D, R z < 1 := fun z hz =>
    (hR4 z hz).trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hRc : Continuous R := continuous_normalWeight m
  have hRs : ContDiff ℝ ∞ R := contDiff_normalWeight m
  have hR2 : ∀ z, ContDiffAt ℝ 2 R z := fun z => (hRs.contDiffAt).of_le two_le_infty
  have hRd : ∀ z, DifferentiableAt ℝ R z := fun z => hRs.differentiable (by simp) z
  have hprojD : ∀ z ∈ D, proj z ∈ ball 0 r' := fun z hz =>
    coordinateProjection_mem_ball hmn hz.1 hr'
  have hprojO' : ∀ z ∈ D, proj z ∈ O' := fun z hz => hBO' (ball_subset_closedBall (hprojD z hz))
  have hfPd : ∀ z ∈ D, DifferentiableAt ℂ fP z := fun z hz =>
    (hf.differentiableAt (hO'.mem_nhds (hprojO' z hz))).comp z
      (coordinateProjection (m + d) m).differentiableAt
  have hfPc : ContinuousOn fP D := fun z hz => (hfPd z hz).continuousAt.continuousWithinAt
  have hfPs : ∀ z ∈ D, ContDiffAt ℝ ∞ fP z := by
    intro z hz
    have hopen : IsOpen (D ∩ proj ⁻¹' O') := hDo.inter (hO'.preimage (coordinateProjection
      (m + d) m).continuous)
    have hdo : DifferentiableOn ℂ fP (D ∩ proj ⁻¹' O') := fun y hy =>
      (hfPd y hy.1).differentiableWithinAt
    exact contDiffAt_real_of_differentiableOn_complex hdo hopen ⟨hz, hprojO' z hz⟩
  -- bounds on `D`
  obtain ⟨Cf, hCf⟩ := (isCompact_closedBall (0 : ComplexModel m) r').exists_bound_of_continuousOn
    (hf.continuousOn.mono hBO')
  set Bf : ℝ := Cf ^ 2
  have hBf : ∀ z ∈ D, ‖fP z‖ ^ 2 ≤ Bf := fun z hz =>
    pow_le_pow_left₀ (norm_nonneg _) (hCf _ (ball_subset_closedBall (hprojD z hz))) 2
  obtain ⟨BP, hBP'⟩ := (isCompact_closure_localDom (n := m + d) (m := m) hr' hr'').exists_bound_of_continuousOn
    (hP.continuousOn.mono hDO)
  have hBP : ∀ z ∈ D, |P z| ≤ BP := fun z hz => by
    have := hBP' z (subset_closure hz); rwa [Real.norm_eq_abs] at this
  have hBf0 : 0 ≤ Bf := by positivity
  have hvolD : volume D < ⊤ := volume_localDom_lt_top hr' hr''
  have hvolU : volume U < ⊤ := (measure_mono hUD).trans_lt hvolD
  -- the twist
  set φ : ComplexModel (m + d) → ℝ := fun z => P z + (d : ℝ) * Real.log (R z) with hφdef
  set a : ComplexModel (m + d) → ℝ := fun z => twistMu ε (Real.log (ε + R z)) with hadef
  set b : ComplexModel (m + d) → ℝ := fun z => twistB (Real.log (ε + R z)) with hbdef
  have hP2 : ∀ z ∈ U, ContDiffAt ℝ 2 P z := fun z hz =>
    (hP.contDiffAt (hO.mem_nhds (hUO hz))).of_le two_le_infty
  have hcurvge : ∀ z ∈ U, ∀ v : ComplexModel (m + d),
      Real.pi * ‖v‖ ^ 2 + ε / R z * holDerivSq (fun y => Real.log (ε + R y)) z v ≤
        twistedCurvature a b φ z v := by
    intro z hz v
    have h := twistedCurvature_normal_pole_ge (hP2 z hz) (hR2 z) (hRpos z hz) (hR4 z (hUD hz))
      hε hεe (q := (d : ℝ)) (by positivity) (A := Real.pi) (B := 0) (Q := ‖v‖ ^ 2) v
      (by positivity) le_rfl (by simp [Real.pi_pos.le]) (hPL z (hUO hz) v)
      (by simpa using leviForm_log_normalWeight_nonneg m (hRpos z hz) v)
    simpa using h
  have hHol : ∀ z ∈ U, ∀ v : ComplexModel (m + d),
      holDerivSq (fun y => Real.log (ε + R y)) z v ≤ R z / ε * twistedCurvature a b φ z v := by
    intro z hz v
    exact holDerivSq_le_of_twistedCurvature (hP2 z hz) (hR2 z) (hRpos z hz) (hR4 z (hUD hz))
      hε hεe (q := (d : ℝ)) (by positivity) (A := Real.pi) (B := 0) (Q := ‖v‖ ^ 2) v
      (by positivity) le_rfl (by simp [Real.pi_pos.le]) (hPL z (hUO hz) v)
      (by simpa using leviForm_log_normalWeight_nonneg m (hRpos z hz) v)
  have hcurv : ∀ z ∈ U, ∀ v : ComplexModel (m + d), v ≠ 0 → 0 < twistedCurvature a b φ z v := by
    intro z hz v hv
    have h1 := hcurvge z hz v
    have h2 : 0 < Real.pi * ‖v‖ ^ 2 := by
      have : 0 < ‖v‖ := norm_pos_iff.mpr hv
      positivity
    have h3 : 0 ≤ ε / R z * holDerivSq (fun y => Real.log (ε + R y)) z v :=
      mul_nonneg (div_pos hε (hRpos z hz)).le (holDerivSq_nonneg _ _ _)
    linarith
  -- the scalar bounds of the twist on `U`
  have htw : ∀ z ∈ U, Real.log ε < Real.log (ε + R z) ∧ Real.log (ε + R z) < -3 ∧
      a z + b z ≤ 5 * Real.log (ε + R z) ^ 2 ∧ 3 ≤ a z ∧ 25 ≤ b z := by
    intro z hz
    obtain ⟨-, h2, h3, -⟩ := twist_sum_le_five_sq hε hεe (hRpos z hz) (hR4 z (hUD hz))
    have h1 : Real.log ε < Real.log (ε + R z) := Real.log_lt_log hε (by linarith [hRpos z hz])
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · have := neg_le_twistMu hε.le (t := Real.log (ε + R z)) (by linarith)
      simp only [hadef]; linarith
    · simp only [hbdef, twistB]; nlinarith
  have hlogε : Real.log ε < -3 := by
    have := Real.log_lt_log hε hεe
    rw [Real.log_exp] at this; linarith
  have hab : ∃ mm MM : ℝ, 0 < mm ∧ ∀ x ∈ U, mm ≤ a x ∧ a x ≤ MM ∧ mm ≤ b x ∧ b x ≤ MM := by
    refine ⟨3, 5 * Real.log ε ^ 2, by norm_num, fun x hx => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := htw x hx
    have hsq : Real.log (ε + R x) ^ 2 ≤ Real.log ε ^ 2 := by nlinarith
    refine ⟨h4, by linarith, by linarith, by linarith⟩
  -- smoothness
  have hφs : ContDiffOn ℝ ∞ φ U := by
    intro z hz
    refine ContDiffAt.contDiffWithinAt ?_
    exact (hP.contDiffAt (hO.mem_nhds (hUO hz))).add
      (contDiffAt_const.mul (hRs.contDiffAt.log (hRpos z hz).ne'))
  have hεR : ∀ z ∈ U, 0 < ε + R z := fun z hz => by linarith [hRpos z hz]
  have hψs : ∀ z ∈ U, ContDiffAt ℝ ∞ (fun y => Real.log (ε + R y)) z := fun z hz =>
    (contDiffAt_const.add hRs.contDiffAt).log (hεR z hz).ne'
  have has : ContDiffOn ℝ ∞ a U := fun z hz =>
    ((contDiffAt_twistMu ε (by linarith [(htw z hz).2.1])).comp z (hψs z hz)).contDiffWithinAt
  have hbs : ContDiffOn ℝ ∞ b U := fun z hz => by
    refine ContDiffAt.contDiffWithinAt ?_
    simp only [hbdef, twistB]
    exact (contDiffAt_const.sub (hψs z hz)).pow 2
  have hGs : ContDiffOn ℝ ∞ G U := fun z hz => by
    refine ContDiffAt.contDiffWithinAt ?_
    refine (hfPs z (hUD hz)).mul ?_
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((contDiff_chenCutoff (k := ⊤)).contDiffAt.comp z (hRs.contDiffAt.div_const ε))
  -- the data densities
  set Dε : ComplexModel (m + d) → ℝ := fun z => 4 * M ^ 2 * ‖fP z‖ ^ 2 * shellInd ε (R z)
    with hDεdef
  set Dσ : ComplexModel (m + d) → ℝ := fun z => M ^ 2 / ε * ‖fP z‖ ^ 2 * shellInd ε (R z)
    with hDσdef
  have hDbound : ∀ z ∈ U, ∀ v : ComplexModel (m + d),
      ‖dbarPairing G z v‖ ^ 2 ≤ Dε z * twistedCurvature a b φ z v := fun z hz v =>
    norm_dbarPairing_cutoff_le (hfPd z (hUD hz)) (hRd z) (hRpos z hz) hε hM v (hHol z hz v)
  have hDσbound : ∀ z ∈ U, ∀ v : ComplexModel (m + d),
      ‖dbarPairing G z v‖ ^ 2 ≤
        Dσ z * (‖v‖ ^ 2 + leviForm (kahlerPot (m + d) m r' r'') z v / Real.pi) := by
    intro z hz v
    have h1 := norm_dbarPairing_cutoff_le_sigma (m := m) (hfPd z (hUD hz)) hε hM v
    have hL := leviForm_kahlerPot_nonneg hr''e hz v
    have hD0 : 0 ≤ Dσ z := by
      simp only [hDσdef]
      exact mul_nonneg (by positivity) (shellInd_nonneg _ _)
    calc ‖dbarPairing G z v‖ ^ 2 ≤ Dσ z * ‖v‖ ^ 2 := h1
      _ ≤ Dσ z * (‖v‖ ^ 2 + leviForm (kahlerPot (m + d) m r' r'') z v / Real.pi) := by
        gcongr
        have := div_nonneg hL Real.pi_pos.le
        linarith
  -- integrability of the data
  have hexpφ : ∀ z ∈ U, Real.exp (-φ z) = Real.exp (-P z) * (R z ^ d)⁻¹ := fun z hz =>
    exp_neg_weight (hRpos z hz) d
  have hdens_le : ∀ (c : ℝ), 0 ≤ c → ∀ z ∈ U,
      c * ‖fP z‖ ^ 2 * shellInd ε (R z) * Real.exp (-φ z) ≤
        c * Bf * (Real.exp BP * (2 / ε) ^ d) := by
    intro c hc z hz
    rw [hexpφ z hz]
    have hz' := hUD hz
    have h1 : Real.exp (-P z) ≤ Real.exp BP := Real.exp_le_exp.mpr (by
      have := hBP z hz'; rw [abs_le] at this; linarith)
    have h2 : c * ‖fP z‖ ^ 2 * shellInd ε (R z) * (R z ^ d)⁻¹ ≤ c * ‖fP z‖ ^ 2 * (2 / ε) ^ d :=
      shell_mul_inv_pow_le hε (by positivity) d
    have h3 : c * ‖fP z‖ ^ 2 ≤ c * Bf := mul_le_mul_of_nonneg_left (hBf z hz') hc
    calc c * ‖fP z‖ ^ 2 * shellInd ε (R z) * (Real.exp (-P z) * (R z ^ d)⁻¹)
        = (c * ‖fP z‖ ^ 2 * shellInd ε (R z) * (R z ^ d)⁻¹) * Real.exp (-P z) := by ring
      _ ≤ (c * ‖fP z‖ ^ 2 * (2 / ε) ^ d) * Real.exp BP := by
        apply mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)
      _ ≤ (c * Bf * (2 / ε) ^ d) * Real.exp BP := by gcongr
      _ = c * Bf * (Real.exp BP * (2 / ε) ^ d) := by ring
  have hint_of : ∀ c : ℝ, 0 ≤ c →
      ∫⁻ z in U, ENNReal.ofReal (c * ‖fP z‖ ^ 2 * shellInd ε (R z) * Real.exp (-φ z)) < ⊤ := by
    intro c hc
    calc ∫⁻ z in U, ENNReal.ofReal (c * ‖fP z‖ ^ 2 * shellInd ε (R z) * Real.exp (-φ z))
        ≤ ∫⁻ _ in U, ENNReal.ofReal (c * Bf * (Real.exp BP * (2 / ε) ^ d)) :=
          setLIntegral_mono' hUo.measurableSet fun z hz =>
            ENNReal.ofReal_le_ofReal (hdens_le c hc z hz)
      _ = ENNReal.ofReal (c * Bf * (Real.exp BP * (2 / ε) ^ d)) * volume U :=
          setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvolU
  have hintσ : ∫⁻ z in U, ENNReal.ofReal (Dσ z * Real.exp (-φ z)) < ⊤ :=
    hint_of (M ^ 2 / ε) (by positivity)
  have hintD : ∫⁻ z in U, ENNReal.ofReal (Dε z * Real.exp (-φ z)) < ⊤ :=
    hint_of (4 * M ^ 2) (by positivity)
  -- the twisted correction on `U`
  obtain ⟨S, hS, hle⟩ := euclideanTwistedCorrection hUo (contDiffOn_kahlerPot hr''e)
    (fun z hz v hv => by
      have h1 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.mpr hv; positivity
      have h2 := div_nonneg (leviForm_kahlerPot_nonneg hr''e hz v) Real.pi_pos.le
      linarith)
    (hasCompleteCutoffs_kahlerPot hr' hr'' hr''e) hφs has hbs hab hcurv hGs hDbound hDσbound hintσ
  -- a lower bound of the weight on `U`
  have hwlow : ∀ z ∈ U, 1 ≤ Real.exp BP * (5 * Real.log ε ^ 2) *
      (Real.exp (-φ z) / (a z + b z)) * R z ^ d := by
    intro z hz
    obtain ⟨h1, h2, h3, h4, h5⟩ := htw z hz
    have hab0 : 0 < a z + b z := by linarith
    have hsq : Real.log (ε + R z) ^ 2 ≤ Real.log ε ^ 2 := by nlinarith
    have hRd0 : 0 < R z ^ d := pow_pos (hRpos z hz) d
    rw [hexpφ z hz]
    have he : 1 ≤ Real.exp BP * Real.exp (-P z) := by
      rw [← Real.exp_add]; apply Real.one_le_exp
      have := hBP z (hUD hz); rw [abs_le] at this; linarith
    have hfrac : 1 ≤ 5 * Real.log ε ^ 2 / (a z + b z) := by
      rw [le_div_iff₀ hab0]; linarith
    calc (1 : ℝ) ≤ (Real.exp BP * Real.exp (-P z)) * (5 * Real.log ε ^ 2 / (a z + b z)) :=
          one_le_mul_of_one_le_of_one_le he hfrac
      _ = Real.exp BP * (5 * Real.log ε ^ 2) * (Real.exp (-P z) * (R z ^ d)⁻¹ / (a z + b z)) *
            R z ^ d := by
          field_simp
  set Cε : ℝ := Real.exp BP * (5 * Real.log ε ^ 2) with hCε
  have hCε0 : 0 ≤ Cε := by positivity
  have hab0 : ∀ z ∈ U, 0 < a z + b z := fun z hz => by
    have := htw z hz; linarith
  have hwlow2 : ∀ z ∈ U, 1 ≤ Cε * (Real.exp (-φ z) / (a z + b z)) := by
    intro z hz
    have h := hwlow z hz
    have hRd1 : R z ^ d ≤ 1 := pow_le_one₀ (hRpos z hz).le (hR1 z (hUD hz)).le
    have h0 : 0 ≤ Cε * (Real.exp (-φ z) / (a z + b z)) :=
      mul_nonneg hCε0 (div_nonneg (Real.exp_pos _).le (hab0 z hz).le)
    calc (1 : ℝ) ≤ Cε * (Real.exp (-φ z) / (a z + b z)) * R z ^ d := h
      _ ≤ Cε * (Real.exp (-φ z) / (a z + b z)) * 1 := mul_le_mul_of_nonneg_left hRd1 h0
      _ = _ := mul_one _
  set X : ComplexModel (m + d) → ℝ := fun z => ‖G z - S z‖ ^ 2 * Real.exp (-φ z) / (a z + b z)
    with hXdef
  have hX0 : ∀ z ∈ U, 0 ≤ X z := fun z hz =>
    div_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) (hab0 z hz).le
  have hcorr_fin : ∫⁻ z in U, ENNReal.ofReal (X z) < ⊤ := lt_of_le_of_lt hle hintD
  -- removable singularity across `{w = 0}`
  set A : Set (ComplexModel (m + d)) := {z | R z = 0} with hAdef
  have hAc : IsClosed A := isClosed_eq hRc continuous_const
  have hDA : D \ A = U := by
    rw [hUdef, localPunct_eq]
  have hL2 : ∀ K : Set (ComplexModel (m + d)), IsCompact K → K ⊆ D →
      ∫⁻ x in K \ A, ENNReal.ofReal (‖S x‖ ^ 2) < ⊤ := by
    intro K hK hKD
    have hKA : K \ A ⊆ U := fun x hx => hDA ▸ ⟨hKD hx.1, hx.2⟩
    have hKAm : MeasurableSet (K \ A) := hK.isClosed.measurableSet.diff hAc.measurableSet
    have hGm : AEMeasurable (fun x => ENNReal.ofReal (2 * ‖G x‖ ^ 2))
        (volume.restrict (K \ A)) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((continuousOn_const.mul ((hGs.continuousOn.mono hKA).norm.pow 2)).aemeasurable hKAm)
    have hpt : ∀ x ∈ K \ A, ENNReal.ofReal (‖S x‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖G x‖ ^ 2) +
        ENNReal.ofReal (2 * Cε) * ENNReal.ofReal (X x) := by
      intro x hx
      have hxU := hKA hx
      have h1 : ‖S x‖ ≤ ‖G x‖ + ‖G x - S x‖ := by
        have := norm_sub_le (G x) (G x - S x)
        rwa [sub_sub_cancel] at this
      have h2 : ‖S x‖ ^ 2 ≤ 2 * ‖G x‖ ^ 2 + 2 * ‖G x - S x‖ ^ 2 := by
        nlinarith [norm_nonneg (S x), norm_nonneg (G x), norm_nonneg (G x - S x),
          sq_nonneg (‖G x‖ - ‖G x - S x‖)]
      have h3 : 2 * ‖G x - S x‖ ^ 2 ≤ 2 * Cε * X x := by
        have hw := hwlow2 x hxU
        have hn : 0 ≤ ‖G x - S x‖ ^ 2 := sq_nonneg _
        calc 2 * ‖G x - S x‖ ^ 2 = 2 * (‖G x - S x‖ ^ 2 * 1) := by ring
          _ ≤ 2 * (‖G x - S x‖ ^ 2 * (Cε * (Real.exp (-φ x) / (a x + b x)))) := by gcongr
          _ = 2 * Cε * X x := by simp only [hXdef]; ring
      calc ENNReal.ofReal (‖S x‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖G x‖ ^ 2 + 2 * Cε * X x) :=
            ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ ENNReal.ofReal (2 * ‖G x‖ ^ 2) + ENNReal.ofReal (2 * Cε * X x) := ENNReal.ofReal_add_le
        _ = _ := by
          congr 1
          exact ENNReal.ofReal_mul (mul_nonneg (by norm_num) hCε0)
    have hGbd : ∫⁻ x in K \ A, ENNReal.ofReal (2 * ‖G x‖ ^ 2) < ⊤ := by
      calc ∫⁻ x in K \ A, ENNReal.ofReal (2 * ‖G x‖ ^ 2)
          ≤ ∫⁻ _ in K \ A, ENNReal.ofReal (2 * Bf) := by
            refine setLIntegral_mono' hKAm fun x hx => ENNReal.ofReal_le_ofReal ?_
            have hx' := hUD (hKA hx)
            have hc : ‖(chenCutoff (R x / ε) : ℂ)‖ ≤ 1 := by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (chenCutoff_nonneg _)]
              exact chenCutoff_le_one _
            have : ‖G x‖ ^ 2 ≤ ‖fP x‖ ^ 2 := by
              simp only [hG, norm_mul]
              exact pow_le_pow_left₀ (by positivity)
                (mul_le_of_le_one_right (norm_nonneg _) hc) 2
            linarith [hBf x hx']
        _ = ENNReal.ofReal (2 * Bf) * volume (K \ A) := setLIntegral_const _ _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            ((measure_mono (hKA.trans hUD)).trans_lt hvolD)
    calc ∫⁻ x in K \ A, ENNReal.ofReal (‖S x‖ ^ 2)
        ≤ ∫⁻ x in K \ A, (ENNReal.ofReal (2 * ‖G x‖ ^ 2) +
            ENNReal.ofReal (2 * Cε) * ENNReal.ofReal (X x)) := setLIntegral_mono' hKAm hpt
      _ = (∫⁻ x in K \ A, ENNReal.ofReal (2 * ‖G x‖ ^ 2)) +
            ENNReal.ofReal (2 * Cε) * ∫⁻ x in K \ A, ENNReal.ofReal (X x) := by
          rw [lintegral_add_left' hGm, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := by
          refine ENNReal.add_lt_top.mpr ⟨hGbd, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
          exact (lintegral_mono_set hKA).trans_lt hcorr_fin
  obtain ⟨F, hF, hFS⟩ := euclideanRemovable hDo hAc (isLocallyAnalyticNull_normalWeight_eq_zero hd)
    (S := S) (by rw [hDA]; exact hS) hL2
  have hFS' : ∀ z ∈ U, F z = S z := fun z hz => hFS z (hDA ▸ hz)
  refine ⟨F, hF, ?_, ?_⟩
  · -- the restriction to `{w = 0}`
    intro z' hz'
    set V : Set (ComplexModel (m + d)) := D ∩ {z | R z < ε / 2} with hVdef
    have hVo : IsOpen V := hDo.inter (isOpen_lt hRc continuous_const)
    have hVD : V ⊆ D := inter_subset_left
    set h : ComplexModel (m + d) → ℂ := fun z => fP z - F z with hhdef
    have hhc : ContinuousOn h V := (hfPc.mono hVD).sub (hF.continuousOn.mono hVD)
    set z₀ := coordinateInclusion (m + d) m z' with hz₀def
    have hz₀pl : z₀ ∈ complexCoordinatePlane (m + d) m :=
      coordinateInclusion_mem_complexCoordinatePlane z'
    have hRz₀ : R z₀ = 0 := (normalWeight_eq_zero_iff z₀).mpr hz₀pl
    have hz₀V : z₀ ∈ V := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [tanWeight_eq_norm_proj hmn, hz₀def, coordinateProjection_coordinateInclusion hmn]
        have := mem_ball_zero_iff.mp hz'
        exact pow_lt_pow_left₀ this (norm_nonneg _) two_ne_zero
      · show R z₀ < r'' ^ 2
        rw [hRz₀]; positivity
      · show R z₀ < ε / 2
        rw [hRz₀]; positivity
    have hint' : ∫⁻ z in V, ENNReal.ofReal (‖h z‖ ^ 2) *
        ENNReal.ofReal (normalWeight (m + d) m z ^ (-(((m + d) - m : ℕ) : ℝ))) ≠ ⊤ := by
      have hdd : ((m + d) - m : ℕ) = d := by omega
      rw [hdd]
      have hae : ∀ᵐ z ∂(volume.restrict V), ENNReal.ofReal (‖h z‖ ^ 2) *
          ENNReal.ofReal (normalWeight (m + d) m z ^ (-(d : ℝ))) ≤ ENNReal.ofReal (Cε * X z) := by
        have h1 := ae_restrict_of_ae_restrict_of_subset hVD
          (ae_restrict_localPunct (m := m) (d := d) (r' := r') (r'' := r'') hd)
        filter_upwards [h1, ae_restrict_mem hVo.measurableSet] with z hzU hzV
        have hRz := hRpos z hzU
        have hGz : G z = fP z := by
          have : chenCutoff (R z / ε) = 1 := chenCutoff_of_le (by
            have h2 : R z < ε / 2 := hzV.2
            rw [div_le_iff₀ hε]; linarith)
          simp only [hG, this, Complex.ofReal_one, mul_one]
        have hhz : h z = G z - S z := by rw [hhdef]; simp only; rw [hGz, hFS' z hzU]
        rw [← ENNReal.ofReal_mul (sq_nonneg _), hhz, Real.rpow_neg hRz.le, Real.rpow_natCast]
        refine ENNReal.ofReal_le_ofReal ?_
        have hw := hwlow z hzU
        have hRd0 : 0 < R z ^ d := pow_pos hRz d
        have hinv : (R z ^ d)⁻¹ ≤ Cε * (Real.exp (-φ z) / (a z + b z)) := by
          rw [inv_le_iff_one_le_mul₀ hRd0]
          linarith [hw, mul_comm (R z ^ d) (Cε * (Real.exp (-φ z) / (a z + b z)))]
        calc ‖G z - S z‖ ^ 2 * (R z ^ d)⁻¹
            ≤ ‖G z - S z‖ ^ 2 * (Cε * (Real.exp (-φ z) / (a z + b z))) := by gcongr
          _ = Cε * X z := by simp only [hXdef]; ring
      refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hae)
      refine ne_of_lt (lt_of_le_of_lt (lintegral_mono_set hVD) ?_)
      rw [← restrict_localPunct_eq hd]
      calc ∫⁻ z in U, ENNReal.ofReal (Cε * X z)
          = ∫⁻ z in U, ENNReal.ofReal Cε * ENNReal.ofReal (X z) :=
            setLIntegral_congr_fun hUo.measurableSet fun z hz => ENNReal.ofReal_mul hCε0
        _ = ENNReal.ofReal Cε * ∫⁻ z in U, ENNReal.ofReal (X z) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcorr_fin
    have h0 := eq_zero_of_lintegral_normalWeight (by omega : m < m + d) hVo hhc hz₀V hz₀pl hint'
    have : F z₀ = fP z₀ := by
      have := h0; simp only [hhdef] at this; exact (sub_eq_zero.mp this).symm
    rw [this]
    simp only [hfP, hproj, hz₀def, coordinateProjection_coordinateInclusion hmn]
  · -- the estimate
    rw [← restrict_localPunct_eq hd]
    calc ∫⁻ z in U, ENNReal.ofReal (‖F z - G z‖ ^ 2 * stepWeight d (P z) (R z) ε)
        ≤ ∫⁻ z in U, ENNReal.ofReal 5 * ENNReal.ofReal (X z) := by
          refine setLIntegral_mono' hUo.measurableSet fun z hz => ?_
          rw [← ENNReal.ofReal_mul (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          obtain ⟨h1, h2, h3, h4, h5⟩ := htw z hz
          have hRz := hRpos z hz
          have hab := hab0 z hz
          have ht2 : 0 < Real.log (ε + R z) ^ 2 := by
            have : Real.log (ε + R z) ≠ 0 := by linarith
            positivity
          have hpow : (( ε + R z) ^ d)⁻¹ ≤ (R z ^ d)⁻¹ :=
            inv_anti₀ (pow_pos hRz d) (pow_le_pow_left₀ hRz.le (by linarith) d)
          have hlog : (Real.log (ε + R z) ^ 2)⁻¹ ≤ 5 / (a z + b z) := by
            rw [inv_le_iff_one_le_mul₀ ht2, div_mul_eq_mul_div, le_div_iff₀ hab]
            linarith
          have hFz : ‖F z - G z‖ = ‖G z - S z‖ := by rw [hFS' z hz, norm_sub_rev]
          rw [hFz]
          unfold stepWeight
          simp only [hXdef]
          rw [hexpφ z hz]
          have he := (Real.exp_pos (-P z)).le
          calc ‖G z - S z‖ ^ 2 * (Real.exp (-P z) * ((ε + R z) ^ d)⁻¹ *
                (Real.log (ε + R z) ^ 2)⁻¹)
              ≤ ‖G z - S z‖ ^ 2 * (Real.exp (-P z) * (R z ^ d)⁻¹ * (5 / (a z + b z))) := by
                gcongr
            _ = 5 * (‖G z - S z‖ ^ 2 * (Real.exp (-P z) * (R z ^ d)⁻¹) / (a z + b z)) := by
                field_simp
      _ = 5 * ∫⁻ z in U, ENNReal.ofReal (X z) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_ofNat]
      _ ≤ 5 * ∫⁻ z in U, ENNReal.ofReal (Dε z * Real.exp (-φ z)) := by gcongr
      _ = 5 * ∫⁻ z in U, ENNReal.ofReal (4 * M ^ 2 * ‖fP z‖ ^ 2 * shellInd ε (R z) *
            (Real.exp (-P z) * (R z ^ d)⁻¹)) := by
          congr 1
          refine setLIntegral_congr_fun hUo.measurableSet fun z hz => ?_
          rw [hexpφ z hz]

end SGPT.Trace.OTExt2
