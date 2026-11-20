import SGPT.NPP.DN2KiselmanSmooth
import SGPT.Foundations.Analysis.SmoothPlurisubharmonic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# FPT `lem:varying-log-radius-minimum`: the Kiselman minimum with a varying end point

Lane DN2, `thm:DNT23_C11bar`; FPT `lem:varying-log-radius-minimum`
(`chapters/inputs/q10-big-envelope-regularity.tex`, lines 368–413), in potential form.

Let `D ⊆ ℂⁿ` be open and let `H, b, Q, c` satisfy `VaryingEndpointData` (`H_s ≥ 0`, `H_ss > 0`,
`H` locally uniformly bounded below, the joint Levi form of `(z, ζ) ↦ H(z, Re ζ)` nonnegative at
the points with `s ≤ b(z)` and `H_s ≤ c`, `ddᶜQ ≥ 0`, `ddᶜb ≤ ddᶜQ`).  Then the constrained minimum

  `v(z) = min_{s ≤ b(z)} (H(z, s) - c s)`

is attained (at a point where `H_s ≤ c`), is continuous, and `v + c Q` is plurisubharmonic on `D`.
FPT's statement `i∂∂̄v ≥ -Λ - c C_b ω̂` is the case `H = H₀ + q_Λ`, `Q = C_b q_ω` with local
potentials `i∂∂̄q_Λ = Λ`, `i∂∂̄q_ω = ω̂`.

## Proof (FPT)

The penalized minima `v_ε` (`DN2KiselmanSmooth`) are smooth with `ddᶜ(v_ε + cQ) ≥ 0`, and
`|v_ε - v| ≤ (log T + c + 1) √ε` with `T = max 1 (2(H(z, b(z)) - m)/c)` locally bounded; a locally
uniform limit of smooth functions with nonnegative Levi form satisfies the disc submean inequality.

## Main results

* `logRadiusMin`: the constrained minimum.
* `VaryingEndpointData.exists_isMinOn_logRadiusMin`, `VaryingEndpointData.logRadiusMin_le`.
* `VaryingEndpointData.continuousOn_logRadiusMin`.
* `VaryingEndpointData.plurisubharmonicOn_logRadiusMin`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ}

/-- The constrained minimum `v(z) = inf_{s ≤ b(z)} (H(z, s) - c s)`. -/
def logRadiusMin (H : ComplexModel n × ℝ → ℝ) (b : ComplexModel n → ℝ) (c : ℝ)
    (z : ComplexModel n) : ℝ :=
  sInf ((fun s => H (z, s) - c * s) '' Iic (b z))

/-! ### Disc submean inequalities -/

section Submean

/-- A function smooth on `W` agrees on a ball with a globally smooth function (bump cutoff). -/
theorem exists_contDiff_eqOn_ball' {W : Set (ComplexModel n)} (hW : IsOpen W)
    {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f W) {c : ComplexModel n} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hRW : closedBall c R ⊆ W) :
    ∃ g : ComplexModel n → ℝ, ContDiff ℝ ∞ g ∧ EqOn g f (ball c r) := by
  let χ : ContDiffBump c := ⟨r, R, hr, hrR⟩
  refine ⟨fun z => χ z * f z, ?_, fun z hz => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun z => ?_
    by_cases hz : z ∈ W
    · exact (χ.contDiff.contDiffAt).mul (hf.contDiffAt (hW.mem_nhds hz))
    · have hzs : z ∉ tsupport χ := by
        rw [χ.tsupport_eq]; exact fun h => hz (hRW h)
      have h0 : (fun z => χ z * f z) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzs] with w hw
        simp [hw]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq h0
  · simp only
    rw [χ.one_of_mem_closedBall (ball_subset_closedBall hz), one_mul]

theorem leviForm_congr' {F G : ComplexModel n → ℝ} {x : ComplexModel n} (h : F =ᶠ[𝓝 x] G)
    (v : ComplexModel n) : leviForm F x v = leviForm G x v := by
  simp only [leviForm, realHessian_eq_fderiv, h.fderiv.fderiv_eq]

/-- The disc criterion from circle submean inequalities, for a function continuous on `U`. -/
theorem discPshOn_of_circleAverage_of_continuousOn {u : ComplexModel n → ℝ}
    {U : Set (ComplexModel n)} (hu : ContinuousOn u U)
    (hmean : ∀ (x v : ComplexModel n) (r : ℝ), 0 < r → affineClosedDisc x v r ⊆ U →
      u x ≤ Real.circleAverage (fun z : ℂ => u (x + z • v)) 0 r) :
    DiscPshOn (fun y => (u y : EReal)) U := by
  refine ⟨fun _ _ => EReal.coe_ne_top _,
    (continuous_coe_real_ereal.comp_continuousOn hu).upperSemicontinuousOn, ?_⟩
  intro x v r hr hD C hC
  have hcirc : Continuous (fun t : ℝ => u (x + circleMap 0 r t • v)) :=
    hu.comp_continuous (by fun_prop) fun t => hD (circle_mem_affineClosedDisc x v hr.le t)
  apply (circleDeficit_coe_le_iff x v r C (hcirc.intervalIntegrable _ _)
    (fun t => EReal.coe_le_coe_iff.mp (hC _ (circle_mem_affineClosedDisc x v hr.le t)))
    (EReal.coe_le_coe_iff.mp (hC x (center_mem_affineClosedDisc x v hr.le)))).mpr
  exact hmean x v r hr hD

theorem mem_affineClosedDisc_of_norm_eq {x v : ComplexModel n} {r : ℝ} {z : ℂ} (hz : ‖z‖ = r) :
    x + z • v ∈ affineClosedDisc x v r :=
  ⟨z, by simp [hz], rfl⟩

/-- The circle of an affine disc inside `U`. -/
theorem continuousOn_line_sphere {u : ComplexModel n → ℝ} {U : Set (ComplexModel n)}
    (hu : ContinuousOn u U) {x v : ComplexModel n} {r : ℝ} (hr : 0 ≤ r)
    (hD : affineClosedDisc x v r ⊆ U) :
    ContinuousOn (fun z : ℂ => u (x + z • v)) (sphere (0 : ℂ) r) := by
  refine hu.comp (by fun_prop) fun z hz => hD ?_
  refine mem_affineClosedDisc_of_norm_eq ?_
  simpa [abs_of_nonneg hr] using hz

/-- The submean inequality for a `C²` function with nonnegative Levi form on `U`. -/
theorem le_circleAverage_of_levi_nonneg {g : ComplexModel n → ℝ} (hg : ContDiff ℝ 2 g)
    {U : Set (ComplexModel n)} (hL : ∀ y ∈ U, ∀ v, 0 ≤ leviForm g y v)
    {x v : ComplexModel n} {r : ℝ} (hr : 0 < r) (hD : affineClosedDisc x v r ⊆ U) :
    g x ≤ Real.circleAverage (fun z : ℂ => g (x + z • v)) 0 r := by
  have hline : ContDiff ℝ 2 (fun z : ℂ => g (x + z • v)) :=
    hg.comp (contDiff_const.add (complexLineLinear v).contDiff)
  have hΔ : ∀ z ∈ closedBall (0 : ℂ) r, 0 ≤ Laplacian.laplacian (fun t : ℂ => g (x + t • v)) z := by
    intro z hz
    exact (laplacian_complexLine_nonneg_iff hg x v z).mpr (hL _ (hD ⟨z, hz, rfl⟩) v)
  simpa only [zero_smul, add_zero] using submean_of_laplacian_nonneg hline 0 hr.le hΔ

/-- Submean inequalities pass to uniform limits. -/
theorem le_circleAverage_of_tendstoUniformlyOn {u : ℕ → ComplexModel n → ℝ}
    {w : ComplexModel n → ℝ} {U : Set (ComplexModel n)} (hconv : TendstoUniformlyOn u w atTop U)
    (hcont : ∀ k, ContinuousOn (u k) U) (hw : ContinuousOn w U)
    (hmean : ∀ k (x v : ComplexModel n) (r : ℝ), 0 < r → affineClosedDisc x v r ⊆ U →
      u k x ≤ Real.circleAverage (fun z : ℂ => u k (x + z • v)) 0 r)
    {x v : ComplexModel n} {r : ℝ} (hr : 0 < r) (hD : affineClosedDisc x v r ⊆ U) :
    w x ≤ Real.circleAverage (fun z : ℂ => w (x + z • v)) 0 r := by
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp hconv (δ / 3) (by positivity)).exists
  have hclose : ∀ y ∈ U, |u k y - w y| < δ / 3 := fun y hy => by
    have := hk y hy; rwa [Real.dist_eq, abs_sub_comm] at this
  have hxU : x ∈ U := hD (center_mem_affineClosedDisc x v hr.le)
  have h1 := hmean k x v r hr hD
  have hcu : CircleIntegrable (fun z : ℂ => u k (x + z • v)) 0 r :=
    (continuousOn_line_sphere (hcont k) hr.le hD).circleIntegrable hr.le
  have hcw : CircleIntegrable (fun z : ℂ => w (x + z • v) + δ / 3) 0 r :=
    ((continuousOn_line_sphere hw hr.le hD).add continuousOn_const).circleIntegrable hr.le
  have hcw' : CircleIntegrable (fun z : ℂ => w (x + z • v)) 0 r :=
    (continuousOn_line_sphere hw hr.le hD).circleIntegrable hr.le
  have h2 : Real.circleAverage (fun z : ℂ => u k (x + z • v)) 0 r ≤
      Real.circleAverage (fun z : ℂ => w (x + z • v) + δ / 3) 0 r := by
    apply Real.circleAverage_mono hcu hcw
    intro z hz
    have hzU : x + z • v ∈ U := hD (mem_affineClosedDisc_of_norm_eq (by simpa [abs_of_pos hr] using hz))
    have := hclose _ hzU
    rw [abs_lt] at this
    linarith
  have h3 : Real.circleAverage (fun z : ℂ => w (x + z • v) + δ / 3) 0 r =
      Real.circleAverage (fun z : ℂ => w (x + z • v)) 0 r + δ / 3 := by
    rw [Real.circleAverage_fun_add hcw' (circleIntegrable_const (δ / 3) 0 r),
      Real.circleAverage_const]
  have h4 := hclose x hxU
  rw [abs_lt] at h4
  linarith

end Submean

namespace VaryingEndpointData

variable {D : Set (ComplexModel n)} {O : Set (ComplexModel n × ℝ)} {H : ComplexModel n × ℝ → ℝ}
  {b Q : ComplexModel n → ℝ} {c : ℝ}

/-! ### The constrained minimum -/

theorem logRadiusMin_eq_of_isMinOn {z : ComplexModel n} {s : ℝ} (hs : s ≤ b z)
    (hmin : IsMinOn (fun t => H (z, t) - c * t) (Iic (b z)) s) :
    logRadiusMin H b c z = H (z, s) - c * s := by
  unfold logRadiusMin
  have hleast : IsLeast ((fun t => H (z, t) - c * t) '' Iic (b z)) (H (z, s) - c * s) :=
    ⟨⟨s, hs, rfl⟩, fun y ⟨t, ht, hty⟩ => hty ▸ hmin ht⟩
  exact hleast.csInf_eq

/-- **The constrained minimum is attained**, at a point where `H_s ≤ c`. -/
theorem exists_isMinOn_logRadiusMin (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n}
    (hz : z ∈ D) : ∃ s ≤ b z, IsMinOn (fun t => H (z, t) - c * t) (Iic (b z)) s ∧
      logRadiusMin H b c z = H (z, s) - c * s ∧ deriv (fun t => H (z, t)) s ≤ c := by
  obtain ⟨m, Pz⟩ := P.exists_profile hz
  obtain ⟨s, hs, hmin, hd⟩ := Pz.exists_isMinOn
  exact ⟨s, hs, hmin, logRadiusMin_eq_of_isMinOn hs hmin, hd⟩

theorem logRadiusMin_le (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n} (hz : z ∈ D)
    {t : ℝ} (ht : t ≤ b z) : logRadiusMin H b c z ≤ H (z, t) - c * t := by
  obtain ⟨s, hs, hmin, heq, -⟩ := P.exists_isMinOn_logRadiusMin hz
  rw [heq]; exact hmin ht

/-- **The penalized minimum is close to the constrained minimum.** -/
theorem abs_penValue_sub_le (P : VaryingEndpointData D O H b Q c) {z : ComplexModel n}
    (hz : z ∈ D) {m : ℝ} (hm : ∀ s ≤ b z, m ≤ H (z, s)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεc : ε ≤ c / 4) :
    |penValue H b c ε z - logRadiusMin H b c z| ≤
      (Real.log (max 1 (2 * (H (z, b z) - m) / c)) + c + 1) * Real.sqrt ε := by
  have Pz : LogRadiusProfile (fun t => H (z, t)) (b z) c m := by
    obtain ⟨m', Pz'⟩ := P.exists_profile hz
    exact ⟨Pz'.c_pos, Pz'.diff, Pz'.diff2, Pz'.deriv_nonneg, Pz'.deriv2_pos, hm⟩
  have hc := P.c_pos
  obtain ⟨hlt, hcrit⟩ := P.penMin_spec hz hε hεc
  set sε := penMin H b c ε z with hsε
  obtain ⟨s, hs, hmin, heq, -⟩ := P.exists_isMinOn_logRadiusMin hz
  set T := max 1 (2 * (H (z, b z) - m) / c) with hT
  have hT1 : 1 ≤ T := le_max_left _ _
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hεsq : ε ≤ Real.sqrt ε := by
    have h1 : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε.le
    have h2 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
    nlinarith [Real.sqrt_nonneg ε]
  have hpen : penValue H b c ε z = (H (z, sε) - c * sε) - ε * Real.log (b z - sε) := by
    simp [penValue, penalty, hsε]
  -- lower bound
  have hlow : logRadiusMin H b c z - ε * Real.log T ≤ penValue H b c ε z := by
    have h1 : logRadiusMin H b c z ≤ H (z, sε) - c * sε := P.logRadiusMin_le hz hlt.le
    have h2 : b z - sε ≤ T := Pz.sub_le_max hε.le (by linarith) hlt hcrit
    have h3 : Real.log (b z - sε) ≤ Real.log T := Real.log_le_log (sub_pos.mpr hlt) h2
    rw [hpen]; nlinarith
  -- upper bound
  have hup : penValue H b c ε z ≤ logRadiusMin H b c z + (c + 1) * Real.sqrt ε := by
    set s' := min s (b z - Real.sqrt ε) with hs'
    have hs'b : s' < b z := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have h1 : penValue H b c ε z ≤ penalty (fun t => H (z, t)) (b z) c ε s' :=
      P.isMinOn_penValue hz hε hεc hs'b
    have h2 : Real.log (Real.sqrt ε) ≤ Real.log (b z - s') :=
      Real.log_le_log hsq (by rw [hs']; have := min_le_right s (b z - Real.sqrt ε); linarith)
    have h3 : -(ε * Real.log (Real.sqrt ε)) ≤ Real.sqrt ε := by
      have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hsq)
      rw [Real.log_inv] at hl
      have : ε * (Real.sqrt ε)⁻¹ = Real.sqrt ε := by
        rw [mul_inv_eq_iff_eq_mul₀ hsq.ne']
        exact (Real.mul_self_sqrt hε.le).symm
      nlinarith
    have h4 : H (z, s') - c * s' ≤ H (z, s) - c * s + c * Real.sqrt ε := by
      rcases le_total s (b z - Real.sqrt ε) with hle | hle
      · rw [hs', min_eq_left hle]; nlinarith
      · rw [hs', min_eq_right hle]
        have hmono := Pz.deriv_mul_le_sub hle hs
        have hd0 := Pz.deriv_nonneg (b z - Real.sqrt ε) (by linarith)
        have hss : s - (b z - Real.sqrt ε) ≤ Real.sqrt ε := by linarith
        have : 0 ≤ deriv (fun t => H (z, t)) (b z - Real.sqrt ε) * (s - (b z - Real.sqrt ε)) :=
          mul_nonneg hd0 (by linarith)
        nlinarith
    have h5 : penalty (fun t => H (z, t)) (b z) c ε s' ≤
        H (z, s') - c * s' - ε * Real.log (Real.sqrt ε) := by
      simp only [penalty]; nlinarith
    rw [heq]; linarith
  rw [abs_le]
  constructor
  · have : ε * Real.log T ≤ Real.log T * Real.sqrt ε := by nlinarith
    nlinarith
  · nlinarith

/-! ### Locally uniform convergence and the conclusion -/

/-- The penalization parameters `ε_k = min 1 (c/4) / (k + 1)`. -/
def epsSeq (c : ℝ) (k : ℕ) : ℝ := min 1 (c / 4) / ((k : ℝ) + 1)

theorem epsSeq_pos {c : ℝ} (hc : 0 < c) (k : ℕ) : 0 < epsSeq c k := by
  unfold epsSeq; have : 0 < min 1 (c / 4) := lt_min one_pos (by positivity)
  positivity

theorem epsSeq_le_one {c : ℝ} (hc : 0 < c) (k : ℕ) : epsSeq c k ≤ 1 := by
  unfold epsSeq
  rw [div_le_iff₀ (by positivity)]
  have := min_le_left 1 (c / 4)
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem epsSeq_le_quarter {c : ℝ} (hc : 0 < c) (k : ℕ) : epsSeq c k ≤ c / 4 := by
  unfold epsSeq
  rw [div_le_iff₀ (by positivity)]
  have := min_le_right 1 (c / 4)
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem tendsto_sqrt_epsSeq (c : ℝ) : Tendsto (fun k => Real.sqrt (epsSeq c k)) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => epsSeq c k) atTop (𝓝 0) := by
    unfold epsSeq
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h2
  exact h2

/-- Local data around a point: a ball on which the penalized minima converge uniformly. -/
theorem exists_ball_tendstoUniformlyOn (P : VaryingEndpointData D O H b Q c) {z₀ : ComplexModel n}
    (hz₀ : z₀ ∈ D) : ∃ r > 0, closedBall z₀ (4 * r) ⊆ D ∧
      TendstoUniformlyOn (fun k => penValue H b c (epsSeq c k)) (logRadiusMin H b c) atTop
        (ball z₀ r) := by
  have hc := P.c_pos
  obtain ⟨V, hV, m, hm⟩ := P.lower z₀ hz₀
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hV (P.isOpen_D.mem_nhds hz₀))
  set r := ρ / 8 with hr
  have hr0 : 0 < r := by positivity
  have hball : closedBall z₀ (4 * r) ⊆ V ∩ D :=
    (closedBall_subset_ball (by rw [hr]; linarith)).trans hρsub
  -- `z ↦ H(z, b z)` is bounded above on the compact ball
  have hcontHb : ContinuousOn (fun z => H (z, b z)) (closedBall z₀ (4 * r)) := by
    refine P.smooth_H.continuousOn.comp (continuousOn_id.prodMk
      (P.smooth_b.continuousOn.mono fun z hz => (hball hz).2)) fun z hz => ?_
    exact P.mem_O z (hball hz).2 (b z) le_rfl
  obtain ⟨B, hB⟩ := (isCompact_closedBall z₀ (4 * r)).exists_bound_of_continuousOn hcontHb
  set T₀ := max 1 (2 * (|B| - m) / c) with hT₀
  refine ⟨r, hr0, fun z hz => (hball hz).2, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hK : 0 < Real.log T₀ + c + 1 := by
    have := Real.log_nonneg (le_max_left 1 (2 * (|B| - m) / c)); linarith
  have hlim := tendsto_sqrt_epsSeq c
  have hev : ∀ᶠ k in atTop, Real.sqrt (epsSeq c k) < δ / (Real.log T₀ + c + 1) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hev] with k hk z hz
  have hzc : z ∈ closedBall z₀ (4 * r) := closedBall_subset_closedBall (by linarith : r ≤ 4 * r) (ball_subset_closedBall hz)
  have hzD : z ∈ D := (hball hzc).2
  have hmz : ∀ s ≤ b z, m ≤ H (z, s) := fun s hs => hm z (hball hzc).1 hzD s hs
  have habs := P.abs_penValue_sub_le hzD hmz (epsSeq_pos hc k) (epsSeq_le_one hc k)
    (epsSeq_le_quarter hc k)
  have hTz : max 1 (2 * (H (z, b z) - m) / c) ≤ T₀ := by
    have hBz : H (z, b z) ≤ |B| := by
      have h1 := hB z hzc
      rw [Real.norm_eq_abs] at h1
      exact (le_abs_self _).trans (h1.trans (le_abs_self _))
    refine max_le_max le_rfl ?_
    exact div_le_div_of_nonneg_right (by linarith) hc.le
  have hlogz : Real.log (max 1 (2 * (H (z, b z) - m) / c)) ≤ Real.log T₀ :=
    Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) hTz
  have hsq0 : 0 ≤ Real.sqrt (epsSeq c k) := Real.sqrt_nonneg _
  rw [Real.dist_eq, abs_sub_comm]
  calc |penValue H b c (epsSeq c k) z - logRadiusMin H b c z|
      ≤ (Real.log (max 1 (2 * (H (z, b z) - m) / c)) + c + 1) * Real.sqrt (epsSeq c k) := habs
    _ ≤ (Real.log T₀ + c + 1) * Real.sqrt (epsSeq c k) := by nlinarith
    _ < (Real.log T₀ + c + 1) * (δ / (Real.log T₀ + c + 1)) :=
        mul_lt_mul_of_pos_left hk hK
    _ = δ := by field_simp

/-- **Continuity of the constrained minimum.** -/
theorem continuousOn_logRadiusMin (P : VaryingEndpointData D O H b Q c) :
    ContinuousOn (logRadiusMin H b c) D := by
  intro z₀ hz₀
  obtain ⟨r, hr, hsub, hconv⟩ := P.exists_ball_tendstoUniformlyOn hz₀
  have hcont : ContinuousOn (logRadiusMin H b c) (ball z₀ r) :=
    hconv.continuousOn (Frequently.of_forall fun k =>
      (P.contDiffOn_penValue (epsSeq_pos P.c_pos k) (epsSeq_le_quarter P.c_pos k)).continuousOn.mono
        fun z hz => hsub (closedBall_subset_closedBall (by linarith : r ≤ 4 * r) (ball_subset_closedBall hz)))
  exact (hcont.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousWithinAt

/-- **FPT `lem:varying-log-radius-minimum`** (potential form): `v + c Q` is plurisubharmonic on
`D`, where `v(z) = min_{s ≤ b(z)} (H(z, s) - c s)`. -/
theorem plurisubharmonicOn_logRadiusMin (P : VaryingEndpointData D O H b Q c) :
    PlurisubharmonicOn (fun z => ((logRadiusMin H b c z + c * Q z : ℝ) : EReal)) D := by
  intro z₀ hz₀
  have hc := P.c_pos
  obtain ⟨r, hr, hsub, hconv⟩ := P.exists_ball_tendstoUniformlyOn hz₀
  have hballD : ball z₀ r ⊆ D := fun z hz => hsub (closedBall_subset_closedBall (by linarith : r ≤ 4 * r) (ball_subset_closedBall hz))
  set u : ℕ → ComplexModel n → ℝ := fun k z => penValue H b c (epsSeq c k) z + c * Q z with hu
  set w : ComplexModel n → ℝ := fun z => logRadiusMin H b c z + c * Q z with hw
  have hQc : ContinuousOn Q D := P.smooth_Q.continuousOn
  have hsmooth : ∀ k, ContDiffOn ℝ ∞ (u k) D := fun k =>
    (P.contDiffOn_penValue (epsSeq_pos hc k) (epsSeq_le_quarter hc k)).add
      (contDiffOn_const.mul P.smooth_Q)
  have hconv' : TendstoUniformlyOn u w atTop (ball z₀ r) := by
    rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
    intro δ hδ
    filter_upwards [hconv δ hδ] with k hk z hz
    have := hk z hz
    simp only [hu, hw, Real.dist_eq] at this ⊢
    rwa [show logRadiusMin H b c z + c * Q z - (penValue H b c (epsSeq c k) z + c * Q z) =
      logRadiusMin H b c z - penValue H b c (epsSeq c k) z by ring]
  have hucont : ∀ k, ContinuousOn (u k) (ball z₀ r) := fun k => (hsmooth k).continuousOn.mono hballD
  have hwcont : ContinuousOn w (ball z₀ r) :=
    (P.continuousOn_logRadiusMin.add (continuousOn_const.mul hQc)).mono hballD
  -- each `u k` satisfies the submean inequality on discs in the ball
  have hmean : ∀ k (x v : ComplexModel n) (ρ : ℝ), 0 < ρ → affineClosedDisc x v ρ ⊆ ball z₀ r →
      u k x ≤ Real.circleAverage (fun z : ℂ => u k (x + z • v)) 0 ρ := by
    intro k x v ρ hρ hD
    obtain ⟨g, hg, hgeq⟩ := exists_contDiff_eqOn_ball' P.isOpen_D
      (hsmooth k) hr (by linarith) hsub
    have hgL : ∀ y ∈ ball z₀ r, ∀ v', 0 ≤ leviForm g y v' := by
      intro y hy v'
      have hloc : g =ᶠ[𝓝 y] u k := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hy) hgeq
      rw [leviForm_congr' hloc]
      exact P.leviForm_penValue_add_nonneg (hballD hy) (epsSeq_pos hc k)
        (epsSeq_le_quarter hc k) v'
    have h := le_circleAverage_of_levi_nonneg (hg.of_le two_le_infty) hgL hρ hD
    have hx : g x = u k x := hgeq (hD (center_mem_affineClosedDisc x v hρ.le))
    have hcirc : Real.circleAverage (fun z : ℂ => g (x + z • v)) 0 ρ =
        Real.circleAverage (fun z : ℂ => u k (x + z • v)) 0 ρ := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      apply hgeq
      apply hD
      apply mem_affineClosedDisc_of_norm_eq
      simpa [abs_of_pos hρ] using hz
    rw [← hx, ← hcirc]
    exact h
  have hdisc : DiscPshOn (fun y => (w y : EReal)) (ball z₀ r) :=
    discPshOn_of_circleAverage_of_continuousOn hwcont fun x v ρ hρ hD =>
      le_circleAverage_of_tendstoUniformlyOn hconv' hucont hwcont hmean hρ hD
  exact ⟨ball z₀ r, isOpen_ball, mem_ball_self hr, hdisc⟩

end VaryingEndpointData

end SGPT.NPP.DN2
