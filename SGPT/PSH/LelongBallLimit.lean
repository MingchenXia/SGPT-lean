import SGPT.PSH.BallGrowth
import SGPT.PSH.VariableLelong
import SGPT.Foundations.Analysis.Pending.ConvexSlopeAtBot
import SGPT.Foundations.Analysis.FirstPass.PshClosedDiscMaximum
import SGPT.Foundations.Analysis.Pending.LelongNumberChartTransport

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH

open Set Filter Metric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SquaredLogLelongSourceNormalization
open scoped Topology ENNReal NNReal

/-- Reuse the genuine main convex slope on the literal original open balls. -/
theorem PSHOn.exists_logBallSup_asymptotic_bounds {n : ℕ}
    {u : ComplexModel n → EReal} (hu : PSHOn u (ball 0 1)) :
    ∃ s : ℝ, 0 ≤ s ∧
      (∃ C t₂ : ℝ, t₂ ≤ 0 ∧ ∀ t < t₂, logBallSup u 0 t ≤ s * t + C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ t₁ D : ℝ,
        ∀ t < t₁, (s + ε) * t + D ≤ logBallSup u 0 t) := by
  apply ConvexSlopeAtBot.exists_slope_atBot
  · intro a b hab hb
    exact hu.monotoneOn_logBallSup (by norm_num) (by simpa using hab.trans_lt hb)
      (by simpa using hb) hab
  · intro a b c hab hbc hc
    exact hu.logBallSup_chord (by norm_num) hab hbc (by simpa using hc)

/-- Actual affine bounds give the quotient limit, without a limit certificate. -/
theorem tendsto_div_atBot_of_affine_bounds {f : ℝ → ℝ} {s : ℝ}
    (hupper : ∃ C t₂ : ℝ, ∀ t < t₂, f t ≤ s * t + C)
    (hlower : ∀ ε : ℝ, 0 < ε → ∃ t₁ D : ℝ,
      ∀ t < t₁, (s + ε) * t + D ≤ f t) :
    Tendsto (fun t => f t / t) atBot (𝓝 s) := by
  obtain ⟨C, t₂, hC⟩ := hupper
  have hdiv (A : ℝ) : Tendsto (fun t : ℝ => A / t) atBot (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => A) atBot (𝓝 A)).mul
        tendsto_inv_atBot_zero
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 2 := by positivity
  obtain ⟨t₁, D, hD⟩ := hlower (ε / 2) he
  have hc := Metric.tendsto_nhds.mp (hdiv C) (ε / 2) he
  have hd := Metric.tendsto_nhds.mp (hdiv D) (ε / 2) he
  filter_upwards [eventually_lt_atBot t₂, eventually_lt_atBot t₁,
    eventually_lt_atBot 0, hc, hd] with t ht₂ ht₁ ht hc' hd'
  have hCt : (s + C / t) * t = s * t + C := by
    rw [add_mul, div_mul_cancel₀ _ ht.ne]
  have hDt : (s + ε / 2 + D / t) * t = (s + ε / 2) * t + D := by
    rw [add_mul, div_mul_cancel₀ _ ht.ne]
  have hlo : s + C / t ≤ f t / t :=
    (le_div_iff_of_neg ht).mpr (hCt ▸ hC t ht₂)
  have hhi : f t / t ≤ s + ε / 2 + D / t :=
    (div_le_iff_of_neg ht).mpr (hDt ▸ hD t ht₁)
  simp only [dist_zero_right, Real.norm_eq_abs] at hc' hd'
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith [(abs_lt.mp hc').1, (abs_lt.mp hd').2]

/-- The true complex disc maximum controls the centre of the literal open ball. -/
theorem PSHOn.ballSup_le_of_punctured_bound {n : ℕ} (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : PSHOn u (ball 0 1))
    {γ C ρ r : ℝ} (hγ : 0 ≤ γ) (hr : 0 < r) (hr1 : r < 1) (hrρ : r < ρ)
    (hb : ∀ z : ComplexModel n, 0 < ‖z‖ → ‖z‖ < ρ →
      u z ≤ ((γ * Real.log ‖z‖ + C : ℝ) : EReal)) :
    ballSup u 0 r ≤ ((γ * Real.log r + C : ℝ) : EReal) := by
  let v : ComplexModel n := PiLp.single 2 (⟨0, hn⟩ : Fin n) (1 : ℂ)
  have hv : ‖v‖ = 1 := by simp [v, PiLp.norm_single]
  let L : ℂ →L[ℂ] ComplexModel n := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  have hLn (z : ℂ) : ‖L z‖ = ‖z‖ := by simp [L, norm_smul, hv]
  have hp : PlurisubharmonicOn (fun z : ℂ => u (L z)) (ball 0 1) := by
    intro z hz
    have hz' : L z ∈ ball (0 : ComplexModel n) 1 := by
      simpa only [mem_ball, dist_zero_right, hLn] using hz
    have hzu : PlurisubharmonicAt u (0 + L z) := by
      simpa only [zero_add] using hu.disc.plurisubharmonicOn isOpen_ball (L z) hz'
    simpa only [zero_add] using PlurisubharmonicAt.comp_affine L 0 hzu
  have h0 : u 0 ≤ ((γ * Real.log r + C : ℝ) : EReal) := by
    have hmax := hp.le_const_on_closedBall_of_le_on_sphere hr
      (closedBall_subset_ball hr1) (C := γ * Real.log r + C) (by
        intro z hz
        have hzr : ‖L z‖ = r := by
          simpa only [mem_sphere, dist_zero_right, hLn] using hz
        simpa only [hzr] using hb (L z) (hzr ▸ hr) (hzr ▸ hrρ))
    simpa only [map_zero] using hmax 0 (mem_closedBall_self hr.le)
  apply iSup₂_le
  intro z hz
  by_cases hz0 : z = 0
  · simpa only [hz0] using h0
  have hzr : ‖z‖ < r := by simpa only [mem_ball, dist_zero_right] using hz
  exact (hb z (norm_pos_iff.mpr hz0) (hzr.trans hrρ)).trans
    (EReal.coe_le_coe_iff.mpr (by
      gcongr))

/-- Doubling the radius puts each actual point strictly inside the original open ball. -/
theorem PSHOn.exists_logBallSup_point_bound {n : ℕ}
    {u : ComplexModel n → EReal} (hu : PSHOn u (ball 0 1)) {s : ℝ}
    (hupper : ∃ C t₂ : ℝ, t₂ ≤ 0 ∧ ∀ t < t₂, logBallSup u 0 t ≤ s * t + C) :
    ∃ C ρ : ℝ, 0 < ρ ∧ ∀ z : ComplexModel n, 0 < ‖z‖ → ‖z‖ < ρ →
      u z ≤ ((s * Real.log ‖z‖ + C : ℝ) : EReal) := by
  obtain ⟨C, t₂, ht₂, hC⟩ := hupper
  refine ⟨C + s * Real.log 2, Real.exp t₂ / 2, by positivity, ?_⟩
  intro z hz hzρ
  have htwo : 0 < 2 * ‖z‖ := by positivity
  have htwoexp : 2 * ‖z‖ < Real.exp t₂ := by linarith
  have ht : Real.log (2 * ‖z‖) < t₂ :=
    (Real.log_lt_iff_lt_exp htwo).mpr htwoexp
  have ht0 : Real.log (2 * ‖z‖) < Real.log 1 := by simpa using ht.trans_le ht₂
  have hzu : u z ≤ (logBallSup u 0 (Real.log (2 * ‖z‖)) : EReal) := by
    have hcoe := hu.coe_logBallSup (by norm_num : (0 : ℝ) < 1) ht0
    have hzball : z ∈ ball (0 : ComplexModel n) (Real.exp (Real.log (2 * ‖z‖))) := by
      rw [Real.exp_log htwo]
      simp only [mem_ball, dist_zero_right]
      linarith
    exact (le_iSup₂
      (f := fun w (_ : w ∈ ball 0 (Real.exp (Real.log (2 * ‖z‖)))) => u w) z hzball).trans_eq
      hcoe.symm
  refine hzu.trans (EReal.coe_le_coe_iff.mpr ?_)
  have := hC _ ht
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne'] at this
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hz.ne']
  linarith

/-- Genuine original growth supremum equals the produced slope, with actual attainment. -/
theorem PSHOn.exists_lelongBall_slope {n : ℕ} (hn : 0 < n)
    {u : ComplexModel n → EReal} (hu : PSHOn u (ball 0 1)) :
    ∃ s : ℝ, 0 ≤ s ∧ squaredLogLelongNumber (n := n) u 0 = ENNReal.ofReal (s / 2) ∧
      Tendsto (fun t => logBallSup u 0 t / t) atBot (𝓝 s) ∧
      ∃ C ρ : ℝ, 0 < ρ ∧ ∀ z : ComplexModel n, 0 < ‖z‖ → ‖z‖ < ρ →
        u z ≤ ((s * Real.log ‖z‖ + C : ℝ) : EReal) := by
  obtain ⟨s, hs, hupper, hlower⟩ := hu.exists_logBallSup_asymptotic_bounds
  have hlim := tendsto_div_atBot_of_affine_bounds
    (by obtain ⟨C, t₂, _, hC⟩ := hupper; exact ⟨C, t₂, hC⟩) hlower
  obtain ⟨C, ρ, hρ, hpoint⟩ := hu.exists_logBallSup_point_bound hupper
  have hν : lelongNumber (n := n) u 0 = ENNReal.ofReal s := by
    apply le_antisymm
    · apply LelongNumberChartTransport.lelongNumber_le_ofReal
      rintro γ ⟨D, hD⟩
      have hD' : ∀ᶠ z in 𝓝[≠] (0 : ComplexModel n),
          u z ≤ (((γ : ℝ) * Real.log ‖z‖ + D : ℝ) : EReal) := by
        simpa only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
          id_eq, sub_zero] using hD
      obtain ⟨V, hV, hVo, hV0⟩ := _root_.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hD')
      obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hVo 0 hV0
      have hbound : ∀ z : ComplexModel n, 0 < ‖z‖ → ‖z‖ < δ →
          u z ≤ (((γ : ℝ) * Real.log ‖z‖ + D : ℝ) : EReal) := by
        intro z hz hzδ
        exact hV (hδV (by simpa using hzδ)) (by simpa using (norm_pos_iff.mp hz))
      have hDdiv : Tendsto (fun t : ℝ => D / t) atBot (𝓝 0) := by
        simpa only [div_eq_mul_inv, mul_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => D) atBot (𝓝 D)).mul
            tendsto_inv_atBot_zero
      have hlim' : Tendsto (fun t => logBallSup u 0 t / t - D / t) atBot (𝓝 s) := by
        simpa only [sub_zero] using hlim.sub hDdiv
      apply ge_of_tendsto hlim'
      filter_upwards [eventually_lt_atBot (Real.log δ), eventually_lt_atBot 0] with t htδ ht0
      have hrδ : Real.exp t < δ := by
        rw [← Real.exp_log hδ]; exact Real.exp_lt_exp.mpr htδ
      have hr1 : Real.exp t < 1 := by simpa using Real.exp_lt_exp.mpr ht0
      have hb := hu.ballSup_le_of_punctured_bound hn γ.coe_nonneg
        (Real.exp_pos t) hr1 hrδ hbound
      rw [← hu.coe_logBallSup (by norm_num) (by simpa using ht0),
        Real.log_exp, EReal.coe_le_coe_iff] at hb
      have hdiv : (γ : ℝ) + D / t ≤ logBallSup u 0 t / t := by
        apply (le_div_iff_of_neg ht0).mpr
        rwa [add_mul, div_mul_cancel₀ _ ht0.ne]
      linarith
    · apply LelongNumberChartTransport.ofReal_le_lelongNumber hs (C := C)
      rw [eventually_nhdsWithin_iff]
      filter_upwards [ball_mem_nhds (0 : ComplexModel n) hρ] with z hz hz0
      simpa only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
        id_eq, sub_zero] using hpoint z (norm_pos_iff.mpr hz0)
          (by simpa only [mem_ball, dist_zero_right] using hz)
  have hsource : squaredLogLelongNumber (n := n) u 0 = ENNReal.ofReal (s / 2) := by
    apply (ENNReal.mul_right_inj (a := 2) (by norm_num) (by norm_num)).mp
    rw [← lelongNumber_eq_two_mul_squaredLog (Nat.ne_of_gt hn), hν]
    calc
      ENNReal.ofReal s = ENNReal.ofReal (2 * (s / 2)) := by congr 1; ring
      _ = ENNReal.ofReal 2 * ENNReal.ofReal (s / 2) := ENNReal.ofReal_mul (by norm_num)
      _ = 2 * ENNReal.ofReal (s / 2) := by norm_num
  exact ⟨s, hs, hsource, hlim, C, ρ, hρ, hpoint⟩

/-- The literal zero-dimensional ball is its unique point. -/
theorem ballSup_zero_dimension (u : ComplexModel 0 → EReal) {r : ℝ} (hr : 0 < r) :
    ballSup u 0 r = u 0 := by
  apply le_antisymm
  · exact iSup₂_le fun z _ => by rw [Subsingleton.elim z 0]
  · exact le_iSup₂ (f := fun z (_ : z ∈ ball 0 r) => u z) 0 (mem_ball_self hr)

/-- Literal original open-ball/squared-log limit, including the original dimension-zero convention. -/
theorem PSHOn.tendsto_ballSup_div_log_squared {n : ℕ}
    {u : ComplexModel n → EReal} (hu : PSHOn u (ball 0 1)) :
    squaredLogLelongNumber (n := n) u 0 ≠ ⊤ ∧
      Tendsto (fun r : ℝ => (ballSup u 0 r).toReal / Real.log (r ^ 2)) (𝓝[>] 0)
        (𝓝 (squaredLogLelongNumber (n := n) u 0).toReal) := by
  cases n with
  | zero =>
      have hlim : Tendsto (fun r : ℝ => (u 0).toReal / (2 * Real.log r))
          (𝓝[>] 0) (𝓝 0) := by
        have h := (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (u 0).toReal) (𝓝[>] 0) (𝓝 (u 0).toReal)).mul
          (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero)
        have hb : Tendsto (fun r : ℝ => (u 0).toReal / Real.log r)
            (𝓝[>] 0) (𝓝 0) := by
          simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using h
        have h' : Tendsto (fun r : ℝ => ((u 0).toReal / Real.log r) / 2)
            (𝓝[>] 0) (𝓝 (0 / 2 : ℝ)) := by
          exact hb.div_const 2
        simpa only [zero_div, div_div, mul_comm (Real.log _) 2] using h'
      refine ⟨by simp [squaredLogLelongNumber], ?_⟩
      have heq : (fun r : ℝ => (ballSup u 0 r).toReal / Real.log (r ^ 2)) =ᶠ[𝓝[>] 0]
          (fun r => (u 0).toReal / (2 * Real.log r)) := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        rw [ballSup_zero_dimension u hr, Real.log_pow]
        norm_num
      simpa only [squaredLogLelongNumber, ite_true, ENNReal.toReal_zero] using
        hlim.congr' heq.symm
  | succ m =>
      obtain ⟨s, hs, hsource, hlim, _⟩ := hu.exists_lelongBall_slope (Nat.succ_pos m)
      refine ⟨hsource ▸ ENNReal.ofReal_ne_top, ?_⟩
      have hlim' : Tendsto (fun r : ℝ => (logBallSup u 0 (Real.log r) / Real.log r) / 2)
          (𝓝[>] 0) (𝓝 (s / 2)) := (hlim.comp Real.tendsto_log_nhdsGT_zero).div_const 2
      have heq : (fun r : ℝ => (ballSup u 0 r).toReal / Real.log (r ^ 2)) =ᶠ[𝓝[>] 0]
          (fun r => (logBallSup u 0 (Real.log r) / Real.log r) / 2) := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        simp only [logBallSup, Real.exp_log hr, Real.log_pow]
        norm_num
        ring
      rw [hsource, ENNReal.toReal_ofReal (by positivity)]
      exact hlim'.congr' heq.symm

/-- The original nonnegative growth supremum is attained by its actual finite value. -/
theorem PSHOn.squaredLogLelongNumber_attained {n : ℕ}
    {u : ComplexModel n → EReal} (hu : PSHOn u (ball 0 1)) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] (0 : ComplexModel n),
      u z ≤ (((squaredLogLelongNumber (n := n) u 0).toReal *
        Real.log (‖z‖ ^ 2) + C : ℝ) : EReal) := by
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      rw [eventually_nhdsWithin_iff]
      exact Eventually.of_forall fun z hz => False.elim (hz (Subsingleton.elim z 0))
  | succ m =>
      obtain ⟨s, hs, hsource, _, C, ρ, hρ, hpoint⟩ :=
        hu.exists_lelongBall_slope (Nat.succ_pos m)
      refine ⟨C, ?_⟩
      rw [eventually_nhdsWithin_iff]
      filter_upwards [ball_mem_nhds (0 : ComplexModel (m + 1)) hρ] with z hz hz0
      have h := hpoint z (norm_pos_iff.mpr hz0)
        (by simpa only [mem_ball, dist_zero_right] using hz)
      rw [hsource, ENNReal.toReal_ofReal (by positivity), Real.log_pow]
      have heq : s / 2 * ((2 : ℕ) * Real.log ‖z‖) + C = s * Real.log ‖z‖ + C := by
        norm_num
        ring
      rwa [heq]

/-- The actual attained exponent bounds every prescribed original smaller ball. -/
theorem PSHOn.squaredLogLelongNumber_upper_bound_on_ball {n : ℕ}
    {u : ComplexModel n → EReal} (hu : PSHOn u (ball 0 1))
    {r₁ : ℝ} (_hr₁ : 0 < r₁) (hr₁1 : r₁ < 1) :
    ∃ C : ℝ, ∀ z ∈ ball (0 : ComplexModel n) r₁, z ≠ 0 →
      u z ≤ (((squaredLogLelongNumber (n := n) u 0).toReal *
        Real.log (‖z‖ ^ 2) + C : ℝ) : EReal) := by
  cases n with
  | zero =>
      exact ⟨0, fun z _ hz => False.elim (hz (Subsingleton.elim z 0))⟩
  | succ m =>
      obtain ⟨s, hs, hsource, _, C, ρ, hρ, hpoint⟩ :=
        hu.exists_lelongBall_slope (Nat.succ_pos m)
      obtain ⟨U, _, hU⟩ := (hu.disc.plurisubharmonicOn isOpen_ball).exists_nonnegative_compact_upper_bound
        (isCompact_closedBall 0 r₁) (closedBall_subset_ball hr₁1)
      refine ⟨max C (U - s * Real.log ρ), ?_⟩
      intro z hz hz0
      have heq : (squaredLogLelongNumber (n := m + 1) u 0).toReal *
          Real.log (‖z‖ ^ 2) = s * Real.log ‖z‖ := by
        rw [hsource, ENNReal.toReal_ofReal (by positivity), Real.log_pow]
        norm_num
        ring
      rw [heq]
      by_cases hzρ : ‖z‖ < ρ
      · exact (hpoint z (norm_pos_iff.mpr hz0) hzρ).trans
          (EReal.coe_le_coe_iff.mpr (by linarith [le_max_left C (U - s * Real.log ρ)]))
      · have hρz : Real.log ρ ≤ Real.log ‖z‖ :=
          Real.log_le_log hρ (le_of_not_gt hzρ)
        exact (hU z (ball_subset_closedBall hz)).trans
          (EReal.coe_le_coe_iff.mpr (by
            linarith [mul_le_mul_of_nonneg_left hρz hs,
              le_max_right C (U - s * Real.log ρ)]))

end SGPT.PSH
