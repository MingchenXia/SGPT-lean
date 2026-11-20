import SGPT.Okounkov.TranscendentalWNLipschitzSmooth
import SGPT.Okounkov.TranscendentalWNEnvelopeStatement
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The Lipschitz bound from a Laplacian bound (package WN-LIP)

Proof of `SGPT.Okounkov.TranscendentalWN.LipschitzOfLaplacianStatement`, the blueprint node
`tok-wn:lipschitz` (D. Witt Nyström, arXiv:2103.03660, Corollary 7.6): there is a universal
constant `A` such that every `h` continuous on the closed unit disc with `|h| ≤ 1` there and
`|Δ h| ≤ 1` as distributions on the open disc satisfies `|h(w) - h(0)| ≤ A |w|` for `|w| ≤ 1/2`.

Route (blueprint `claude-tok-wn-lip`, node `tok-wn-lip:mollify`): extend `h` by zero off the closed
disc (`discExt`) and mollify, `h_ε = discExt h ⋆ ρ_ε` with the normed bump `ρ_ε` of radius `ε`
(`mollifier`).  Then `h_ε` is smooth, `|h_ε| ≤ 1`, and for `|x| + ε < 1`,
`Δ h_ε(x) = ∫ h(t) Δ_t[ρ_ε(x - t)] dt`, so the distributional hypothesis applied to the test
function `t ↦ ρ_ε(x - t)` gives `|Δ h_ε(x)| ≤ ∫ ρ_ε = 1`.  The smooth case
(`exists_lipschitz_of_smooth`) gives `|h_ε(w) - h_ε(0)| ≤ A₀ |w|` with `A₀` independent of `ε`,
and `h_ε → h` at the continuity points `w` and `0` of `h`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open MeasureTheory Metric Laplacian Set Filter
open scoped Convolution ContDiff Topology

namespace Lipschitz

/-- The extension of `h` by zero outside the closed unit disc. -/
def discExt (h : ℂ → ℝ) : ℂ → ℝ := (closedBall (0 : ℂ) 1).indicator h

/-- `discExt h` is integrable when `h` is continuous on the closed unit disc. -/
theorem integrable_discExt {h : ℂ → ℝ} (hcont : ContinuousOn h (closedBall 0 1)) :
    Integrable (discExt h) :=
  (integrable_indicator_iff measurableSet_closedBall).mpr
    (hcont.integrableOn_compact (isCompact_closedBall 0 1))

/-- `|discExt h| ≤ 1` when `|h| ≤ 1` on the closed unit disc. -/
theorem abs_discExt_le {h : ℂ → ℝ} (hb : ∀ z ∈ closedBall (0 : ℂ) 1, |h z| ≤ 1) (t : ℂ) :
    |discExt h t| ≤ 1 := by
  by_cases ht : t ∈ closedBall (0 : ℂ) 1
  · rw [discExt, indicator_of_mem ht]
    exact hb t ht
  · rw [discExt, indicator_of_notMem ht, abs_zero]
    exact zero_le_one

/-- `discExt h = h` on the closed unit disc. -/
theorem discExt_of_mem {h : ℂ → ℝ} {t : ℂ} (ht : t ∈ closedBall (0 : ℂ) 1) :
    discExt h t = h t := by
  rw [discExt, indicator_of_mem ht]

/-- The bump of radius `ε` used as a mollifier. -/
def mollifier {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : ℂ) :=
  ⟨ε / 2, ε, by positivity, by linarith⟩

/-- The mollified function is smooth. -/
theorem contDiff_mollify {h : ℂ → ℝ} (hcont : ContinuousOn h (closedBall 0 1)) {ε : ℝ}
    (hε : 0 < ε) : ContDiff ℝ ∞ (discExt h ⋆ (mollifier hε).normed volume) :=
  (mollifier hε).hasCompactSupport_normed.contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) (integrable_discExt hcont).locallyIntegrable
    ((mollifier hε).contDiff_normed (n := ⊤))

/-- `∫ ρ_ε(x - t) dt = 1`. -/
theorem integral_mollifier_sub {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∫ t, (mollifier hε).normed volume (x - t) = 1 := by
  rw [integral_sub_left_eq_self ((mollifier hε).normed volume) volume x]
  exact (mollifier hε).integral_normed

/-- `|h_ε| ≤ 1`. -/
theorem abs_mollify_le {h : ℂ → ℝ} (hb : ∀ z ∈ closedBall (0 : ℂ) 1, |h z| ≤ 1) {ε : ℝ}
    (hε : 0 < ε) (x : ℂ) : |(discExt h ⋆ (mollifier hε).normed volume) x| ≤ 1 := by
  set B : ContDiffBump (0 : ℂ) := mollifier hε with hB
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hg : Integrable (fun t => B.normed volume (x - t)) :=
    B.integrable_normed.comp_sub_left x
  calc |∫ t, discExt h t * B.normed volume (x - t)|
      = ‖∫ t, discExt h t * B.normed volume (x - t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, B.normed volume (x - t) := by
        refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun t => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (B.nonneg_normed _)]
        calc |discExt h t| * B.normed volume (x - t) ≤ 1 * B.normed volume (x - t) :=
              mul_le_mul_of_nonneg_right (abs_discExt_le hb t) (B.nonneg_normed _)
          _ = B.normed volume (x - t) := one_mul _
    _ = 1 := integral_mollifier_sub hε x

/-- **`|Δ h_ε| ≤ 1` from the distributional bound.**  For `|x| + ε < 1`, the function
`t ↦ ρ_ε(x - t)` is a test function on the open unit disc, and `Δ h_ε(x)` is the pairing of `h`
with its Laplacian. -/
theorem abs_laplacian_mollify_le {h : ℂ → ℝ} (hcont : ContinuousOn h (closedBall 0 1))
    (hΔ : ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 1 →
      |∫ z, h z * Δ φ z| ≤ ∫ z, |φ z|)
    {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : ‖x‖ + ε < 1) :
    |Δ (discExt h ⋆ (mollifier hε).normed volume) x| ≤ 1 := by
  set B : ContDiffBump (0 : ℂ) := mollifier hε with hB
  have hρs : ContDiff ℝ ∞ (B.normed volume) := B.contDiff_normed (n := ⊤)
  have hρc : HasCompactSupport (B.normed volume) := B.hasCompactSupport_normed
  rw [laplacian_convolution_right (integrable_discExt hcont).locallyIntegrable hρc hρs x,
    convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  set φ : ℂ → ℝ := fun t => B.normed volume (x - t) with hφ
  have hφs : ContDiff ℝ ∞ φ := hρs.comp (contDiff_const.sub contDiff_id)
  have hsupp : Function.support φ ⊆ ball x ε := by
    intro t ht
    have h1 : x - t ∈ Function.support (B.normed volume) := ht
    rw [B.support_normed_eq, mem_ball, dist_zero_right] at h1
    rw [mem_ball, dist_eq_norm, norm_sub_rev]
    exact h1
  have htsupp : tsupport φ ⊆ closedBall x ε :=
    (closure_mono hsupp).trans closure_ball_subset_closedBall
  have hφc : HasCompactSupport φ :=
    (isCompact_closedBall x ε).of_isClosed_subset (isClosed_tsupport φ) htsupp
  have hφD : tsupport φ ⊆ ball 0 1 := by
    refine htsupp.trans fun t ht => ?_
    rw [mem_closedBall, dist_eq_norm] at ht
    rw [mem_ball, dist_zero_right]
    calc ‖t‖ = ‖(t - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖t - x‖ + ‖x‖ := norm_add_le _ _
      _ < 1 := by linarith
  have hΔφ : ∀ t, Δ φ t = Δ (B.normed volume) (x - t) := fun t =>
    laplacian_comp_sub_left (hρs.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) x t
  have heq : ∫ t, discExt h t * Δ (B.normed volume) (x - t) = ∫ t, h t * Δ φ t := by
    congr 1
    funext t
    by_cases ht : t ∈ tsupport φ
    · rw [hΔφ t, discExt_of_mem (ball_subset_closedBall (hφD ht))]
    · have h0 : Δ φ t = 0 :=
        SGPT.Foundations.Analysis.Pending.LelongPoincareOneVariable.laplacian_eq_zero_of_notMem_tsupport
          ht
      rw [← hΔφ t, h0, mul_zero, mul_zero]
  have hint1 : ∫ t, |φ t| = 1 := by
    have : (fun t => |φ t|) = fun t => B.normed volume (x - t) :=
      funext fun t => abs_of_nonneg (B.nonneg_normed _)
    rw [this]
    exact integral_mollifier_sub hε x
  rw [heq, ← hint1]
  exact hΔ φ hφs hφc hφD

/-- **`h_ε → h` at continuity points.**  If `|h(y) - h(x)| ≤ δ` for `|y - x| < ε` and
`|x| + ε ≤ 1`, then `|h_ε(x) - h(x)| ≤ δ`. -/
theorem abs_mollify_sub_le {h : ℂ → ℝ} (hcont : ContinuousOn h (closedBall 0 1)) {ε : ℝ}
    (hε : 0 < ε) {x : ℂ} {δ : ℝ} (hx : ‖x‖ + ε ≤ 1)
    (hδ : ∀ y, dist y x < ε → |h y - h x| ≤ δ) :
    |(discExt h ⋆ (mollifier hε).normed volume) x - h x| ≤ δ := by
  set B : ContDiffBump (0 : ℂ) := mollifier hε with hB
  have hswap : (discExt h ⋆ B.normed volume) x =
      (B.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] discExt h) x := by
    rw [convolution_def, convolution_lsmul_swap]
    congr 1
    funext t
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_comm]
  have hx1 : x ∈ closedBall (0 : ℂ) 1 := by
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hdist := B.dist_normed_convolution_le (μ := volume) (x₀ := x) (ε := δ)
    (integrable_discExt hcont).aestronglyMeasurable (fun y hy => by
      have hy' : dist y x < ε := hy
      have hy1 : y ∈ closedBall (0 : ℂ) 1 := by
        rw [mem_closedBall, dist_zero_right]
        have : ‖y‖ ≤ ‖x‖ + dist y x := by
          rw [dist_eq_norm]
          calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
            _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
        linarith
      rw [discExt_of_mem hy1, discExt_of_mem hx1, Real.dist_eq]
      exact hδ y hy')
  rw [hswap, ← discExt_of_mem (h := h) hx1, ← Real.dist_eq]
  exact hdist

end Lipschitz

open Lipschitz in
/-- **`tok-wn:lipschitz`** (WN21 Corollary 7.6): there is a universal constant `A` such that every
function `h` continuous on the closed unit disc of `ℂ` with `|h| ≤ 1` there and `|Δh| ≤ 1` as
distributions on the open unit disc satisfies `|h(w) - h(0)| ≤ A |w|` for `|w| ≤ 1/2`. -/
theorem lipschitzOfLaplacianStatement : LipschitzOfLaplacianStatement := by
  obtain ⟨A₀, hA₀⟩ := exists_lipschitz_of_smooth
  refine ⟨A₀, ?_⟩
  intro h hcont hb hΔ w hw
  have hcAt : ∀ x : ℂ, ‖x‖ ≤ 1 / 2 → ContinuousAt h x := by
    intro x hx
    refine hcont.continuousAt (closedBall_mem_nhds_of_mem ?_)
    rw [mem_ball, dist_zero_right]
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hδ2 : 0 < δ / 2 := half_pos hδ
  obtain ⟨ε₁, hε₁, H₁⟩ := Metric.continuousAt_iff.mp (hcAt w hw) (δ / 2) hδ2
  obtain ⟨ε₂, hε₂, H₂⟩ := Metric.continuousAt_iff.mp (hcAt 0 (by simp)) (δ / 2) hδ2
  set ε : ℝ := min (min ε₁ ε₂) (1 / 16) with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) (by norm_num)
  have hε1 : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hε16 : ε ≤ 1 / 16 := min_le_right _ _
  set m : ℂ → ℝ := discExt h ⋆ (mollifier hε).normed volume with hm
  have hmw : |m w - h w| ≤ δ / 2 :=
    abs_mollify_sub_le hcont hε (by linarith) fun y hy =>
      (H₁ (lt_of_lt_of_le hy hε1)).le.trans' (by rw [Real.dist_eq])
  have hm0 : |m 0 - h 0| ≤ δ / 2 :=
    abs_mollify_sub_le hcont hε (by simp only [norm_zero]; linarith) fun y hy =>
      (H₂ (lt_of_lt_of_le hy hε2)).le.trans' (by rw [Real.dist_eq])
  have hlip := hA₀ m (contDiff_mollify hcont hε) (fun x _ => abs_mollify_le hb hε x)
    (fun x hx => abs_laplacian_mollify_le hcont hΔ hε (by
      rw [mem_ball, dist_zero_right] at hx
      linarith)) w hw
  calc |h w - h 0| = |(m w - m 0) - (m w - h w) + (m 0 - h 0)| := by ring_nf
    _ ≤ |m w - m 0| + |m w - h w| + |m 0 - h 0| := by
        refine (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _) |>.trans ?_
        exact le_of_eq (by ring)
    _ ≤ A₀ * ‖w‖ + δ / 2 + δ / 2 := by linarith
    _ = A₀ * ‖w‖ + δ := by ring

end SGPT.Okounkov.TranscendentalWN
