import SGPT.GAGA.H0LocalCorrectionC1

/-!
# Corrections that interpolate along a non-integrable pole set


Let `Ψ` be plurisubharmonic on `B(0, R) ⊆ ℂ^m` and `a` a `C¹` function on `B(0, R)` with finite
weighted energy `∫_{B(0,R)} |∂̄a|² e^{-Ψ - |z|²} < ∞`.  The local `L²` correction
(`SGPT.GAGA.H0.localBallCorrectionC1`) gives `G` holomorphic on `B(0, r)` with
`∫_{B(0,r)} |a - G|² e^{-Ψ - |z|²} < ∞`.  If `e^{-Ψ}` is not integrable on any ball around a
point `p` of a set `Y`, the continuous function `a - G` must vanish at `p`: this is how the
`L²` method forces the correction to interpolate the datum along `Y`
(`exists_holomorphic_eq_on_of_nonintegrable`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.PSH.GlobalL2

variable {m : ℕ}

/-- **The `L²` correction interpolates along non-integrable poles.**  Let `Ψ` be
plurisubharmonic on `B(0, R)`, `a` of class `C¹` on `B(0, R)` with
`∫_{B(0,R)} |∂̄a|² e^{-Ψ - |z|²} < ∞`, and `Y` a set such that `e^{-Ψ}` is not integrable on any
ball around any point of `Y ∩ B(0, r)`, `0 < r < R`.  Then there is `H` holomorphic on
`B(0, r)` with `H = a` on `Y ∩ B(0, r)`. -/
theorem exists_holomorphic_eq_on_of_nonintegrable {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {Ψ : ComplexModel m → EReal} (hΨ : PlurisubharmonicOn Ψ (ball 0 R))
    {a : ComplexModel m → ℂ} (ha : ContDiffOn ℝ 1 a (ball 0 R))
    (hE : ∫⁻ z in ball (0 : ComplexModel m) R,
      ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ 1 0 z ≠ ⊤)
    {Y : Set (ComplexModel m)}
    (hY : ∀ p ∈ Y, p ∈ ball (0 : ComplexModel m) r → ∀ δ : ℝ, 0 < δ →
      ∫⁻ z in ball p δ, multiplierWeight 1 (Ψ z) = ⊤) :
    ∃ H : ComplexModel m → ℂ, DifferentiableOn ℂ H (ball 0 r) ∧
      ∀ p ∈ Y, p ∈ ball (0 : ComplexModel m) r → H p = a p := by
  obtain ⟨G, hG, hGb⟩ := localBallCorrectionC1 0 r R hr hrR 1 one_pos Ψ hΨ a ha
  have hfin : ∫⁻ z in ball (0 : ComplexModel m) r, ENNReal.ofReal (‖a z - G z‖ ^ 2) *
      ballWeight Ψ 1 0 z ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE) hGb
  refine ⟨G, hG, fun p hpY hp => ?_⟩
  by_contra hne
  have hpos : 0 < ‖a p - G p‖ ^ 2 / 2 := by
    have : a p - G p ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    positivity
  -- `|a - G|² ≥ |a p - G p|² / 2` near `p`
  have hcont : ContinuousAt (fun z => ‖a z - G z‖ ^ 2) p := by
    have hrR' : ball (0 : ComplexModel m) r ⊆ ball 0 R := ball_subset_ball hrR.le
    have h1 : ContinuousAt a p :=
      ha.continuousOn.continuousAt (isOpen_ball.mem_nhds (hrR' hp))
    have h2 : ContinuousAt G p := hG.continuousOn.continuousAt (isOpen_ball.mem_nhds hp)
    exact ((h1.sub h2).norm).pow 2
  have hev : ∀ᶠ z in 𝓝 p, ‖a p - G p‖ ^ 2 / 2 < ‖a z - G z‖ ^ 2 :=
    hcont.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff_ball.mp
    (hev.and (isOpen_ball.mem_nhds hp))
  -- the contradiction
  have hinf := hY p hpY hp δ hδ
  set c : ℝ≥0∞ := ENNReal.ofReal (‖a p - G p‖ ^ 2 / 2) * ENNReal.ofReal (Real.exp (-R ^ 2))
    with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr hpos).ne' (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hle : c * ∫⁻ z in ball p δ, multiplierWeight 1 (Ψ z) ≤
      ∫⁻ z in ball (0 : ComplexModel m) r, ENNReal.ofReal (‖a z - G z‖ ^ 2) *
        ballWeight Ψ 1 0 z := by
    rw [← lintegral_const_mul' _ _ (by
      rw [hc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    have hsub : ball p δ ⊆ ball (0 : ComplexModel m) r := fun z hz => (hδb z hz).2
    refine le_trans ?_ (lintegral_mono_set hsub)
    refine setLIntegral_mono' isOpen_ball.measurableSet fun z hz => ?_
    have hzR : z ∈ ball (0 : ComplexModel m) R := ball_subset_ball hrR.le (hsub hz)
    have hΨz : Ψ z ≠ ⊤ := (hΨ z hzR).ne_top
    rw [ballWeight_eq_mul hΨz 1 0, sub_zero, one_mul]
    have h1 : ENNReal.ofReal (‖a p - G p‖ ^ 2 / 2) ≤ ENNReal.ofReal (‖a z - G z‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (hδb z hz).1.le
    have h2 : ENNReal.ofReal (Real.exp (-R ^ 2)) ≤ ENNReal.ofReal (Real.exp (-‖z‖ ^ 2)) := by
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have : ‖z‖ < R := mem_ball_zero_iff.mp hzR
      nlinarith [norm_nonneg z]
    calc c * multiplierWeight 1 (Ψ z)
        = ENNReal.ofReal (‖a p - G p‖ ^ 2 / 2) *
            (multiplierWeight 1 (Ψ z) * ENNReal.ofReal (Real.exp (-R ^ 2))) := by
          rw [hc]; ring
      _ ≤ ENNReal.ofReal (‖a z - G z‖ ^ 2) *
            (multiplierWeight 1 (Ψ z) * ENNReal.ofReal (Real.exp (-‖z‖ ^ 2))) := by
          gcongr
  rw [hinf, ENNReal.mul_top hc0] at hle
  exact hfin (top_le_iff.mp hle)

end SGPT.GAGA.H0
