import SGPT.Foundations.Analysis.Pending.LocalUniformLogarithmicExponentBound
import SGPT.Foundations.Analysis.Pending.LelongNumberChartTransport

set_option autoImplicit false

/-! # Actual upper semicontinuity of the pointwise logarithmic Lelong reader -/

open Metric Set Filter
open scoped Topology ENNReal NNReal

namespace SGPT.Foundations.Analysis.Pending.PshLelongUpperSemicontinuity

open FirstPass FirstPass.NonKahlerLocus LelongNumberChartTransport

noncomputable section

variable {n : ℕ}

/-- A strict finite threshold for the actual logarithmic Lelong reader
persists near a point of an actual open PSH domain. -/
theorem eventually_lelongNumber_lt_of_lt {u : ComplexModel n → EReal}
    {Ω : Set (ComplexModel n)} (hu : PlurisubharmonicOn u Ω) (hΩ : IsOpen Ω)
    {x : ComplexModel n} (hx : x ∈ Ω) {a : ℝ}
    (hν : lelongNumber (n := n) u x < ENNReal.ofReal a) :
    ∀ᶠ y in 𝓝 x, lelongNumber (n := n) u y < ENNReal.ofReal a := by
  classical
  have ha : 0 < a := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hν)
  obtain ⟨S, hS, hSsub⟩ := Metric.isOpen_iff.mp hΩ x hx
  let R : ℝ := S / 3
  have hR : 0 < R := by dsimp [R]; positivity
  have hclosed : closedBall x (2 * R) ⊆ Ω := by
    intro z hz
    apply hSsub
    apply mem_ball.mpr
    have hz' := mem_closedBall.mp hz
    dsimp [R] at hz'
    linarith
  obtain ⟨z₀, hz₀, hmax⟩ := (hu.upperSemicontinuousOn.mono hclosed).exists_isMaxOn
    ⟨x, mem_closedBall_self (by positivity : 0 ≤ 2 * R)⟩ (isCompact_closedBall x (2 * R))
  obtain ⟨A₀, hA₀, _⟩ := EReal.exists_rat_btwn_of_lt
    (lt_top_iff_ne_top.mpr ((hu z₀ (hclosed hz₀)).ne_top))
  let A : ℝ := A₀
  have hA : ∀ z ∈ closedBall x (2 * R), u z ≤ (A : EReal) :=
    fun z hz => (hmax hz).trans hA₀.le
  let C : ℝ := A - a * Real.log R
  have hex : ∃ p : ComplexModel n, 0 < ‖p - x‖ ∧ ‖p - x‖ < R / 2 ∧
      (((a * Real.log ‖p - x‖ + C : ℝ)) : EReal) < u p := by
    by_contra hno
    have hall (p : ComplexModel n) (hp0 : 0 < ‖p - x‖) (hpR : ‖p - x‖ < R / 2) :
        u p ≤ (((a * Real.log ‖p - x‖ + C : ℝ)) : EReal) :=
      le_of_not_gt (fun hgt => hno ⟨p, hp0, hpR, hgt⟩)
    have hevent : ∀ᶠ p in 𝓝[≠] x,
        u p ≤ (((a * Real.log
          ‖(complexChartAt (n := n) x).val p - (complexChartAt (n := n) x).val x‖ + C : ℝ)) : EReal) := by
      filter_upwards [eventually_mem_chart_ball (n := n) (M := ComplexModel n)
        (x := x) (show 0 < R / 2 by positivity)] with p hp
      simpa [complexChartAt, chartAt_self_eq] using
        hall p (by simpa [complexChartAt, chartAt_self_eq] using hp.2.1)
          (by simpa [complexChartAt, chartAt_self_eq] using hp.2.2)
    exact hν.not_ge (ofReal_le_lelongNumber ha.le hevent)
  obtain ⟨p, hp0, hpR, hpbad⟩ := hex
  have hpbig : p ∈ closedBall x (2 * R) := by
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    linarith
  have hptop : u p ≠ ⊤ := (hu p (hclosed hpbig)).ne_top
  have hpbot : u p ≠ ⊥ := by
    intro h
    rw [h] at hpbad
    exact not_lt_bot hpbad
  let B : ℝ := (u p).toReal
  have hB : (B : EReal) = u p := EReal.coe_toReal hptop hpbot
  have hBA : B ≤ A := EReal.coe_le_coe_iff.mp (hB ▸ hA p hpbig)
  have hpR' : ‖p - x‖ < R := by linarith
  have hden : 0 < Real.log R - Real.log ‖p - x‖ :=
    sub_pos.mpr (Real.log_lt_log hp0 hpR')
  have hbadreal : a * Real.log ‖p - x‖ + C < B := by
    rw [← hB] at hpbad
    exact EReal.coe_lt_coe_iff.mp hpbad
  let b : ℝ := (A - B) / (Real.log R - Real.log ‖p - x‖)
  have hba : b < a := by
    apply (div_lt_iff₀ hden).mpr
    dsimp [C] at hbadreal
    linarith
  let s : ℝ := (b + a) / 2
  have hbs : b < s := by dsimp [s]; linarith
  have hsa : s < a := by dsimp [s]; linarith
  have hn : ContinuousAt (fun y : ComplexModel n => ‖p - y‖) x := by fun_prop
  have hratio : ContinuousAt
      (fun y : ComplexModel n => (A - B) / (Real.log R - Real.log ‖p - y‖)) x :=
    continuousAt_const.div (continuousAt_const.sub (hn.log (ne_of_gt hp0))) (ne_of_gt hden)
  have heventratio : ∀ᶠ y in 𝓝 x,
      (A - B) / (Real.log R - Real.log ‖p - y‖) < s :=
    hratio.eventually (isOpen_Iio.mem_nhds hbs)
  have heventpos : ∀ᶠ y in 𝓝 x, 0 < ‖p - y‖ :=
    hn.eventually (isOpen_Ioi.mem_nhds hp0)
  have heventR : ∀ᶠ y in 𝓝 x, ‖p - y‖ < R :=
    hn.eventually (isOpen_Iio.mem_nhds hpR')
  filter_upwards [heventratio, heventpos, heventR,
    isOpen_ball.mem_nhds (mem_ball_self (show 0 < R / 2 by positivity))] with y hys hypos hypR hyball
  have hysub : closedBall y R ⊆ closedBall x (2 * R) := by
    intro z hz
    apply mem_closedBall.mpr
    have hz' := mem_closedBall.mp hz
    have hy' := mem_ball.mp hyball
    have htri := dist_triangle z y x
    linarith
  have hνy : lelongNumber (n := n) u y ≤ ENNReal.ofReal s := by
    apply lelongNumber_le_ofReal
    intro γ hγ
    obtain ⟨Cγ, hCγ⟩ := hγ
    obtain ⟨ρ, hρ, hρbound⟩ := exists_chart_radius_of_eventually (n := n) hCγ
    have hadm (z : ComplexModel n) (hz0 : 0 < ‖z - y‖) (hzρ : ‖z - y‖ < ρ) :
        u z ≤ ((((γ : ℝ) * Real.log ‖z - y‖ + Cγ : ℝ)) : EReal) := by
      have hb := hρbound z
        (by simpa [complexChartAt, chartAt_self_eq] using hz0)
        (by simpa [complexChartAt, chartAt_self_eq] using hzρ)
      simpa [complexChartAt, chartAt_self_eq] using hb.2
    exact (LocalUniformLogarithmicExponentBound.log_exponent_le_of_point_bounds hu
      (hysub.trans hclosed) hypR (by exact sub_ne_zero.mp (norm_pos_iff.mp hypos))
      (fun z hz => hA z (hysub hz)) hB.le hρ hadm).trans hys.le
  exact hνy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff ha).mpr hsa)

/-- The actual extended-nonnegative logarithmic Lelong reader of a genuine
PSH function is upper semicontinuous on its actual open domain. -/
theorem upperSemicontinuousOn_lelongNumber {u : ComplexModel n → EReal}
    {Ω : Set (ComplexModel n)} (hu : PlurisubharmonicOn u Ω) (hΩ : IsOpen Ω) :
    UpperSemicontinuousOn (fun x => lelongNumber (n := n) u x) Ω := by
  intro x hx b hb
  obtain ⟨a, ha, hab⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hb
  have h := eventually_lelongNumber_lt_of_lt hu hΩ hx (a := (a : ℝ))
    (by simpa only [ENNReal.ofReal_coe_nnreal] using ha)
  exact (h.mono fun y hy => hy.trans (by simpa only [ENNReal.ofReal_coe_nnreal] using hab)).filter_mono
    nhdsWithin_le_nhds

end
end SGPT.Foundations.Analysis.Pending.PshLelongUpperSemicontinuity
