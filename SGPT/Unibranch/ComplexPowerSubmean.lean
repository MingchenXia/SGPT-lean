import SGPT.PSH.SubharmonicStrip
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Genuine extended circle submean descent under an actual finite power.
Blueprint: complex-power-submean.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis
namespace SGPT.Unibranch.RamifiedPower

/-- Actual infinite-valued periodic angular integral under a nonzero
integer cover; no finite-integrability substitute is used. -/
theorem lintegral_periodic_mul {T : ℝ} (hT : 0 < T)
    {f : ℝ → ℝ≥0∞} (hf : Function.Periodic f T) (hm : Measurable f)
    (k : ℤ) (hk : k ≠ 0) :
    (∫⁻ t in Ioc 0 T,f ((k : ℝ)*t)) = ∫⁻ t in Ioc 0 T,f t := by
  let ramifiedPowerPositivePeriod : Fact (0 < T) := ⟨hT⟩
  have hmlift : Measurable hf.lift := by
    have heq : hf.lift = fun x : AddCircle T =>
        f ((AddCircle.measurableEquivIoc T 0 x).val) := by
      funext x
      let q := AddCircle.measurableEquivIoc T 0
      have hx : ((q x).val : AddCircle T) = x := q.symm_apply_apply x
      calc
        hf.lift x = hf.lift (((q x).val : ℝ) : AddCircle T) := congrArg hf.lift hx.symm
        _ = f ((q x).val) := hf.lift_coe _
    rw [heq]
    exact hm.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIoc T 0).measurable)
  have hmp := Measure.measurePreserving_zsmul (volume : Measure (AddCircle T)) hk
  have h1 := AddCircle.lintegral_preimage T 0 (fun x : AddCircle T => hf.lift (k • x))
  have h2 := AddCircle.lintegral_preimage T 0 hf.lift
  have hc := hmp.lintegral_comp hmlift
  have hreal (t : ℝ) : hf.lift (k • (t : AddCircle T)) = f ((k : ℝ)*t) := by
    rw [← QuotientAddGroup.mk_zsmul,Function.Periodic.lift_coe,zsmul_eq_mul]
  simp only [zero_add,hreal,Function.Periodic.lift_coe] at h1 h2
  exact h1.trans (hc.trans h2.symm)

/-- Literal deficit identity for the SAME function under an actual finite
ramified power, retaining poles and infinite lower integrals. -/
theorem circleDeficit_pow {u : ℂ → EReal} (hu : Measurable u)
    (k : ℕ) (hk : 0 < k) (r C : ℝ) :
    circleDeficit (fun z : ℂ => u (z^k)) 0 1 r C =
      circleDeficit u 0 1 (r^k) C := by
  let f : ℝ → ℝ≥0∞ := fun t => ((C : EReal)-u (circleMap 0 (r^k) t)).toENNReal
  have hf : Function.Periodic f (2*Real.pi) := by
    intro t
    simp only [f,periodic_circleMap 0 (r^k) t]
  have hm : Measurable f :=
    (measurable_const.sub (hu.comp (continuous_circleMap 0 (r^k)).measurable)).ereal_toENNReal
  have h := lintegral_periodic_mul Real.two_pi_pos hf hm (k : ℤ) (by omega)
  simpa only [circleDeficit,smul_eq_mul,mul_one,zero_add,circleMap_zero_pow,
    Int.cast_natCast,f] using h

/-- The SAME extended circle mean, with its original normalization and bound. -/
theorem circleMean_pow {u : ℂ → EReal} (hu : Measurable u)
    (k : ℕ) (hk : 0 < k) (r C : ℝ) :
    SGPT.PSH.circleMean (fun z : ℂ => u (z^k)) 0 1 r C =
      SGPT.PSH.circleMean u 0 1 (r^k) C := by
  unfold SGPT.PSH.circleMean
  rw [circleDeficit_pow hu k hk]

/-- Exact ORIGINAL branch-point submean descent along the actual finite
power. This is a genuine scalar analytic producer, not a lifting certificate. -/
theorem center_submean_of_comp_pow {u : ℂ → EReal} (hu : Measurable u)
    (k : ℕ) (hk : 0 < k) {R r : ℝ}
    (hcomp : SGPT.PSH.SubharmonicOn (fun z => u (z^k)) (ball 0 R))
    (hr : 0 < r) (hrR : r < R) (C : ℝ)
    (hC : ∀ z ∈ closedBall (0 : ℂ) (r^k),u z ≤ (C : EReal)) :
    u 0 ≤ SGPT.PSH.circleMean u 0 1 (r^k) C := by
  have hD : closedBall (0 : ℂ) r ⊆ ball 0 R := closedBall_subset_ball hrR
  have hbound : ∀ z ∈ closedBall (0 : ℂ) r,u (z^k) ≤ (C : EReal) := by
    intro z hz
    apply hC
    rw [mem_closedBall_zero_iff,norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_zero_iff.mp hz) k
  have h := hcomp.submean 0 r hr hD C hbound
  rw [circleMean_pow hu k hk] at h
  simpa only [zero_pow (Nat.ne_of_gt hk)] using h

end SGPT.Unibranch.RamifiedPower
