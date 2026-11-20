import SGPT.Foundations.Analysis.Pending.LocalUniformLogarithmicExponentBound
import SGPT.Foundations.Analysis.Pending.ThetaPshUniformL1Bound

set_option autoImplicit false

/-! # Internally produced uniform chart logarithmic bounds for normalized PSH families -/

open Metric Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.NormalizedPshChartLogarithmicBound
open FirstPass ThetaPshUniformL1Bound

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [CompactSpace M] [ConnectedSpace M]
  {θ : SmoothRealForm n M 2}

/-- Compact connected Harnack transfer and a genuine annular first moment
produce the uniform logarithmic-exponent bound; no point-bound certificate is an input. -/
theorem exists_uniform_log_exponent_bound (hn : 0 < n)
    (hθ : HasSmoothLocalPotentials θ) (H : HarnackBall θ) (c : ℝ) :
    ∃ K : ℝ, ∀ u : M → EReal, ThetaPlurisubharmonic θ u → (∀ x, u x ≤ 0) →
      (∃ x₀, ((-c : ℝ) : EReal) ≤ u x₀) →
      ∀ p ∈ ball H.z (H.r / 4), ∀ γ C ρ : ℝ, 0 < ρ →
        (∀ w : ComplexModel n, 0 < ‖w - p‖ → ‖w - p‖ < ρ →
          H.corrected u w ≤ ((γ * Real.log ‖w - p‖ + C : ℝ) : EReal)) → γ ≤ K := by
  classical
  let O : Set (ComplexModel n) := ball H.z H.r \ closedBall H.z (3 * H.r / 4)
  have hOopen : IsOpen O := isOpen_ball.inter isClosed_closedBall.isOpen_compl
  have hOne : O.Nonempty := by
    let e : ComplexModel n := EuclideanSpace.single ⟨0, hn⟩ 1
    have he : ‖e‖ = 1 := by simp [e]
    let y : ComplexModel n := H.z + ((7 * H.r / 8 : ℝ) : ℂ) • e
    have hy : dist y H.z = 7 * H.r / 8 := by
      simp only [y, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by linarith [H.r_pos])
    refine ⟨y, ?_⟩
    change y ∈ ball H.z H.r ∧ y ∉ closedBall H.z (3 * H.r / 4)
    rw [mem_ball, mem_closedBall, hy]
    constructor <;> linarith [H.r_pos]
  obtain ⟨c₀, hc₀⟩ := exists_forall_mem_set_le hθ H c
  obtain ⟨c₁, hc₁⟩ := H.exists_point O hOopen hOne (fun _ hx => hx.1) c₀
  obtain ⟨A, P, hAP⟩ := H.exists_bounds
  refine ⟨(A + (c₁ - P)) / (Real.log (2 * H.r) - Real.log (5 * H.r / 4)),
    fun u hu hle hex p hp γ C ρ hρ hadm => ?_⟩
  obtain ⟨x, hx, hcx⟩ := hc₀ u hu hle hex
  have hpoint : ∃ y₀ ∈ ball H.z H.r, ((-c₀ : ℝ) : EReal) ≤ u (H.e.val.symm y₀) := by
    refine ⟨H.e.val x, hx.2, ?_⟩
    rw [H.e.val.left_inv hx.1]
    exact hcx
  obtain ⟨y, hyO, hcy⟩ := hc₁ u hu hle hpoint
  have hyball : dist y H.z < H.r := mem_ball.mp hyO.1
  have hynot : 3 * H.r / 4 < dist y H.z := lt_of_not_ge (fun h => hyO.2 (mem_closedBall.mpr h))
  have hpdist : dist p H.z < H.r / 4 := mem_ball.mp hp
  have hyneq : y ≠ p := by
    intro h
    rw [h] at hynot
    linarith [H.r_pos]
  have hyr : ‖y - p‖ ≤ 5 * H.r / 4 := by
    rw [← dist_eq_norm]
    have htri := dist_triangle y H.z p
    rw [dist_comm H.z p] at htri
    linarith
  have hclosed : closedBall p (2 * H.r) ⊆ H.W := by
    intro w hw
    apply H.closedBall_subset
    apply mem_closedBall.mpr
    have hw' := mem_closedBall.mp hw
    have htri := dist_triangle w p H.z
    linarith [H.r_pos]
  have hupper : ∀ w ∈ closedBall p (2 * H.r), H.corrected u w ≤ (A : EReal) := by
    intro w hw
    have hbig : w ∈ closedBall H.z (3 * H.r) := by
      apply mem_closedBall.mpr
      have hw' := mem_closedBall.mp hw
      have htri := dist_triangle w p H.z
      linarith [H.r_pos]
    calc H.corrected u w = u (H.e.val.symm w) + (H.ρ w : EReal) := rfl
      _ ≤ 0 + (A : EReal) := add_le_add (hle _) (EReal.coe_le_coe_iff.mpr (hAP w hbig).2)
      _ = (A : EReal) := zero_add _
  have hlower : ((-(c₁ - P) : ℝ) : EReal) ≤ H.corrected u y := by
    have hPy : P ≤ H.ρ y := (hAP y (H.ball_subset_closedBall hyO.1)).1
    calc ((-(c₁ - P) : ℝ) : EReal) = ((-c₁ : ℝ) : EReal) + (P : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
      _ ≤ u (H.e.val.symm y) + (H.ρ y : EReal) :=
        add_le_add hcy (EReal.coe_le_coe_iff.mpr hPy)
      _ = H.corrected u y := rfl
  have hpsh : PlurisubharmonicOn (H.corrected u) H.W :=
    ThetaPshDecreasingLimit.plurisubharmonicOn_corrected_of_thetaPlurisubharmonic hu H.e H.potential
  exact LocalUniformLogarithmicExponentBound.log_exponent_le_uniform_point_bound hpsh hclosed
    hyr (by linarith [H.r_pos]) hyneq hupper hlower hρ hadm

end
end SGPT.Foundations.Analysis.Pending.NormalizedPshChartLogarithmicBound
