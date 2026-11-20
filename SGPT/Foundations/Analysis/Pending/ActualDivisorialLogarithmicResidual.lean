import SGPT.Foundations.Analysis.Pending.ActualClosedThresholdDivisorialSliceBound
import SGPT.Foundations.Analysis.Pending.ActualAnalyticFactorResidualPsh

set_option autoImplicit false

/-! # Removing the exact divisorial logarithm

The original point Lelong lower bounds produce both the residual upper bound
and its genuine PSH extension. No residual, noncollapse or mass certificate
is an input; this local ingredient does not assert the global P/I identity.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.ActualDivisorialLogarithmicResidual

open FirstPass PshCodimTwoExtension ActualClosedThresholdDivisorialSliceBound
  ActualAnalyticFactorResidualPsh

noncomputable section

/-- The finite logarithmic correction has an actual PSH extension at the exact
native coordinate growth coefficient, even for identically bottom inputs. -/
theorem coordinate_residual_psh_of_le_lelongNumber {m : ℕ}
    {u : ComplexModel (m + 1) → EReal} {Ω : Set (ComplexModel (m + 1))}
    (hu : PlurisubharmonicOn u Ω) {p : ComplexModel (m + 1)}
    (hp : p (Fin.last m) = 0) {r : ℝ} (hr : 0 < r)
    (hΩ : closedBall p (2 * r) ⊆ Ω) {K : ℝ}
    (hK : ∀ z ∈ closedBall p (2 * r), u z ≤ (K : EReal))
    {a : ℝ≥0}
    (hν : ∀ z ∈ ball p r, z (Fin.last m) = 0 →
      (a : ℝ≥0∞) ≤ FirstPass.NonKahlerLocus.lelongNumber (n := m + 1) u z) :
    let A : Set (ComplexModel (m + 1)) := {z | z (Fin.last m) = 0}
    let ψ := fun z => u z +
      ((-(a : ℝ) / 2 * Real.log (Complex.normSq (z (Fin.last m))) : ℝ) : EReal)
    let q := extension A ψ
    PlurisubharmonicOn q (ball p r) ∧
      (∀ z ∈ ball p r, q z ≤ ((K - (a : ℝ) * Real.log r : ℝ) : EReal)) ∧
      EqOn q ψ (ball p r \ A) := by
  classical
  let A : Set (ComplexModel (m + 1)) := {z | z (Fin.last m) = 0}
  let ψ := fun z => u z +
    ((-(a : ℝ) / 2 * Real.log (Complex.normSq (z (Fin.last m))) : ℝ) : EReal)
  let q := extension A ψ
  change PlurisubharmonicOn q (ball p r) ∧ _
  have hsmall : ball p r ⊆ Ω :=
    ((ball_subset_ball (by linarith : r ≤ 2 * r)).trans ball_subset_closedBall).trans hΩ
  have hd : DifferentiableOn ℂ (fun z : ComplexModel (m + 1) => z (Fin.last m))
      (ball p r) := (EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).differentiable.differentiableOn
  have hW : IsOpen (ball p r \ A) :=
    hd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hψ : PlurisubharmonicOn ψ (ball p r \ A) :=
    ((hu.mono hsmall).mono sdiff_subset).add
      (plurisubharmonicOn_real_log_normSq_off_zeros isOpen_ball hd (-(a : ℝ) / 2))
  have hbound (z : ComplexModel (m + 1)) (hz : z ∈ ball p r) (hzA : z ∉ A) :
      ψ z ≤ ((K - (a : ℝ) * Real.log r : ℝ) : EReal) := by
    have hz0 : z (Fin.last m) ≠ 0 := hzA
    have hs := le_log_last_add_of_le_lelongNumber hu hp hr hΩ hK hν hz hz0
    have hlog : Real.log (Complex.normSq (z (Fin.last m))) =
        2 * Real.log ‖z (Fin.last m)‖ := by
      rw [Complex.normSq_eq_norm_sq, Real.log_pow]
      norm_num
    calc ψ z ≤ (((a : ℝ) * Real.log ‖z (Fin.last m)‖ +
        (K - (a : ℝ) * Real.log r) : ℝ) : EReal) +
          ((-(a : ℝ) / 2 * Real.log (Complex.normSq (z (Fin.last m))) : ℝ) : EReal) :=
        add_le_add hs le_rfl
      _ = ((K - (a : ℝ) * Real.log r : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        congr 1
        rw [hlog]
        ring
  have hlocal : PshHypersurfaceRemovable.LocallyBoundedAboveOff A (ball p r) ψ := by
    intro x hx
    exact ⟨ball p r, isOpen_ball.mem_nhds hx, K - (a : ℝ) * Real.log r, hbound⟩
  have hq : PlurisubharmonicOn q (ball p r) :=
    PshAnalyticRemovable.plurisubharmonicOn_extension_of_zeroLocus isOpen_ball hψ hlocal
      (g := fun _ : Fin 1 => fun z : ComplexModel (m + 1) => z (Fin.last m))
      (fun _ => hd) (by intro z _; simp [A])
  refine ⟨hq, ?_, ?_⟩
  · intro z hz
    change uscRegularization (fun y => if y ∈ A then (⊥ : EReal) else ψ y) z ≤
      ((K - (a : ℝ) * Real.log r : ℝ) : EReal)
    exact (uscRegularization_le_localSup
      (fun y => if y ∈ A then (⊥ : EReal) else ψ y) (isOpen_ball.mem_nhds hz)).trans
      (iSup₂_le fun y hy => by
        by_cases hyA : y ∈ A
        · simp only [if_pos hyA]
          exact bot_le
        · simpa only [if_neg hyA] using hbound y hy hyA)
  · intro z hz
    exact extension_eq hψ hW hz

end
end SGPT.Foundations.Analysis.Pending.ActualDivisorialLogarithmicResidual
