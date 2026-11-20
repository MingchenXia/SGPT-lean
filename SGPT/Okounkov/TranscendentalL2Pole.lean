import SGPT.Foundations.Analysis.Pending.LogCutoffLevi
import SGPT.Foundations.Analysis.Pending.HormanderPairingBound
import SGPT.Foundations.Analysis.DistributionRegularization
import SGPT.Foundations.Analysis.Pending.PshRadialRegularization

/-!
# The cut-off logarithmic pole

Plan `tok/RELGEN2/PLAN.md`, part of step P8 (blueprint `l2:cutoff-pole`, chapter
`claude-tok-l2`).

For a smooth compactly supported cut-off `χ₀` on `ℂⁿ` equal to `1` on `B(0, ρ)`, the cut-off pole
at `w₀`, `P(w) = χ₀(w - w₀) log ‖w - w₀‖²`, is smooth off `w₀` and its Levi form is bounded below
by `-C₁ ‖v‖²` with `C₁` independent of `w₀` (`exists_neg_le_leviForm_cutoffPole`): on `B(w₀, ρ)`
it is `log ‖w - w₀‖²`, which is plurisubharmonic, and off `B(w₀, ρ)` it is a translate of a fixed
smooth function supported in a compact set avoiding the pole.
-/

set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

noncomputable section

namespace SGPT.Okounkov.TranscendentalL2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {n : ℕ}

/-- The cut-off pole `P(w) = χ₀(w - w₀) log ‖w - w₀‖²`. -/
def cutoffPole (χ₀ : ComplexModel n → ℝ) (w₀ w : ComplexModel n) : ℝ :=
  χ₀ (w - w₀) * Real.log (‖w - w₀‖ ^ 2)

theorem contDiffAt_cutoffPole {χ₀ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ₀)
    {w₀ w : ComplexModel n} (hw : w ≠ w₀) : ContDiffAt ℝ ∞ (cutoffPole χ₀ w₀) w := by
  have h1 : ContDiffAt ℝ ∞ (fun w : ComplexModel n ↦ χ₀ (w - w₀)) w :=
    (hχ.comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hpos : (‖w - w₀‖ ^ 2) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw))
  have h2 : ContDiffAt ℝ ∞ (fun w : ComplexModel n ↦ Real.log (‖w - w₀‖ ^ 2)) w :=
    (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt).log hpos
  exact h1.mul h2

/-- **The Levi form of the cut-off pole is bounded below uniformly in the pole** (plan P8). -/
theorem exists_neg_le_leviForm_cutoffPole {χ₀ : ComplexModel n → ℝ} (hχ : ContDiff ℝ ∞ χ₀)
    (hχc : HasCompactSupport χ₀) {ρ : ℝ} (hρ : 0 < ρ) (hχ1 : ∀ w ∈ ball 0 ρ, χ₀ w = 1) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ w₀ w : ComplexModel n, w ≠ w₀ → ∀ v,
      -C₁ * ‖v‖ ^ 2 ≤ leviForm (cutoffPole χ₀ w₀) w v := by
  set u : ComplexModel n → ℝ := cutoffPole χ₀ 0 with hu
  have hO : IsOpen ({0}ᶜ : Set (ComplexModel n)) := isOpen_compl_singleton
  have hus : ContDiffOn ℝ ∞ u {0}ᶜ := fun w hw ↦ (contDiffAt_cutoffPole hχ hw).contDiffWithinAt
  -- the second derivative is continuous off the pole
  have hd1 : ContDiffOn ℝ ∞ (fderiv ℝ u) {0}ᶜ :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hO).mp hus).2
  have hd2 : ContinuousOn (fderiv ℝ (fderiv ℝ u)) {0}ᶜ :=
    hd1.continuousOn_fderiv_of_isOpen hO (by simp)
  set K : Set (ComplexModel n) := tsupport χ₀ \ ball 0 ρ with hK
  have hKc : IsCompact K := hχc.isCompact.diff isOpen_ball
  have hK0 : K ⊆ {0}ᶜ := fun w hw h0 ↦ hw.2 (by rw [mem_singleton_iff.mp h0]; exact mem_ball_self hρ)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M := by
    exact hKc.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ u)) (hd2.mono hK0)
  refine ⟨max M 0 / 2, by positivity, fun w₀ w hw v ↦ ?_⟩
  have htr : cutoffPole χ₀ w₀ = fun y ↦ u (y - w₀) := by
    funext y; simp [hu, cutoffPole]
  rw [htr, leviForm_comp_sub]
  set x := w - w₀ with hx
  have hx0 : x ≠ 0 := sub_ne_zero.mpr hw
  by_cases hxρ : x ∈ ball 0 ρ
  · -- near the pole, `u = log ‖·‖²`
    have hEq : EqOn u (fun y ↦ Real.log (‖y‖ ^ 2)) (ball 0 ρ) := fun y hy ↦ by
      simp [hu, cutoffPole, hχ1 y hy]
    rw [Hormander.leviForm_congr_of_eqOn isOpen_ball hEq hxρ]
    have h := LogCutoffLevi.leviForm_log_normSq_nonneg (ContinuousLinearMap.id ℂ (ComplexModel n))
      (z := x) hx0 v
    simp only [ContinuousLinearMap.id_apply] at h
    have : 0 ≤ max M 0 / 2 * ‖v‖ ^ 2 := by positivity
    linarith
  · by_cases hxs : x ∈ tsupport χ₀
    · -- on the compact set `K`, the Hessian is bounded
      have hxK : x ∈ K := ⟨hxs, hxρ⟩
      have hB : ∀ a : ComplexModel n, |realHessian u x a a| ≤ max M 0 * ‖a‖ ^ 2 := by
        intro a
        rw [realHessian_eq_fderiv]
        calc |fderiv ℝ (fderiv ℝ u) x a a| = ‖fderiv ℝ (fderiv ℝ u) x a a‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ (fderiv ℝ u) x a‖ * ‖a‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ * ‖a‖ * ‖a‖ := by
              gcongr; exact ContinuousLinearMap.le_opNorm _ _
          _ ≤ max M 0 * ‖a‖ ^ 2 := by
              rw [mul_assoc, ← sq]
              gcongr
              exact (hM x hxK).trans (le_max_left _ _)
      have h1 := hB v
      have h2 := hB (Complex.I • v)
      rw [norm_smul, Complex.norm_I, one_mul] at h2
      simp only [leviForm]
      have := abs_le.mp h1
      have := abs_le.mp h2
      linarith
    · -- away from the support, `u = 0`
      have hev : u =ᶠ[𝓝 x] fun _ ↦ 0 := by
        have h0 := notMem_tsupport_iff_eventuallyEq.mp hxs
        filter_upwards [h0] with y hy
        simp [hu, cutoffPole, hy]
      rw [PshRadialRegularization.leviForm_congr hev, leviForm_const]
      have : 0 ≤ max M 0 / 2 * ‖v‖ ^ 2 := by positivity
      linarith

end SGPT.Okounkov.TranscendentalL2
