import SGPT.Okounkov.TranscendentalWNConv7Main
import SGPT.Okounkov.TranscendentalWNConv6Cutoff
import SGPT.Okounkov.TranscendentalWNConv6Obstacle
import SGPT.Okounkov.TranscendentalLiftingExtension

/-!
# `tok-wn:convergence` from measure control and the analytic core; first steps of WN21 §7

Blueprint `claude-tok-wn-conv7`, nodes `tok-wn-conv7:assembly`, `tok-wn-conv7:weight-setup` and
`tok-wn-conv7:monotone`; source WN21 §7.

* `keyConvergence_of_contactMassLimit`: `MeasureControlStatement F` (WN21 §6, lane WN-CONV6) and
  `ContactMassLimitStatement F` (the analytic core of WN21 §7) give `KeyConvergenceStatement F`
  (`tok-wn:convergence`).  The cutoff `χ` and the continuity of the obstacles `g_k` are lane
  WN-CONV6's `exists_isWNCutoff` and `continuous_cutoffObstacleLine`.
* `exists_gentle_ge_thetaPshSupremum` (WN21 §7, first line; `tok:sing-decrease`): a potential
  `ψ ∈ Ω(β + ε{η'})` of a gentle Kähler current with `ũ = V_{θ̃} ≤ ψ`.
* `cutoffObstacleLine_sub_one_le`, `prescribedEnvelope_cutoffObstacle_sub_one_le` (WN21
  Proposition 7.2): `g_k + k` increases with `k`, hence so does `v_k + k = P_Θ[ψ](g_k) + k`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Okounkov.TranscendentalMain
open SGPT.Okounkov.TranscendentalCore

/-! ### The assembly -/

/-- **`tok-wn:convergence`** (WN21 §7, the hard inequality of Theorem 1.7 up to a Kähler
perturbation), conditional on measure control (WN21 §6) and the analytic core of WN21 §7:
`vol(ξ) ≤ vol_{𝒳|X'}(β + ε{η'}) + vol_{𝒳|ℰ}(β + ε{η'})`. -/
theorem keyConvergence_of_contactMassLimit {m : ℕ} (F : OriginalFlagGeometry.{u} (m + 1))
    (hMC : MeasureControlStatement F) (hCore : ContactMassLimitStatement F) :
    KeyConvergenceStatement F := by
  obtain ⟨χ, hχ⟩ := exists_isWNCutoff
  exact keyConvergence_of_contactMassLimit_of_cutoff F hχ (continuous_cutoffObstacleLine hχ) hMC
    hCore

/-! ### The weight `ψ` -/

/-- **A gentle Kähler current above `ũ`** (WN21 §7, first line: "there exists a
`θ̃ + εη`-psh function `ψ` with analytic singularities such that `ψ ≥ ũ`"; `tok:sing-decrease`).
If `V_{θ₀}` (`thetaPshSupremum`) is a `θ₀`-psh potential (e.g. `{θ₀}` big), then for every
Kähler form `η'` and `ε > 0` there is `ψ ∈ Ω(θ₀ + εη')` (gentle analytic singularities and
`θ₀ + εη' + dd^c ψ ≥ (ε/4) η'`) with `V_{θ₀} ≤ ψ`. -/
theorem exists_gentle_ge_thetaPshSupremum {N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel N) M] [IsComplexManifold N M] [CompactSpace M]
    {θ₀ : ClosedRealOneOneForm N M} (hV : IsThetaPshPotential θ₀.val (thetaPshSupremum θ₀.val))
    (η' : KahlerBackground N M) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : M → EReal, ψ ∈ gentleKahlerCurrents (θ₀ + ε • η'.form) ∧
      ∀ z, thetaPshSupremum θ₀.val z ≤ ψ z := by
  have hφ : IsThetaPshPotential
      ((θ₀ + ε • η'.form) - (TranscendentalLifting.kahlerSmul η' hε).form).val
      (thetaPshSupremum θ₀.val) := by
    rw [TranscendentalLifting.kahlerSmul_form, add_sub_cancel_right]
    exact hV
  obtain ⟨ψ, hψ, -, hle⟩ := TranscendentalBody.exists_mem_gentleKahlerCurrents_ge hφ
  exact ⟨ψ, hψ, hle⟩

/-! ### Monotonicity of `v_k + k` (WN21 Proposition 7.2) -/

/-- **`g_k + k` increases with `k`**: `g_k - 1 ≤ g_{k+1}` on `ℙ¹` (`χ` is increasing). -/
theorem cutoffObstacleLine_sub_one_le {χ : ℝ → ℝ} (hχ : IsWNCutoff χ) (k : ℕ)
    (p : ProjectiveLine) : cutoffObstacleLine χ k p - 1 ≤ cutoffObstacleLine χ (k + 1) p := by
  by_cases hp : p = projectiveInfinity
  · subst hp
    rw [cutoffObstacleLine_infinity, cutoffObstacleLine_infinity]
    norm_num
  · have hpt : p = affineLinePoint (projectiveAffine p) := by
      have h1 : p.rep 1 ≠ 0 := by
        intro h1
        apply hp
        rw [← Projectivization.mk_rep p, mk_eq_projectiveInfinity_iff]; exact h1
      conv_lhs => rw [← Projectivization.mk_rep p]
      rw [affineLinePoint_eq_mk, Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 (p.rep 1) h1, ?_⟩
      ext i
      fin_cases i <;> simp [projectiveAffine, Units.smul_def]
      field_simp
    rw [hpt, cutoffObstacleLine_affineLinePoint, cutoffObstacleLine_affineLinePoint]
    set τ := projectiveAffine p
    have hlog : cutoffLog χ (Real.exp k * ‖τ‖ ^ 2) ≤
        cutoffLog χ (Real.exp ((k + 1 : ℕ) : ℝ) * ‖τ‖ ^ 2) := by
      by_cases hτ : τ = 0
      · simp [hτ, cutoffLog_zero]
      · have hn : 0 < ‖τ‖ ^ 2 := by positivity
        rw [cutoffLog_of_pos χ (by positivity), cutoffLog_of_pos χ (by positivity),
          Real.log_mul (Real.exp_pos _).ne' hn.ne', Real.log_mul (Real.exp_pos _).ne' hn.ne',
          Real.log_exp, Real.log_exp]
        exact hχ.monotone (by push_cast; linarith)
    push_cast at hlog ⊢
    linarith

/-- **WN21 Proposition 7.2** (`tok-wn-conv7:monotone`): `v_k - 1 ≤ v_{k+1}` for
`v_k = P_Θ[ψ](g_k)`, i.e. `v_k + k` increases with `k`. -/
theorem prescribedEnvelope_cutoffObstacle_sub_one_le {X : Type*} {N : ℕ} {𝒳 : Type*}
    [TopologicalSpace 𝒳] [ChartedSpace (ComplexModel N) 𝒳] [IsComplexManifold N 𝒳]
    {μ : 𝒳 → X × ProjectiveLine} {χ : ℝ → ℝ} (hχ : IsWNCutoff χ)
    (Θ : ClosedRealOneOneForm N 𝒳) (ψ : 𝒳 → EReal) (k : ℕ) (z : 𝒳) :
    prescribedEnvelope Θ (cutoffObstacle μ χ k) ψ z + ((-1 : ℝ) : EReal) ≤
      prescribedEnvelope Θ (cutoffObstacle μ χ (k + 1)) ψ z :=
  sub_one_le_prescribedEnvelope (fun y => cutoffObstacleLine_sub_one_le hχ k (μ y).2) z

end SGPT.Okounkov.TranscendentalWN
