import SGPT.NPP.CodexC11OriginalChartDensity

/-! A bounded directional Levi density around every point of an actual chart.

Promoted by lane NPP-PROMOTE from the Codex draft `wip/RESUME-20261110/NPP-ENVELOPE-COMPARISON/C11ChartBallDensity.lean` (module `C11ChartBallDensity`), with module and namespace renamed.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Metric
open scoped ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Okounkov.TranscendentalWNReg SGPT.NPP.Codex.C11OriginalChartDensity

namespace SGPT.NPP.Codex.C11ChartBallDensity
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Around any target point there is one actual chart ball on which each
fixed direction has a bounded density of the source obstacle's Levi form. -/
theorem exists_chart_ball_directional_densities
    {f : M → ℝ} (hf : IsCOneOneBar (N := n) f)
    (e : ComplexChart n M) {z₀ : ComplexModel n} (hz₀ : z₀ ∈ e.val.target) :
    ∃ r : ℝ, 0 < r ∧ closedBall z₀ (2*r) ⊆ e.val.target ∧
      let Ω : Opens (ComplexModel n) := ⟨ball z₀ r, isOpen_ball⟩
      ∀ v : ComplexModel n, ∃ (A : ℝ) (d : Ω → ℝ), 0 ≤ A ∧ Measurable d ∧
        (∀ᵐ z ∂(volume.comap Subtype.val), |d z| ≤ A) ∧
        ∀ φ : 𝓓(Ω, ℝ),
          (∫ z, f (e.val.symm z) * leviForm φ z v) =
            ∫ z : Ω, φ z * d z ∂(volume.comap Subtype.val) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp e.val.open_target z₀ hz₀
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have h2 : 2*r < ε := by dsimp [r]; linarith
  have hK : closedBall z₀ (2*r) ⊆ e.val.target :=
    (closedBall_subset_ball h2).trans hball
  refine ⟨r,hr,hK,?_⟩
  intro v
  apply exists_original_chart_directional_density hf e (isCompact_closedBall _ _) hK
  exact (ball_subset_closedBall).trans (closedBall_subset_closedBall (by linarith))

end SGPT.NPP.Codex.C11ChartBallDensity
