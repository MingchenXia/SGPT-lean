import SGPT.Foundations.Analysis.Pending.ActualZeroLeviDistributionSmoothness
import SGPT.Foundations.Analysis.FirstPass.LocalCurrents

set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped ContDiff Distributions Topology

namespace SGPT.Foundations.Analysis.Pending.DistributionPotentialSmoothOverlap
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Two arbitrary original signed scalar potentials of the same complete
native current have an internally smooth pluriharmonic distributional difference.
No locally integrable representative of either potential is supplied. -/
theorem exists_smooth_difference_of_equal_ddC
    (μ : Measure E) [μ.IsAddHaarMeasure] {Ω : Opens E}
    (S T : 𝓓'(Ω, ℝ)) (heq : ddC S = ddC T) (x : E) (hx : x ∈ Ω) :
    ∃ (U : Opens E) (hU : U ≤ Ω) (h : E → ℝ),
      x ∈ U ∧ ContDiff ℝ (⊤ : ℕ∞) h ∧
      ∃ hh : LocallyIntegrableOn h U μ,
        restrictDistribution (S-T) hU = regularDistribution μ h hh ∧
        ∀ z ∈ U, ∀ v : E, leviForm h z v = 0 := by
  have hzero : ∀ v : E, distributionalLeviCLM v (S-T) = 0 := by
    intro v
    have hline : (1 / Real.pi : ℝ) •
        (distributionalLeviCLM v S - distributionalLeviCLM v T) = 0 := by
      rw [smul_sub, ← ddC_complexLine, ← ddC_complexLine]
      exact sub_eq_zero.mpr (congrArg (fun A => A ![v, Complex.I • v]) heq)
    rw [map_sub]
    exact (smul_eq_zero.mp hline).resolve_left (one_div_ne_zero Real.pi_ne_zero)
  exact ActualZeroLeviDistributionSmoothness.exists_smooth_local_representative_of_zero_levi
    μ (S-T) hzero x hx

end SGPT.Foundations.Analysis.Pending.DistributionPotentialSmoothOverlap
