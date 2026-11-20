import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityGeometricModelLimit
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

/-! # Actual model limits of uniform-positive native Cauchy sequences

SGPT PDF0230--0231 uniform-positive model-space sequence argument.
Actual native Cauchy extraction internally produces geometric steps;
the genuine target-free model construction gives a positive model limit,
and the uniform-space subsequence criterion recovers the whole sequence.
No target, supplied convergent subsequence, or completeness assumption is used.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelCauchyLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  ThetaPshL1Topology SingularCanonicalSingularityDistance
  SingularCanonicalSingularityGeometricModelLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- A natural uniform-positive model Cauchy sequence internally produces
its actual model limit, the retained mass lower bound, and native convergence. -/
theorem exists_model_limit_of_cauchySeq
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (hmodels : ∀ i, IsModelPotential θ (ui i).val)
    {δ : ℝ} (hδ : 0 < δ) (hstage : ∀ i, ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (ui i).val (ui i).property) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    CauchySeq ui → ∃ U : ThetaPshL1 θ.val, IsModelPotential θ U.val ∧
      ENNReal.ofReal δ ≤ diagonalPotentialMass θ U.val U.property ∧ Tendsto ui atTop (𝓝 U) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hcauchy
  let C : ℝ := 3 * (2 : ℝ) ^ (n + 2) * ((n : ℝ) + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by
    have hp : (1 : ℝ) ≤ 2 ^ (n + 2) := one_le_pow₀ (by norm_num)
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [C]
    nlinarith
  let r : ℝ := 1 / (2 * C)
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    apply (div_lt_one (by positivity : 0 < 2 * C)).mpr
    linarith
  have hCr : C * r = 1 / 2 := by
    dsimp [r]
    field_simp
  have hrC : C * r < 1 := by rw [hCr]; norm_num
  obtain ⟨f, hf, hbound⟩ := Metric.exists_subseq_bounded_of_cauchySeq ui hcauchy
    (fun i => r ^ i) (fun i => pow_pos hr0 i)
  have hstep (i : ℕ) : dist (ui (f i)) (ui (f (i + 1))) ≤ 1 * r ^ i := by
    rw [one_mul, dist_comm]
    exact (hbound i (f (i + 1)) (hf.monotone (Nat.le_succ i))).le
  obtain ⟨U, hU, hδU, hsub, _⟩ := exists_model_limit_of_geometric_steps omega θ hbig
    (fun i => ui (f i)) (fun i => hmodels (f i)) hδ (fun i => hstage (f i))
    (by norm_num : (0 : ℝ) ≤ 1) hr0 hr1 hrC hstep
  exact ⟨U, hU, hδU, tendsto_nhds_of_cauchySeq_of_subseq hcauchy hf.tendsto_atTop hsub⟩

end

end SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelCauchyLimit
