import SGPT.PSH.QuasiEquisingular
import SGPT.Foundations.Analysis.Pending.ActualAllDimensionGentleQea

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation
open SGPT.Foundations.Analysis.Pending.ActualOriginalSquaredDensityGentle
open scoped Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Original def:analy-sing, using the actual all-stalk divisor equation,
finite smooth exponential and proper modification from a Kahler manifold.
The source quasi-PSH class retains its actual existential global closed
background. The exact analytic type produces positive rational coefficient
and genuine coherent original ideal; no extra validity field is imposed. -/
def SourceGentleAnalyticSingularities (v : M → EReal) (c : ℚ)
    (𝔞 : GermIdeal n M) : Prop :=
  (∃ θ : ClosedRealOneOneForm n M, IsThetaPshPotential θ.val v) ∧
    HasGentleAnalyticSingularitiesOfType (n := n) v c 𝔞

/-- An actual cofinal finite tail preserves all four literal original QEA
conditions, including pole convergence and the separated multiplier inclusion. -/
theorem sourceQuasiEquisingularApproximation_tail
    {θ : ClosedRealOneOneForm n M} {u : M → EReal} {v : ℕ → M → EReal}
    (hsource : SourceQuasiEquisingularApproximation θ u v) (k : ℕ) :
    SourceQuasiEquisingularApproximation θ u (fun j => v (j + k)) := by
  obtain ⟨ω, ε, h⟩ := native_of_sourceQuasiEquisingularApproximation hsource
  have htail : IsQuasiEquisingularApproximation ω θ u
      (fun j => ε (j + k)) (fun j => v (j + k)) := by
    refine ⟨h.target,
      ⟨fun j => h.error_nonneg (j + k),
        fun a b hab => h.error_antitone (Nat.add_le_add_right hab k),
        h.error_tendsto.comp (tendsto_add_atTop_nat k)⟩,
      fun j => h.term (j + k), fun j => h.term_hasAnalyticSingularityType (j + k),
      ⟨fun x a b hab => h.term_antitone x (Nat.add_le_add_right hab k),
        fun x => (h.term_tendsto x).comp (tendsto_add_atTop_nat k)⟩, ?_⟩
    intro c d hc hcd
    exact (tendsto_add_atTop_nat k).eventually (h.eventually_multiplierIdealIncluded hc hcd)
  exact sourceQuasiEquisingularApproximation_of_native htail

/-- Whole original thm:qequi with its LITERAL positive-index dyadic ideals.
Nat j denotes book index j+1, so discard the native level-zero term rather
than silently assigning coefficient one to the book's first coefficient1/2.
Every approximation/gentle field is produced from genuine original data;
the actual zero-dimensional branch remains the original constant potential. -/
theorem exists_sourceGentleQuasiEquisingularApproximation [CompactSpace M]
    (ω : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u) :
    ∃ v : ℕ → M → EReal,
      SourceQuasiEquisingularApproximation θ u v ∧
      ∀ j : ℕ, SourceGentleAnalyticSingularities (v j)
        (((2 ^ (j + 1) : ℕ) : ℚ)⁻¹)
        (multiplierIdeal (n := n) ((2 ^ (j + 1) : ℕ) : ℝ) u) := by
  obtain ⟨ε, v, hqea, hgentle⟩ :=
    SGPT.Foundations.Analysis.Pending.ActualAllDimensionGentleQea.exists_all_dimension_gentle_qea
      ω θ hu
  refine ⟨fun j => v (j + 1),
    sourceQuasiEquisingularApproximation_tail
      (sourceQuasiEquisingularApproximation_of_native hqea) 1, ?_⟩
  intro j
  exact ⟨⟨θ + ε (j + 1) • ω.form, hqea.term (j + 1)⟩, hgentle (j + 1)⟩

end SGPT.PSH
