import SGPT.Foundations.Analysis.Pending.FiniteAnalyticMaxima
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.FirstPass.QuasiEquisingularApproximation

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.QuasiEquisingularFiniteGluing

open FirstPass
open FirstPass.QuasiEquisingularApproximation
open DemaillyAnalyticType

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The local compatibility needed to take a finite global maximum without
changing its analytic-singularity convention: at each chart germ, all terms
have logarithmic presentations with one common rational coefficient. -/
def HasCompatibleFiniteAnalyticPresentations {k : ℕ}
    (u : Fin (k + 1) → M → EReal) : Prop :=
  ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
    ∃ c : ℚ, ∀ i, ∃ N : ℕ, ∃ f : Fin N → ComplexModel n → ℂ,
      LogarithmicTypeAt (chartFunction (u i) e) (c : ℝ) f z

/-- A nonempty finite pointwise supremum of global theta-PSH potentials is
again theta-PSH. -/
theorem isThetaPshPotential_fin_iSup
    {θ : SmoothRealForm n M 2} {k : ℕ} (u : Fin (k + 1) → M → EReal)
    (hu : ∀ i, IsThetaPshPotential θ (u i)) :
    IsThetaPshPotential θ (fun x => ⨆ i, u i x) := by
  induction k with
  | zero =>
      have h0 := hu 0
      convert h0 using 1
      funext x
      exact iSup_fin_one_eq (fun i => u i x)
  | succ k ih =>
      have htail : ∀ i : Fin (k + 1), IsThetaPshPotential θ (u i.succ) :=
        fun i => hu i.succ
      have h0 := hu 0
      have hind := ih (fun i => u i.succ) htail
      have hmax := IsThetaPshPotential.max h0 hind
      convert hmax using 1
      funext x
      exact iSup_fin_succ_eq_max (fun i => u i x)

/- Compatible local finite presentations make the finite global supremum have
chartwise analytic singularity type. -/
omit [IsComplexManifold n M] in
theorem hasManifoldAnalyticSingularityType_fin_iSup
    {k : ℕ} (u : Fin (k + 1) → M → EReal)
    (hu : HasCompatibleFiniteAnalyticPresentations (n := n) u) :
    HasManifoldAnalyticSingularityType (n := n) (fun x => ⨆ i, u i x) := by
  intro e z hz
  obtain ⟨c, hc⟩ := hu e z hz
  have htype := hasAnalyticSingularityTypeAt_fin_iSup_of_same_coefficient
    (fun i => chartFunction (u i) e) hc
  have hchart : chartFunction (fun x => ⨆ i, u i x) e =
      fun y => ⨆ i, chartFunction (u i) e y := by
    funext y
    simp only [FirstPass.chartFunction]
  rw [hchart]
  exact htype

/-- **Conditional finite gluing.**  A finite family of global theta-PSH
potentials whose chart germs share a rational logarithmic coefficient at each
point has a theta-PSH supremum with manifold analytic singularity type. -/
theorem finite_iSup_thetaPsh_hasManifoldAnalyticSingularityType
    {θ : SmoothRealForm n M 2} {k : ℕ} (u : Fin (k + 1) → M → EReal)
    (hpsh : ∀ i, IsThetaPshPotential θ (u i))
    (han : HasCompatibleFiniteAnalyticPresentations (n := n) u) :
    IsThetaPshPotential θ (fun x => ⨆ i, u i x) ∧
      HasManifoldAnalyticSingularityType (n := n) (fun x => ⨆ i, u i x) :=
  ⟨isThetaPshPotential_fin_iSup u hpsh,
    hasManifoldAnalyticSingularityType_fin_iSup u han⟩

end SGPT.Foundations.Analysis.Pending.QuasiEquisingularFiniteGluing
