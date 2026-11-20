import SGPT.Toric.Toric5YaoTheorem
import SGPT.Toric.BigToricConvexBodies
import SGPT.Toric.Toric4Examples

/-!
# The converse of Yao's theorem (1) fails

Source `chapter_toric_ample.tex`, `ex:toric-ample:L966`: "In general, in the setup of
`thm:Yao`, there exists `m ∈ M ∩ (P ∖ Δ(ω, φ))` such that `χ^m ∈ H⁰(X, L ⊗ 𝓘(φ))`.  As a
concrete example, let us take `P = [0, 1]`.  Take `φ` so that `Δ(ω, φ) = [0, 1/2]`.  We claim
that `χ^1` is `L²`-integrable."

We prove the claim for *every* `φ ∈ PSH_tor(X, ω)` with `Δ(ω, φ) = [0, 1/2]` on `X = X_{[0,1]}`
(`= ℙ¹`, `P1toric_projectiveLine`), and that such `φ` exist (`thm:toricpshbig`, every convex body
in `P` is a Newton body).  The source verifies the convergence of `eq:torictobefinite2` after the
reduction to `P_ω[φ]`; here we use the exponent criterion
`BigToricMetric.latticeCharacter_mem_toricMultiplierSections_of_exponent` (the local form of the
proof of `thm:Yao` (1)): the rays of `[0,1]` are `±1`, and for `x₀ ∈ {G_φ < ∞}` with
`1/4 < x₀ ≤ 1/2` both exponents `±(1 - x₀)` exceed `-1`.
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff BigOperators Manifold ENNReal Pointwise

namespace BigToricMetric

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The exponent criterion (proof of `thm:Yao` (1)): if `m ∈ M ∩ kP_D` and in every vertex chart
there is `x₀ ∈ {G_φ < ∞}` with all exponents `⟨m - k x₀, u_j(v)⟩ > -1`, then
`χ^m ∈ H⁰(X, L^k ⊗ 𝓘(kφ))`. -/
theorem latticeCharacter_mem_toricMultiplierSections_of_exponent
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) {k : ℕ} (hk : 0 < k)
    {m : Fin n → ℤ} (hm : m ∈ toricLatticePoints ((k : ℤ) • D))
    (hx : ∀ v : latticePolytopeVertices γ, ∃ x₀, h.legendre u x₀ < ⊤ ∧
      ∀ j, -1 < latticeFunctional (polytopeToricRayGenerator γ hs v j)
        (latticeVector m - (k : ℝ) • x₀)) :
    (fun a => (latticeCharacter m a : ℂ)) ∈
      toricMultiplierSections ((k : ℤ) • D) (by exact_mod_cast hk : (0 : ℝ) < k)
        (h.isQPSH_of_mem hu) := by
  rw [mem_toricMultiplierSections_iff]
  refine ⟨latticeCharacter_mem_toricSections _ hm, fun v f hf hgf z => ?_⟩
  rw [coeff_latticeCharacter_eq hm v hf hgf]
  obtain ⟨x₀, hx₀, hexp⟩ := hx v
  exact h.multiplierIntegrableAt_toricMonomial_of_exponent hu hk hm v hx₀ hexp z

end BigToricMetric

/-! ### `P = [0, 1]`, `Δ = [0, 1/2]` -/

section P1

variable (hs : latticePolytopeEdgeSmooth (simplexGenerator 1))

/-- The interval `[0, 1/2] ⊆ M_ℝ = ℝ`. -/
def halfInterval : Set (EuclideanSpace ℝ (Fin 1)) := {m | 0 ≤ m 0 ∧ m 0 ≤ 1 / 2}

/-- `P = [0, 1]` for the model `X_{[0,1]}`. -/
theorem P1_momentPolytope :
    polytopeToricMomentPolytope (simplexGenerator 1) = {m | 0 ≤ m 0 ∧ m 0 ≤ 1} := by
  rw [← (P1toric_facets simplex_edgeSmooth).2.2, ← simplexHyperplaneDivisor_eq_ample simplex_edgeSmooth,
    P1toric_polytope simplex_edgeSmooth]

theorem P1_ampleDivisorPolytope :
    toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 1) hs) =
      {m | 0 ≤ m 0 ∧ m 0 ≤ 1} := by
  rw [(P1toric_facets hs).2.2, P1_momentPolytope]

theorem halfInterval_nonempty : halfInterval.Nonempty := ⟨0, by simp [halfInterval]⟩

theorem convex_halfInterval : Convex ℝ halfInterval := by
  intro x hx y hy a b ha hb hab
  simp only [halfInterval, mem_ofPred_eq, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy ⊢
  constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]

theorem isCompact_halfInterval : IsCompact halfInterval := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_const (PiLp.continuous_apply 2 _ 0)).inter
      (isClosed_le (PiLp.continuous_apply 2 _ 0) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 1))) (r := 1)).subset ?_
    intro m hm
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_one,
      Real.sqrt_le_one, Real.norm_eq_abs, sq_abs]
    obtain ⟨h0, h1⟩ := hm
    nlinarith

theorem halfInterval_subset : halfInterval ⊆
    toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 1) hs) := by
  rw [P1_ampleDivisorPolytope hs]
  rintro m ⟨h0, h1⟩
  exact ⟨h0, by linarith⟩

/-- Source `ex:toric-ample:L966` (setup): on `X_{[0,1]}` there is `φ ∈ PSH_tor(X, ω)` with
`Δ(ω, φ) = [0, 1/2]`. -/
theorem exists_newtonBody_eq_halfInterval :
    ∃ u ∈ PolytopeToricPSH (simplexGenerator 1) hs,
      polytopeToricNewtonBody (simplexGenerator 1) hs u = halfInterval := by
  have hP : (toricDivisorPolytope (polytopeToricAmpleDivisor (simplexGenerator 1) hs)).Nonempty :=
    halfInterval_nonempty.mono (halfInterval_subset hs)
  obtain ⟨u, hu, -, hΔ⟩ := (guilleminBigToricMetric (simplexGenerator 1) hs).exists_newtonBody_eq hP
    halfInterval_nonempty isCompact_halfInterval convex_halfInterval (halfInterval_subset hs)
  exact ⟨u, hu, by rw [← guilleminBigToricMetric_newtonBody hu]; exact hΔ⟩

/-- Every ray of `[0, 1]` is `±1`. -/
theorem P1_ray_cases (u : Fin 1 → ℤ) (hu : u ∈ PolytopeToricRays (simplexGenerator 1) hs) :
    u 0 = 1 ∨ u 0 = -1 := by
  rw [(P1toric_facets hs).1] at hu
  rcases hu with rfl | rfl
  · left; simp
  · right; rfl

/-- Source `ex:toric-ample:L966`: for `P = [0, 1]` and every `φ ∈ PSH_tor(X, ω)` with
`Δ(ω, φ) = [0, 1/2]`, the lattice point `1 ∈ P ∖ Δ(ω, φ)` has `χ^1 ∈ H⁰(X, L ⊗ 𝓘(φ))`. -/
theorem toricAmple_L966 {u : PolytopeToricVariety (simplexGenerator 1) hs → EReal}
    (hu : u ∈ PolytopeToricPSH (simplexGenerator 1) hs)
    (hΔ : polytopeToricNewtonBody (simplexGenerator 1) hs u = halfInterval) :
    latticeVector (fun _ => 1) ∈ polytopeToricMomentPolytope (simplexGenerator 1) \
        polytopeToricNewtonBody (simplexGenerator 1) hs u ∧
      (fun a => (latticeCharacter (fun _ => 1) a : ℂ)) ∈
        ampleMultiplierSections (simplexGenerator 1) hs hu := by
  refine ⟨⟨by rw [P1_momentPolytope]; simp, by rw [hΔ]; simp [halfInterval]; norm_num⟩, ?_⟩
  set h := guilleminBigToricMetric (simplexGenerator 1) hs
  have hu' : u ∈ h.PSHTor := hu
  have hP := h.nonempty_toricDivisorPolytope_of_mem hu'
  -- a point `x₀ ∈ {G_φ < ∞}` with `1/4 < x₀ ≤ 1/2`
  have hΔ' : h.newtonBody u = halfInterval := by rw [guilleminBigToricMetric_newtonBody hu, hΔ]
  have hhalf : (EuclideanSpace.single 0 (1 / 2 : ℝ)) ∈ halfInterval := by
    simp [halfInterval]
  have hcl : (EuclideanSpace.single 0 (1 / 2 : ℝ)) ∈ closure (effectiveDomain (h.legendre u)) := by
    rw [← convexNewtonBody, ← h.newtonBody_eq_closure_effectiveDomain hP hu', hΔ']
    exact hhalf
  obtain ⟨x₀, hx₀, hdist⟩ := Metric.mem_closure_iff.mp hcl (1 / 4) (by norm_num)
  have hx₀Δ : x₀ ∈ halfInterval := by
    rw [← hΔ', h.newtonBody_eq_closure_effectiveDomain hP hu']
    exact subset_closure hx₀
  have hx₀low : 1 / 4 < x₀ 0 := by
    have h1 : |(1 / 2 : ℝ) - x₀ 0| < 1 / 4 := by
      have := (PiLp.norm_apply_le (EuclideanSpace.single 0 (1 / 2 : ℝ) - x₀) 0).trans_lt
        (by rw [← dist_eq_norm]; exact hdist)
      simpa [Real.norm_eq_abs] using this
    rw [abs_lt] at h1
    linarith
  -- the exponent criterion
  have hlat : (fun _ => (1 : ℤ)) ∈ toricLatticePoints (((1 : ℕ) : ℤ) • polytopeToricAmpleDivisor
      (simplexGenerator 1) hs) := by
    change latticeVector _ ∈ toricDivisorPolytope _
    rw [Nat.cast_one, one_smul, P1_ampleDivisorPolytope hs]
    simp
  have hmem := h.latticeCharacter_mem_toricMultiplierSections_of_exponent hu' one_pos hlat
    (fun v => ⟨x₀, hx₀, fun j => ?_⟩)
  · rwa [toricMultiplierSections_congr (by rw [Nat.cast_one, one_smul]) Nat.cast_one] at hmem
  · have hray := P1_ray_cases hs (polytopeToricRayGenerator (simplexGenerator 1) hs v j)
      ⟨v, j, rfl⟩
    rw [latticeFunctional_apply, Fin.sum_univ_one]
    simp only [PiLp.sub_apply, latticeVector_apply, Nat.cast_one, one_smul, Int.cast_one]
    rcases hray with h1 | h1 <;> rw [h1] <;> push_cast <;> linarith [hx₀Δ.2]

/-- Source `ex:toric-ample:L966`: in the setup of `thm:Yao`, the converse of (1) fails: on
`X_{[0,1]}` there are `φ ∈ PSH_tor(X, ω)` and `m ∈ M ∩ (P ∖ Δ(ω, φ))` with
`χ^m ∈ H⁰(X, L ⊗ 𝓘(φ))`. -/
theorem exists_mem_ampleMultiplierSections_not_mem_newtonBody :
    ∃ (u : PolytopeToricVariety (simplexGenerator 1) hs → EReal)
      (hu : u ∈ PolytopeToricPSH (simplexGenerator 1) hs) (m : Fin 1 → ℤ),
      latticeVector m ∈ polytopeToricMomentPolytope (simplexGenerator 1) \
          polytopeToricNewtonBody (simplexGenerator 1) hs u ∧
        (fun a => (latticeCharacter m a : ℂ)) ∈ ampleMultiplierSections (simplexGenerator 1) hs hu := by
  obtain ⟨u, hu, hΔ⟩ := exists_newtonBody_eq_halfInterval hs
  exact ⟨u, hu, fun _ => 1, toricAmple_L966 hs hu hΔ⟩

end P1

end SGPT.Toric
