import SGPT.Toric.Toric5IOrder
import SGPT.Toric.Toric3OkounkovBody
import SGPT.Toric.GeodesicChart
import SGPT.Toric.BigToric2MetricExistence
import SGPT.Okounkov.NativeFlagGermCartier
import SGPT.Foundations.Analysis.PlurisubharmonicAE

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology ContDiff BigOperators Manifold ENNReal

variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- A literal lattice point in the divisor polytope produces its finite linear
profile with the original support-growth condition, in every dimension. -/
theorem linearProfile_mem_growth {p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ toricDivisorPolytope D) :
    (fun x => inner ℝ x p) ∈
      RealGrowthClass (innerₗ (EuclideanSpace ℝ (Fin n))) (toricDivisorPolytope D) := by
  refine ⟨isConvex_coe_iff.mp (isConvex_linear ((innerₗ _).flip p)), ?_⟩
  refine ⟨0, fun x _ => ?_⟩
  simp only [EReal.coe_zero, add_zero]
  exact le_iSup_of_le (⟨p, hp⟩ : toricDivisorPolytope D) le_rfl

/-- The actual global PSH extension of the normalized character profile.
The definition contains neither a desired body nor a desired valuation. -/
def linearPotential {p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ toricDivisorPolytope D) :
    PolytopeToricVariety γ hs → EReal :=
  h.extension (fun x => inner ℝ x p) (linearProfile_mem_growth hp)

theorem linearPotential_mem {p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ toricDivisorPolytope D) : h.linearPotential hp ∈ h.PSHTor :=
  h.extension_mem _ (linearProfile_mem_growth hp)

theorem profile_linearPotential {p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ toricDivisorPolytope D) :
    h.profile (h.linearPotential hp) = fun x => (inner ℝ x p : EReal) :=
  h.profile_extension _ (linearProfile_mem_growth hp)

theorem realProfile_linearPotential {p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ toricDivisorPolytope D) :
    h.realProfile (h.linearPotential hp) = fun x => inner ℝ x p := by
  funext x
  rw [realProfile, h.profile_linearPotential hp]
  rfl

private theorem support_singleton_inner (p : EuclideanSpace ℝ (Fin n)) :
    support (innerₗ (EuclideanSpace ℝ (Fin n))).flip {p} =
      fun x => (inner ℝ x p : EReal) := by
  funext x
  apply le_antisymm
  · apply iSup_le
    intro q
    have hq : q.val = p := q.property
    change ((inner ℝ x q.val : ℝ) : EReal) ≤ (inner ℝ x p : EReal)
    rw [hq]
  · exact le_iSup_of_le (⟨p, mem_singleton p⟩ : ({p} : Set _)) le_rfl

/-- The independently computed genuine Legendre transform is a singleton
indicator; zero-dimensional conventions are inherited literally. -/
theorem legendre_linearPotential {p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ toricDivisorPolytope D) :
    h.legendre (h.linearPotential hp) = SGPT.Convex.indicator {p} := by
  rw [legendre, h.profile_linearPotential hp, ← support_singleton_inner p]
  exact conjugate_support_of_isContPerfPair
    (innerₗ (EuclideanSpace ℝ (Fin n))) (convex_singleton p)
    isClosed_singleton

theorem newtonBody_linearPotential {p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ toricDivisorPolytope D) :
    h.newtonBody (h.linearPotential hp) = {p} := by
  rw [h.newtonBody_eq_closure_effectiveDomain ⟨p, hp⟩ (h.linearPotential_mem hp),
    convexNewtonBody, h.legendre_linearPotential hp, effectiveDomain_indicator,
    isClosed_singleton.closure_eq]

end BigToricMetric
end SGPT.Toric
