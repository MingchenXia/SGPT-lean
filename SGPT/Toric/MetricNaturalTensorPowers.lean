import SGPT.Toric.MetricFiniteSums
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff ENNReal Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The genuine integral tensor power of the ORIGINAL metric. Every step
uses actual frame transitions and smooth curvature, including tensor power0. -/
def naturalTensorPower (h : BigToricMetric D) : (N : ℕ) → BigToricMetric (N • D)
  | 0 => castMetric (by simp) zeroMetric
  | N+1 => castMetric (succ_nsmul D N).symm ((h.naturalTensorPower N).addMetric h)

@[simp] theorem naturalTensorPower_form (N : ℕ) :
    (h.naturalTensorPower N).form = (N : ℝ) • h.form := by
  induction N with
  | zero => simp [naturalTensorPower, zeroMetric]
  | succ N ih =>
    rw [naturalTensorPower, castMetric_form]
    change (h.naturalTensorPower N).form + h.form = ((N+1 : ℕ) : ℝ) • h.form
    rw [ih, Nat.cast_add, Nat.cast_one, add_smul, one_smul]

@[simp] theorem naturalTensorPower_potential (N : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (h.naturalTensorPower N).potential x = (N : ℝ) * h.potential x := by
  induction N with
  | zero => simp [naturalTensorPower]
  | succ N ih =>
    rw [naturalTensorPower, castMetric_potential, addMetric_potential, ih]
    push_cast
    ring

/-- The actual tensor metric and literal scaled original potential give
exactly the literal scaled original profile, including all original poles. -/
theorem naturalTensorPower_profile (N : ℕ) (u : PolytopeToricVariety γ hs → EReal) :
    (h.naturalTensorPower N).profile (fun p => ((N : ℝ) : EReal) * u p) =
      fun x => ((N : ℝ) : EReal) * h.profile u x := by
  funext x
  rw [profile, naturalTensorPower_potential, EReal.coe_mul, profile]
  exact (EReal.left_distrib_of_nonneg_of_ne_top (by positivity)
    (EReal.coe_ne_top (N : ℝ)) _ _).symm

/-- Positive integral tensor powers retain the genuine original PSH and
compact-torus invariance, constructed from the original source potential. -/
theorem mem_PSHTor_naturalTensorPower (N : ℕ) (hN : 0 < N)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    (fun p => ((N : ℝ) : EReal) * u p) ∈ (h.naturalTensorPower N).PSHTor := by
  refine ⟨?_, ?_⟩
  · apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    change IsThetaPshPotential (h.naturalTensorPower N).form.val _
    rw [naturalTensorPower_form]
    exact RestrictedApproximantComparison.isThetaPshPotential_smul
      ((isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1) (by exact_mod_cast hN)
  · intro a ha p
    exact congrArg (fun z : EReal => ((N : ℝ) : EReal) * z) (hu.2 a ha p)

end BigToricMetric
end SGPT.Toric
