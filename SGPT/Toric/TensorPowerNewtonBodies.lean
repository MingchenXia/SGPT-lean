import SGPT.Toric.MetricNaturalTensorPowers
import SGPT.Convex.FiniteConvexBodyScaling

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas SGPT.Convex
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff ENNReal Classical Pointwise
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The genuine integral tensor power's ORIGINAL Newton body is the actual
positive-scaled original body, proved from literal supporting inequalities. -/
theorem naturalTensorPower_newtonBody (N : ℕ) (hN : 0 < N)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    (h.naturalTensorPower N).newtonBody (fun p => ((N : ℝ) : EReal) * u p) =
      (N : ℝ) • h.newtonBody u := by
  simp only [newtonBody, naturalTensorPower_profile, (h.realProfile_mem hu).2, ←EReal.coe_mul]
  exact closure_rawSubgradientImage_coe_pos_mul (h.realProfile u) (by exact_mod_cast hN)

/-- The genuine Kähler perturbation of the integral tensor power has the
literal original Minkowski body N*Delta+P_H, with no assumed body identity. -/
theorem naturalTensorPower_addGuillemin_newtonBody (N : ℕ) (hN : 0 < N)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    (h.naturalTensorPower N).addGuillemin.newtonBody (fun p => ((N : ℝ) : EReal) * u p) =
      (N : ℝ) • h.newtonBody u + polytopeToricMomentPolytope γ := by
  have huN := h.mem_PSHTor_naturalTensorPower N hN hu
  rw [(h.naturalTensorPower N).newtonBody_addGuillemin
    ((h.naturalTensorPower N).nonempty_toricDivisorPolytope_of_mem huN) huN,
    h.naturalTensorPower_newtonBody N hN hu]

/-- An actual original PSH current plus the original Guillemin Kähler form
has positive ordinary MA mass, including original mass0 and ambient dim0. -/
theorem MA_addGuillemin_pos {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    0 < h.addGuillemin.MA (h.mem_PSHTor_addGuillemin hu) univ := by
  change DiagonalMass.HasPositivePotentialMass
    (h.form + (polytopeToricKahlerBackground γ hs).form) u _
  have hun : IsThetaPshPotential h.form.val u :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1
  simpa only [one_smul] using
    SingularPositiveCommonBackgroundExistence.hasPositivePotentialMass_add_smul
      (polytopeToricKahlerBackground γ hs)
      hun zero_lt_one

end BigToricMetric
end SGPT.Toric
