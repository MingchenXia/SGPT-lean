import SGPT.Foundations.Analysis.Pending.LocalHolomorphicLelongReaderCovariance
import SGPT.Foundations.Analysis.Pending.DemaillyApproximantDivisorialLelong

set_option autoImplicit false

/-! # Genuine flattened point readers and the whole-divisor infimum bound

The whole infimum is bounded by actual local pieces after genuine chart
covariance. No equality of generic minima or Siu certificate is supplied.
This supplementary raw-reader adaptation preserves all extended values.
Reference: Demailly, CADG, local holomorphic coordinates; Xia, divisorial
Lelong readers, with the distinction between local pieces and whole divisors.
-/

open Set Filter Metric
open scoped Topology Manifold ENNReal

namespace SGPT.Foundations.Analysis.Pending.FlattenedGlobalGenericLelongComparison

open FirstPass FirstPass.NonKahlerLocus DemaillyApproximantDivisorialLelong

noncomputable section

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  {E : Set Y} {x : Y}

/-- Genuine charts identify the literal reader at every point in the actual
flattening target, for arbitrary extended-real weights. -/
theorem lelongNumber_comp_point_eq (Φ : DivisorFlattening (m := m) E x)
    (v : Y → EReal) {z : ComplexModel (m + 1)} (hz : z ∈ Φ.Φ.target) :
    lelongNumber (n := m + 1) (fun w => v (Φ.point w)) z =
      lelongNumber (n := m + 1) v (Φ.point z) := by
  let e := complexChartAt (n := m + 1) x
  have hcov := LocalHolomorphicLelongReaderCovariance.lelongNumber_comp_inv_eq
    Φ.Φ (Φ.Φ.mapsTo_invFun hz) (u := chartFunction v e)
  rw [Φ.Φ.right_inv z hz] at hcov
  have hchart := LelongChartReaderInvariance.lelongNumber_chartFunction_eq e
    (Φ.point_mem_source hz) (u := v)
  rw [Φ.chart_point hz] at hchart
  exact hcov.trans hchart

/-- An actual positive radius is supplied internally, and the whole divisor
infimum is at most every local hyperplane-piece infimum inside this radius. -/
theorem exists_radius_generic_le_local (Φ : DivisorFlattening (m := m) E x)
    (v : Y → EReal) :
    ∃ r : ℝ, 0 < r ∧ ∀ R : ℝ, 0 < R → R ≤ r →
      (⨅ y ∈ E, lelongNumber (n := m + 1) v y) ≤
        (⨅ z ∈ ball (0 : ComplexModel (m + 1)) R ∩ {z | z (Fin.last m) = 0},
          lelongNumber (n := m + 1) (fun w => v (Φ.point w)) z) := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    (Φ.Φ.isOpen_target.mem_nhds Φ.zero_mem_target)
  refine ⟨r, hr, fun R _ hRr => le_iInf fun z => le_iInf fun hz => ?_⟩
  have hzT : z ∈ Φ.Φ.target := hsub ((ball_subset_ball hRr) hz.1)
  have hpoint : Φ.point z ∈ E := Φ.point_mem hzT hz.2
  calc
    _ ≤ lelongNumber (n := m + 1) v (Φ.point z) :=
      iInf_le_of_le (Φ.point z) (iInf_le_of_le hpoint le_rfl)
    _ = _ := (lelongNumber_comp_point_eq Φ v hzT).symm

end
end SGPT.Foundations.Analysis.Pending.FlattenedGlobalGenericLelongComparison
