import SGPT.PSH.HermitianComparisonCompactPartition

/-! # Actual unit bounds for the manufactured compact chart partition -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonGlobalOneFactor

open Set Filter MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open ChartPartitionRelativeSupports
open Hermitian HermitianGlobalProducts
open scoped Topology ContDiff Distributions

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

namespace CompactPartition

/-- The original nonnegative partition with sum one bounds every actual
compact coordinate test by one, including its zero extension. -/
theorem weight_le_one (C : CompactPartition omega) (i : Fin C.outer.count)
    (z : ComplexModel (m + 1)) : C.weight i z ≤ 1 := by
  rw [C.weight_eq, chartWeight]
  by_cases hz : z ∈ (C.outer.patch i).geometry.chart.val.target
  · rw [indicator_of_mem hz, ← C.outer.sum_one ((C.outer.patch i).geometry.chart.val.symm z)]
    exact Finset.single_le_sum (fun j _ => C.outer.nonneg j _) (Finset.mem_univ i)
  · rw [indicator_of_notMem hz]
    exact zero_le_one

/-- Actual absolute unit bound used by the local derivative-density estimate. -/
theorem abs_weight_le_one (C : CompactPartition omega) (i : Fin C.outer.count)
    (z : ComplexModel (m + 1)) : |C.weight i z| ≤ 1 := by
  rw [abs_of_nonneg (C.weight_nonneg i z)]
  exact C.weight_le_one i z

end CompactPartition

end SGPT.PSH.HermitianComparisonGlobalOneFactor
