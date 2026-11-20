import SGPT.Foundations.Analysis.Pending.XiaoPureSmoothTopology
import SGPT.Foundations.Analysis.Pending.XiaoSmoothBottChernClosure

set_option autoImplicit false

/-! # Actual pure coefficient quotient closure and Xiao's literal nef difference criterion -/

open Set Filter Topology
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.XiaoPureSmoothBottChernClosure

open FirstPass FirstPass.PositiveClasses XiaoPureSmoothTopology XiaoSmoothBottChernClosure
  XiaoBottChernC0Closure

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- The genuine Bott-Chern quotient topology coinduced only by actual compact scalar coefficient jets. -/
abbrev classPureSmoothTopology : TopologicalSpace (RealBottChern n M) :=
  TopologicalSpace.coinduced RealBottChern.ofRepresentative formPureSmoothTopology

/-- The actual joined smooth quotient equals the independently defined actual pure coefficient quotient. -/
theorem classSmoothTopology_eq_pure (w : KahlerBackground n M) :
    classSmoothTopology w = classPureSmoothTopology := by
  rw [classSmoothTopology, formSmoothTopology_eq_pure]

/-- The actual representative projection is genuinely open and quotient for the actual pure coefficient topology. -/
theorem isOpenQuotientMap_ofRepresentative (w : KahlerBackground n M) :
    @IsOpenQuotientMap (ClosedRealOneOneForm n M) (RealBottChern n M)
      formPureSmoothTopology classPureSmoothTopology RealBottChern.ofRepresentative := by
  rw [← formSmoothTopology_eq_pure w, ← classSmoothTopology_eq_pure w]
  exact XiaoSmoothBottChernClosure.isOpenQuotientMap_ofRepresentative w

/-- Closure of the actual Kähler cone in the actual pure coefficient quotient is genuine smooth nef approximation. -/
theorem mem_pureClosure_iff_classNef (w : KahlerBackground n M) (α : RealBottChern n M) :
    α ∈ @closure (RealBottChern n M) classPureSmoothTopology actualKahlerCone ↔
      ClassNefWithRespectTo w α := by
  rw [← classSmoothTopology_eq_pure w]
  exact mem_smoothClosure_iff_classNef w α

/-- Xiao's actual numerical criterion consumes closure in the actual pure smooth coefficient quotient. -/
theorem isBigClass_sub_of_pureClosure_gap
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [CompactSpace X] [PreconnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    (w : KahlerBackground (m + 1) X) (α β : RealBottChern (m + 1) X)
    (hα : α ∈ @closure (RealBottChern (m + 1) X) classPureSmoothTopology actualKahlerCone)
    (hβ : β ∈ @closure (RealBottChern (m + 1) X) classPureSmoothTopology actualKahlerCone)
    (hgap : 0 < XiaoClassNefDifference.classTopIntersection w α -
      4 * (m + 1 : ℝ) * XiaoClassNefDifference.classOneSlotIntersection w α β) :
    NonKahlerLocus.IsBigClass (α - β) :=
  XiaoClassNefDifference.isBigClass_sub_of_classNef_gap w α β
    ((mem_pureClosure_iff_classNef w α).mp hα)
    ((mem_pureClosure_iff_classNef w β).mp hβ) hgap

end

end SGPT.Foundations.Analysis.Pending.XiaoPureSmoothBottChernClosure
