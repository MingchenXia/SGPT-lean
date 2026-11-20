import SGPT.Toric.PointBlowupGeometry
import SGPT.Toric.BigToric2MetricExistence

/-! Manufacture the actual physical H-E metric from its original Cartier sections. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.BDivisor.StrictPencilNext

open SGPT.Toric SGPT.Toric.BlowdownDraft
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff BigOperators

variable (hs : latticePolytopeEdgeSmooth blowupGenerator)

theorem originalPencil_isFubiniStudyDivisor :
    IsFubiniStudyDivisor (blowupDirectionDivisor hs) := by
  intro v w i
  obtain ⟨j, hj⟩ := blowupDirectionDatum_occurs hs w
  have hm := (mem_toricLatticePoints_iff (blowupDirectionDivisor hs)
    (blowupDirectionLatticePoint hs j).val).mp
      (blowupDirectionLatticePoint hs j).property v i
  change 0 ≤ fsExponent (blowupDirectionDivisor hs) v w i
  rw [fsExponent, ← hj]
  simpa only [intPairing, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    using sub_nonneg.mpr hm

def originalPencilFsWeightFamily : ToricWeightFamily (blowupDirectionDivisor hs) where
  weight := fsWeight (blowupDirectionDivisor hs)
  smooth := contDiff_fsWeight (blowupDirectionDivisor hs)
  invariant := fsWeight_action (blowupDirectionDivisor hs)
  transition := fsWeight_transition (blowupDirectionDivisor hs)
    (originalPencil_isFubiniStudyDivisor hs)
  pluriharmonic := smoothDDC_fsWeight_sub (blowupDirectionDivisor hs)
    (originalPencil_isFubiniStudyDivisor hs)

def originalPencilFsMetric : BigToricMetric (blowupDirectionDivisor hs) :=
  (originalPencilFsWeightFamily hs).toBigToricMetric

theorem originalPencilFsMetric_weight (v : latticePolytopeVertices blowupGenerator)
    (z : ComplexModel 2) :
    (originalPencilFsMetric hs).weight v z = fsWeight (blowupDirectionDivisor hs) v z := rfl

end SGPT.BDivisor.StrictPencilNext
