import SGPT.Trace.BertiniNativeCanonicalFiberResidue
import SGPT.Trace.BertiniPreferredNativeChartCore

/-! Actual native canonical frame coefficients in their fixed original
preferred charts. This supplies coordinate readback for proving actual
adjunction-section holomorphy, without an incoming canonical-frame dictionary. -/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

variable [CompactSpace X]

theorem nativeCanonicalFiberInPreferredChart_coordinates (a x : X)
    (hx : x ∈ (complexChartAt (n := n) a).val.source)
    (u : (nativeCanonicalBundle (n := n) (X := X)).Fiber x)
    (v : Fin n → ComplexModel n) :
    nativeCanonicalFiberInChart (complexChartAt (n := n) a) x hx u v =
      ((nativeCanonicalFrame (n := n) a).val ⟨x, u⟩).2 *
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det v := by
  change nativeCanonicalFiberEquiv (n := n) x u
    (fun k => (nativeOriginalChartTangentEquiv (complexChartAt (n := n) a) x hx).symm (v k)) = _
  change nativeCanonicalFiberEquiv (n := n) x u
    (fun k => ((mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n))
      (complexChartAt (n := n) a).property).mfderiv hx).symm (v k)) = _
  simp_rw [nativePreferredChartTangent_symm_eq_core]
  exact nativeCanonicalFiberEquiv_coordinates a x hx u v

end SGPT.Trace.Bertini
