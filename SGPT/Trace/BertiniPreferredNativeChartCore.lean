import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace SGPT.Trace.Bertini

open Bundle Set Filter
open scoped Manifold ContDiff Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

theorem nativePreferredChartTangent_eq_core (a x : X)
    (hx : x ∈ (complexChartAt (n := n) a).val.source)
    (v : TangentSpace 𝓘(ℂ, ComplexModel n) x) :
    ((mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n)) (complexChartAt (n := n) a).property).mfderiv hx) v =
      (tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange
        (achart (ComplexModel n) x) (achart (ComplexModel n) a) x v := by
  have h := TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓘(ℂ, ComplexModel n)) hx
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx] at h
  have hv := DFunLike.congr_fun h v
  change mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (complexChartAt (n := n) a).val x v = _
  change (tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange
    (achart (ComplexModel n) x) (achart (ComplexModel n) a) x v =
      mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (complexChartAt (n := n) a).val x v at hv
  exact hv.symm

theorem nativePreferredChartTangent_symm_eq_core (a x : X)
    (hx : x ∈ (complexChartAt (n := n) a).val.source) (v : ComplexModel n) :
    (((mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n)) (complexChartAt (n := n) a).property).mfderiv hx)).symm v =
      (tangentBundleCore 𝓘(ℂ, ComplexModel n) X).coordChange
        (achart (ComplexModel n) a) (achart (ComplexModel n) x) x v := by
  let A := ((mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n)) (complexChartAt (n := n) a).property).mfderiv hx)
  apply A.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change v = ((mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, ComplexModel n)) (complexChartAt (n := n) a).property).mfderiv hx) _
  rw [nativePreferredChartTangent_eq_core]
  let T := tangentBundleCore 𝓘(ℂ, ComplexModel n) X
  have hC := T.coordChange_linear_comp (achart (ComplexModel n) a)
    (achart (ComplexModel n) x) (achart (ComplexModel n) a) x
    ⟨⟨hx, mem_chart_source (ComplexModel n) x⟩, hx⟩
  have h := DFunLike.congr_fun hC v
  exact (h.trans (T.coordChange_self (achart (ComplexModel n) a) x hx v)).symm

end SGPT.Trace.Bertini
