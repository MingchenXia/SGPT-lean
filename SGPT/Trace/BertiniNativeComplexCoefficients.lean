import SGPT.Trace.BertiniNativeCoefficientDictionary
import SGPT.Trace.BertiniNativeNormalKernel
import SGPT.Trace.BertiniDiscExhaustion

/-! Literal SAME-domain ordinary complex parameter transport for genuine native coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace SGPT.Trace.BertiniFamilyCanonical
open Set Filter Metric
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Trace.BertiniNativeNormalKernel SGPT.Trace.BertiniDiscExhaustion

def ordinaryCoefficientDomain (V : TopologicalSpace.Opens (ComplexModel 1)) :
    TopologicalSpace.Opens ℂ :=
  ⟨modelOneScalarEquiv.symm ⁻¹' V,V.isOpen.preimage modelOneScalarEquiv.symm.continuous⟩

def ordinaryNativeCoefficient {r : ℕ} (V : TopologicalSpace.Opens (ComplexModel 1))
    (f : V → Fin r → ℂ) (tau : ℂ) : Fin r → ℂ := by
  classical
  exact if h : modelOneScalarEquiv.symm tau ∈ V then f ⟨modelOneScalarEquiv.symm tau,h⟩ else 0

theorem ordinaryNativeCoefficient_at_actual {r : ℕ} (V : TopologicalSpace.Opens (ComplexModel 1))
    (f : V → Fin r → ℂ) (t : V) : ordinaryNativeCoefficient V f (modelOneScalarEquiv t.val) = f t := by
  classical
  simp only [ordinaryNativeCoefficient,LinearIsometryEquiv.symm_apply_apply,dif_pos t.property]

theorem differentiableOn_ordinaryNativeCoefficient {r : ℕ} (V : TopologicalSpace.Opens (ComplexModel 1))
    (f : V → Fin r → ℂ) (hf : ContMDiff 𝓘(ℂ,ComplexModel 1) 𝓘(ℂ,Fin r → ℂ) ∞ f) :
    DifferentiableOn ℂ (ordinaryNativeCoefficient V f) (ordinaryCoefficientDomain V) := by
  classical
  let O := ordinaryCoefficientDomain V
  let g : O → V := fun tau => ⟨modelOneScalarEquiv.symm tau.val,tau.property⟩
  have hg : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ComplexModel 1) ∞ g := by
    apply (ContMDiff.subtypeVal_comp_iff V g).mp
    exact modelOneScalarEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.contMDiff.comp contMDiff_subtype_val
  have heq : (fun tau : O => ordinaryNativeCoefficient V f tau.val) = f ∘ g := by
    funext tau
    have htau : modelOneScalarEquiv.symm tau.val ∈ V := tau.property
    simp only [ordinaryNativeCoefficient,dif_pos htau,Function.comp_apply,g]
  have hcomp : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin r → ℂ) ∞
      (fun tau : O => ordinaryNativeCoefficient V f tau.val) := by
    rw [heq]
    exact hf.comp hg
  intro tau htau
  have hm : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,Fin r → ℂ) ∞ (ordinaryNativeCoefficient V f) tau :=
    contMDiffAt_subtype_iff.mp (hcomp ⟨tau,htau⟩)
  exact (mdifferentiableAt_iff_differentiableAt.mp (hm.mdifferentiableAt (by simp))).differentiableWithinAt

theorem ordinaryCoefficientDomain_parameterDisc (rho : ℝ) :
    (ordinaryCoefficientDomain (parameterDisc rho) : Set ℂ) = ball 0 rho := by
  ext tau
  change dist (modelOneScalarEquiv.symm tau) 0 < rho ↔ dist tau 0 < rho
  rw [dist_zero_right,dist_zero_right,modelOneScalarEquiv.symm.norm_map]

theorem native_pencil_parameter_ordinary {N : ℕ} (a v : ComplexModel N) (tau : ℂ) :
    a-(modelOneScalarEquiv.symm tau) 0 • v = a-tau • v := by
  rw [← modelOneScalarEquiv_apply,modelOneScalarEquiv.apply_symm_apply]

end SGPT.Trace.BertiniFamilyCanonical
