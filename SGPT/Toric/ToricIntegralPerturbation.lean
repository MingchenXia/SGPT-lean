import SGPT.Toric.TensorPowerNewtonBodies
import SGPT.Toric.ToricFaceKahlerRestriction
import SGPT.Trace.TraceEnvelope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SourceTraceRepresentativeDefinition
open scoped Topology Manifold ContDiff ENNReal Classical Pointwise
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}
namespace BigToricMetric
variable {D : ToricDivisor γ hs} (h : BigToricMetric D)

/-- The genuine smooth toric metric on the ACTUAL integral divisor N*D+H.
This construction uses actual tensor products and the original Guillemin metric. -/
def integralKahlerPerturbation (N : ℕ) :
    BigToricMetric (N • D + polytopeToricAmpleDivisor γ hs) :=
  (h.naturalTensorPower N).addGuillemin

/-- Literal original curvature of the integral perturbation. -/
theorem integralKahlerPerturbation_form (N : ℕ) :
    (h.integralKahlerPerturbation N).form =
      (N : ℝ) • h.form + (polytopeToricKahlerBackground γ hs).form := by
  rw [integralKahlerPerturbation, addGuillemin_form, naturalTensorPower_form]
  rfl

/-- The original scaled potential lies in the genuine perturbed toric PSH
class, internally produced without a target current/model presentation. -/
theorem mem_PSHTor_integralKahlerPerturbation (N : ℕ) (hN : 0 < N)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    (fun p => ((N : ℝ) : EReal) * u p) ∈ (h.integralKahlerPerturbation N).PSHTor :=
  (h.naturalTensorPower N).mem_PSHTor_addGuillemin (h.mem_PSHTor_naturalTensorPower N hN hu)

/-- The actual perturbed original Newton body is N*Delta+P_H, retaining
all original masses and dimension0. -/
theorem integralKahlerPerturbation_newtonBody (N : ℕ) (hN : 0 < N)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    (h.integralKahlerPerturbation N).newtonBody (fun p => ((N : ℝ) : EReal) * u p) =
      (N : ℝ) • h.newtonBody u + polytopeToricMomentPolytope γ :=
  h.naturalTensorPower_addGuillemin_newtonBody N hN hu

/-- The genuine integral perturbation has positive ORIGINAL ordinary MA,
including when the original current has mass zero. -/
theorem MA_integralKahlerPerturbation_pos (N : ℕ) (hN : 0 < N)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor) :
    0 < (h.integralKahlerPerturbation N).MA (h.mem_PSHTor_integralKahlerPerturbation N hN hu) univ :=
  (h.naturalTensorPower N).MA_addGuillemin_pos (h.mem_PSHTor_naturalTensorPower N hN hu)

/-- The original generic-zero condition internally produces the ACTUAL
positive normalized source trace domain of every genuine integral
perturbation. Actual Kähler pullback is proved from the original geometry. -/
theorem integralKahlerPerturbation_sourceTrace_defined (N : ℕ) (hN : 0 < N)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (hν : sourceGenericLelongNumber (n := n) (toricFaceSourceInclusion (hs := hs) v J) u = 0) :
    SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J)
      (h.integralKahlerPerturbation N).form (fun p => ((N : ℝ) : EReal) * u p) := by
  have huN := h.mem_PSHTor_naturalTensorPower N hN hu
  have hunN : IsThetaPshPotential (h.naturalTensorPower N).form.val
      (fun p => ((N : ℝ) : EReal) * u p) :=
    (isThetaPSH_iff_nativeThetaPotential (h.naturalTensorPower N).atlasForm _).mp huN.1
  have hνN : sourceGenericLelongNumber (n := n) (toricFaceSourceInclusion (hs := hs) v J)
      (fun p => ((N : ℝ) : EReal) * u p) = 0 := by
    rw [SGPT.TraceOperations.sourceGenericLelongNumber_pos_smul _ u (by exact_mod_cast hN), hν, mul_zero]
  change SGPT.Trace.HasPositiveSourceTraceAlong _ _ _
    ((h.naturalTensorPower N).form + (polytopeToricKahlerBackground γ hs).form) _
  exact SGPT.Trace.hasPositiveSourceTraceAlong_add_kahler (toricFaceDimension_le J)
    (polytopeToricKahlerBackground γ hs) (polytopeToricKahlerBackground γ hs)
    (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
    (contMDiff_toricFaceSourceInclusion (hs := hs) v J)
    (isKahler_pullback_toricFaceSourceInclusion v J (polytopeToricKahlerBackground γ hs))
    hunN hνN

end BigToricMetric
end SGPT.Toric
