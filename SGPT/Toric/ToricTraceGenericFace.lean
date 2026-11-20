import SGPT.Toric.ToricSourceTraceNewtonFace
import SGPT.Toric.BigToric2Lelong
import SGPT.Trace.TraceMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SourceTraceRepresentativeDefinition
open scoped Topology Manifold ContDiff ENNReal Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual native source inclusion has EXACTLY the original carrier's
generic source Lelong value, proved from its genuine surjective image. -/
theorem sourceGenericLelong_toricFaceSourceInclusion
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (u : PolytopeToricVariety γ hs → EReal) :
    sourceGenericLelongNumber (n := n) (toricFaceSourceInclusion (hs := hs) v J) u =
      (ofFixedModel n (PolytopeToricVariety γ hs)).sourceGenericLelong u
        (toricOrbitClosure (polytopeToricRay γ hs v '' J)) := by
  obtain ⟨e,i,he⟩ := exists_toricFlagSelectedIndices J
  subst J
  rw [←toricFlagRays_eq_selectedIndices]
  change _ = (ofFixedModel n (PolytopeToricVariety γ hs)).sourceGenericLelong u (toricFlag hs v e i)
  rw [←range_toricFaceNativeEmbedding_eq_toricFlag]
  simp only [sourceGenericLelongNumber, sourceGenericLelong, sourceLelong_ofFixedModel_eq,
    iInf_range, toricFaceSourceInclusion]
  rfl

/-- Source generic zero is equivalent to the original Newton body meeting
its original selected face, in every dimension and without positive mass. -/
theorem BigToricMetric.sourceGenericLelong_nativeFace_eq_zero_iff
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    sourceGenericLelongNumber (n := n) (toricFaceSourceInclusion (hs := hs) v J) u = 0 ↔
      (h.newtonBody u ∩ toricDivisorFace D (polytopeToricRay γ hs v '' J)).Nonempty := by
  rw [sourceGenericLelong_toricFaceSourceInclusion]
  have hf := (h.sourceGenericLelong_toricOrbitClosure_eq_zero_tfae hu v J.toFinset).out 0 2
  simpa only [Set.coe_toFinset, toricDivisorFace] using hf

end SGPT.Toric
