import SGPT.Toric.ToricFaceSourceTracePotential
import SGPT.Toric.SourceToricPartialBody

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The original normalized trace is genuine source theta-PSH in the
LITERAL actual restricted tensor; its proof is produced from the defined
trace domain and stores no target invariant or volume certificate. -/
theorem sourceThetaPSH_toricFaceSourceTrace
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) {u : PolytopeToricVariety γ hs → EReal}
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u) :
    (ofFixedModel (toricFaceDimension J)
      (PolytopeToricVariety (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))).IsThetaPSH
      (nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback
        (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form))
      (SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
        (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined) := by
  let β := ClosedRealOneOneForm.pullback (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  have hr : atlasClosedFormToNative (nativeClosedFormToAtlas β) = β := by
    rcases β with ⟨β,hβ⟩
    cases β
    rfl
  rw [hr]
  exact SGPT.Trace.isThetaPshPotential_sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
    (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
    (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined

/-- The ORIGINAL I-volume vol(θ|Y,Tr^θ_Y(u)), using the actual source
I-envelope/measure construction. It is independent of any desired Newton
face/volume equality and requires no caller target PSH presentation. -/
def toricFaceSourceTraceIVolume
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) {u : PolytopeToricVariety γ hs → EReal}
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u) : ENNReal :=
  sourceIVolume
    (nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form))
    (SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined)
    (sourceThetaPSH_toricFaceSourceTrace h v J hdefined)

end SGPT.Toric
