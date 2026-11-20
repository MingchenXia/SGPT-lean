import SGPT.Toric.ToricFaceOriginalTailBridge
import SGPT.Okounkov.FlagTraceDimensionTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Okounkov SGPT.Okounkov.ToricTransport SGPT.Okounkov.SourceMultiSlice
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff Classical
variable {m k : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (m + k) → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The SAME original point inclusion of Y, now read in the independently
proved ORIGINAL remaining dimension m. -/
def toricFaceRemainingInclusion (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    (toricFaceRemainingFlagGeometry (hs := hs) v e).carrier →
      (toricFlagGeometry (hs := hs) v e).carrier :=
  fun p => (toricFaceOriginalDirectHomeomorph (hs := hs) v e p).val

theorem contMDiff_toricFaceRemainingInclusion (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel (m + k)) ∞
      (toricFaceRemainingInclusion (hs := hs) v e) := by
  let := directCarrierCharts m k (toricFlagGeometry (hs := hs) v e)
  exact (directCarrierInclusion_contMDiff m k (toricFlagGeometry (hs := hs) v e)).comp
    (contMDiff_toricFaceOriginalDirectHomeomorph (hs := hs) v e)

/-- Equality of actual original point maps, before any trace or body identity. -/
theorem toricFaceRemainingInclusion_eq_source (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    toricFaceRemainingInclusion (hs := hs) v e =
      toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)) := rfl

local instance remainingFaceMeasurable (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    MeasurableSpace (toricFaceRemainingFlagGeometry (hs := hs) v e).carrier := borel _
local instance remainingFaceBorel (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) :
    BorelSpace (toricFaceRemainingFlagGeometry (hs := hs) v e).carrier := ⟨rfl⟩

/-- ORIGINAL defined-trace domain readback on the SAME Y and SAME map,
under the proved rank equality. It is produced, never an extra caller domain. -/
theorem hasPositiveSourceTraceAlong_toricFaceRemaining
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) {u : PolytopeToricVariety γ hs → EReal}
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground
        (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)))
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v
          (toricFlagSelectedIndices e (originalIndex m k))))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form u) :
    SGPT.Trace.HasPositiveSourceTraceAlong (toricFlagGeometry (hs := hs) v e).omega
      (toricFaceRemainingFlagGeometry (hs := hs) v e).omega
      (contMDiff_toricFaceRemainingInclusion (hs := hs) v e) h.form u :=
  hasPositiveSourceTraceAlong_changeFlagDimension (toricFaceOriginalDimension e)
    (toricFaceNativeFlagGeometry (hs := hs) v e) (polytopeToricKahlerBackground γ hs)
    (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)))
    h.form u hdefined

/-- The actual restricted curvature is the SAME original tensor under the
proved rank equality and genuine original point inclusion. -/
theorem toricFaceRemaining_restrictedForm
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k))
    (mσ : Fin (m + k) → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v ''
      toricFlagSelectedIndices e (originalIndex m k)) mσ) :
    changeFlagDimensionForm (toricFaceOriginalDimension e) (toricFaceNativeFlagGeometry (hs := hs) v e)
      (toricFaceRestrictedMetric h v (toricFlagSelectedIndices e (originalIndex m k)) mσ hσ).form =
      ClosedRealOneOneForm.pullback (contMDiff_toricFaceRemainingInclusion (hs := hs) v e) h.form := by
  change changeFlagDimensionForm (toricFaceOriginalDimension e) (toricFaceNativeFlagGeometry (hs := hs) v e)
    (ClosedRealOneOneForm.pullback
      (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form) = _
  exact changeFlagDimensionForm_pullback (toricFaceOriginalDimension e)
    (toricFaceNativeFlagGeometry (hs := hs) v e)
    (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form

/-- POINTWISE literal normalized-trace readback between the SAME actual
native Y dimension descriptions. This preserves every original pole. -/
theorem sourceTraceEnvelope_toricFaceRemaining_eq
    {D : ToricDivisor γ hs} (h : BigToricMetric D) (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k)) {u : PolytopeToricVariety γ hs → EReal}
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground
        (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)))
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v
          (toricFlagSelectedIndices e (originalIndex m k))))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form u) :
    SGPT.Trace.sourceTraceEnvelope (toricFlagGeometry (hs := hs) v e).omega
      (toricFaceRemainingFlagGeometry (hs := hs) v e).omega
      (contMDiff_toricFaceRemainingInclusion (hs := hs) v e) h.form u
      (hasPositiveSourceTraceAlong_toricFaceRemaining h v e hdefined) =
      SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground
          (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)))
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v
            (toricFlagSelectedIndices e (originalIndex m k))))
        (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form u hdefined :=
  sourceTraceEnvelope_changeFlagDimension (toricFaceOriginalDimension e)
    (toricFaceNativeFlagGeometry (hs := hs) v e) (polytopeToricKahlerBackground γ hs)
    (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form u hdefined

/-- The literal SAME original tail inclusion, with actual remaining model
dimension; no commutative-square certificate is supplied externally. -/
theorem toricFaceRemainingInclusion_comp_tail (v : latticePolytopeVertices γ)
    (e : Fin (m + k) ≃ Fin (m + k))
    (y : (originalTail m k (toricFlagGeometry (hs := hs) v e)).carrier) :
    toricFaceRemainingInclusion (hs := hs) v e (toricFaceOriginalTailHomeomorph (hs := hs) v e y) =
      originalInclusion m k (toricFlagGeometry (hs := hs) v e) y :=
  toricFaceOriginalTailHomeomorph_inclusion (hs := hs) v e y

end SGPT.Toric
