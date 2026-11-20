import SGPT.Toric.ToricTraceDomainPositivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

private theorem normalizedTraceIVolume_congr_form
    {d : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
    [IsComplexManifold d Y] [MeasurableSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    {α β : AtlasClosedRealOneOneForm (ofFixedModel d Y)} {f : Y → EReal}
    (heq : α = β) (hα : (ofFixedModel d Y).IsThetaPSH α f)
    (hβ : (ofFixedModel d Y).IsThetaPSH β f) :
    sourceIVolume α f hα = sourceIVolume β f hβ := by
  cases heq
  rfl

/-- Literal ORIGINAL source I-volume of the actual normalized trace, with
EXACTLY the book's convention0 when the normalized trace is undefined.
This is defined entirely from the original source trace and I-envelope,
independently of every Newton body or proposed volume identity. -/
def toricFaceNormalizedTraceVolume
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (u : PolytopeToricVariety γ hs → EReal) : ENNReal :=
  if hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u then
    toricFaceSourceTraceIVolume h v J hdefined
  else 0

/-- For the literal actual normalized toric trace, original source I-volume
and original ordinary trace mass agree. Actual source I-envelopes, the
produced genuine invariant PSH target and the independent toric MA formula
prove this equality, including the undefined-trace0 convention. -/
theorem BigToricMetric.normalizedTraceVolume_eq_sourceTraceMass
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (mσ : Fin n → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ) :
    toricFaceNormalizedTraceVolume h v J u =
      SGPT.Trace.sourceTraceMass (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
        (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u := by
  by_cases hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u
  · rw [toricFaceNormalizedTraceVolume,dif_pos hdefined]
    obtain ⟨hτ,hmass⟩ := h.sourceTraceMass_eq_nativeFace_MA hu v J mσ hσ hdefined
    let η := toricFaceRestrictedMetric h v J mσ hσ
    let τ := SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined
    have hform := toricFaceRestrictedMetric_form_sourceInclusion h v J mσ hσ
    have hIVeq : toricFaceSourceTraceIVolume h v J hdefined = sourceIVolume η.atlasForm τ hτ.1 := by
      unfold toricFaceSourceTraceIVolume
      exact normalizedTraceIVolume_congr_form (congrArg nativeClosedFormToAtlas hform).symm _ _
    rw [hIVeq,hmass,η.sourceIVolume_eq_factorial_volume_newtonBody hτ,
      η.MA_univ (η.nonempty_toricDivisorPolytope_of_mem hτ) hτ]
  · simp only [toricFaceNormalizedTraceVolume,SGPT.Trace.sourceTraceMass,dif_neg hdefined]

end SGPT.Toric
