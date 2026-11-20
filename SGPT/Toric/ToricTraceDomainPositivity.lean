import SGPT.Toric.ToricPositiveSourceTraceMass
import SGPT.Toric.ToricTraceGenericFace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SourceTraceRepresentativeDefinition DiagonalMass
open scoped Topology Manifold ContDiff ENNReal Classical
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

private theorem sourceIVolume_congr_form
    {d : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel d) Y]
    [IsComplexManifold d Y] [MeasurableSpace Y] [CompactSpace Y] [ConnectedSpace Y]
    {α β : AtlasClosedRealOneOneForm (ofFixedModel d Y)} {f : Y → EReal}
    (heq : α = β) (hα : (ofFixedModel d Y).IsThetaPSH α f)
    (hβ : (ofFixedModel d Y).IsThetaPSH β f) :
    sourceIVolume α f hα = sourceIVolume β f hβ := by
  cases heq
  rfl

/-- The original defined normalized-trace domain already produces positive
original I-volume for the same toric source trace. The independent actual
source I-envelope construction and genuine toric MA formula prove this;
no face formula or target volume positivity is assumed. -/
theorem BigToricMetric.toricFaceSourceTraceIVolume_pos
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (mσ : Fin n → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u) :
    0 < toricFaceSourceTraceIVolume h v J hdefined := by
  obtain ⟨hτ,hτpos⟩ := exists_sourceTraceEnvelope_nativeFace_mem_positive h v J mσ hσ hu.2 hdefined
  let η := toricFaceRestrictedMetric h v J mσ hσ
  let τ := SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
    (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
    (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined
  have hform := toricFaceRestrictedMetric_form_sourceInclusion h v J mσ hσ
  have hIV0 : 0 < sourceIVolume η.atlasForm τ hτ.1 := by
    rw [η.sourceIVolume_eq_factorial_volume_newtonBody hτ,
      ←η.MA_univ (η.nonempty_toricDivisorPolytope_of_mem hτ) hτ]
    exact hτpos
  have hIVeq : toricFaceSourceTraceIVolume h v J hdefined = sourceIVolume η.atlasForm τ hτ.1 := by
    unfold toricFaceSourceTraceIVolume
    exact sourceIVolume_congr_form (congrArg nativeClosedFormToAtlas hform).symm _ _
  rw [hIVeq]
  exact hIV0

/-- An original source normalized trace can only be defined at source
generic Lelong zero. This is read from its actual full trace reader. -/
theorem sourceGenericLelong_zero_of_toricFaceTrace_defined
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    {u : PolytopeToricVariety γ hs → EReal}
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u) :
    sourceGenericLelongNumber (n := n) (toricFaceSourceInclusion (hs := hs) v J) u = 0 := by
  obtain ⟨τ,hT,_⟩ := hdefined
  exact hT.1

end SGPT.Toric
