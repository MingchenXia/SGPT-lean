import SGPT.Toric.ToricFaceRemainingInclusion
import SGPT.Toric.ToricSourceBodyReadback
import SGPT.Okounkov.FlagNormalizedTraceBodySlice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.Okounkov SGPT.Okounkov.ToricTransport SGPT.Okounkov.SourceMultiSlice
open SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open scoped Topology Manifold ContDiff Classical ENNReal
variable {m k : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (m + k) → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- ACTUAL native source body slice for the original normalized toric trace.
The genuine restricted metric, normalized trace PSH/positive MA, original-tail
trace/P-equivalence, entire flag geometry and actual body transport are ALL
produced internally. The inputs are original toric PSH and defined trace,
arbitrary original Cartier representative and original toric geometry only. -/
theorem toricFace_sourcePartialBody_zeroSlice
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {φ : PolytopeToricVariety γ hs → EReal} (hφ : φ ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (e : Fin (m + k) ≃ Fin (m + k))
    (mσ : Fin (m + k) → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v ''
      toricFlagSelectedIndices e (originalIndex m k)) mσ)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground
        (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)))
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v
          (toricFlagSelectedIndices e (originalIndex m k))))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form φ) :
    let τ := SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground
        (toricFaceProjectedFamily (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k)))
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v
          (toricFlagSelectedIndices e (originalIndex m k))))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))) h.form φ hdefined
    let η := toricFaceRestrictedMetric h v (toricFlagSelectedIndices e (originalIndex m k)) mσ hσ
    ∃ hτ : τ ∈ η.PSHTor, 0 < η.MA hτ univ ∧
      zeroSlice m k (h.sourceToricPartialBody hφ v e) =
        (fun q : Fin (toricFaceDimension (toricFlagSelectedIndices e (originalIndex m k))) → ℝ =>
          fun j : Fin m => q (Fin.cast (toricFaceOriginalDimension e).symm j)) ''
          η.sourceToricPartialBody hτ
            (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))
              (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))))
            (toricFaceTailOrder (hs := hs) v e (originalIndex m k)) := by
  intro τ η
  obtain ⟨hτ,hτpos⟩ := exists_sourceTraceEnvelope_nativeFace_mem_positive h v
    (toricFlagSelectedIndices e (originalIndex m k)) mσ hσ hφ.2 hdefined
  refine ⟨hτ,hτpos,?_⟩
  let F := toricFlagGeometry (hs := hs) v e
  let W := toricFaceRemainingFlagGeometry (hs := hs) v e
  let N := toricFaceNativeFlagGeometry (hs := hs) v e
  let : MeasurableSpace W.carrier := borel _
  let : BorelSpace W.carrier := ⟨rfl⟩
  let hd := toricFaceOriginalDimension e
  let hι := contMDiff_toricFaceRemainingInclusion (hs := hs) v e
  let hdefined' := hasPositiveSourceTraceAlong_toricFaceRemaining h v e hdefined
  have hφn : IsThetaPshPotential h.form.val φ :=
    (isThetaPSH_iff_nativeThetaPotential h.atlasForm φ).mp hφ.1
  have hτn : IsThetaPshPotential η.form.val τ :=
    (isThetaPSH_iff_nativeThetaPotential η.atlasForm τ).mp hτ.1
  have hτcast : IsThetaPshPotential (changeFlagDimensionForm hd N η.form).val τ :=
    thetaPsh_changeFlagDimension hd N hτn
  have hslice := normalizedTrace_zeroSlice_of_originalTail_biholomorphic m k F W
    (toricFaceOriginalTailHomeomorph (hs := hs) v e)
    (toricFaceOriginalTailHomeomorph_image_flag (hs := hs) v e)
    (contMDiff_toricFaceOriginalTailHomeomorph (hs := hs) v e)
    (contMDiff_toricFaceOriginalTailHomeomorph_symm (hs := hs) v e) hι
    (toricFaceRemainingInclusion_comp_tail (hs := hs) v e) hφn hdefined'
  have hform := toricFaceRemaining_restrictedForm h v e mσ hσ
  have hpotential := sourceTraceEnvelope_toricFaceRemaining_eq h v e hdefined
  have hbody := sourceGeneralBody_congr W hform.symm hpotential
    (SGPT.Trace.isThetaPshPotential_sourceTraceEnvelope F.omega W.omega hι h.form φ hdefined') hτcast
  have hdimBody := sourceGeneralBody_changeFlagDimension hd N hτn
  calc
    zeroSlice m k (h.sourceToricPartialBody hφ v e) =
        zeroSlice m k (SourceTestCurveAllDimensions.generalBody F h.form ⟨φ,hφn⟩) := by
      rw [h.sourceToricPartialBody_eq_sourceGeneralBody hφ v e]
    _ = SourceTestCurveAllDimensions.generalBody W (ClosedRealOneOneForm.pullback hι h.form)
        ⟨SGPT.Trace.sourceTraceEnvelope F.omega W.omega hι h.form φ hdefined',
          SGPT.Trace.isThetaPshPotential_sourceTraceEnvelope F.omega W.omega hι h.form φ hdefined'⟩ := hslice
    _ = SourceTestCurveAllDimensions.generalBody W (changeFlagDimensionForm hd N η.form) ⟨τ,hτcast⟩ := hbody
    _ = (fun q : Fin (toricFaceDimension (toricFlagSelectedIndices e (originalIndex m k))) → ℝ =>
        fun j : Fin m => q (Fin.cast hd.symm j)) ''
        SourceTestCurveAllDimensions.generalBody N η.form ⟨τ,hτn⟩ := hdimBody
    _ = _ := by
      exact congrArg (Set.image (fun q : Fin (toricFaceDimension (toricFlagSelectedIndices e (originalIndex m k))) → ℝ =>
        fun j : Fin m => q (Fin.cast hd.symm j)))
        (η.sourceToricPartialBody_eq_sourceGeneralBody hτ
          (toricFaceVertexEquiv (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))
            (toricFaceBaseVertex (hs := hs) v (toricFlagSelectedIndices e (originalIndex m k))))
          (toricFaceTailOrder (hs := hs) v e (originalIndex m k))).symm

end SGPT.Toric
