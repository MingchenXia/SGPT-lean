import SGPT.Toric.ToricPerturbedFaceBodies
import SGPT.Toric.ToricTraceDomainPositivity
import SGPT.Toric.ToricStratumVolumeAlgebra
import SGPT.Trace.SourceTraceIntegralPerturbationMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SourceTraceRepresentativeDefinition
open scoped Topology Pointwise Manifold ContDiff ENNReal Classical
variable {m k : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (m+k) → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- Every genuine rational Kähler perturbation has the actual source trace
mass prescribed by the genuine original thickened face, with ALL producer
hypotheses of the positive theorem constructed internally. Neither original
ordinary mass positivity nor an originally defined trace is required. -/
theorem BigToricMetric.sourceTraceMass_inverse_nat_perturbation_eq_faceVolume
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Set (Fin (m+k))) (hJ : Fintype.card J = k)
    (mσ : Fin (m+k) → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (hν : sourceGenericLelongNumber (n := m+k) (toricFaceSourceInclusion (hs := hs) v J) u = 0)
    (N : ℕ) (hN : 0 < N) :
    SGPT.Trace.sourceTraceMass (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J)
      (h.form + (N : ℝ)⁻¹ • (polytopeToricKahlerBackground γ hs).form) u =
      ((toricFaceDimension J).factorial : ENNReal) *
        toricStratumNormalizedVolume (hs := hs) v J
          (toricStratumTranslatedFace D v J mσ (h.newtonBody u) +
            (N : ℝ)⁻¹ • toricStratumReferenceFace (hs := hs) v J) := by
  let H := h.integralKahlerPerturbation N
  let uN : PolytopeToricVariety γ hs → EReal := fun p => ((N : ℝ) : EReal) * u p
  let mH := toricCartierDatum (polytopeToricAmpleDivisor γ hs) v
  let mN := N • mσ + mH
  have huN := h.mem_PSHTor_integralKahlerPerturbation N hN hu
  have hσN : IsToricCartierDatumAlong (N • D + polytopeToricAmpleDivisor γ hs)
      (polytopeToricRay γ hs v '' J) mN :=
    isToricCartierDatumAlong_nsmul_add hσ
      (isToricCartierDatumAlong_vertex (polytopeToricAmpleDivisor γ hs) v J) N
  have hdefined := h.integralKahlerPerturbation_sourceTrace_defined N hN hu v J hν
  have hνN : sourceGenericLelongNumber (n := m+k) (toricFaceSourceInclusion (hs := hs) v J) uN = 0 := by
    rw [SGPT.TraceOperations.sourceGenericLelongNumber_pos_smul _ u (by exact_mod_cast hN),hν,mul_zero]
  have hpositive := H.sourceTraceMass_eq_factorial_faceVolume_of_positive huN
    (h.MA_integralKahlerPerturbation_pos N hN hu) v J hJ mN hσN hνN hdefined
    (H.toricFaceSourceTraceIVolume_pos huN v J mN hσN hdefined)
  dsimp only [H,mN,mH] at hpositive
  rw [h.integralKahlerPerturbation_form N,
    h.integralKahlerPerturbation_translatedFace hu v J mσ hσ N hN] at hpositive
  have hscale := SGPT.Trace.sourceTraceMass_integral_perturbation (toricFaceDimension_le J)
    (polytopeToricKahlerBackground γ hs)
    (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
    (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hα0 : ENNReal.ofReal ((N : ℝ) ^ toricFaceDimension J) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (pow_pos hNR _)).ne'
  apply (ENNReal.mul_right_inj hα0 ENNReal.ofReal_ne_top).mp
  calc
    _ = SGPT.Trace.sourceTraceMass (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
        (contMDiff_toricFaceSourceInclusion (hs := hs) v J)
        ((N : ℝ) • h.form + (polytopeToricKahlerBackground γ hs).form) uN := hscale.symm
    _ = ((toricFaceDimension J).factorial : ENNReal) *
        toricStratumNormalizedVolume (hs := hs) v J
          ((N : ℝ) • toricStratumTranslatedFace D v J mσ (h.newtonBody u) +
            toricStratumReferenceFace (hs := hs) v J) := hpositive
    _ = _ := by
      rw [toricStratumNormalizedVolume_smul_add v J hNR]
      ac_rfl

end SGPT.Toric
