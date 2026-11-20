import SGPT.Toric.ToricStratumNormalizedVolume
import SGPT.Trace.TraceMass

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

/-- The original normalized trace mass is the genuine native target MA mass.
The target invariant PSH presentation is produced internally from the source
trace domain; equality uses the literal pulled-back form and actual measures. -/
theorem BigToricMetric.sourceTraceMass_eq_nativeFace_MA
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Set (Fin n)) (mσ : Fin n → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u) :
    let τ := SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined
    let η := toricFaceRestrictedMetric h v J mσ hσ
    ∃ hτ : τ ∈ η.PSHTor,
      SGPT.Trace.sourceTraceMass (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
        (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u = η.MA hτ univ := by
  intro τ η
  obtain ⟨hτ, _hτpos⟩ := exists_sourceTraceEnvelope_nativeFace_mem_positive h v J mσ hσ hu.2 hdefined
  refine ⟨hτ, ?_⟩
  have hform := toricFaceRestrictedMetric_form_sourceInclusion h v J mσ hσ
  have hp := SGPT.Trace.isThetaPshPotential_sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
    (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
    (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined
  have hnative : atlasClosedFormToNative η.atlasForm = η.form := by
    change atlasClosedFormToNative (nativeClosedFormToAtlas η.form) = η.form
    rcases η.form with ⟨β, hβ⟩
    cases β
    rfl
  have hpn := (isThetaPSH_iff_nativeThetaPotential η.atlasForm τ).mp hτ.1
  have hgeo : (atlasClosedFormToNative η.atlasForm).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form).val := by
    rw [hnative]
    dsimp only [η]
    rw [hform]
    exact fun _ _ _ => rfl
  have hmassEq := ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq hgeo hpn hp
  unfold SGPT.Trace.sourceTraceMass
  rw [dif_pos hdefined]
  change diagonalPotentialMass _ τ hp =
    diagonalPotentialMass (atlasClosedFormToNative η.atlasForm) τ hpn
  exact hmassEq.symm

section PositiveOriginalDomain
variable {m k : ℕ} {γ' : K → Fin (m+k) → ℤ} {hs' : latticePolytopeEdgeSmooth γ'}

/-- On the COMPLETE original positive theorem's domain, the source trace
mass is dim(Y)! times actual original lattice-normalized face volume. No
mass is defined from the RHS, and no target Newton or invariant certificate
is supplied. The general zero-ambient-mass corollary is a separate theorem. -/
theorem BigToricMetric.sourceTraceMass_eq_factorial_faceVolume_of_positive
    {D : ToricDivisor γ' hs'} (h : BigToricMetric D)
    {u : PolytopeToricVariety γ' hs' → EReal} (hu : u ∈ h.PSHTor)
    (hupos : 0 < h.MA hu univ)
    (v : latticePolytopeVertices γ') (J : Set (Fin (m+k))) (hJ : Fintype.card J = k)
    (mσ : Fin (m+k) → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ' hs' v '' J) mσ)
    (hν : sourceGenericLelongNumber (n := m+k) (toricFaceSourceInclusion (hs := hs') v J) u = 0)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ' hs')
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs') v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs') v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs') v J) h.form u)
    (hTraceIVolume : 0 < toricFaceSourceTraceIVolume h v J hdefined) :
    SGPT.Trace.sourceTraceMass (polytopeToricKahlerBackground γ' hs')
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs') v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs') v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs') v J) h.form u =
      ((toricFaceDimension J).factorial : ENNReal) *
        toricStratumNormalizedVolume (hs := hs') v J
          (toricStratumTranslatedFace D v J mσ (h.newtonBody u)) := by
  obtain ⟨hτ, hface⟩ := h.sourceTrace_newtonBody_face_of_cone hu hupos v J hJ mσ hσ hν hdefined hTraceIVolume
  obtain ⟨hτ', hmass⟩ := h.sourceTraceMass_eq_nativeFace_MA hu v J mσ hσ hdefined
  let η := toricFaceRestrictedMetric h v J mσ hσ
  let τ := SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ' hs')
    (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs') v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs') v J))
    (contMDiff_toricFaceSourceInclusion (hs := hs') v J) h.form u hdefined
  have hcompact : IsCompact (η.newtonBody τ) :=
    (η.newtonBody_properties (η.nonempty_toricDivisorPolytope_of_mem hτ) hτ).2.1
  rw [hmass, η.MA_univ (η.nonempty_toricDivisorPolytope_of_mem hτ') hτ']
  congr 1
  change volume (η.newtonBody τ) =
    toricStratumNormalizedVolume v J (toricStratumTranslatedFace D v J mσ (h.newtonBody u))
  change (toricFaceRealCharacterCoordinates (hs := hs') v J).symm '' η.newtonBody τ =
    toricStratumTranslatedFace D v J mσ (h.newtonBody u) at hface
  rw [←hface]
  exact (toricStratumNormalizedVolume_image v J hcompact).symm

end PositiveOriginalDomain
end SGPT.Toric
