import SGPT.Toric.ToricFaceRestrictedMetric
import SGPT.Toric.ToricFaceTorusEquivariance
import SGPT.Toric.PolytopeToricOperations
import SGPT.Toric.BigToricMongeAmpere
import SGPT.Trace.BiholomorphicSourceTrace
import SGPT.Trace.TraceMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open DiagonalMass
open scoped Topology Manifold ContDiff ENNReal
variable {n : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin n → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- The actual original inclusion of the genuine native realization of Y,
with the SAME original source toric manifold types recorded explicitly. -/
def toricFaceSourceInclusion (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    PolytopeToricVariety (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J) →
      PolytopeToricVariety γ hs := toricFaceNativeEmbedding (hs := hs) v J

theorem contMDiff_toricFaceSourceInclusion (v : latticePolytopeVertices γ) (J : Set (Fin n)) :
    ContMDiff 𝓘(ℂ, ComplexModel (toricFaceDimension J)) 𝓘(ℂ, ComplexModel n) ∞
      (toricFaceSourceInclusion (hs := hs) v J) := contMDiff_toricFaceNativeEmbedding v J

/-- Actual dimension bound, manufactured from the real complement lattice. -/
theorem toricFaceDimension_le (J : Set (Fin n)) : toricFaceDimension J ≤ n := by
  classical
  simpa only [toricFaceDimension, Fintype.card_fin] using
    Fintype.card_subtype_le (fun j : Fin n => j ∉ J)

/-- The source trace reference is EXACTLY the SAME actual restricted metric
curvature, rather than a cohomology-class or form-preservation certificate. -/
theorem toricFaceRestrictedMetric_form_sourceInclusion
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ) :
    (toricFaceRestrictedMetric h v J mσ hσ).form =
      ClosedRealOneOneForm.pullback (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form := rfl

/-- The ACTUAL source normalized trace in the genuine native realization of
the SAME original Y is pointwise compact-torus invariant, including every
original pole and all dimensions. Actual compact lifts, the literal commuting
square and actual restricted metric produce all symmetry hypotheses internally. -/
theorem sourceTraceEnvelope_nativeFace_invariant
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    {u : PolytopeToricVariety γ hs → EReal} (hu : PolytopeToricInvariant γ hs u)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u) :
    PolytopeToricInvariant (toricFaceProjectedFamily (hs := hs) v J)
      (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J)
      (SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
        (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined) := by
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  let hmetric := toricFaceRestrictedMetric h v J mσ hσ
  let := originalPolytopeNativeChartedSpace γ hs
  let := originalPolytopeNativeIsComplexManifold γ hs
  let := originalPolytopeNativeChartedSpace γY hY
  let := originalPolytopeNativeIsComplexManifold γY hY
  have hform := toricFaceRestrictedMetric_form_sourceInclusion h v J mσ hσ
  have hpres (a : Fin (toricFaceDimension J) → ℂˣ) (ha : IsCompactTorusElement a) :
      (ClosedRealOneOneForm.pullback (contMDiff_originalPolytopeNativeAction γY hY a ∞)
        (ClosedRealOneOneForm.pullback (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form)).val.GeometricallyEq
      (ClosedRealOneOneForm.pullback (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form).val := by
    rw [← hform, ClosedRealOneOneForm.pullback_val, hmetric.form_compact_pullback_eq a ha]
    exact fun _ _ _ => rfl
  intro a ha p
  let b := toricFaceTorusSection (hs := hs) v J a
  have hb := toricFaceTorusSection_compact (hs := hs) v J a ha
  have hcomm (y : PolytopeToricVariety γY hY) :
      originalPolytopeNativeAction γ b (toricFaceSourceInclusion (hs := hs) v J y) =
        toricFaceSourceInclusion (hs := hs) v J (originalPolytopeNativeAction γY a y) := by
    have heq := toricFaceNativeEmbedding_equivariant (hs := hs) v J b y
    rw [toricFaceTorusQuotient_section] at heq
    exact heq.symm
  exact SGPT.Trace.sourceTraceEnvelope_comp_biholomorphic_symmetry (toricFaceDimension_le J)
    (polytopeToricKahlerBackground γ hs) (polytopeToricKahlerBackground γY hY)
    (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form
    (originalPolytopeNativeAction γ b) (originalPolytopeNativeAction γY a)
    (contMDiff_originalPolytopeNativeAction γ hs b ∞)
    (contMDiff_originalPolytopeNativeAction γ hs b⁻¹ ∞)
    (contMDiff_originalPolytopeNativeAction γY hY a ∞)
    (contMDiff_originalPolytopeNativeAction γY hY a⁻¹ ∞)
    hcomm (hpres a ha) (hpres a⁻¹ (isCompactTorusElement_inv ha)) (funext (hu b hb)) hdefined p

/-- Source thm:tracetor's actual target potential and positive-mass producer.
The ORIGINAL defined normalized-trace domain produces genuine toric PSH and
positive original MA internally in the SAME restricted metric; neither an
invariant presentation nor extra target mass is supplied by the caller. -/
theorem exists_sourceTraceEnvelope_nativeFace_mem_positive
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    (v : latticePolytopeVertices γ) (J : Set (Fin n))
    (mσ : Fin n → ℤ) (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ)
    {u : PolytopeToricVariety γ hs → EReal} (hu : PolytopeToricInvariant γ hs u)
    (hdefined : SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u) :
    ∃ hτ : SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
        (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined ∈
      (toricFaceRestrictedMetric h v J mσ hσ).PSHTor,
      0 < (toricFaceRestrictedMetric h v J mσ hσ).MA hτ univ := by
  let γY := toricFaceProjectedFamily (hs := hs) v J
  let hY := latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J
  let η := toricFaceRestrictedMetric h v J mσ hσ
  let τ := SGPT.Trace.sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
    (polytopeToricKahlerBackground γY hY) (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined
  have hform := toricFaceRestrictedMetric_form_sourceInclusion h v J mσ hσ
  have hp := SGPT.Trace.isThetaPshPotential_sourceTraceEnvelope (polytopeToricKahlerBackground γ hs)
    (polytopeToricKahlerBackground γY hY) (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u hdefined
  have hpη : IsThetaPshPotential η.form.val τ := by
    dsimp only [η]
    rw [hform]
    exact hp
  have hτ : τ ∈ η.PSHTor :=
    ⟨(isThetaPSH_iff_nativeThetaPotential η.atlasForm τ).mpr hpη,
      sourceTraceEnvelope_nativeFace_invariant h v J mσ hσ hu hdefined⟩
  refine ⟨hτ, ?_⟩
  have hmass := (SGPT.Trace.hasPositiveSourceTraceAlong_iff_sourceTraceMass_pos
    (toricFaceDimension_le J) (polytopeToricKahlerBackground γ hs)
    (polytopeToricKahlerBackground γY hY) (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u).mp hdefined
  have hmassη : 0 < diagonalPotentialMass η.form τ hpη := by
    unfold SGPT.Trace.sourceTraceMass at hmass
    split_ifs at hmass with hd
    · exact hmass
    · exact False.elim (hd hdefined)
  have hnative : atlasClosedFormToNative η.atlasForm = η.form := by
    change atlasClosedFormToNative (nativeClosedFormToAtlas η.form) = η.form
    rcases η.form with ⟨β, hβ⟩
    cases β
    rfl
  have hpn := (isThetaPSH_iff_nativeThetaPotential η.atlasForm τ).mp hτ.1
  have hgeo : (atlasClosedFormToNative η.atlasForm).val.GeometricallyEq η.form.val := by
    rw [hnative]
    exact fun _ _ _ => rfl
  have hmassEq := ModificationMassInvariance.diagonalPotentialMass_congr_geometricallyEq hgeo hpn hpη
  change 0 < diagonalPotentialMass (atlasClosedFormToNative η.atlasForm) τ hpn
  rw [hmassEq]
  exact hmassη

end SGPT.Toric
