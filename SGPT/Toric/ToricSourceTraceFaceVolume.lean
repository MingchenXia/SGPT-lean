import SGPT.Toric.ToricIntegralTraceFaceMass
import SGPT.Convex.CompactMinkowskiRightLimit
import SGPT.Toric.ToricNormalizedTraceVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SourceTraceRepresentativeDefinition DiagonalMass
open scoped Topology Pointwise Manifold ContDiff ENNReal Classical
variable {m k : ℕ} {K : Type*} [Fintype K] [Nonempty K]
variable {γ : K → Fin (m+k) → ℤ} {hs : latticePolytopeEdgeSmooth γ}

/-- COMPLETE original source cor:tor_tr_vol for EVERY original toric PSH
potential, including zero original ordinary MA mass, undefined normalized
trace with ORIGINAL mass0 convention, all poles, every cone/rank, arbitrary
original Cartier representative and ambient/target dimension0. The RHS is
the independent Haar measure on the ACTUAL original annihilator, normalized
by its genuine integral basis. All positive perturbations, trace domains,
restricted metrics, face identities and both limits are produced internally;
no target invariant, trace, body, limit or volume certificate is an input. -/
theorem BigToricMetric.sourceTraceMass_eq_factorial_faceVolume
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Set (Fin (m+k))) (hJ : Fintype.card J = k)
    (mσ : Fin (m+k) → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ) :
    SGPT.Trace.sourceTraceMass (polytopeToricKahlerBackground γ hs)
      (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
        (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
      (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u =
      ((toricFaceDimension J).factorial : ENNReal) *
        toricStratumNormalizedVolume (hs := hs) v J
          (toricStratumTranslatedFace D v J mσ (h.newtonBody u)) := by
  by_cases hν : sourceGenericLelongNumber (n := m+k) (toricFaceSourceInclusion (hs := hs) v J) u = 0
  · by_cases hn : m+k = 0
    · have hun : IsThetaPshPotential h.form.val u :=
        (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1
      obtain ⟨τ,hT⟩ := SGPT.TraceOperations.exists_sourceTrace_of_globalQuasiPshPotential
        (toricFaceDimension_le J) (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
        hun.quasiPshPotential (contMDiff_toricFaceSourceInclusion (hs := hs) v J) hν
      have hdefined := SGPT.Trace.hasPositiveSourceTraceAlong_of_dim_zero
        (toricFaceDimension_le J) hn h.form hT
      have hMA : 0 < h.MA hu univ := by
        have hpn := (isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1
        change 0 < diagonalPotentialMass (atlasClosedFormToNative h.atlasForm) u hpn
        exact SGPT.Trace.hasPositivePotentialMass_of_dim_zero hn _ hpn
      exact h.sourceTraceMass_eq_factorial_faceVolume_of_positive hu hMA v J hJ mσ hσ hν hdefined
        (h.toricFaceSourceTraceIVolume_pos hu v J mσ hσ hdefined)
    · let A := toricStratumTranslatedFace D v J mσ (h.newtonBody u)
      let B := toricStratumReferenceFace (hs := hs) v J
      let μ := toricStratumNormalizedVolume (hs := hs) v J
      let t : ℕ → ℝ := fun j => ((j+1 : ℕ) : ℝ)⁻¹
      have hA : IsCompact A := isCompact_toricStratumTranslatedFace v J mσ hσ
        (h.newtonBody_properties (h.nonempty_toricDivisorPolytope_of_mem hu) hu).2.2.2
        (h.newtonBody_properties (h.nonempty_toricDivisorPolytope_of_mem hu) hu).2.1
      have ht : ∀ j, 0 < t j := fun j => by dsimp only [t]; positivity
      have hanti : Antitone t := by
        intro i j hij
        simpa only [t,one_div] using one_div_le_one_div_of_le
          (show (0 : ℝ) < ((i+1 : ℕ) : ℝ) by positivity)
          (show ((i+1 : ℕ) : ℝ) ≤ ((j+1 : ℕ) : ℝ) by exact_mod_cast Nat.add_le_add_right hij 1)
      have hlim : Tendsto t atTop (𝓝 0) := by
        simpa only [t,Nat.cast_add,Nat.cast_one,one_div] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hseq : Tendsto t atTop (𝓝[>] 0) :=
        tendsto_nhdsWithin_iff.mpr ⟨hlim,Eventually.of_forall ht⟩
      have hM := (SGPT.Trace.tendsto_sourceTraceMass_add_smul_right (toricFaceDimension_le J) hn
        (polytopeToricKahlerBackground γ hs) (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
        (contMDiff_toricFaceSourceInclusion (hs := hs) v J)
        (isKahler_pullback_toricFaceSourceInclusion v J (polytopeToricKahlerBackground γ hs)) h.form
        ((isThetaPSH_iff_nativeThetaPotential h.atlasForm u).mp hu.1) hν).comp hseq
      have hV := SGPT.Convex.tendsto_measure_compact_add_pos_smul μ hA
        (isCompact_toricStratumReferenceFace v J) (convex_toricStratumReferenceFace v J)
        (zero_mem_toricStratumReferenceFace v J) ht hanti hlim
      have hVF := ENNReal.Tendsto.const_mul (a := ((toricFaceDimension J).factorial : ENNReal)) hV
        (Or.inr (by simp))
      have hfun : (fun j => SGPT.Trace.sourceTraceMass (polytopeToricKahlerBackground γ hs)
          (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
            (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
          (contMDiff_toricFaceSourceInclusion (hs := hs) v J)
          (h.form + t j • (polytopeToricKahlerBackground γ hs).form) u) =
          (fun j => ((toricFaceDimension J).factorial : ENNReal) * μ (A + t j • B)) := by
        funext j
        exact h.sourceTraceMass_inverse_nat_perturbation_eq_faceVolume hu v J hJ mσ hσ hν (j+1) (by omega)
      dsimp only [Function.comp_def] at hM
      rw [hfun] at hM
      exact tendsto_nhds_unique hM hVF
  · have hnot : ¬ SGPT.Trace.HasPositiveSourceTraceAlong (polytopeToricKahlerBackground γ hs)
        (polytopeToricKahlerBackground (toricFaceProjectedFamily (hs := hs) v J)
          (latticePolytopeEdgeSmooth_toricFaceProjectedFamily (hs := hs) v J))
        (contMDiff_toricFaceSourceInclusion (hs := hs) v J) h.form u := by
      rintro ⟨τ,hT,_⟩
      exact hν hT.1
    have hnotFace : ¬ (h.newtonBody u ∩ toricDivisorFace D (polytopeToricRay γ hs v '' J)).Nonempty :=
      fun hne => hν ((h.sourceGenericLelong_nativeFace_eq_zero_iff hu v J).mpr hne)
    have hS0 : toricStratumTranslatedFace D v J mσ (h.newtonBody u) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hnotFace ⟨x.val + latticeVector mσ,hx⟩)
    rw [SGPT.Trace.sourceTraceMass,dif_neg hnot,hS0,measure_empty,mul_zero]

/-- Exact original source cor:tor_tr_vol on the ORIGINAL independently
constructed I-volume of the literal normalized trace, understood as0 if
undefined. The ordinary-mass identity above and its genuine I-envelope
comparison retain the complete original source contract. -/
theorem BigToricMetric.normalizedTraceVolume_eq_factorial_faceVolume
    {D : ToricDivisor γ hs} (h : BigToricMetric D)
    {u : PolytopeToricVariety γ hs → EReal} (hu : u ∈ h.PSHTor)
    (v : latticePolytopeVertices γ) (J : Set (Fin (m+k))) (hJ : Fintype.card J = k)
    (mσ : Fin (m+k) → ℤ)
    (hσ : IsToricCartierDatumAlong D (polytopeToricRay γ hs v '' J) mσ) :
    toricFaceNormalizedTraceVolume h v J u =
      ((toricFaceDimension J).factorial : ENNReal) *
        toricStratumNormalizedVolume (hs := hs) v J
          (toricStratumTranslatedFace D v J mσ (h.newtonBody u)) :=
  (h.normalizedTraceVolume_eq_sourceTraceMass hu v J mσ hσ).trans
    (h.sourceTraceMass_eq_factorial_faceVolume hu v J hJ mσ hσ)

end SGPT.Toric
