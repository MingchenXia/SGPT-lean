import SGPT.Bergman.SourcePartialEnvelopes
import SGPT.PSH.SourceComparisonEnvelopeCharacterizations

/-! A derived implementation bridge from actual original candidates.
It receives zero independent source credit. The complete proof precedes this
file in global-weight-approximation.tex (gwa:ideal-ordinary-bridge). -/
set_option autoImplicit false
noncomputable section

namespace SGPT.Bergman.PartialEnvelopeIComparison

open Set SGPT.PSH SGPT.PSH.VariableComplexAtlas
open SGPT.Bergman.PartialEnvelope
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- Compact normalization turns the actual ALL-I-order characterization into
ordinary additive comparison with the actual normalized I-envelope. -/
theorem sourceIOrder_iff_singularityLE_iEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {η φ : M → EReal}
    (hη : (ofFixedModel n M).IsThetaPSH θ η)
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) :
    sourceIOrder (ofFixedModel n M) η φ ↔
      SGPT.PSH.SingularityLE η (sourceIEnvelope θ φ) := by
  constructor
  · intro hI
    obtain ⟨C, hC⟩ := ((isThetaPSH_iff_nativeThetaPotential θ η).mp hη).exists_global_upper_bound
    let χ : M → EReal := fun x => η x + ((-C : ℝ) : EReal)
    have hχ := sourceThetaPSH_add_const hη (-C)
    have hχ0 : χ ≤ 0 := by
      intro x
      simpa only [χ, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, Pi.zero_apply] using
        add_le_add (hC x) (le_refl ((-C : ℝ) : EReal))
    have hχI : sourceIOrder (ofFixedModel n M) χ φ :=
      sourceIOrder_trans (sourceIOrder_of_singularityLE hχ hη ⟨-C, fun _ _ => le_rfl⟩) hI
    have hle : χ ≤ sourceIEnvelope θ φ := by
      rw [sourceIEnvelope_eq_sSup_sourceIOrder hφ]
      exact le_sSup ⟨hχ, hχ0, hχI⟩
    apply (singularityLE_iff_exists_real _ _).mpr
    refine ⟨C, fun x => ?_⟩
    have h := add_le_add (hle x) (le_refl (C : EReal))
    simpa only [χ, add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero] using h
  · intro hmore
    exact sourceIOrder_trans
      (sourceIOrder_of_singularityLE hη (isThetaPSH_sourceIEnvelope hφ) hmore)
      (sourceIEquivalent_iEnvelope hφ).2

/-- BOTH inclusions of the SAME original genuine/QE-obstacle competitor
families give the literal operator identity. No output certificate is supplied. -/
theorem partialIEnvelope_eq_partialEnvelope_iEnvelope
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ) (K : Set M) (f : K → EReal) :
    partialIEnvelope θ φ K f = partialEnvelope θ (sourceIEnvelope θ φ) K f := by
  apply congrArg uscRegularization
  funext x
  apply le_antisymm
  · apply iSup_le
    intro a
    exact le_iSup
      (fun b : partialCompetitors θ (sourceIEnvelope θ φ) K f => b.val x)
      ⟨a.val, a.property.1, a.property.2.1,
        (sourceIOrder_iff_singularityLE_iEnvelope a.property.1 hφ).mp a.property.2.2⟩
  · apply iSup_le
    intro a
    exact le_iSup (fun b : partialICompetitors θ φ K f => b.val x)
      ⟨a.val, a.property.1, a.property.2.1,
        (sourceIOrder_iff_singularityLE_iEnvelope a.property.1 hφ).mpr a.property.2.2⟩


end SGPT.Bergman.PartialEnvelopeIComparison
