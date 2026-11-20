import SGPT.PSH.SourceComparisonEnvelopeCharacterizations

/-! # Original I-envelope monotonicity under additive singularity order

The whole source lemma `lma:PIenvmono1` keeps the original theta-PSH inputs,
one global finite additive comparison, and the literal normalized I-envelopes.
No positive mass, big class, or supplied envelope comparison is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- Whole original `lma:PIenvmono1`, including arbitrary zero-mass inputs. -/
theorem sourceIEnvelope_mono_of_singularityLE
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {φ ψ : M → EReal}
    (hφ : (ofFixedModel n M).IsThetaPSH θ φ)
    (hψ : (ofFixedModel n M).IsThetaPSH θ ψ)
    (h : SGPT.PSH.SingularityLE φ ψ) :
    sourceIEnvelope θ φ ≤ sourceIEnvelope θ ψ := by
  obtain ⟨C, hC⟩ := (SGPT.PSH.singularityLE_iff_exists_real φ ψ).mp h
  have hI : IEnvelope.IOrderOnManifold (n := n) φ ψ :=
    iOrderOnManifold_of_le_add
      ((isThetaPSH_iff_nativeThetaPotential θ ψ).mp hψ).1.quasiPlurisubharmonic hC
  apply (sourceIOrder_iff_sourceIEnvelope_le hφ hψ).mp
  exact (sourceIOrder_iff_native ⟨θ, hφ⟩ ⟨θ, hψ⟩).mpr hI

end SGPT.PSH.VariableComplexAtlas
