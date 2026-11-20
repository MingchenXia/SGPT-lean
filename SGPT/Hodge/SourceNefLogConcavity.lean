import SGPT.Hodge.SourceNefIntersection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SGPT.Hodge.BDivChain.SourceNefLogConcavityDraft
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
  SGPT.PSH.VariableComplexAtlas SGPT.BDivisor SGPT.Hodge.BDivChain.NativeDraft
  SGPT.Hodge.BDivChain.NativeDraft.VolumeNetRealDraft
  SGPT.Hodge.BDivChain.SourceCorrespondenceDraft SGPT.Hodge.BDivChain.SourceIntersection
  SGPT.Hodge.BDivChain.SourceNefProjectiveDraft
  SGPT.Hodge.BDivChain.SourceNefIntersectionDraft

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Actual original big-nef b-divisor log-concavity, with every realizing
current produced internally and the independent original pure-volume reader. -/
theorem prod_volumeRealAny_rpow_le_bigNefIntersection (ω : KahlerBackground n X)
    (D : Fin n → BigNefFamily (n := n) (X := X)) :
    ∏ i,volumeRealAny (D i).val ^ ((n : ℝ)⁻¹)≤(bigNefIntersection ω D).toReal := by
  have h := SGPT.IGood.LogVolume.prod_sourceIVolume_rpow_le_sourceGeneralMixedIVolume_of_dim ω
    (fun i => currentPresentationBackground (realizingCurrent ω (D i)).val)
    (fun i => currentPresentationPotential (realizingCurrent ω (D i)).val)
    (fun i => presentationPSH (realizingCurrent ω (D i)).val)
  change (∏ i,(currentIVolumeAny (realizingCurrent ω (D i)).val).toReal ^ ((n : ℝ)⁻¹))≤
    (bigNefIntersection ω D).toReal at h
  simpa only [currentIVolumeAny_eq_bdivisorVolume ω,realizingCurrent_family,volumeRealAny] using h

/-- WHOLE original prop:bdiv:L692: every nef original book-model family,
all dimensions and all zero-volume cases, with no supplied realization or
positive-volume premise and the genuine original intersection/volume. -/
theorem source_nefIntersection_logConcavity (ω : KahlerBackground n X)
    (D : Fin n → WeilFamilyAny (ModelSystem.blowup n X))
    (hD : ∀ i,IsNefAny (D i)) :
    ∏ i,volumeRealAny (D i) ^ ((n : ℝ)⁻¹)≤(nefIntersection D).toReal := by
  let A : Ioi (0 : ℝ) → Fin n → BigNefFamily (n := n) (X := X) :=
    fun ε i => kahlerPerturbedBigNef ω ω (D i) (hD i) ε.val ε.property
  have hpure (i : Fin n) :
      Tendsto (fun ε : Ioi (0 : ℝ) => volumeRealAny (A ε i).val) atBot
        (𝓝 (volumeRealAny (D i))) := by
    have h := volumeAny_add_smul_tendsto ω (D i)
      (rootCartierAny (RealBottChern.ofRepresentative ω.form))
      (isPseudoeffectiveAny_of_isNef ω (D i) (hD i)) (rootKahler_pseudoeffective ω)
      (fun ε : Ioi (0 : ℝ) => ε.val) (fun ε => ε.property.le) source_positiveParameter_tendsto
    exact (ENNReal.tendsto_toReal (volumeAny_lt_top_blowup ⟨ω⟩ (D i)).ne).comp h
  have hleft : Tendsto (fun ε : Ioi (0 : ℝ) =>
      ∏ i,volumeRealAny (A ε i).val ^ ((n : ℝ)⁻¹)) atBot
      (𝓝 (∏ i,volumeRealAny (D i) ^ ((n : ℝ)⁻¹))) := by
    apply tendsto_finsetProd
    intro i _
    exact (hpure i).rpow_const (Or.inr (inv_nonneg.mpr (Nat.cast_nonneg n)))
  have hright : Tendsto (fun ε : Ioi (0 : ℝ) => (bigNefIntersection ω (A ε)).toReal)
      atBot (𝓝 (nefIntersection D).toReal) :=
    (ENNReal.tendsto_toReal (nefIntersection_lt_top D).ne).comp (source_DFext_limit ω ω D hD)
  exact le_of_tendsto_of_tendsto' hleft hright
    (fun ε => prod_volumeRealAny_rpow_le_bigNefIntersection ω (A ε))

end SGPT.Hodge.BDivChain.SourceNefLogConcavityDraft
