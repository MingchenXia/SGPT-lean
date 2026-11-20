import SGPT.PSH.SourceGeneralMixedIVolumePerturbation
import SGPT.PSH.SourceCurrentMixedIVolume
import SGPT.PSH.SourceModificationConvergence
import SGPT.Okounkov.IEnvelopeModification
import SGPT.Okounkov.AnalyticModificationCurrent
import SGPT.Foundations.Analysis.Pending.DominationIntersectionNumbers

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open AnalyticModificationLocalDiscrepancy AnalyticModificationStrongPullback
open NaturalThetaPshGeometricCurrent CanonicalCurrentFrame GlobalPositiveCurrentACRestriction

section Modification
variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [MeasurableSpace Y] [BorelSpace Y] in
private theorem biminvPullPSH {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) :
    (ofFixedModel n Y).IsThetaPSH
      (nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative θ)))
      (u ∘ π) := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact isThetaPshPotential_comp_of_isAnalyticModification hπ _
    ((isThetaPSH_iff_nativeThetaPotential θ _).mp hu)

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
private theorem biminvPullQ {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n X)} {u : X → EReal}
    (hu : (ofFixedModel n X).IsThetaPSH θ u) :
    sourceIEnvelope
      (nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative θ)))
      (u ∘ π) = sourceIEnvelope θ u ∘ π := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  rw [sourceIEnvelope_eq_native _ _ (biminvPullPSH hπ hu), sourceIEnvelope_eq_native θ u hu,
    sourceNativeAtlasForm_roundTrip]
  exact SGPT.Okounkov.iSingularityEnvelope_modification_pullback hπ _
    ((isThetaPSH_iff_nativeThetaPotential θ u).mp hu)

/-- Actual direct mixed I-envelope mass is invariant before any positive-volume
restriction; all whole tensors/functions/poles and the empty tuple are retained. -/
theorem sourceEnvelopeMixedIVolume_modification_pullback
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n X))
    (v : Fin n → X → EReal) (hv : ∀ i, (ofFixedModel n X).IsThetaPSH (θ i) (v i)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    sourceEnvelopeMixedIVolume
      (fun i => nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative (θ i))))
      (fun i => v i ∘ π) (fun i => biminvPullPSH hπ (hv i)) = sourceEnvelopeMixedIVolume θ v hv := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  have hQ i := biminvPullQ hπ (hv i)
  simp only [sourceEnvelopeMixedIVolume_eq_native, sourceNativeAtlasForm_roundTrip, hQ]
  exact AnalyticModificationMixedMass.globalMixedMeasure_univ_pullback_of_isAnalyticModification
    hπ (fun i => ((isThetaPSH_iff_nativeThetaPotential (θ i) _).mp
      (isThetaPSH_sourceIEnvelope (hv i))).1)

/-- Original SINGLE I-volume is preserved, including zero, by whole I-envelope
commutation and actual diagonal non-pluripolar mass invariance. -/
theorem sourceIVolume_modification_pullback
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n X))
    (v : X → EReal) (hv : (ofFixedModel n X).IsThetaPSH θ v) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    sourceIVolume
      (nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative θ)))
      (v ∘ π) (biminvPullPSH hπ hv) = sourceIVolume θ v hv := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  simpa only [sourceEnvelopeMixedIVolume_diagonal] using
    sourceEnvelopeMixedIVolume_modification_pullback hπ (fun _ => θ) (fun _ => v) (fun _ => hv)
end Modification

section Semipositive
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
private theorem biminvAddPSH
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)} {v : M → EReal}
    (hv : (ofFixedModel n M).IsThetaPSH θ v)
    (σ : ClosedRealOneOneForm n M) (hσ : σ.val.IsSemipositive) :
    (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas (atlasClosedFormToNative θ + σ)) v := by
  apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
  rw [sourceNativeAtlasForm_roundTrip]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive
    ((isThetaPSH_iff_nativeThetaPotential θ v).mp hv) hσ

private theorem biminvMonoSemi (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (v : Fin n → M → EReal)
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i))
    (σ : ClosedRealOneOneForm n M) (hσ : σ.val.IsSemipositive) :
    sourceGeneralMixedIVolume ω θ v hv ≤ sourceGeneralMixedIVolume ω
      (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + σ)) v
      (fun i => biminvAddPSH (hv i) σ hσ) := by
  have hz : (ofFixedModel n M).IsThetaPSH (nativeClosedFormToAtlas σ) (fun _ => (0 : EReal)) := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    rw [sourceNativeAtlasForm_roundTrip]
    exact (LocalPotentials.isThetaPshPotential_zero_iff σ).mpr hσ
  have h := sourceGeneralMixedIVolume_mono_independent_add ω θ (fun _ => nativeClosedFormToAtlas σ)
    v (fun _ _ => (0 : EReal)) hv (fun _ => hz)
  simpa only [sourceNativeAtlasForm_roundTrip, add_zero] using h

/-- The actual all-slot general quantity after a genuine smooth semipositive
perturbation. Every enlarged source PSH domain is produced internally. -/
def sourceGeneralMixedIVolume_semipositivePerturbed (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (v : Fin n → M → EReal)
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i))
    (σ : ClosedRealOneOneForm n M) (hσ : σ.val.IsSemipositive) (t : NNReal) : ENNReal :=
  sourceGeneralMixedIVolume ω
    (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (t : ℝ) • σ)) v
    (fun i => biminvAddPSH (hv i) ((t : ℝ) • σ)
      (KahlerDomination.isSemipositive_smul hσ t.property))

/-- Actual small semipositive perturbations converge at ALL original inputs,
including zero I-volumes and dimension zero; domination and finiteness are outputs. -/
theorem tendsto_sourceGeneralMixedIVolume_semipositive_perturbation (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (v : Fin n → M → EReal)
    (hv : ∀ i, (ofFixedModel n M).IsThetaPSH (θ i) (v i))
    (σ : ClosedRealOneOneForm n M) (hσ : σ.val.IsSemipositive) :
    Tendsto (sourceGeneralMixedIVolume_semipositivePerturbed ω θ v hv σ hσ)
      (𝓝[>] (0 : NNReal)) (𝓝 (sourceGeneralMixedIVolume ω θ v hv)) := by
  obtain ⟨C, hC, hdom⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul ω (-σ)
  have hdom' : (C • ω.form - σ).val.IsSemipositive := by
    simpa only [sub_eq_neg_add] using hdom
  obtain ⟨K, hK, hbound⟩ := sourceGeneralMixedIVolume_class_uniform_perturbation_bound ω
    (fun i => RealBottChern.ofRepresentative (atlasClosedFormToNative (θ i)))
  let f := sourceGeneralMixedIVolume_semipositivePerturbed ω θ v hv σ hσ
  let G := sourceGeneralMixedIVolume ω θ v hv
  have hf t : f t < ⊤ := sourceGeneralMixedIVolume_lt_top ω _ _ _
  have hG : G < ⊤ := sourceGeneralMixedIVolume_lt_top ω θ v hv
  have hlow t : G ≤ f t := biminvMonoSemi ω θ v hv ((t : ℝ) • σ)
    (KahlerDomination.isSemipositive_smul hσ t.property)
  have hupp t : f t ≤ sourceGeneralMixedIVolumeKahlerPerturbed ω θ v hv
      (C * (t : ℝ)) (mul_nonneg hC.le t.property) := by
    have h := biminvMonoSemi ω
      (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (t : ℝ) • σ)) v
      (fun i => biminvAddPSH (hv i) ((t : ℝ) • σ)
        (KahlerDomination.isSemipositive_smul hσ t.property))
      ((t : ℝ) • (C • ω.form - σ))
      (KahlerDomination.isSemipositive_smul hdom' t.property)
    change f t ≤ sourceGeneralMixedIVolume ω
      (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (C * (t : ℝ)) • ω.form)) v _
    have he : (fun i => nativeClosedFormToAtlas
        (atlasClosedFormToNative (nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (t : ℝ) • σ)) +
          (t : ℝ) • (C • ω.form - σ))) =
        (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (C * (t : ℝ)) • ω.form)) := by
      funext i
      simp only [sourceNativeAtlasForm_roundTrip]
      congr 1
      module
    simpa only [f, sourceGeneralMixedIVolume_semipositivePerturbed, he] using h
  have htlim : Tendsto (fun t : NNReal => C * (t : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have ht0 : Tendsto (fun t : NNReal => (t : ℝ)) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
      (NNReal.continuous_coe.tendsto (0 : NNReal)).mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : NNReal => C) (𝓝[>] 0) (𝓝 C)).mul ht0
  have hsmall : ∀ᶠ t : NNReal in 𝓝[>] 0, C * (t : ℝ) < 1 :=
    (tendsto_order.mp htlim).2 1 zero_lt_one
  have hupperReal : ∀ᶠ t : NNReal in 𝓝[>] 0,
      (f t).toReal ≤ G.toReal + K * (C * (t : ℝ)) := by
    filter_upwards [hsmall] with t ht
    have hfin : sourceGeneralMixedIVolumeKahlerPerturbed ω θ v hv
        (C * (t : ℝ)) (mul_nonneg hC.le t.property) < ⊤ :=
      sourceGeneralMixedIVolume_lt_top ω _ _ _
    have ho := ENNReal.toReal_mono hfin.ne (hupp t)
    have hb := (hbound θ v hv (fun _ => rfl) (C * (t : ℝ)) (mul_nonneg hC.le t.property) ht.le).2
    linarith
  have hreal : Tendsto (fun t => (f t).toReal) (𝓝[>] (0 : NNReal)) (𝓝 G.toReal) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [mul_zero, add_zero] using tendsto_const_nhds.add (tendsto_const_nhds.mul htlim))
      (Filter.Eventually.of_forall fun t => ENNReal.toReal_mono (hf t).ne (hlow t)) hupperReal
  have hext := ENNReal.tendsto_ofReal hreal
  have heq : (fun t : NNReal => ENNReal.ofReal (f t).toReal) = f :=
    funext fun t => ENNReal.ofReal_toReal (hf t).ne
  rw [heq, ENNReal.ofReal_toReal hG.ne] at hext
  exact hext
end Semipositive

section GeneralModification
variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- All-input original represented bimeromorphic invariance. The pulled Kähler
form is only semipositive; positive perturbed I-volumes and every upstairs
geometric/domain fact are internally produced, including all-zero inputs. -/
theorem sourceGeneralMixedIVolume_modification_pullback
    {π : Y → X} (hπ : IsAnalyticModification (n := n) π)
    (ωX : KahlerBackground n X) (ωY : KahlerBackground n Y)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n X))
    (v : Fin n → X → EReal) (hv : ∀ i, (ofFixedModel n X).IsThetaPSH (θ i) (v i)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    sourceGeneralMixedIVolume ωY
      (fun i => nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative (θ i))))
      (fun i => v i ∘ π) (fun i => biminvPullPSH hπ (hv i)) =
      sourceGeneralMixedIVolume ωX θ v hv := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  let α := ClosedRealOneOneForm.pullback hπ.1 ωX.form
  have hα : α.val.IsSemipositive := ClosedRealOneOneForm.pullback_isSemipositive hπ.1 ωX.isSemipositive
  let β i := nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative (θ i)))
  let w i := v i ∘ π
  have hw i : (ofFixedModel n Y).IsThetaPSH (β i) (w i) := biminvPullPSH hπ (hv i)
  have hlimY := tendsto_sourceGeneralMixedIVolume_semipositive_perturbation ωY β w hw α hα
  have heq : ∀ᶠ t : NNReal in 𝓝[>] 0,
      sourceGeneralMixedIVolume_semipositivePerturbed ωY β w hw α hα t =
        sourceMixedIVolumeKahlerPerturbation ωX θ v hv t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    let Θ i := nativeClosedFormToAtlas (atlasClosedFormToNative (θ i) + (t : ℝ) • ωX.form)
    have hΘ i : (ofFixedModel n X).IsThetaPSH (Θ i) (v i) :=
      biminvAddPSH (hv i) ((t : ℝ) • ωX.form)
        (KahlerDomination.isSemipositive_smul ωX.isSemipositive t.property)
    let Β i := nativeClosedFormToAtlas (ClosedRealOneOneForm.pullback hπ.1 (atlasClosedFormToNative (Θ i)))
    have hΒ i : (ofFixedModel n Y).IsThetaPSH (Β i) (w i) := biminvPullPSH hπ (hΘ i)
    have hpos i : 0 < sourceIVolume (Β i) (w i) (hΒ i) := by
      rw [sourceIVolume_modification_pullback hπ (Θ i) (v i) (hΘ i)]
      exact sourceIVolume_add_kahler_pos ωX (hv i) (by exact_mod_cast ht)
    have hD := sourceGeneralMixedIVolume_eq_positive ωY Β w hΒ hpos
    have hM := sourceEnvelopeMixedIVolume_modification_pullback hπ Θ v hΘ
    have hform : Β = (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (β i) + (t : ℝ) • α)) := by
      funext i
      simp only [Β, Θ, β, α, sourceNativeAtlasForm_roundTrip, DominationIntersectionNumbers.pullback_add_smul]
    change sourceGeneralMixedIVolume ωY
      (fun i => nativeClosedFormToAtlas (atlasClosedFormToNative (β i) + (t : ℝ) • α)) w _ =
        sourceEnvelopeMixedIVolume Θ v hΘ
    simpa only [hform] using hD.trans hM
  have hsame := hlimY.congr' heq
  exact tendsto_nhds_unique hsame (sourceGeneralMixedIVolume_tendsto ωX θ v hv)
end GeneralModification

section OriginalCurrents
variable {m : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [MeasurableSpace Y] [BorelSpace Y]

/-- The actual ORIGINAL whole-current pullback selected from the existing
unique unflagged geometric producer. No selected representation is an input. -/
def sourceCurrentModificationPullback
    {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : IsFullPositive T) : GlobalCurrent (m + 1) Y (degreeTwo (Nat.succ_pos m)) :=
  Classical.choose (SGPT.Okounkov.exists_unique_compact_current_analyticModification_pullback hπ T hc h11 hp)

omit [MeasurableSpace X] [BorelSpace X] [ConnectedSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- Natural domains and EVERY genuine whole-current readback are outputs for
the same actual original pullback, with all exceptional support retained. -/
theorem sourceCurrentModificationPullback_spec
    {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (T : GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hc : T.IsClosed (canonicalBasis (m + 1)))
    (h11 : T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m)) (hp : IsFullPositive T) :
    (sourceCurrentModificationPullback hπ T hc h11 hp).IsClosed (canonicalBasis (m + 1)) ∧
    (sourceCurrentModificationPullback hπ T hc h11 hp).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
    IsFullPositive (sourceCurrentModificationPullback hπ T hc h11 hp) ∧
    ∀ (θ : ClosedRealOneOneForm (m + 1) X) (v : X → EReal) (hv : IsThetaPshPotential θ.val v),
      T = thetaPotentialCurrent θ.val v hv →
      sourceCurrentModificationPullback hπ T hc h11 hp = SGPT.Okounkov.analyticModificationThetaCurrent hπ θ v hv :=
  (Classical.choose_spec (SGPT.Okounkov.exists_unique_compact_current_analyticModification_pullback hπ T hc h11 hp)).1

/-- WHOLE original prop:biminv for arbitrary original currents, all original
I-volumes including zero, and genuine arbitrary proper bimeromorphic maps.
Every representation, pullback and upstairs natural domain is internally produced. -/
theorem sourceCurrentMixedIVolume_modification_pullback
    {π : Y → X} (hπ : IsAnalyticModification (n := m + 1) π)
    (ωX : KahlerBackground (m + 1) X) (ωY : KahlerBackground (m + 1) Y)
    (T : Fin (m + 1) → GlobalCurrent (m + 1) X (degreeTwo (Nat.succ_pos m)))
    (hc : ∀ i, (T i).IsClosed (canonicalBasis (m + 1)))
    (h11 : ∀ i, (T i).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m))
    (hp : ∀ i, IsFullPositive (T i)) :
    letI : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
    letI : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
    sourceCurrentMixedIVolume ωY (fun i => sourceCurrentModificationPullback hπ (T i) (hc i) (h11 i) (hp i))
      (fun i => (sourceCurrentModificationPullback_spec hπ (T i) (hc i) (h11 i) (hp i)).1)
      (fun i => (sourceCurrentModificationPullback_spec hπ (T i) (hc i) (h11 i) (hp i)).2.1)
      (fun i => (sourceCurrentModificationPullback_spec hπ (T i) (hc i) (h11 i) (hp i)).2.2.1) =
      sourceCurrentMixedIVolume ωX T hc h11 hp := by
  let : CompactSpace Y := compactSpace_of_isAnalyticModification hπ
  let : ConnectedSpace Y := SGPT.Okounkov.connectedSpace_source_of_isAnalyticModification hπ
  choose θ v hv hread hchart using fun i =>
    OriginalPositiveCurrentThetaRepresentation.exists_theta_representation_of_original_closed_full_positive
      (T i) (hc i) (h11 i) (hp i)
  let η i := ClosedRealOneOneForm.pullback hπ.1 (θ i)
  let w i := v i ∘ π
  have hw i : IsThetaPshPotential (η i).val (w i) :=
    isThetaPshPotential_comp_of_isAnalyticModification hπ (θ i) (hv i)
  have hreadY i : sourceCurrentModificationPullback hπ (T i) (hc i) (h11 i) (hp i) =
      thetaPotentialCurrent (η i).val (w i) (hw i) :=
    (sourceCurrentModificationPullback_spec hπ (T i) (hc i) (h11 i) (hp i)).2.2.2 (θ i) (v i) (hv i) (hread i)
  rw [sourceCurrentMixedIVolume_eq_representation ωY _ _ _ _ η w hw hreadY,
    sourceCurrentMixedIVolume_eq_representation ωX T hc h11 hp θ v hv hread]
  have hs i : (ofFixedModel (m + 1) X).IsThetaPSH (nativeClosedFormToAtlas (θ i)) (v i) := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    simpa only [sourceNativeAtlasForm_roundTrip] using hv i
  simpa only [η, w, sourceNativeAtlasForm_roundTrip] using
    sourceGeneralMixedIVolume_modification_pullback hπ ωX ωY (fun i => nativeClosedFormToAtlas (θ i)) v hs
end OriginalCurrents
end SGPT.PSH.VariableComplexAtlas
