import SGPT.PSH.SourceSingularityDistance
import SGPT.Foundations.Analysis.Pending.MinimalBackgroundFixedAmbient

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace SGPT.PSH.VariableComplexAtlas

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
open SGPT.PSH.VariableComplexAtlas
open SingularCanonicalSingularityDistance ThetaPshL1Topology
open MinimalBackgroundFixedAmbient

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem native_tendsto_of_form_eq (omega : KahlerBackground n M)
    (σ ρ : ClosedRealOneOneForm n M) (heq : σ = ρ)
    (hσ : IsBigClass (RealBottChern.ofRepresentative σ))
    (hρ : IsBigClass (RealBottChern.ofRepresentative ρ))
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v : M → EReal}
    (huσ : ∀ i, IsThetaPshPotential σ.val (u i)) (hvσ : IsThetaPshPotential σ.val v)
    (huρ : ∀ i, IsThetaPshPotential ρ.val (u i)) (hvρ : IsThetaPshPotential ρ.val v)
    (hn : Tendsto (fun i => (⟨u i, huρ i⟩ : ThetaPshL1 ρ.val)) F
      (@nhds (ThetaPshL1 ρ.val)
        (singularityPseudoMetricSpace omega ρ hρ).toUniformSpace.toTopologicalSpace ⟨v, hvρ⟩)) :
    Tendsto (fun i => (⟨u i, huσ i⟩ : ThetaPshL1 σ.val)) F
      (@nhds (ThetaPshL1 σ.val)
        (singularityPseudoMetricSpace omega σ hσ).toUniformSpace.toTopologicalSpace ⟨v, hvσ⟩) := by
  subst ρ
  exact hn

private theorem source_sameFunction_tendsto
    (omega : KahlerBackground n M) (A : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hA : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative A)))
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ i, IsThetaPshPotential (atlasClosedFormToNative A).val (u i))
    (hv : IsThetaPshPotential (atlasClosedFormToNative A).val v)
    (hn : Tendsto (fun i => (⟨u i, hu i⟩ : ThetaPshL1 (atlasClosedFormToNative A).val)) F
      (@nhds (ThetaPshL1 (atlasClosedFormToNative A).val)
        (singularityPseudoMetricSpace omega (atlasClosedFormToNative A) hA).toUniformSpace.toTopologicalSpace
        ⟨v, hv⟩)) :
    Tendsto (fun i => (⟨u i, (isThetaPSH_iff_nativeThetaPotential A _).mpr (hu i)⟩ :
      SourceThetaPotentialL1 A)) F
      (@nhds (SourceThetaPotentialL1 A) (sourceSingularityTopology omega A hA)
        ⟨v, (isThetaPSH_iff_nativeThetaPotential A _).mpr hv⟩) := by
  let := sourceSingularityPseudoMetricSpace omega A hA
  let : UniformSpace (SourceThetaPotentialL1 A) := sourceSingularityUniformSpace omega A hA
  let : TopologicalSpace (SourceThetaPotentialL1 A) := sourceSingularityTopology omega A hA
  let := singularityPseudoMetricSpace omega (atlasClosedFormToNative A) hA
  let : UniformSpace (ThetaPshL1 (atlasClosedFormToNative A).val) :=
    (singularityPseudoMetricSpace omega (atlasClosedFormToNative A) hA).toUniformSpace
  let : TopologicalSpace (ThetaPshL1 (atlasClosedFormToNative A).val) :=
    (singularityPseudoMetricSpace omega (atlasClosedFormToNative A) hA).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative A) :=
    Topology.IsInducing.induced _
  exact hmap.tendsto_nhds_iff.mpr hn

/-- Exact source Step 1: actual original minimal envelopes converge in the
FIXED theta+omega source topology. Every common-carrier membership is output. -/
theorem sourceMinimalEnvelope_positive_fixedAmbient
    (omega : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (ε : I → Ioo (0 : ℝ) 1)
    (hε : Tendsto (fun i => (ε i).val) F (𝓝 0)) :
    let A := nativeClosedFormToAtlas (atlasClosedFormToNative θ + omega.form)
    ∃ hA : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative A)),
    ∃ h0 : IsThetaPSH A (sourceMinimalEnvelope θ),
    ∃ hE : ∀ i, IsThetaPSH A (sourceMinimalEnvelope
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε i).val • omega.form))),
      Tendsto (fun i => (⟨sourceMinimalEnvelope
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + (ε i).val • omega.form)), hE i⟩ :
          SourceThetaPotentialL1 A)) F
        (@nhds (SourceThetaPotentialL1 A) (sourceSingularityTopology omega A hA)
          ⟨sourceMinimalEnvelope θ, h0⟩) := by
  let A := nativeClosedFormToAtlas (atlasClosedFormToNative θ + omega.form)
  obtain ⟨hA, h0, hE, hn⟩ := exists_tendsto_fixedAmbient_positive_minimal
    omega (atlasClosedFormToNative θ) hbig F ε hε
  have hAS : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative A)) := by
    simpa only [A, sourceNativeAtlasForm_roundTrip] using hA
  have hv : IsThetaPshPotential (atlasClosedFormToNative A).val (sourceMinimalEnvelope θ) := by
    simpa only [A, sourceNativeAtlasForm_roundTrip, sourceMinimalEnvelope_eq_native] using h0
  have hu (i : I) : IsThetaPshPotential (atlasClosedFormToNative A).val
      (sourceMinimalEnvelope (nativeClosedFormToAtlas
        (atlasClosedFormToNative θ + (ε i).val • omega.form))) := by
    simpa only [A, sourceNativeAtlasForm_roundTrip, sourceMinimalEnvelope_eq_native] using hE i
  refine ⟨hAS, (isThetaPSH_iff_nativeThetaPotential A _).mpr hv,
    fun i => (isThetaPSH_iff_nativeThetaPotential A _).mpr (hu i), ?_⟩
  apply source_sameFunction_tendsto omega A hAS F hu hv
  have huρ (i : I) : IsThetaPshPotential (atlasClosedFormToNative θ + omega.form).val
      (sourceMinimalEnvelope (nativeClosedFormToAtlas
        (atlasClosedFormToNative θ + (ε i).val • omega.form))) := by
    simpa only [sourceMinimalEnvelope_eq_native, sourceNativeAtlasForm_roundTrip] using hE i
  have hvρ : IsThetaPshPotential (atlasClosedFormToNative θ + omega.form).val
      (sourceMinimalEnvelope θ) := by
    simpa only [sourceMinimalEnvelope_eq_native] using h0
  apply native_tendsto_of_form_eq omega (atlasClosedFormToNative A)
    (atlasClosedFormToNative θ + omega.form) (sourceNativeAtlasForm_roundTrip _)
    hAS hA F hu hv huρ hvρ
  simpa only [sourceMinimalEnvelope_eq_native, sourceNativeAtlasForm_roundTrip] using hn

/-- Exact source Step 2 retains the STRONGER ORIGINAL theta topology, not
merely an enlarged background. The radius and smaller-class bigness are outputs. -/
theorem sourceMinimalEnvelope_negative_original
    (omega : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {I : Type*} (F : Filter I) (ε : I → Ioo (0 : ℝ) δ),
      Tendsto (fun i => (ε i).val) F (𝓝 0) →
      ∃ hE : ∀ i, IsThetaPSH θ (sourceMinimalEnvelope
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ - (ε i).val • omega.form))),
      ∃ _hsmall : ∀ i, IsBigClass (RealBottChern.ofRepresentative
        (atlasClosedFormToNative θ - (ε i).val • omega.form)),
        Tendsto (fun i => (⟨sourceMinimalEnvelope
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ - (ε i).val • omega.form)), hE i⟩ :
            SourceThetaPotentialL1 θ)) F
          (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig)
            ⟨sourceMinimalEnvelope θ, sourceMinimalEnvelope_thetaPSH omega θ hbig⟩) := by
  obtain ⟨δ, hδ, hnegative⟩ := exists_tendsto_original_negative_minimal
    omega (atlasClosedFormToNative θ) hbig
  refine ⟨δ, hδ, fun {I} F ε hε => ?_⟩
  obtain ⟨hE, hsmall, hn⟩ := hnegative F ε hε
  have hu (i : I) : IsThetaPshPotential (atlasClosedFormToNative θ).val
      (sourceMinimalEnvelope (nativeClosedFormToAtlas
        (atlasClosedFormToNative θ - (ε i).val • omega.form))) := by
    simpa only [sourceMinimalEnvelope_eq_native, sourceNativeAtlasForm_roundTrip] using hE i
  have hv : IsThetaPshPotential (atlasClosedFormToNative θ).val (sourceMinimalEnvelope θ) :=
    (isThetaPSH_iff_nativeThetaPotential θ _).mp (sourceMinimalEnvelope_thetaPSH omega θ hbig)
  refine ⟨fun i => (isThetaPSH_iff_nativeThetaPotential θ _).mpr (hu i), hsmall, ?_⟩
  apply source_sameFunction_tendsto omega θ hbig F hu hv
  simpa only [sourceMinimalEnvelope_eq_native, sourceNativeAtlasForm_roundTrip] using hn

end

end SGPT.PSH.VariableComplexAtlas
