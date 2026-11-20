import SGPT.PSH.SourceSingularityDistance
import SGPT.Foundations.Analysis.Pending.SingularNativeOrderSandwich
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityScalarEquivalence

/-! # Whole original order squeezing and fixed positive scaling

The complete source-first route is in `source-singularity-order-scaling.tex`.
Every order is the original global P-order; every topology is the actual dS
topology, and all scaled memberships and big-class data are genuine outputs.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual scaled big-current witness supplies the scaled source class. -/
theorem sourcePositiveScaledBackground_big
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {c : ℝ} (hc : 0 < c) :
    IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)))) := by
  rw [sourceNativeAtlasForm_roundTrip, RealBottChern.ofRepresentative_smul]
  exact ActualPositiveClassScaling.isBigClass_positive_smul hθ hc

/-- Literal positive scaling in the full scaled background, with genuine
PSH membership produced from the original input. -/
def sourcePositiveScaledPotential
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {c : ℝ} (hc : 0 < c) (u : SourceThetaPotentialL1 θ) :
    SourceThetaPotentialL1 (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)) :=
  ⟨fun x ↦ (c : EReal) * u.val x,
    (isThetaPSH_iff_nativeThetaPotential _ _).mpr (by
      rw [sourceNativeAtlasForm_roundTrip]
      exact RestrictedApproximantComparison.isThetaPshPotential_smul
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property) hc)⟩

/-- Entire original positive-scaled function readback, retaining all poles. -/
theorem sourcePositiveScaledPotential_val
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    {c : ℝ} (hc : 0 < c) (u : SourceThetaPotentialL1 θ) :
    (sourcePositiveScaledPotential hc u).val = fun x ↦ (c : EReal) * u.val x := rfl

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

private theorem native_tendsto_iff_of_form_eq
    (ω : KahlerBackground n M) (θ σ : ClosedRealOneOneForm n M) (heq : θ = σ)
    (hθ : IsBigClass (RealBottChern.ofRepresentative θ))
    (hσ : IsBigClass (RealBottChern.ofRepresentative σ))
    {I : Type*} (F : Filter I) {u : I → M → EReal} {v : M → EReal}
    (huθ : ∀ i, IsThetaPshPotential θ.val (u i)) (hvθ : IsThetaPshPotential θ.val v)
    (huσ : ∀ i, IsThetaPshPotential σ.val (u i)) (hvσ : IsThetaPshPotential σ.val v) :
    Tendsto (fun i ↦ (⟨u i, huθ i⟩ : ThetaPshL1Topology.ThetaPshL1 θ.val)) F
      (@nhds (ThetaPshL1Topology.ThetaPshL1 θ.val)
        (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω θ hθ).toUniformSpace.toTopologicalSpace
        ⟨v, hvθ⟩) ↔
    Tendsto (fun i ↦ (⟨u i, huσ i⟩ : ThetaPshL1Topology.ThetaPshL1 σ.val)) F
      (@nhds (ThetaPshL1Topology.ThetaPshL1 σ.val)
        (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω σ hσ).toUniformSpace.toTopologicalSpace
        ⟨v, hvσ⟩) := by
  subst σ
  rfl

/-- WHOLE original `cor:dsconvupplower` for every filter: actual global P
orders and two genuine outer limits give the SAME original middle limit. -/
theorem tendsto_sourceSingularityTopology_of_sourcePOrder_sandwich
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (a b c : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hab : ∀ i, GlobalPComparison.sourcePOrder (n := n) (a i).val (b i).val)
    (hbc : ∀ i, GlobalPComparison.sourcePOrder (n := n) (b i).val (c i).val)
    (ha : Tendsto a F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) v))
    (hc : Tendsto c F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) v)) :
    Tendsto b F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) v) := by
  let := sourceSingularityPseudoMetricSpace ω θ hθ
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hθ
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hθ
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hθ
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hθ).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hθ).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  apply hmap.tendsto_nhds_iff.mpr
  exact SingularNativeOrderSandwich.tendsto_native_of_sourcePOrder_sandwich
    ω (atlasClosedFormToNative θ) hθ F
    (fun i ↦ sourceThetaPotentialL1EquivNative θ (a i))
    (fun i ↦ sourceThetaPotentialL1EquivNative θ (b i))
    (fun i ↦ sourceThetaPotentialL1EquivNative θ (c i))
    (sourceThetaPotentialL1EquivNative θ v) hab hbc
    (hmap.tendsto_nhds_iff.mp ha) (hmap.tendsto_nhds_iff.mp hc)

/-- WHOLE original `lma:dS_res`: both actual source topologies, the genuine
scaled big class and literal positive-scaled functions. No scaled distance
or mixed-mass identity is assumed, including at zero mass and in n=0. -/
theorem tendsto_sourceSingularityTopology_positive_scaling_iff
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {c : ℝ} (hc : 0 < c) {I : Type*} (F : Filter I)
    (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    Tendsto (fun i ↦ sourcePositiveScaledPotential hc (w i)) F
      (@nhds
        (SourceThetaPotentialL1 (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)))
        (sourceSingularityTopology ω (nativeClosedFormToAtlas (c • atlasClosedFormToNative θ))
          (sourcePositiveScaledBackground_big θ hθ hc))
        (sourcePositiveScaledPotential hc v)) ↔
    Tendsto w F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) v) := by
  let T := nativeClosedFormToAtlas (c • atlasClosedFormToNative θ)
  let hT := sourcePositiveScaledBackground_big θ hθ hc
  let := sourceSingularityPseudoMetricSpace ω θ hθ
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hθ
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hθ
  let := sourceSingularityPseudoMetricSpace ω T hT
  let : UniformSpace (SourceThetaPotentialL1 T) := sourceSingularityUniformSpace ω T hT
  let : TopologicalSpace (SourceThetaPotentialL1 T) := sourceSingularityTopology ω T hT
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hθ
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hθ).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hθ).toUniformSpace.toTopologicalSpace
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative T) hT
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative T).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative T) hT).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative T).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative T) hT).toUniformSpace.toTopologicalSpace
  have hmapθ : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  have hmapT : Topology.IsInducing (sourceThetaPotentialL1EquivNative T) :=
    Topology.IsInducing.induced _
  have hnative := SingularCanonicalSingularityScalarEquivalence.tendsto_native_positive_smul_iff
    ω (atlasClosedFormToNative θ) hθ hc F
    (fun i ↦ sourceThetaPotentialL1EquivNative θ (w i)) (sourceThetaPotentialL1EquivNative θ v)
  have hbigc : IsBigClass (RealBottChern.ofRepresentative (c • atlasClosedFormToNative θ)) := by
    rw [RealBottChern.ofRepresentative_smul]
    exact ActualPositiveClassScaling.isBigClass_positive_smul hθ hc
  have hscaled := native_tendsto_iff_of_form_eq ω (atlasClosedFormToNative T)
    (c • atlasClosedFormToNative θ) (sourceNativeAtlasForm_roundTrip _) hT hbigc F
    (fun i ↦ (isThetaPSH_iff_nativeThetaPotential T _).mp
      (sourcePositiveScaledPotential hc (w i)).property)
    ((isThetaPSH_iff_nativeThetaPotential T _).mp (sourcePositiveScaledPotential hc v).property)
    (fun i ↦ RestrictedApproximantComparison.isThetaPshPotential_smul
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp (w i).property) hc)
    (RestrictedApproximantComparison.isThetaPshPotential_smul
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property) hc)
  constructor
  · intro h
    apply hmapθ.tendsto_nhds_iff.mpr
    exact hnative.mp (hscaled.mp (hmapT.tendsto_nhds_iff.mp h))
  · intro h
    apply hmapT.tendsto_nhds_iff.mpr
    exact hscaled.mpr (hnative.mpr (hmapθ.tendsto_nhds_iff.mp h))

end SGPT.PSH.VariableComplexAtlas
