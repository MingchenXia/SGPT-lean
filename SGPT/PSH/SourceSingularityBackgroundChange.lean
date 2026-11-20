import SGPT.PSH.SourceSingularityDistance
import SGPT.Foundations.Analysis.Pending.SingularNativeCommonBackground

/-! # Whole original semipositive background independence

The complete mathematical route precedes this implementation in
`source-singularity-background-change.tex`. The added original form is
arbitrary semipositive, including zero; the ambient Kahler metric is separate.
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

/-- An actual big-current witness survives arbitrary semipositive addition.
The enlarged class's bigness is produced, rather than supplied by the caller. -/
theorem sourceBigClass_add_semipositive
    (θ η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive) :
    IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative (θ.add η))) := by
  change IsBigClass (RealBottChern.ofRepresentative
    (atlasClosedFormToNative θ + atlasClosedFormToNative η))
  obtain ⟨T⟩ := hbig
  refine ⟨{
    representative := T.representative + atlasClosedFormToNative η
    represents := by
      rw [RealBottChern.ofRepresentative_add, T.represents, RealBottChern.ofRepresentative_add]
    potential := T.potential
    lowerBound := T.lowerBound
    strictlyPsh := ?_ }⟩
  have hform : T.representative + atlasClosedFormToNative η - T.lowerBound.form =
      (T.representative - T.lowerBound.form) + atlasClosedFormToNative η := by abel
  rw [hform]
  exact LocalPotentials.isThetaPshPotential_add_of_semipositive T.strictlyPsh hη

/-- The same entire original function with its genuinely produced membership
in the full semipositive enlargement; every negative-infinite pole is retained. -/
def sourceSemipositiveBackgroundPotential
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (u : SourceThetaPotentialL1 θ) : SourceThetaPotentialL1 (θ.add η) :=
  ⟨u.val, (isThetaPSH_iff_nativeThetaPotential (θ.add η) u.val).mpr (by
    change IsThetaPshPotential
      (atlasClosedFormToNative θ + atlasClosedFormToNative η).val u.val
    exact LocalPotentials.isThetaPshPotential_add_of_semipositive
      ((isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property) hη)⟩

/-- Literal value readback on the original source carrier. -/
theorem sourceSemipositiveBackgroundPotential_val
    {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    (u : SourceThetaPotentialL1 θ) :
    (sourceSemipositiveBackgroundPotential η hη u).val = u.val := rfl

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Actual source/native common-background equivalence on unchanged original
functions. The common-carrier premises are genuine PSH membership only. -/
theorem tendsto_sourceSingularityTopology_iff_common_backgrounds
    (ω : KahlerBackground n M) (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hσ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative σ)))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hwσ : ∀ i, (ofFixedModel n M).IsThetaPSH σ (w i).val)
    (hvσ : (ofFixedModel n M).IsThetaPSH σ v.val) :
    Tendsto w F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) v) ↔
    Tendsto (fun i ↦ (⟨(w i).val, hwσ i⟩ : SourceThetaPotentialL1 σ)) F
      (@nhds (SourceThetaPotentialL1 σ) (sourceSingularityTopology ω σ hσ) ⟨v.val, hvσ⟩) := by
  let := sourceSingularityPseudoMetricSpace ω θ hθ
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hθ
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hθ
  let := sourceSingularityPseudoMetricSpace ω σ hσ
  let : UniformSpace (SourceThetaPotentialL1 σ) := sourceSingularityUniformSpace ω σ hσ
  let : TopologicalSpace (SourceThetaPotentialL1 σ) := sourceSingularityTopology ω σ hσ
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hθ
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hθ).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hθ).toUniformSpace.toTopologicalSpace
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative σ) hσ
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative σ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative σ) hσ).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative σ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative σ) hσ).toUniformSpace.toTopologicalSpace
  have hmapθ : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  have hmapσ : Topology.IsInducing (sourceThetaPotentialL1EquivNative σ) :=
    Topology.IsInducing.induced _
  have hnative :=
    SingularNativeCommonBackground.tendsto_native_iff_common_backgrounds
      ω (atlasClosedFormToNative θ) (atlasClosedFormToNative σ) hθ hσ F
      (fun i ↦ (isThetaPSH_iff_nativeThetaPotential θ _).mp (w i).property)
      ((isThetaPSH_iff_nativeThetaPotential θ _).mp v.property)
      (fun i ↦ (isThetaPSH_iff_nativeThetaPotential σ _).mp (hwσ i))
      ((isThetaPSH_iff_nativeThetaPotential σ _).mp hvσ)
  constructor
  · intro h
    apply hmapσ.tendsto_nhds_iff.mpr
    exact hnative.mp (hmapθ.tendsto_nhds_iff.mp h)
  · intro h
    apply hmapθ.tendsto_nhds_iff.mpr
    exact hnative.mpr (hmapσ.tendsto_nhds_iff.mp h)

/-- WHOLE original `cor:dSconv_changetheta`: arbitrary closed smooth
semipositive addition (including zero), with all enlarged data produced. -/
theorem tendsto_sourceSingularityTopology_iff_semipositive_enlargement
    (ω : KahlerBackground n M) (θ η : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hη : (atlasClosedFormToNative η).val.IsSemipositive)
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ) :
    Tendsto w F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) v) ↔
    Tendsto (fun i ↦ sourceSemipositiveBackgroundPotential η hη (w i)) F
      (@nhds (SourceThetaPotentialL1 (θ.add η))
        (sourceSingularityTopology ω (θ.add η) (sourceBigClass_add_semipositive θ η hθ hη))
        (sourceSemipositiveBackgroundPotential η hη v)) :=
  tendsto_sourceSingularityTopology_iff_common_backgrounds ω θ (θ.add η) hθ
    (sourceBigClass_add_semipositive θ η hθ hη) F w v
    (fun i ↦ (sourceSemipositiveBackgroundPotential η hη (w i)).property)
    (sourceSemipositiveBackgroundPotential η hη v).property

end SGPT.PSH.VariableComplexAtlas
