import SGPT.PSH.SourceSingularityDistance
import SGPT.Envelopes.SourceOrdinaryEnvelopeAlgebra
import SGPT.Foundations.Analysis.Pending.SingularNativeAdditionCancellation

/-! # Addition in the original singularity topologies

The complete source-first mathematical route is in
`source-singularity-addition.tex`. Independent original big forms, literal
genuine sums, all filters, poles and zero original masses are retained.
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

/-- The actual big-current witness and a genuine independent summand
manufacture bigness of the literal original coefficient-sum background. -/
theorem sourceIndependentSumBackground_big
    (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (v : SourceThetaPotentialL1 σ) :
    IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)))) := by
  rw [sourceNativeAtlasForm_roundTrip]
  obtain ⟨T⟩ := hθ
  refine ⟨{
    representative := T.representative + atlasClosedFormToNative σ
    represents := by simp only [RealBottChern.ofRepresentative_add, T.represents]
    potential := fun x => T.potential x + v.val x
    lowerBound := T.lowerBound
    strictlyPsh := ?_ }⟩
  have hp : (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (T.representative - T.lowerBound.form)) T.potential := by
    apply (isThetaPSH_iff_nativeThetaPotential _ _).mpr
    simpa only [sourceNativeAtlasForm_roundTrip] using T.strictlyPsh
  have hsum := sourceIndependentSum_thetaPSH hp v.property
  have hn := (isThetaPSH_iff_nativeThetaPotential _ _).mp hsum
  have heq : (T.representative - T.lowerBound.form) + atlasClosedFormToNative σ =
      (T.representative + atlasClosedFormToNative σ) - T.lowerBound.form := by abel
  simpa only [sourceNativeAtlasForm_roundTrip, heq] using hn

/-- The same whole extended-real sum in its genuine original carrier;
its local nondegeneracy is produced from the two given input memberships. -/
def sourceThetaPotentialSum
    {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M)}
    (u : SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 σ) :
    SourceThetaPotentialL1
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) :=
  ⟨fun x => u.val x + v.val x, sourceIndependentSum_thetaPSH u.property v.property⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

private theorem source_tendsto_iff_native_of_form_eq
    (ω : KahlerBackground n M) (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (β : ClosedRealOneOneForm n M) (hform : atlasClosedFormToNative θ = β)
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hβ : IsBigClass (RealBottChern.ofRepresentative β))
    {I : Type*} (F : Filter I) (w : I → SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 θ)
    (hw : ∀ i, IsThetaPshPotential β.val (w i).val) (hv : IsThetaPshPotential β.val v.val) :
    Tendsto w F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) v) ↔
      Tendsto (fun i => (⟨(w i).val, hw i⟩ : ThetaPshL1Topology.ThetaPshL1 β.val)) F
        (@nhds (ThetaPshL1Topology.ThetaPshL1 β.val)
          (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω β hβ).toUniformSpace.toTopologicalSpace
          ⟨v.val, hv⟩) := by
  subst β
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hθ
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace
      ω (atlasClosedFormToNative θ) hθ).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  exact hmap.tendsto_nhds_iff

/-- The first TWO original limits give the THIRD in the actual original
sum-background topology, including arbitrary filters and zero original masses. -/
theorem tendsto_sourceSingularityTopology_add
    (ω : KahlerBackground n M) (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hσ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative σ)))
    {I : Type*} (F : Filter I) (a : I → SourceThetaPotentialL1 θ) (b : I → SourceThetaPotentialL1 σ)
    (p : SourceThetaPotentialL1 θ) (q : SourceThetaPotentialL1 σ)
    (ha : Tendsto a F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) p))
    (hb : Tendsto b F (@nhds (SourceThetaPotentialL1 σ) (sourceSingularityTopology ω σ hσ) q)) :
    Tendsto (fun i => sourceThetaPotentialSum (a i) (b i)) F
      (@nhds
        (SourceThetaPotentialL1
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)))
        (sourceSingularityTopology ω
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
          (sourceIndependentSumBackground_big θ σ hθ q))
        (sourceThetaPotentialSum p q)) := by
  let γ := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  have hγ := sourceIndependentSumBackground_big θ σ hθ q
  have hγn : IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) := by
    simpa only [sourceNativeAtlasForm_roundTrip] using hγ
  let A := fun i => sourceThetaPotentialL1EquivNative θ (a i)
  let B := fun i => sourceThetaPotentialL1EquivNative σ (b i)
  let P := sourceThetaPotentialL1EquivNative θ p
  let Q := sourceThetaPotentialL1EquivNative σ q
  have hA := (source_tendsto_iff_native_of_form_eq ω θ (atlasClosedFormToNative θ)
    rfl hθ hθ F a p (fun i => (A i).property) P.property).mp ha
  have hB := (source_tendsto_iff_native_of_form_eq ω σ (atlasClosedFormToNative σ)
    rfl hσ hσ F b q (fun i => (B i).property) Q.property).mp hb
  have hsum (u : SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 σ) :
      IsThetaPshPotential (atlasClosedFormToNative θ + atlasClosedFormToNative σ).val
        (sourceThetaPotentialSum u v).val := by
    have h := (isThetaPSH_iff_nativeThetaPotential γ _).mp (sourceThetaPotentialSum u v).property
    simpa only [γ, sourceNativeAtlasForm_roundTrip] using h
  apply (source_tendsto_iff_native_of_form_eq ω γ
    (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
    (sourceNativeAtlasForm_roundTrip _) hγ hγn F
    (fun i => sourceThetaPotentialSum (a i) (b i)) (sourceThetaPotentialSum p q)
    (fun i => hsum (a i) (b i)) (hsum p q)).mpr
  exact SingularNativeAdditionContinuity.tendsto_native_add ω
    (atlasClosedFormToNative θ) (atlasClosedFormToNative σ) hθ hσ F A B P Q hA hB

/-- The first and third original limits give the second. Actual native
cancellation manufactures the needed endpoint and maximum mass limits. -/
theorem tendsto_sourceSingularityTopology_of_left_and_add
    (ω : KahlerBackground n M) (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hσ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative σ)))
    {I : Type*} (F : Filter I) (a : I → SourceThetaPotentialL1 θ) (b : I → SourceThetaPotentialL1 σ)
    (p : SourceThetaPotentialL1 θ) (q : SourceThetaPotentialL1 σ)
    (ha : Tendsto a F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) p))
    (hadd : Tendsto (fun i => sourceThetaPotentialSum (a i) (b i)) F
      (@nhds
        (SourceThetaPotentialL1
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)))
        (sourceSingularityTopology ω
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
          (sourceIndependentSumBackground_big θ σ hθ q))
        (sourceThetaPotentialSum p q))) :
    Tendsto b F (@nhds (SourceThetaPotentialL1 σ) (sourceSingularityTopology ω σ hσ) q) := by
  let γ := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  have hγ := sourceIndependentSumBackground_big θ σ hθ q
  have hγn : IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) := by
    simpa only [sourceNativeAtlasForm_roundTrip] using hγ
  let A := fun i => sourceThetaPotentialL1EquivNative θ (a i)
  let B := fun i => sourceThetaPotentialL1EquivNative σ (b i)
  let P := sourceThetaPotentialL1EquivNative θ p
  let Q := sourceThetaPotentialL1EquivNative σ q
  have hA := (source_tendsto_iff_native_of_form_eq ω θ (atlasClosedFormToNative θ)
    rfl hθ hθ F a p (fun i => (A i).property) P.property).mp ha
  have hsum (u : SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 σ) :
      IsThetaPshPotential (atlasClosedFormToNative θ + atlasClosedFormToNative σ).val
        (sourceThetaPotentialSum u v).val := by
    have h := (isThetaPSH_iff_nativeThetaPotential γ _).mp (sourceThetaPotentialSum u v).property
    simpa only [γ, sourceNativeAtlasForm_roundTrip] using h
  have hsumNative := (source_tendsto_iff_native_of_form_eq ω γ
    (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
    (sourceNativeAtlasForm_roundTrip _) hγ hγn F
    (fun i => sourceThetaPotentialSum (a i) (b i)) (sourceThetaPotentialSum p q)
    (fun i => hsum (a i) (b i)) (hsum p q)).mp hadd
  apply (source_tendsto_iff_native_of_form_eq ω σ (atlasClosedFormToNative σ)
    rfl hσ hσ F b q (fun i => (B i).property) Q.property).mpr
  exact SingularNativeAdditionCancellation.tendsto_native_of_native_and_native_add ω
    (atlasClosedFormToNative θ) (atlasClosedFormToNative σ) hθ hσ F A B P Q hA hsumNative

/-- The second and third original limits give the first, with exact
commutation of the original sum background and all extended function values. -/
theorem tendsto_sourceSingularityTopology_of_right_and_add
    (ω : KahlerBackground n M) (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hσ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative σ)))
    {I : Type*} (F : Filter I) (a : I → SourceThetaPotentialL1 θ) (b : I → SourceThetaPotentialL1 σ)
    (p : SourceThetaPotentialL1 θ) (q : SourceThetaPotentialL1 σ)
    (hb : Tendsto b F (@nhds (SourceThetaPotentialL1 σ) (sourceSingularityTopology ω σ hσ) q))
    (hadd : Tendsto (fun i => sourceThetaPotentialSum (a i) (b i)) F
      (@nhds
        (SourceThetaPotentialL1
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)))
        (sourceSingularityTopology ω
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
          (sourceIndependentSumBackground_big θ σ hθ q))
        (sourceThetaPotentialSum p q))) :
    Tendsto a F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) p) := by
  let γ := nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
  have hγ := sourceIndependentSumBackground_big θ σ hθ q
  have hγn : IsBigClass (RealBottChern.ofRepresentative
      (atlasClosedFormToNative θ + atlasClosedFormToNative σ)) := by
    simpa only [sourceNativeAtlasForm_roundTrip] using hγ
  let A := fun i => sourceThetaPotentialL1EquivNative θ (a i)
  let B := fun i => sourceThetaPotentialL1EquivNative σ (b i)
  let P := sourceThetaPotentialL1EquivNative θ p
  let Q := sourceThetaPotentialL1EquivNative σ q
  have hB := (source_tendsto_iff_native_of_form_eq ω σ (atlasClosedFormToNative σ)
    rfl hσ hσ F b q (fun i => (B i).property) Q.property).mp hb
  have hsum (u : SourceThetaPotentialL1 θ) (v : SourceThetaPotentialL1 σ) :
      IsThetaPshPotential (atlasClosedFormToNative θ + atlasClosedFormToNative σ).val
        (sourceThetaPotentialSum u v).val := by
    have h := (isThetaPSH_iff_nativeThetaPotential γ _).mp (sourceThetaPotentialSum u v).property
    simpa only [γ, sourceNativeAtlasForm_roundTrip] using h
  have hsumNative := (source_tendsto_iff_native_of_form_eq ω γ
    (atlasClosedFormToNative θ + atlasClosedFormToNative σ)
    (sourceNativeAtlasForm_roundTrip _) hγ hγn F
    (fun i => sourceThetaPotentialSum (a i) (b i)) (sourceThetaPotentialSum p q)
    (fun i => hsum (a i) (b i)) (hsum p q)).mp hadd
  apply (source_tendsto_iff_native_of_form_eq ω θ (atlasClosedFormToNative θ)
    rfl hθ hθ F a p (fun i => (A i).property) P.property).mpr
  exact SingularNativeAdditionCancellation.tendsto_native_of_native_right_and_native_add ω
    (atlasClosedFormToNative θ) (atlasClosedFormToNative σ) hθ hσ F A B P Q hB hsumNative

/-- WHOLE original `thm:dSadditivity`: any TWO of the THREE actual
original limits imply the third, with independent big forms and all filters. -/
theorem sourceSingularityTopology_addition_two_out_of_three
    (ω : KahlerBackground n M) (θ σ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hθ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (hσ : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative σ)))
    {I : Type*} (F : Filter I) (a : I → SourceThetaPotentialL1 θ) (b : I → SourceThetaPotentialL1 σ)
    (p : SourceThetaPotentialL1 θ) (q : SourceThetaPotentialL1 σ) :
    let A := Tendsto a F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hθ) p)
    let B := Tendsto b F
      (@nhds (SourceThetaPotentialL1 σ) (sourceSingularityTopology ω σ hσ) q)
    let S := Tendsto (fun i => sourceThetaPotentialSum (a i) (b i)) F
      (@nhds
        (SourceThetaPotentialL1
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ)))
        (sourceSingularityTopology ω
          (nativeClosedFormToAtlas (atlasClosedFormToNative θ + atlasClosedFormToNative σ))
          (sourceIndependentSumBackground_big θ σ hθ q))
        (sourceThetaPotentialSum p q))
    (A → B → S) ∧ (A → S → B) ∧ (B → S → A) :=
  ⟨tendsto_sourceSingularityTopology_add ω θ σ hθ hσ F a b p q,
    tendsto_sourceSingularityTopology_of_left_and_add ω θ σ hθ hσ F a b p q,
    tendsto_sourceSingularityTopology_of_right_and_add ω θ σ hθ hσ F a b p q⟩

end SGPT.PSH.VariableComplexAtlas
