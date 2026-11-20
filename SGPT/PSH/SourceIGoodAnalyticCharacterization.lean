import SGPT.PSH.SourceSingularityDistance
import SGPT.PSH.QuasiEquisingular
import SGPT.PSH.SourceIGoodBackground
import SGPT.Foundations.Analysis.Pending.IGoodAnalyticCharacterization

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter MeasureTheory
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- The actual original PSH equivalence preserves the explicitly selected genuine dS convergence. -/
theorem sourceSingularity_tendsto_iff_native {I : Type*} (F : Filter I)
    (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (v : I → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ) :
    Tendsto v F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig) u) ↔
      Tendsto (fun i => sourceThetaPotentialL1EquivNative θ (v i)) F
        (@nhds (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val)
          (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace omega
            (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
          (sourceThetaPotentialL1EquivNative θ u)) := by
  let := sourceSingularityPseudoMetricSpace omega θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace omega θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology omega θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace omega (atlasClosedFormToNative θ) hbig
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace omega
      (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  let e := sourceSingularityHomeomorphNative omega θ hbig
  constructor
  · intro hv
    exact (e.continuous.tendsto u).comp hv
  · intro hv
    change Tendsto (fun i => e (v i)) F (𝓝 (e u)) at hv
    have h := (e.symm.continuous.tendsto (e u)).comp hv
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using h

/-- The auxiliary Kahler form changes only proofs of the SAME defining radial distance. -/
theorem sourceSingularityDistance_auxiliary_eq (omega kappa : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u v : SourceThetaPotentialL1 θ) :
    sourceSingularityDistance omega θ hbig u v = sourceSingularityDistance kappa θ hbig u v := by
  rw [sourceSingularityDistance_eq_native, sourceSingularityDistance_eq_native]
  rfl

/-- Genuine distance-generated topology uses the proved finite defining source distance. -/
theorem sourceSingularity_tendsto_iff_distance {I : Type*} (F : Filter I)
    (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (v : I → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ) :
    Tendsto v F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig) u) ↔
      Tendsto (fun i => (sourceSingularityDistance omega θ hbig (v i) u).toReal) F (𝓝 0) := by
  let := sourceSingularityPseudoMetricSpace omega θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace omega θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology omega θ hbig
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [sourceSingularityPseudoMetricSpace_dist]

/-- An arbitrary original approximation's auxiliary form need not equal the named source choice. -/
theorem sourceSingularity_tendsto_auxiliary_iff {I : Type*} (F : Filter I)
    (omega kappa : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (v : I → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ) :
    Tendsto v F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig) u) ↔
      Tendsto v F (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology kappa θ hbig) u) := by
  rw [sourceSingularity_tendsto_iff_distance, sourceSingularity_tendsto_iff_distance]
  simp only [sourceSingularityDistance_auxiliary_eq omega kappa θ hbig]


/-- The original analytic approximation condition on the ENTIRE source PSH carrier and actual dS topology. -/
def SourceIGoodAnalyticApproximation (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) : Prop :=
  ∃ v : ℕ → SourceThetaPotentialL1 θ,
    (∀ j, FirstPass.QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) (v j).val) ∧
    Tendsto v atTop (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig) u)

/-- The original strengthening retains a PRODUCED positive genuine current margin at EVERY term. -/
def SourceIGoodAnalyticCurrentApproximation (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) : Prop :=
  ∃ v : ℕ → SourceThetaPotentialL1 θ,
    (∀ j, FirstPass.QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) (v j).val ∧
      ∃ δ : ℝ, 0 < δ ∧ (ofFixedModel n M).IsThetaPSH
        (nativeClosedFormToAtlas (atlasClosedFormToNative θ - δ • omega.form)) (v j).val) ∧
    Tendsto v atTop (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig) u)

/-- SAME original analytic functions and target; only genuine PSH membership proofs change. -/
theorem sourceIGoodAnalyticApproximation_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) :
    SourceIGoodAnalyticApproximation omega θ hbig u ↔
      ∃ v : ℕ → ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val,
        (∀ j, FirstPass.QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) (v j).val) ∧
        Tendsto v atTop (@nhds (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val)
          (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace omega
            (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
          (sourceThetaPotentialL1EquivNative θ u)) := by
  constructor
  · rintro ⟨v,hA,hv⟩
    exact ⟨fun j => sourceThetaPotentialL1EquivNative θ (v j), hA,
      (sourceSingularity_tendsto_iff_native atTop omega θ hbig v u).mp hv⟩
  · rintro ⟨v,hA,hv⟩
    let w : ℕ → SourceThetaPotentialL1 θ := fun j => (sourceThetaPotentialL1EquivNative θ).symm (v j)
    refine ⟨w,hA, (sourceSingularity_tendsto_iff_native atTop omega θ hbig w u).mpr ?_⟩
    have heq : (fun j => sourceThetaPotentialL1EquivNative θ (w j)) = v := by
      funext j
      exact (sourceThetaPotentialL1EquivNative θ).apply_symm_apply (v j)
    rw [heq]
    exact hv

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M] in
/-- An entire actual smaller background, not a cohomological or scalar surrogate, encodes the margin. -/
theorem sourceIGood_current_margin_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M)) (v : M → EReal) :
    (∃ δ : ℝ, 0 < δ ∧ (ofFixedModel n M).IsThetaPSH
      (nativeClosedFormToAtlas (atlasClosedFormToNative θ - δ • omega.form)) v) ↔
    ∃ δ : ℝ, 0 < δ ∧ IsThetaPshPotential (atlasClosedFormToNative θ - δ • omega.form).val v := by
  constructor
  · rintro ⟨δ,hδ,hv⟩
    refine ⟨δ,hδ,?_⟩
    have h := (isThetaPSH_iff_nativeThetaPotential _ _).mp hv
    simpa only [sourceNativeAtlasForm_roundTrip] using h
  · rintro ⟨δ,hδ,hv⟩
    refine ⟨δ,hδ, (isThetaPSH_iff_nativeThetaPotential _ _).mpr ?_⟩
    simpa only [sourceNativeAtlasForm_roundTrip] using hv


/-- The actual original current strengthening transports every term and its produced positive margin. -/
theorem sourceIGoodAnalyticCurrentApproximation_iff_native (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) :
    SourceIGoodAnalyticCurrentApproximation omega θ hbig u ↔
      ∃ v : ℕ → ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val,
        (∀ j, FirstPass.QuasiEquisingularApproximation.HasManifoldAnalyticSingularityType (n := n) (v j).val ∧
          ∃ δ : ℝ, 0 < δ ∧ IsThetaPshPotential (atlasClosedFormToNative θ - δ • omega.form).val (v j).val) ∧
        Tendsto v atTop (@nhds (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val)
          (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace omega
            (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
          (sourceThetaPotentialL1EquivNative θ u)) := by
  constructor
  · rintro ⟨v,hA,hv⟩
    refine ⟨fun j => sourceThetaPotentialL1EquivNative θ (v j), fun j => ?_,
      (sourceSingularity_tendsto_iff_native atTop omega θ hbig v u).mp hv⟩
    exact ⟨(hA j).1, (sourceIGood_current_margin_iff_native omega θ (v j).val).mp (hA j).2⟩
  · rintro ⟨v,hA,hv⟩
    let w : ℕ → SourceThetaPotentialL1 θ := fun j => (sourceThetaPotentialL1EquivNative θ).symm (v j)
    refine ⟨w,fun j => ?_, (sourceSingularity_tendsto_iff_native atTop omega θ hbig w u).mpr ?_⟩
    · exact ⟨(hA j).1, (sourceIGood_current_margin_iff_native omega θ (w j).val).mpr (hA j).2⟩
    · have heq : (fun j => sourceThetaPotentialL1EquivNative θ (w j)) = v := by
        funext j
        exact (sourceThetaPotentialL1EquivNative θ).apply_symm_apply (v j)
      rw [heq]
      exact hv

/-- ALL three original equivalences and the actual per-term Kahler-current strengthening. -/
theorem sourceIGood_analytic_mass_envelope_equivalences (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ) :
    (SourceIGoodAnalyticApproximation omega θ hbig u ↔
      sourcePotentialNonPluripolarMeasure θ u.val u.property univ = sourceIVolume θ u.val u.property) ∧
    (SourceIGoodAnalyticApproximation omega θ hbig u ↔
      sourceSingularityEnvelope θ u.val = sourceIEnvelope θ u.val) ∧
    (SourceIGoodAnalyticApproximation omega θ hbig u ↔
      SourceIGoodAnalyticCurrentApproximation omega θ hbig u) := by
  let hu := (isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property
  obtain ⟨hm,he,hk⟩ := IGoodAnalyticCharacterization.analytic_native_mass_envelope_current_equivalences
    omega (atlasClosedFormToNative θ) hbig hu hpos
  have hA := sourceIGoodAnalyticApproximation_iff_native omega θ hbig u
  refine ⟨?_,?_,?_⟩
  · rw [sourceIVolume_eq_native θ u.val u.property hu.1.hasSmoothLocalPotentials]
    exact hA.trans hm
  · rw [sourceSingularityEnvelope_eq_native, sourceIEnvelope_eq_native θ u.val u.property]
    exact hA.trans he
  · exact hA.trans (hk.trans (sourceIGoodAnalyticCurrentApproximation_iff_native omega θ hbig u).symm)


/-- ANY four-clause ORIGINAL QEA with original-background PSH stages obeys the source criterion,
including approximations whose auxiliary Kahler form is different from the named source choice. -/
theorem sourceIGood_any_qea_tendsto_iff (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) (U : ℕ → SourceThetaPotentialL1 θ)
    (hQ : SGPT.PSH.SourceQuasiEquisingularApproximation (atlasClosedFormToNative θ) u.val
      (fun j => (U j).val))
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ) :
    Tendsto U atTop (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig) u) ↔
      sourceSingularityEnvelope θ u.val = sourceIEnvelope θ u.val := by
  obtain ⟨kappa,ε,happ⟩ := SGPT.PSH.native_of_sourceQuasiEquisingularApproximation hQ
  let hu := (isThetaPSH_iff_nativeThetaPotential θ u.val).mp u.property
  have hid := FullQEANativeIGoodCriterion.native_qea_tendsto_target_iff_iGoodWith
    kappa (atlasClosedFormToNative θ) hbig happ
    (fun j => (isThetaPSH_iff_nativeThetaPotential θ (U j).val).mp (U j).property) hpos
  have hlim : Tendsto U atTop (@nhds (SourceThetaPotentialL1 θ)
      (sourceSingularityTopology kappa θ hbig) u) ↔ IGoodWith (atlasClosedFormToNative θ) u.val hu := by
    rw [sourceSingularity_tendsto_iff_native atTop kappa θ hbig U u]
    exact hid
  have hgood : IGoodWith (atlasClosedFormToNative θ) u.val hu ↔
      sourceSingularityEnvelope θ u.val = sourceIEnvelope θ u.val := by
    rw [← sourceIGoodWith_iff_native θ u.val u.property]
    change (0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ ∧ _) ↔ _
    exact and_iff_right hpos
  exact (sourceSingularity_tendsto_auxiliary_iff atTop omega kappa θ hbig U u).trans (hlim.trans hgood)

/-- The ENTIRE original theorem: three equivalences, per-term current strengthening,
and the final universal quantifier over original fixed-background QEA families. -/
theorem sourceIGood_characterization_whole (omega : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ)
    (hpos : 0 < sourcePotentialNonPluripolarMeasure θ u.val u.property univ) :
    (SourceIGoodAnalyticApproximation omega θ hbig u ↔
      sourcePotentialNonPluripolarMeasure θ u.val u.property univ = sourceIVolume θ u.val u.property) ∧
    (SourceIGoodAnalyticApproximation omega θ hbig u ↔
      sourceSingularityEnvelope θ u.val = sourceIEnvelope θ u.val) ∧
    (SourceIGoodAnalyticApproximation omega θ hbig u ↔
      SourceIGoodAnalyticCurrentApproximation omega θ hbig u) ∧
    (SourceIGoodAnalyticApproximation omega θ hbig u → ∀ U : ℕ → SourceThetaPotentialL1 θ,
      SGPT.PSH.SourceQuasiEquisingularApproximation (atlasClosedFormToNative θ) u.val (fun j => (U j).val) →
      Tendsto U atTop (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology omega θ hbig) u)) := by
  obtain ⟨hm,he,hk⟩ := sourceIGood_analytic_mass_envelope_equivalences omega θ hbig u hpos
  exact ⟨hm,he,hk,fun hA U hQ =>
    (sourceIGood_any_qea_tendsto_iff omega θ hbig u U hQ hpos).mpr (he.mp hA)⟩

end SGPT.PSH.VariableComplexAtlas
