import SGPT.PSH.SourceSingularityDistanceConvergence
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityInterpolation

/-! # Whole original minimal-potential interpolation limits

The actual original minimal potential, EReal zero-coefficient convention,
entire PSH carrier and explicitly selected source dS topology are retained. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending ThetaPshConvexCombination EndpointMixedMassConvexCombination
open SingularMinimalCanonicalRay

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The original literal interpolation. Zero EReal coefficients retain the
book's endpoint convention even when either original value is a pole. -/
def sourceMinimalInterpolationPotential
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (t : ℝ) (u : M → EReal) : M → EReal :=
  convexComb (1 - t) u (sourceMinimalEnvelope θ)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Genuine source membership is manufactured from the original input and
the internally produced minimal potential on the entire closed parameter interval. -/
def sourceMinimalInterpolation (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (t : Icc (0 : ℝ) 1) (u : SourceThetaPotentialL1 θ) : SourceThetaPotentialL1 θ :=
  ⟨sourceMinimalInterpolationPotential θ t.val u.val,
    (isThetaPSH_iff_nativeThetaPotential θ _).mpr
      (isThetaPshPotential_convexComb_closed
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property)
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp (sourceMinimalEnvelope_thetaPSH ω θ hbig))
        (sub_nonneg.mpr t.property.2) (sub_le_self 1 t.property.1))⟩

/-- Entire original formula, with the SAME input and actual minimal potential. -/
theorem sourceMinimalInterpolation_val (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (t : Icc (0 : ℝ) 1) (u : SourceThetaPotentialL1 θ) :
    (sourceMinimalInterpolation ω θ hbig t u).val =
      fun x ↦ (((1 - t.val : ℝ)) : EReal) * u.val x +
        (t.val : EReal) * sourceMinimalEnvelope θ x := by
  funext x
  change (((1 - t.val : ℝ)) : EReal) * u.val x +
    (((1 - (1 - t.val) : ℝ)) : EReal) * sourceMinimalEnvelope θ x = _
  rw [show 1 - (1 - t.val) = t.val by ring]

/-- The zero endpoint keeps the entire original input, including its poles. -/
theorem sourceMinimalInterpolation_zero (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) :
    (sourceMinimalInterpolation ω θ hbig ⟨0, by constructor <;> norm_num⟩ u).val = u.val := by
  funext x
  simp only [sourceMinimalInterpolation_val, sub_zero, EReal.coe_one, one_mul,
    EReal.coe_zero, zero_mul, add_zero]

/-- The printed t=1 convention gives exactly the minimal potential even at poles. -/
theorem sourceMinimalInterpolation_one (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) :
    (sourceMinimalInterpolation ω θ hbig ⟨1, by constructor <;> norm_num⟩ u).val =
      sourceMinimalEnvelope θ := by
  funext x
  simp only [sourceMinimalInterpolation_val, sub_self, EReal.coe_zero, zero_mul,
    EReal.coe_one, one_mul, zero_add]

/-- Whole original fixed-interpolation lemma on the actual source dS topology,
strengthened to both coefficient endpoints and all original zero-mass inputs. -/
theorem sourceMinimalInterpolation_continuous (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (t : Icc (0 : ℝ) 1) :
    letI := sourceSingularityPseudoMetricSpace ω θ hbig
    letI : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
    letI : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
    Continuous (sourceMinimalInterpolation ω θ hbig t) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  let e := sourceSingularityHomeomorphNative ω θ hbig
  let Q : ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val →
      ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val := fun v ↦
    ⟨convexComb (1 - t.val) v.val (thetaPshSupremum (atlasClosedFormToNative θ).val),
      isThetaPshPotential_convexComb_closed v.property
        (isModelPotential_thetaPshSupremum ω (atlasClosedFormToNative θ) hbig).plurisubharmonic
        (sub_nonneg.mpr t.property.2) (sub_le_self 1 t.property.1)⟩
  have hQ : Continuous Q :=
    SingularCanonicalSingularityInterpolation.continuous_native_convexComb_minimal
      ω (atlasClosedFormToNative θ) hbig (sub_nonneg.mpr t.property.2)
      (sub_le_self 1 t.property.1)
  have heq : sourceMinimalInterpolation ω θ hbig t = e.symm ∘ Q ∘ e := by
    funext u
    apply Subtype.ext
    change convexComb (1 - t.val) u.val (sourceMinimalEnvelope θ) =
      convexComb (1 - t.val) u.val (thetaPshSupremum (atlasClosedFormToNative θ).val)
    rw [sourceMinimalEnvelope_eq_native]
  rw [heq]
  exact e.symm.continuous.comp (hQ.comp e.continuous)

/-- Whole original `lma:dsconvpertV` along every incoming filter, including
the printed t=1 endpoint and its original zero-coefficient pole convention. -/
theorem tendsto_sourceMinimalInterpolation (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    {I : Type*} (F : Filter I) (ui : I → SourceThetaPotentialL1 θ) (u : SourceThetaPotentialL1 θ)
    (t : Icc (0 : ℝ) 1)
    (hlim : Tendsto ui F (@nhds (SourceThetaPotentialL1 θ)
      (sourceSingularityTopology ω θ hbig) u)) :
    Tendsto (fun i ↦ sourceMinimalInterpolation ω θ hbig t (ui i)) F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig)
        (sourceMinimalInterpolation ω θ hbig t u)) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  exact ((sourceMinimalInterpolation_continuous ω θ hbig t).tendsto u).comp hlim

/-- Whole original `lma:linearpertbyVtheta`, strengthened to arbitrary filters
of genuine original interior parameters tending to zero. -/
theorem tendsto_sourceMinimalInterpolation_zero (ω : KahlerBackground n M)
    (θ : AtlasClosedRealOneOneForm (ofFixedModel n M))
    (hbig : IsBigClass (RealBottChern.ofRepresentative (atlasClosedFormToNative θ)))
    (u : SourceThetaPotentialL1 θ) {I : Type*} (F : Filter I) (t : I → Ioo (0 : ℝ) 1)
    (ht : Tendsto (fun i ↦ (t i).val) F (𝓝 0)) :
    Tendsto (fun i ↦ sourceMinimalInterpolation ω θ hbig
      ⟨(t i).val, (t i).property.1.le, (t i).property.2.le⟩ u) F
      (@nhds (SourceThetaPotentialL1 θ) (sourceSingularityTopology ω θ hbig) u) := by
  let := sourceSingularityPseudoMetricSpace ω θ hbig
  let : UniformSpace (SourceThetaPotentialL1 θ) := sourceSingularityUniformSpace ω θ hbig
  let : TopologicalSpace (SourceThetaPotentialL1 θ) := sourceSingularityTopology ω θ hbig
  let := SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig
  let : UniformSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace
  let : TopologicalSpace (ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val) :=
    (SingularCanonicalSingularityDistance.singularityPseudoMetricSpace ω (atlasClosedFormToNative θ) hbig).toUniformSpace.toTopologicalSpace
  have hmap : Topology.IsInducing (sourceThetaPotentialL1EquivNative θ) :=
    Topology.IsInducing.induced _
  apply hmap.tendsto_nhds_iff.mpr
  let Q : I → ThetaPshL1Topology.ThetaPshL1 (atlasClosedFormToNative θ).val := fun i ↦
    ⟨convexComb (1 - (t i).val) u.val (thetaPshSupremum (atlasClosedFormToNative θ).val),
      isThetaPshPotential_convexComb_closed
        ((isThetaPSH_iff_nativeThetaPotential θ _).mp u.property)
        (isModelPotential_thetaPshSupremum ω (atlasClosedFormToNative θ) hbig).plurisubharmonic
        (sub_nonneg.mpr (t i).property.2.le) (sub_le_self 1 (t i).property.1.le)⟩
  have hn : Tendsto Q F (𝓝 (sourceThetaPotentialL1EquivNative θ u)) :=
    SingularCanonicalSingularityInterpolation.tendsto_native_convexComb_minimal_zero
      ω (atlasClosedFormToNative θ) hbig (sourceThetaPotentialL1EquivNative θ u) F t ht
  have heq : (sourceThetaPotentialL1EquivNative θ) ∘
      (fun i ↦ sourceMinimalInterpolation ω θ hbig
        ⟨(t i).val, (t i).property.1.le, (t i).property.2.le⟩ u) = Q := by
    funext i
    apply Subtype.ext
    change convexComb (1 - (t i).val) u.val (sourceMinimalEnvelope θ) =
      convexComb (1 - (t i).val) u.val (thetaPshSupremum (atlasClosedFormToNative θ).val)
    rw [sourceMinimalEnvelope_eq_native]
  rw [heq]
  exact hn

end SGPT.PSH.VariableComplexAtlas
