import SGPT.Foundations.Analysis.Pending.DirectedMetricNearLimitSequences
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingModels
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityModelMetricSpace
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz
import SGPT.Foundations.Analysis.Pending.SingularNativeGlobalPOrderClosed
import SGPT.Foundations.Analysis.Pending.ActualMixedMassGlobalPMonotone
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge

set_option autoImplicit false

/-! # Actual whole-net infimum of decreasing P-envelopes

SGPT PDF0243 Proposition 6.2.6, (6.27). Each directed tail internally
supplies a monotone near-limit sequence and a uniform positive mass
bound. Actual positive model sequence infima recover the whole-net
pointwise identity; no countable cofinal sequence or infimum certificate.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.SingularDecreasingPEnvelopeNets

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.POrder
  DiagonalMass MixedMass GlobalNonPluripolar ThetaPshL1Topology
  SingularCanonicalSingularityDistance SingularCanonicalDistanceZeroPEquivalence
  SingularGlobalPOrder SingularGlobalPEnvelopeBridge SingularNativeGlobalPOrderClosed
  ActualMixedMassGlobalPMonotone SingularCanonicalSingularityMassLipschitz
  ActualDecreasingModelInfimum ActualDecreasingModelPositiveInfimum
  SingularCanonicalSingularityDecreasingModels DirectedMetricNearLimitSequences

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem envelope_isModel_of_positive (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hpos : 0 < diagonalPotentialMass θ u hu) :
    IsModelPotential θ (singularityEnvelope θ.val u) := by
  have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1
    θ.property.2 hu.1.hasSmoothLocalPotentials u hu
  exact ⟨hP, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
    omega θ u hu hpos).symm,
    (singularityEnvelopeMassPreserving omega θ u hu hP).symm ▸ hpos⟩

private theorem model_eq_envelope_of_two_native_limits
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (w : ℕ → ThetaPshL1 θ.val) (W v : ThetaPshL1 θ.val)
    (hW : IsModelPotential θ W.val)
    (hpos : 0 < diagonalPotentialMass θ v.val v.property)
    (hwW : Tendsto w atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace W))
    (hwv : Tendsto w atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v)) :
    W.val = singularityEnvelope θ.val v.val := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  have hzReal : dist W v = 0 := by
    have h := hwW.dist hwv
    simp only [dist_self] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  obtain ⟨m, _, _, _, hm⟩ := exists_tendsto_singularityDistance omega θ hbig
    W.property v.property
  have hmzero : m = 0 := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig, hm,
      EReal.toReal_coe] using hzReal
  have hz : singularityDistance omega θ hbig W.val v.val = 0 := by
    rw [hm, hmzero, EReal.coe_zero]
  have hsource := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
    W.property v.property).mp hz
  exact hW.envelope_eq.trans (pEquivalentWith_iff_envelope_eq.mp
    ((sourcePEquivalent_iff_pEquivalentWith omega θ W.property v.property
      hW.positive_mass hpos).mp hsource))

private theorem exists_tail_sequence_envelope_iInf_eq
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (horder : ∀ i j, i ≤ j → POrderWith θ (ui j).val (ui i).val)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v))
    (hpos : 0 < diagonalPotentialMass θ v.val v.property) (i₀ : I) :
    ∃ j : ℕ → I, (∀ k, i₀ ≤ j k) ∧
      (⨅ k, singularityEnvelope θ.val (ui (j k)).val) =
        singularityEnvelope θ.val v.val := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  let μ : I → ℝ≥0∞ := fun i => diagonalPotentialMass θ (ui i).val (ui i).property
  let μv := diagonalPotentialMass θ v.val v.property
  have hfinite : μv ≠ ∞ := (globalMixedMass_lt_top omega
    (fun _ : Fin n => v.property.1)).ne
  have hrealpos : 0 < μv.toReal := ENNReal.toReal_pos hpos.ne' hfinite
  let δ : ℝ := μv.toReal / 2
  have hδ : 0 < δ := half_pos hrealpos
  have hδlt : δ < μv.toReal := half_lt_self hrealpos
  have hmasslim : Tendsto (fun i => (μ i).toReal) atTop (𝓝 μv.toReal) :=
    ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto v).comp hlim
  have htail : {i | ENNReal.ofReal δ ≤ μ i} ∈ (atTop : Filter I) := by
    have hevent := (tendsto_order.mp hmasslim).1 δ hδlt
    filter_upwards [hevent] with i hi
    exact (ENNReal.ofReal_le_iff_le_toReal
      (globalMixedMass_lt_top omega (fun _ : Fin n => (ui i).property.1)).ne).mpr hi.le
  obtain ⟨j, hmono, hi₀, hjmass, hjlim⟩ :=
    exists_monotone_sequence_in_tail_tendsto hlim i₀ htail
  have hstagepos (k : ℕ) : 0 < μ (j k) :=
    (ENNReal.ofReal_pos.mpr hδ).trans_le (hjmass k)
  have hmodels (k : ℕ) : IsModelPotential θ
      (singularityEnvelope θ.val (ui (j k)).val) :=
    envelope_isModel_of_positive omega (ui (j k)).property (hstagepos k)
  let w : ℕ → ThetaPshL1 θ.val := fun k =>
    ⟨singularityEnvelope θ.val (ui (j k)).val, (hmodels k).plurisubharmonic⟩
  have hanti : Antitone fun k => (w k).val := by
    intro a b hab
    exact horder (j a) (j b) (hmono hab)
  have hbound (k : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (w k).val (hmodels k).plurisubharmonic :=
    (hjmass k).trans_eq (singularityEnvelopeMassPreserving omega θ (ui (j k)).val
      (ui (j k)).property (hmodels k).plurisubharmonic).symm
  have hInf := isModelPotential_iInf_of_uniform_positive_stage_mass
    omega hmodels hanti hδ hbound
  let W : ThetaPshL1 θ.val := ⟨⨅ k, (w k).val, hInf.plurisubharmonic⟩
  have hwW : Tendsto w atTop (𝓝 W) :=
    tendsto_native_iInf_of_uniform_positive_stage_mass omega θ hbig
      w hmodels hanti hδ hbound
  have hzero (k : ℕ) : dist (w k) (ui (j k)) = 0 := by
    have he := sourcePEquivalent_singularityEnvelope omega θ (ui (j k)).property
    have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      (w k).property (ui (j k)).property).mpr ⟨he.2, he.1⟩
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hz, EReal.toReal_zero]
  have hwv : Tendsto w atTop (𝓝 v) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hdist := tendsto_iff_dist_tendsto_zero.mp hjlim
    apply squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) hdist
    have h := dist_triangle (w k) (ui (j k)) v
    simpa only [hzero, zero_add] using h)
  exact ⟨j, hi₀, model_eq_envelope_of_two_native_limits omega θ hbig
    w W v hInf hpos hwW hwv⟩

/-- The true native limit with positive original mass recovers the actual
whole-net envelope infimum for every decreasing fixed-background P-net. -/
theorem iInf_singularityEnvelope_eq_of_fixedPOrder_tendsto_native
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (horder : ∀ i j, i ≤ j → POrderWith θ (ui j).val (ui i).val)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v))
    (hpos : 0 < diagonalPotentialMass θ v.val v.property) :
    (⨅ i, singularityEnvelope θ.val (ui i).val) = singularityEnvelope θ.val v.val := by
  classical
  apply le_antisymm
  · obtain ⟨j, _, heq⟩ := exists_tail_sequence_envelope_iInf_eq
      omega θ hbig ui v horder hlim hpos (Classical.choice inferInstance)
    rw [← heq]
    exact le_iInf fun k => iInf_le _ (j k)
  · apply le_iInf
    intro i
    obtain ⟨j, hij, heq⟩ := exists_tail_sequence_envelope_iInf_eq
      omega θ hbig ui v horder hlim hpos i
    rw [← heq]
    exact (iInf_le _ 0).trans (horder i (j 0) (hij 0))

/-- In the source's genuine global P-order, actual closedness and mixed
mass monotonicity produce all original stage positivity before converting
to the fixed-background identity. -/
theorem iInf_singularityEnvelope_eq_of_sourcePOrder_tendsto_native
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (ui : I → ThetaPshL1 θ.val) (v : ThetaPshL1 θ.val)
    (horder : ∀ i j, i ≤ j → SourcePOrder (n := n) (ui j).val (ui i).val)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace v))
    (hpos : 0 < diagonalPotentialMass θ v.val v.property) :
    (⨅ i, singularityEnvelope θ.val (ui i).val) = singularityEnvelope θ.val v.val := by
  have hstagepos (i : I) : 0 < diagonalPotentialMass θ (ui i).val (ui i).property := by
    have hconst := @tendsto_const_nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
      I (ui i) atTop
    have hclosed := sourcePOrder_of_native_limits omega θ hbig atTop
      ui (fun _ => ui i) v (ui i) hlim hconst
      ((eventually_ge_atTop i).mono fun j hij => horder i j hij)
    have hmass : diagonalPotentialMass θ v.val v.property ≤
        diagonalPotentialMass θ (ui i).val (ui i).property :=
      globalMixedMass_mono_of_sourcePOrder omega
        (fun _ : Fin n => v.property) (fun _ : Fin n => (ui i).property)
        (fun _ => hclosed)
    exact hpos.trans_le hmass
  exact iInf_singularityEnvelope_eq_of_fixedPOrder_tendsto_native omega θ hbig ui v
    (fun i j hij => (sourcePOrder_iff_pOrderWith omega θ (ui j).property (ui i).property
      (hstagepos j) (hstagepos i)).mp (horder i j hij)) hlim hpos

end
end SGPT.Foundations.Analysis.Pending.SingularDecreasingPEnvelopeNets
