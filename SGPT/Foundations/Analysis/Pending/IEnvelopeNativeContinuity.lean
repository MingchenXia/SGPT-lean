import SGPT.Foundations.Analysis.Pending.IEnvelopeModelSubsequenceNativeLimit
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

set_option autoImplicit false

/-! # Genuine native I-envelope continuity at every positive-mass potential -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.IEnvelopeNativeContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  ThetaPshL1Topology SingularCanonicalSingularityDistance DiagonalMass MixedMass
  IEnvelopeMonotoneNativeLimits IEnvelopeModelSubsequenceNativeLimit
  SingularGlobalPEnvelopeBridge SingularCanonicalDistanceZeroPEquivalence
  SingularCanonicalSingularityMassLipschitz

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem tendsto_iEnvelope_sequence_of_positive_limit
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (ui : ℕ → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hpos : HasPositivePotentialMass θ u.val u.property)
    (hlim : Tendsto ui atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    Tendsto (fun j => iEnvelopeReader θ (ui j)) atTop
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        (iEnvelopeReader θ u)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let v : ℕ → ThetaPshL1 θ.val := fun j => ui (ns j)
  have hvlim : Tendsto v atTop (𝓝 u) := hlim.comp hns
  let L : ℝ≥0∞ := diagonalPotentialMass θ u.val u.property
  have hLtop : L ≠ ⊤ := (globalMixedMass_lt_top omega
    (fun _ : Fin n => u.property.1)).ne
  have hLpos : 0 < L.toReal := ENNReal.toReal_pos hpos.ne' hLtop
  let δ : ℝ := L.toReal / 2
  have hδ : 0 < δ := half_pos hLpos
  have hδlt : δ < L.toReal := half_lt_self hLpos
  have hmass : Tendsto (fun j => (diagonalPotentialMass θ (v j).val
      (v j).property).toReal) atTop (𝓝 L.toReal) :=
    ((diagonalPotentialMass_uniformContinuous omega θ hbig).continuous.tendsto u).comp hvlim
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.mp hmass).1 δ hδlt)
  have hstage (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (v (j + N)).val (v (j + N)).property :=
    (ENNReal.ofReal_le_iff_le_toReal
      (globalMixedMass_lt_top omega (fun _ : Fin n => (v (j + N)).property.1)).ne).mpr
        (hN (j + N) (Nat.le_add_left N j)).le
  have hmodel (j : ℕ) : IsModelPotential θ
      (singularityEnvelope θ.val (v (j + N)).val) := by
    have hp : HasPositivePotentialMass θ (v (j + N)).val (v (j + N)).property :=
      (ENNReal.ofReal_pos.mpr hδ).trans_le (hstage j)
    have hP := singularityEnvelope_isThetaPshPotential θ.val θ.property.1 θ.property.2
      (v (j + N)).property.1.hasSmoothLocalPotentials (v (j + N)).val (v (j + N)).property
    exact ⟨hP, (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
      omega θ (v (j + N)).val (v (j + N)).property hp).symm,
      (singularityEnvelopeMassPreserving omega θ (v (j + N)).val
        (v (j + N)).property hP).symm ▸ hp⟩
  let w : ℕ → ThetaPshL1 θ.val := fun j =>
    ⟨singularityEnvelope θ.val (v (j + N)).val, (hmodel j).plurisubharmonic⟩
  have hwstage (j : ℕ) : ENNReal.ofReal δ ≤
      diagonalPotentialMass θ (w j).val (w j).property :=
    (hstage j).trans_eq (singularityEnvelopeMassPreserving omega θ
      (v (j + N)).val (v (j + N)).property (w j).property).symm
  have htail : Tendsto (fun j => v (j + N)) atTop (𝓝 u) :=
    hvlim.comp (tendsto_add_atTop_nat N)
  have hzero (j : ℕ) : dist (w j) (v (j + N)) = 0 := by
    have he := sourcePEquivalent_singularityEnvelope omega θ (v (j + N)).property
    have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
      (w j).property (v (j + N)).property).mpr ⟨he.2, he.1⟩
    rw [dist_eq_singularityDistance_toReal omega θ hbig, hz, EReal.toReal_zero]
  have hwlim : Tendsto w atTop (𝓝 u) := tendsto_iff_dist_tendsto_zero.mpr (by
    have hd := tendsto_iff_dist_tendsto_zero.mp htail
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hd
    simpa only [hzero, zero_add] using dist_triangle (w j) (v (j + N)) u)
  obtain ⟨f, _, hf⟩ := exists_strictMono_tendsto_iEnvelope_of_models
    omega θ hbig w u hmodel hδ hwstage hpos hwlim
  have he : (fun j => iEnvelopeReader θ (w (f j))) =
      fun j => iEnvelopeReader θ (ui (ns (f j + N))) := by
    funext j
    apply Subtype.ext
    exact iSingularityEnvelope_singularityEnvelope θ.val θ.property.1 θ.property.2
      (v (f j + N)).property.1.hasSmoothLocalPotentials
      (v (f j + N)).val (v (f j + N)).property
  exact ⟨fun j => f j + N, he ▸ hf⟩

/-- Actual native continuity at every naturally positive-mass potential;
stage positivity and normalized model approximants are internally produced. -/
theorem continuousAt_iEnvelope_of_positive_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (u : ThetaPshL1 θ.val) (hpos : HasPositivePotentialMass θ u.val u.property) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    ContinuousAt (iEnvelopeReader θ) u := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  exact tendsto_nhds_iff_seq_tendsto.mpr fun ui hlim =>
    tendsto_iEnvelope_sequence_of_positive_limit omega θ hbig ui u hpos hlim

/-- Every actual native convergent filter with positive genuine limit has
the true I-envelope native limit; no order, countable cofinality or model inputs. -/
theorem tendsto_iEnvelope_of_tendsto_positive_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} (F : Filter I) (ui : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hpos : HasPositivePotentialMass θ u.val u.property)
    (hlim : Tendsto ui F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u)) :
    Tendsto (fun i => iEnvelopeReader θ (ui i)) F
      (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        (iEnvelopeReader θ u)) := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  exact (continuousAt_iEnvelope_of_positive_mass omega θ hbig u hpos).tendsto.comp hlim

end
end SGPT.Foundations.Analysis.Pending.IEnvelopeNativeContinuity
