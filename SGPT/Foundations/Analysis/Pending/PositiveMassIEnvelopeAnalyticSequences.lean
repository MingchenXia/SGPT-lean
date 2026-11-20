import SGPT.Foundations.Analysis.Pending.IEnvelopeOrderedConvexNativeLimit
import SGPT.Foundations.Analysis.Pending.PositiveMassCurrentBelow
import SGPT.Foundations.Analysis.Pending.CalibratedQuasiEquisingularApproximation
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.SingularGlobalPEnvelopeBridge
import Mathlib.Topology.Sequences

set_option autoImplicit false

/-! # Genuine original-background analytic sequences from actual positive mass -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.PositiveMassIEnvelopeAnalyticSequences

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation DiagonalMass
  ThetaPshConvexCombination ThetaPshL1Topology SingularCanonicalSingularityDistance
  PositiveMassCurrentBelow IEnvelopeOrderedConvexNativeLimit
  CalibratedQuasiEquisingularApproximation SingularGlobalPEnvelopeBridge
  SingularCanonicalDistanceZeroPEquivalence SingularGlobalPOrder

noncomputable section

/-- Sequential extraction from two genuinely produced levels of approximation. -/
private theorem exists_seq_of_approximated_limit {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (B : ℕ → X) (b : X) (hlim : Tendsto B atTop (𝓝 b))
    (hB : ∀ j, ∃ A : ℕ → X, (∀ k, A k ∈ S) ∧ Tendsto A atTop (𝓝 (B j))) :
    ∃ A : ℕ → X, (∀ k, A k ∈ S) ∧ Tendsto A atTop (𝓝 b) := by
  have hclosure (j : ℕ) : B j ∈ closure S := by
    obtain ⟨A, hA, hlimA⟩ := hB j
    exact mem_closure_of_tendsto hlimA (Eventually.of_forall hA)
  exact mem_closure_iff_seq_limit.mp
    (isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall hclosure))

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Positive original mass internally produces a genuine analytic sequence
in the original background converging natively to the actual I-envelope. -/
theorem exists_analytic_sequence_native_iEnvelope_of_positive_mass
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    ∃ (hI : IsThetaPshPotential θ.val (iSingularityEnvelope θ.val u))
      (A : ℕ → ThetaPshL1 θ.val),
      (∀ j, HasManifoldAnalyticSingularityType (n := n) (A j).val) ∧
      Tendsto A atTop (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        ⟨iSingularityEnvelope θ.val u, hI⟩) := by
  obtain ⟨δ, hδ, p, hpSmall, hpu⟩ :=
    exists_strict_thetaPsh_potential_le omega θ hbig hu hpos
  have hp : IsThetaPshPotential θ.val p := by
    have hh := LocalPotentials.isThetaPshPotential_add_of_semipositive hpSmall
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hδ.le)
    simpa only [sub_add_cancel] using hh
  let t : ℕ → Ioo (0 : ℝ) 1 := fun j => ⟨1 / ((j : ℝ) + 2), by
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by linarith)⟩
  have ht : Tendsto (fun j => (t j).val) atTop (𝓝 (0 : ℝ)) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, t, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using hh
  have hstrict (j : ℕ) : IsThetaPshPotential
      (θ - ((t j).val * δ) • omega.form).val (convexComb (1 - (t j).val) u p) := by
    have huZero : IsThetaPshPotential (θ - (0 : ℝ) • omega.form).val u := by
      simpa only [zero_smul, sub_zero] using hu
    have hh := AmbientConvexCurrent.isThetaPshPotential_convexComb_sub_smul
      omega (sub_pos.mpr (t j).property.2) (by linarith [(t j).property.1])
      huZero hpSmall
    simpa only [mul_zero, zero_add, sub_sub_cancel] using hh
  obtain ⟨hB, hI, hlim⟩ :=
    tendsto_native_iEnvelope_ordered_convex omega θ hbig hu hp hpu atTop t ht
  let S : Set (ThetaPshL1 θ.val) :=
    {v | HasManifoldAnalyticSingularityType (n := n) v.val}
  let B : ℕ → ThetaPshL1 θ.val := fun j =>
    ⟨iSingularityEnvelope θ.val (convexComb (1 - (t j).val) u p), hB j⟩
  let P : ThetaPshL1 θ.val := ⟨iSingularityEnvelope θ.val u, hI⟩
  have hlimB : Tendsto B atTop (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace P) := hlim
  obtain ⟨A, hA, hlimA⟩ := @exists_seq_of_approximated_limit (ThetaPshL1 θ.val)
    (singularityPseudoMetricSpace omega θ hbig) S B P hlimB (by
      intro j
      obtain ⟨_, ε, U, happ, _, hU, hIj, _, hlimj⟩ :=
        exists_iEnvelope_native_analytic_approximation_of_current_margin
          omega θ (mul_pos (t j).property.1 hδ) (hstrict j)
      exact ⟨fun k => ⟨U k, hU k⟩, happ.term_hasAnalyticSingularityType, hlimj⟩)
  exact ⟨hI, A, hA, hlimA⟩

/-- Relative I-goodness internally identifies the original potential with
its I-envelope in the actual native pseudometric topology, so the same
produced analytic sequence converges to the original potential. -/
theorem exists_analytic_sequence_native_of_iGoodWith
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hgood : IGoodWith θ u hu) :
    ∃ A : ℕ → ThetaPshL1 θ.val,
      (∀ j, HasManifoldAnalyticSingularityType (n := n) (A j).val) ∧
      Tendsto A atTop (@nhds (ThetaPshL1 θ.val)
        (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
        ⟨u, hu⟩) := by
  obtain ⟨hI, A, hA, hlim⟩ :=
    exists_analytic_sequence_native_iEnvelope_of_positive_mass omega θ hbig hu hgood.positiveMass
  have heq : SourcePEquivalent (n := n) u (iSingularityEnvelope θ.val u) := by
    simpa only [hgood.envelope_eq] using sourcePEquivalent_singularityEnvelope omega θ hu
  have hzero : singularityDistance omega θ hbig u (iSingularityEnvelope θ.val u) = 0 :=
    (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig hu hI).mpr heq
  let U : ThetaPshL1 θ.val := ⟨u, hu⟩
  let P : ThetaPshL1 θ.val := ⟨iSingularityEnvelope θ.val u, hI⟩
  let native := singularityPseudoMetricSpace omega θ hbig
  have hdist : @dist (ThetaPshL1 θ.val) native.toDist U P = 0 := by
    simpa only [U, P, hzero, EReal.toReal_zero] using
      dist_eq_singularityDistance_toReal omega θ hbig U P
  have hnhds := (@Metric.inseparable_iff (ThetaPshL1 θ.val) native U P).mpr hdist
  change @nhds (ThetaPshL1 θ.val) native.toUniformSpace.toTopologicalSpace U =
    @nhds (ThetaPshL1 θ.val) native.toUniformSpace.toTopologicalSpace P at hnhds
  exact ⟨A, hA, hnhds.symm ▸ hlim⟩

end

end SGPT.Foundations.Analysis.Pending.PositiveMassIEnvelopeAnalyticSequences
