import SGPT.Foundations.Analysis.Pending.ActualPositiveModelMixedContinuity

set_option autoImplicit false

/-! # Genuine positive-target native mixed-mass continuity

SGPT PDF0235--0237, Theorem 6.2.1, positive-target sequence case.
Actual native diagonal continuity produces eventual stage positivity;
actual P-models, zero native projection distance, and genuine independent
mixed-mass preservation are internal producers. No target limit is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualPositiveMixedMassNativeContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  DiagonalMass MixedMass ThetaPshL1Topology
  SingularCanonicalSingularityDistance SingularCanonicalSingularityMassLipschitz
  SingularGlobalPEnvelopeBridge SingularCanonicalDistanceZeroPEquivalence
  SingularGlobalPMixedMassEquality ActualPositiveModelMixedContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Genuine independent native sequences with positive target diagonal masses
internally produce their true extended mixed-mass convergence. -/
theorem tendsto_globalMixedMass_of_native_positive
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (θ a)))
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j a, IsThetaPshPotential (θ a).val (u j a))
    (hv : ∀ a, IsThetaPshPotential (θ a).val (v a))
    (hvpos : ∀ a, 0 < diagonalPotentialMass (θ a) (v a) (hv a))
    (hlim : ∀ a, Tendsto
      (fun j => (⟨u j a, hu j a⟩ : ThetaPshL1 (θ a).val)) atTop
      (@nhds (ThetaPshL1 (θ a).val)
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
        ⟨v a, hv a⟩)) :
    Tendsto (fun j => globalMixedMass θ (u j) (fun a => (hu j a).1)) atTop
      (𝓝 (globalMixedMass θ v (fun a => (hv a).1))) := by
  have hevent : ∀ᶠ j in atTop, ∀ a, 0 < diagonalPotentialMass (θ a) (u j a) (hu j a) := by
    apply eventually_all.mpr
    intro a
    let : PseudoMetricSpace (ThetaPshL1 (θ a).val) :=
      singularityPseudoMetricSpace omega (θ a) (hbig a)
    let : UniformSpace (ThetaPshL1 (θ a).val) :=
      (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace
    let : TopologicalSpace (ThetaPshL1 (θ a).val) :=
      (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
    have hp : 0 < (diagonalPotentialMass (θ a) (v a) (hv a)).toReal :=
      ENNReal.toReal_pos_iff.mpr ⟨hvpos a,
        globalMixedMass_lt_top omega (fun _ : Fin n => (hv a).1)⟩
    have hm := (diagonalPotentialMass_uniformContinuous omega (θ a) (hbig a)).continuous.tendsto
      (⟨v a, hv a⟩ : ThetaPshL1 (θ a).val) |>.comp (hlim a)
    filter_upwards [hm.eventually (Ioi_mem_nhds hp)] with j hj
    change 0 < (diagonalPotentialMass (θ a) (u j a) (hu j a)).toReal at hj
    exact (ENNReal.toReal_pos_iff.mp hj).1
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let w : ℕ → Fin n → M → EReal := fun j a => singularityEnvelope (θ a).val (u (j + N) a)
  have hP (j : ℕ) (a : Fin n) : IsThetaPshPotential (θ a).val (w j a) :=
    singularityEnvelope_isThetaPshPotential (θ a).val (θ a).property.1 (θ a).property.2
      (hu (j + N) a).1.hasSmoothLocalPotentials (u (j + N) a) (hu (j + N) a)
  have hmodel (j : ℕ) (a : Fin n) : IsModelPotential (θ a) (w j a) := by
    have hpos := hN (j + N) (Nat.le_add_left N j) a
    exact ⟨hP j a,
      (RooftopEnvelopeIdempotence.singularityEnvelope_idempotent_of_positive_mass
        omega (θ a) (u (j + N) a) (hu (j + N) a) hpos).symm,
      (singularityEnvelopeMassPreserving omega (θ a) (u (j + N) a)
        (hu (j + N) a) (hP j a)).symm ▸ hpos⟩
  have hwlim (a : Fin n) : Tendsto
      (fun j => (⟨w j a, hP j a⟩ : ThetaPshL1 (θ a).val)) atTop
      (@nhds (ThetaPshL1 (θ a).val)
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
        ⟨v a, hv a⟩) := by
    let : PseudoMetricSpace (ThetaPshL1 (θ a).val) :=
      singularityPseudoMetricSpace omega (θ a) (hbig a)
    let : TopologicalSpace (ThetaPshL1 (θ a).val) :=
      (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
    let wT : ℕ → ThetaPshL1 (θ a).val := fun j => ⟨w j a, hP j a⟩
    let uT : ℕ → ThetaPshL1 (θ a).val := fun j => ⟨u (j + N) a, hu (j + N) a⟩
    let vT : ThetaPshL1 (θ a).val := ⟨v a, hv a⟩
    change Tendsto wT atTop (𝓝 vT)
    have hzero (j : ℕ) : dist (wT j) (uT j) = 0 := by
      have he := sourcePEquivalent_singularityEnvelope omega (θ a) (hu (j + N) a)
      have hz := (singularityDistance_eq_zero_iff_sourcePEquivalent omega (θ a) (hbig a)
        (hP j a) (hu (j + N) a)).mpr ⟨he.2, he.1⟩
      rw [dist_eq_singularityDistance_toReal omega (θ a) (hbig a), hz, EReal.toReal_zero]
    have huTl : Tendsto uT atTop (𝓝 vT) :=
      (hlim a).comp (tendsto_add_atTop_nat N)
    have hd := tendsto_iff_dist_tendsto_zero.mp huTl
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hd
    have h := dist_triangle (wT j) (uT j) vT
    simpa only [hzero, zero_add] using h
  have hm := tendsto_globalMixedMass_of_model_native_positive omega hbig hmodel hv hvpos hwlim
  have heq : (fun j => globalMixedMass θ (w j) (fun a => (hP j a).1)) =
      (fun j => globalMixedMass θ (u (j + N)) (fun a => (hu (j + N) a).1)) := by
    funext j
    exact globalMixedMass_eq_of_sourcePEquivalent omega (hP j) (hu (j + N))
      (fun a => let h := sourcePEquivalent_singularityEnvelope omega (θ a) (hu (j + N) a)
        ⟨h.2, h.1⟩)
  change Tendsto (fun j => globalMixedMass θ (w j) (fun a => (hP j a).1)) atTop
    (𝓝 (globalMixedMass θ v (fun a => (hv a).1))) at hm
  rw [heq] at hm
  exact (tendsto_add_atTop_iff_nat N).mp hm

end
end SGPT.Foundations.Analysis.Pending.ActualPositiveMixedMassNativeContinuity
