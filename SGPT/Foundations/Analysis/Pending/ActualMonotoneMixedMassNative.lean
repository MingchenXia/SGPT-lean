import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityIncreasing
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityDecreasingModels
import SGPT.Foundations.Analysis.Pending.SingularCanonicalSingularityMassLipschitz
import SGPT.Foundations.Analysis.Pending.SingularCanonicalDistanceZeroPEquivalence
import SGPT.Foundations.Analysis.Pending.SingularGlobalPMixedMassEquality

set_option autoImplicit false

/-! # Actual monotone independent mixed masses at native singularity limits

SGPT PDF0235--0237, monotone part of Theorem 6.2.1. True increasing
regularized-supremum and contact-first decreasing-infimum producers
are identified with native targets through actual global P-equivalence.
Full nonmonotone mixed-mass continuity remains a subsequent consumer.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMonotoneMixedMassNative

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
  GlobalNonPluripolar MixedMass DiagonalMass IncreasingMixedDirectedNets
  SingularMinimalCanonicalRay SingularCanonicalSingularityIncreasing
  SingularCanonicalSingularityDecreasingModels SingularCanonicalSingularityMassLipschitz
  SingularCanonicalSingularityDistance SingularCanonicalDistanceZeroPEquivalence
  SingularGlobalPOrder SingularGlobalPMixedMassEquality ThetaPshL1Topology
  ActualDecreasingModelInfimum ActualDecreasingModelPositiveInfimum

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

private theorem sourcePEquivalent_of_two_native_limits
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    {I : Type*} {F : Filter I} [F.NeBot]
    (w : I → ThetaPshL1 θ.val) (u v : ThetaPshL1 θ.val) :
    letI := singularityPseudoMetricSpace omega θ hbig
    letI : TopologicalSpace (ThetaPshL1 θ.val) :=
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
    Tendsto w F (𝓝 u) → Tendsto w F (𝓝 v) →
      SourcePEquivalent (n := n) u.val v.val := by
  let := singularityPseudoMetricSpace omega θ hbig
  let : TopologicalSpace (ThetaPshL1 θ.val) :=
    (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace
  intro hu hv
  have hz : dist u v = 0 := tendsto_nhds_unique
    (hu.dist tendsto_const_nhds) (tendsto_iff_dist_tendsto_zero.mp hv)
  obtain ⟨m, _, _, _, hm⟩ := exists_tendsto_singularityDistance omega θ hbig
    u.property v.property
  have hm0 : m = 0 := by
    simpa only [dist_eq_singularityDistance_toReal omega θ hbig, hm,
      EReal.toReal_coe] using hz
  apply (singularityDistance_eq_zero_iff_sourcePEquivalent omega θ hbig
    u.property v.property).mp
  rw [hm, hm0, EReal.coe_zero]

/-- A genuine directed increasing tuple and its actual native target
internally produce the true extended independent mixed-mass limit. -/
theorem tendsto_globalMixedMass_of_monotone_native
    (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (θ a)))
    {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {u : I → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j a, IsThetaPshPotential (θ a).val (u j a))
    (hv : ∀ a, IsThetaPshPotential (θ a).val (v a))
    (hmono : ∀ a, Monotone fun j => u j a)
    {C : Fin n → ℝ} (hC : ∀ a j x, u j a x ≤ (C a : EReal))
    (hlim : ∀ a, Tendsto
      (fun j => (⟨u j a, hu j a⟩ : ThetaPshL1 (θ a).val)) atTop
      (@nhds (ThetaPshL1 (θ a).val)
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
        ⟨v a, hv a⟩)) :
    Tendsto (fun j => globalMixedMass θ (u j) (fun a => (hu j a).1)) atTop
      (𝓝 (globalMixedMass θ v (fun a => (hv a).1))) := by
  let S : Fin n → M → EReal := fun a => uscRegularization (⨆ j, u j a)
  have hS : ∀ a, IsThetaPshPotential (θ a).val (S a) := fun a =>
    isThetaPshPotential_regularized_of_uniformlyBounded (fun j => hu j a) (hC a)
  have hP : ∀ a, SourcePEquivalent (n := n) (S a) (v a) := by
    intro a
    exact sourcePEquivalent_of_two_native_limits omega (θ a) (hbig a)
      (fun j => ⟨u j a, hu j a⟩) ⟨S a, hS a⟩ ⟨v a, hv a⟩
      (tendsto_native_of_monotone_uniformlyBounded omega (θ a) (hbig a)
        (fun j => ⟨u j a, hu j a⟩) (hmono a) (hC a)) (hlim a)
  have hm : globalMixedMass θ S (fun a => (hS a).1) =
      globalMixedMass θ v (fun a => (hv a).1) :=
    globalMixedMass_eq_of_sourcePEquivalent omega hS hv hP
  have hr : Tendsto (fun j => (globalMixedMass θ (u j) (fun a => (hu j a).1)).toReal)
      atTop (𝓝 (globalMixedMass θ S (fun a => (hS a).1)).toReal) :=
    tendsto_mixed_mass_of_directed_monotone_uniformlyBounded omega hu hmono hC
  have he := ENNReal.continuous_ofReal.tendsto
    (globalMixedMass θ S (fun a => (hS a).1)).toReal |>.comp hr
  simpa only [Function.comp_def,
    ENNReal.ofReal_toReal (globalMixedMass_lt_top omega (fun a => (hu _ a).1)).ne,
    ENNReal.ofReal_toReal (globalMixedMass_lt_top omega (fun a => (hS a).1)).ne, hm,
    ENNReal.ofReal_toReal (globalMixedMass_lt_top omega (fun a => (hv a).1)).ne] using he

/-- Positive native target masses internally supply uniform stage bounds,
so decreasing actual model tuples have the true full mixed-mass limit. -/
theorem tendsto_globalMixedMass_of_antitone_model_native
    (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M}
    (hbig : ∀ a, IsBigClass (RealBottChern.ofRepresentative (θ a)))
    {u : ℕ → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ j a, IsModelPotential (θ a) (u j a))
    (hv : ∀ a, IsThetaPshPotential (θ a).val (v a))
    (hanti : ∀ a, Antitone fun j => u j a)
    (hvpos : ∀ a, 0 < diagonalPotentialMass (θ a) (v a) (hv a))
    (hlim : ∀ a, Tendsto
      (fun j => (⟨u j a, (hu j a).plurisubharmonic⟩ : ThetaPshL1 (θ a).val)) atTop
      (@nhds (ThetaPshL1 (θ a).val)
        (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
        ⟨v a, hv a⟩)) :
    Tendsto (fun j => globalMixedMass θ (u j)
      (fun a => (hu j a).plurisubharmonic.1)) atTop
      (𝓝 (globalMixedMass θ v (fun a => (hv a).1))) := by
  let δ : Fin n → ℝ := fun a => (diagonalPotentialMass (θ a) (v a) (hv a)).toReal
  have hvfinite (a : Fin n) : diagonalPotentialMass (θ a) (v a) (hv a) < ⊤ :=
    globalMixedMass_lt_top omega (fun _ : Fin n => (hv a).1)
  have hδ (a : Fin n) : 0 < δ a :=
    ENNReal.toReal_pos_iff.mpr ⟨hvpos a, hvfinite a⟩
  have hbound (j : ℕ) (a : Fin n) : ENNReal.ofReal (δ a) ≤
      diagonalPotentialMass (θ a) (u j a) (hu j a).plurisubharmonic := by
    let := singularityPseudoMetricSpace omega (θ a) (hbig a)
    let : UniformSpace (ThetaPshL1 (θ a).val) :=
      (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace
    let : TopologicalSpace (ThetaPshL1 (θ a).val) :=
      (singularityPseudoMetricSpace omega (θ a) (hbig a)).toUniformSpace.toTopologicalSpace
    have hc : Continuous (fun q : ThetaPshL1 (θ a).val =>
        (diagonalPotentialMass (θ a) q.val q.property).toReal) :=
      (diagonalPotentialMass_uniformContinuous omega (θ a) (hbig a)).continuous
    have ht := hc.tendsto (⟨v a, hv a⟩ : ThetaPshL1 (θ a).val)
    have hm := ht.comp (hlim a)
    have hmassAnti : Antitone fun k =>
        (diagonalPotentialMass (θ a) (u k a) (hu k a).plurisubharmonic).toReal := by
      intro k l hkl
      apply ENNReal.toReal_mono
        (globalMixedMass_lt_top omega (fun _ : Fin n => (hu k a).plurisubharmonic.1)).ne
      exact diagonalPotentialMass_mono_of_kahler omega (hu l a).plurisubharmonic
        (hu k a).plurisubharmonic
        (MoreSingularOn.of_le fun x _ => hanti a hkl x)
    have hle := hmassAnti.le_of_tendsto hm j
    have he := (ENNReal.toReal_le_toReal (hvfinite a).ne
      (globalMixedMass_lt_top omega (fun _ : Fin n => (hu j a).plurisubharmonic.1)).ne).mp hle
    change diagonalPotentialMass (θ a) (v a) (hv a) ≤
      diagonalPotentialMass (θ a) (u j a) (hu j a).plurisubharmonic at he
    simpa only [δ, ENNReal.ofReal_toReal (hvfinite a).ne] using he
  let S : Fin n → M → EReal := fun a => ⨅ j, u j a
  have hS (a : Fin n) : IsThetaPshPotential (θ a).val (S a) :=
    isThetaPshPotential_iInf_of_antitone_model (fun j => hu j a) (hanti a)
  have hP : ∀ a, SourcePEquivalent (n := n) (S a) (v a) := by
    intro a
    exact sourcePEquivalent_of_two_native_limits omega (θ a) (hbig a)
      (fun j => ⟨u j a, (hu j a).plurisubharmonic⟩) ⟨S a, hS a⟩ ⟨v a, hv a⟩
      (tendsto_native_iInf_of_uniform_positive_stage_mass omega (θ a) (hbig a)
        (fun j => ⟨u j a, (hu j a).plurisubharmonic⟩) (fun j => hu j a) (hanti a)
        (hδ a) (fun j => hbound j a)) (hlim a)
  have hm : globalMixedMass θ S (fun a => (hS a).1) =
      globalMixedMass θ v (fun a => (hv a).1) :=
    globalMixedMass_eq_of_sourcePEquivalent omega hS hv hP
  have ht := tendsto_globalMixedMass_iInf_of_uniform_positive_stage_mass
    omega hu hanti hδ hbound
  change Tendsto (fun j => globalMixedMass θ (u j)
    (fun a => (hu j a).plurisubharmonic.1)) atTop
    (𝓝 (globalMixedMass θ S (fun a => (hS a).1))) at ht
  simpa only [hm] using ht

end

end SGPT.Foundations.Analysis.Pending.ActualMonotoneMixedMassNative
