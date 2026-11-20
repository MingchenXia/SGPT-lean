import SGPT.Envelopes.SourceNonPluripolarMassOrder
import SGPT.Foundations.Analysis.Pending.IncreasingMixedDirectedNets

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual source mixed product, with its finite witness manufactured. -/
def sourceFiniteMixedNonPluripolarMeasure (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ a, (ofFixedModel n M).IsThetaPSH (θ a) (u a)) : FiniteMeasure M :=
  ⟨sourceMixedNonPluripolarMeasure θ u hu, ⟨sourceMixedNonPluripolarMass_lt_top ω θ u hu⟩⟩

/-- Packaging the actual source product does not change its underlying measure. -/
theorem sourceFiniteMixedNonPluripolarMeasure_coe (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ a, (ofFixedModel n M).IsThetaPSH (θ a) (u a)) :
    (sourceFiniteMixedNonPluripolarMeasure ω θ u hu : Measure M) =
      sourceMixedNonPluripolarMeasure θ u hu := rfl

/-- The native finite mixed product has exactly the same forms, functions and measure. -/
theorem sourceFiniteMixedNonPluripolarMeasure_eq_native (ω : KahlerBackground n M)
    (θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)) (u : Fin n → M → EReal)
    (hu : ∀ a, (ofFixedModel n M).IsThetaPSH (θ a) (u a)) :
    sourceFiniteMixedNonPluripolarMeasure ω θ u hu =
      IncreasingMixedContinuity.finiteMixedMeasure ω (fun a => atlasClosedFormToNative (θ a)) u
        (fun a => (isThetaPSH_iff_nativeThetaPotential (θ a) (u a)).mp (hu a)) := rfl

variable {I : Type*} [Nonempty I]
  {θ : Fin n → AtlasClosedRealOneOneForm (ofFixedModel n M)} {u : I → Fin n → M → EReal}

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- Original common finite upper bounds internally produce the genuine WHOLE USC suprema. -/
theorem sourceIncreasingMixed_regularized_thetaPSH
    (hu : ∀ i a, (ofFixedModel n M).IsThetaPSH (θ a) (u i a))
    {C : Fin n → ℝ} (hC : ∀ a i x, u i a x ≤ (C a : EReal)) (a : Fin n) :
    (ofFixedModel n M).IsThetaPSH (θ a) (uscRegularization (⨆ i, u i a)) :=
  (isThetaPSH_iff_nativeThetaPotential (θ a) _).mpr
    (IncreasingMixedDirectedNets.isThetaPshPotential_regularized_of_uniformlyBounded
      (fun i => (isThetaPSH_iff_nativeThetaPotential (θ a) (u i a)).mp (hu i a)) (hC a))

variable [Preorder I] [IsDirectedOrder I]

/-- The actual independent mixed products converge along the WHOLE directed net,
with every limit potential manufactured from the original uniform bounds. -/
theorem sourceIncreasingMixed_weakTendsto (ω : KahlerBackground n M)
    (hu : ∀ i a, (ofFixedModel n M).IsThetaPSH (θ a) (u i a))
    (hm : ∀ a, Monotone (fun i => u i a))
    {C : Fin n → ℝ} (hC : ∀ a i x, u i a x ≤ (C a : EReal)) :
    Tendsto (fun i => sourceFiniteMixedNonPluripolarMeasure ω θ (u i) (hu i)) atTop
      (𝓝 (sourceFiniteMixedNonPluripolarMeasure ω θ
        (fun a => uscRegularization (⨆ i, u i a))
        (sourceIncreasingMixed_regularized_thetaPSH hu hC))) :=
  IncreasingMixedDirectedNets.weakTendsto_mixed_of_directed_monotone_uniformlyBounded ω
    (fun i a => (isThetaPSH_iff_nativeThetaPotential (θ a) (u i a)).mp (hu i a)) hm hC

/-- Every continuous real test integral converges against the same actual source products. -/
theorem sourceIncreasingMixed_integral_tendsto (ω : KahlerBackground n M)
    (hu : ∀ i a, (ofFixedModel n M).IsThetaPSH (θ a) (u i a))
    (hm : ∀ a, Monotone (fun i => u i a))
    {C : Fin n → ℝ} (hC : ∀ a i x, u i a x ≤ (C a : EReal)) (χ : C(M, ℝ)) :
    Tendsto (fun i => ∫ x, χ x ∂sourceMixedNonPluripolarMeasure θ (u i) (hu i)) atTop
      (𝓝 (∫ x, χ x ∂sourceMixedNonPluripolarMeasure θ
        (fun a => uscRegularization (⨆ i, u i a))
        (sourceIncreasingMixed_regularized_thetaPSH hu hC))) :=
  (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
    (sourceIncreasingMixed_weakTendsto ω hu hm hC))
    (BoundedContinuousFunction.mkOfCompact χ)

/-- The whole original mass limit as actual extended nonnegative masses. -/
theorem sourceIncreasingMixed_mass_tendsto (ω : KahlerBackground n M)
    (hu : ∀ i a, (ofFixedModel n M).IsThetaPSH (θ a) (u i a))
    (hm : ∀ a, Monotone (fun i => u i a))
    {C : Fin n → ℝ} (hC : ∀ a i x, u i a x ≤ (C a : EReal)) :
    Tendsto (fun i => sourceMixedNonPluripolarMass θ (u i) (hu i)) atTop
      (𝓝 (sourceMixedNonPluripolarMass θ
        (fun a => uscRegularization (⨆ i, u i a))
        (sourceIncreasingMixed_regularized_thetaPSH hu hC))) := by
  have h := ENNReal.continuous_coe.continuousAt.tendsto.comp
    (sourceIncreasingMixed_weakTendsto ω hu hm hC).mass
  simpa only [Function.comp_def, FiniteMeasure.ennreal_mass, sourceFiniteMixedNonPluripolarMeasure_coe,
    sourceMixedNonPluripolarMass] using h

/-- The same whole original limit as finite real masses, using the existing mass reader. -/
theorem sourceIncreasingMixed_mass_real_tendsto (ω : KahlerBackground n M)
    (hu : ∀ i a, (ofFixedModel n M).IsThetaPSH (θ a) (u i a))
    (hm : ∀ a, Monotone (fun i => u i a))
    {C : Fin n → ℝ} (hC : ∀ a i x, u i a x ≤ (C a : EReal)) :
    Tendsto (fun i => (sourceMixedNonPluripolarMass θ (u i) (hu i)).toReal) atTop
      (𝓝 (sourceMixedNonPluripolarMass θ
        (fun a => uscRegularization (⨆ i, u i a))
        (sourceIncreasingMixed_regularized_thetaPSH hu hC)).toReal) := by
  have h := NNReal.continuous_coe.continuousAt.tendsto.comp
    (sourceIncreasingMixed_weakTendsto ω hu hm hC).mass
  simpa only [Function.comp_def, ← ENNReal.coe_toReal, FiniteMeasure.ennreal_mass,
    sourceFiniteMixedNonPluripolarMeasure_coe, sourceMixedNonPluripolarMass] using h

omit [Nonempty I] [Preorder I] [IsDirectedOrder I] in
/-- The source's second whole clause: actual independent mixed SEQUENCE weak convergence. -/
theorem sourceIncreasingMixed_sequence_weakTendsto (ω : KahlerBackground n M)
    {u : ℕ → Fin n → M → EReal}
    (hu : ∀ i a, (ofFixedModel n M).IsThetaPSH (θ a) (u i a))
    (hm : ∀ a, Monotone (fun i => u i a))
    {C : Fin n → ℝ} (hC : ∀ a i x, u i a x ≤ (C a : EReal)) :
    Tendsto (fun i => sourceFiniteMixedNonPluripolarMeasure ω θ (u i) (hu i)) atTop
      (𝓝 (sourceFiniteMixedNonPluripolarMeasure ω θ
        (fun a => uscRegularization (⨆ i, u i a))
        (sourceIncreasingMixed_regularized_thetaPSH hu hC))) :=
  sourceIncreasingMixed_weakTendsto ω hu hm hC

end SGPT.PSH.VariableComplexAtlas
