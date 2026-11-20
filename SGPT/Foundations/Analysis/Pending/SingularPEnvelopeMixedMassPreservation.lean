import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof
import SGPT.Foundations.Analysis.Pending.IncreasingMixedRegularizedContinuity
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim

set_option autoImplicit false

/-! # Actual independent mixed mass preservation by slotwise P-envelopes -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.SingularPEnvelopeMixedMassPreservation

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar MixedMass
  IncreasingMixedRegularizedContinuity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual truncated envelopes, internally produced regularized-limit witnesses and genuine independent mixed weak continuity give the full mixed-slot mass preservation statement, with no positive original mass or idempotence assumption. -/
theorem globalMixedMass_singularityEnvelope_eq (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) :
    globalMixedMass θ (fun i => singularityEnvelope (θ i).val (u i))
      (fun i => (singularityEnvelope_isThetaPshPotential (θ i).val (θ i).property.1
        (θ i).property.2 (hu i).1.hasSmoothLocalPotentials (u i) (hu i)).1) =
      globalMixedMass θ u (fun i => (hu i).1) := by
  classical
  choose C hC using fun i => (hu i).exists_normalized_sub_const
  let v : ℕ → Fin n → M → EReal := fun j i =>
    truncatedSingularityEnvelope (θ i).val (u i) (-C i + j)
  have hlevel (i : Fin n) (j : ℕ) : -C i ≤ -C i + j :=
    le_add_of_nonneg_right j.cast_nonneg
  have hv : ∀ j i, IsThetaPshPotential (θ i).val (v j i) := fun j i =>
    truncatedSingularityEnvelope_isThetaPshPotential (hu i).1.hasSmoothLocalPotentials
      ⟨_, sub_const_mem_truncatedSingularityCompetitors (hC i) (hlevel i j)⟩
  have hm : ∀ i, Monotone fun j => v j i := fun i j k hjk =>
    truncatedSingularityEnvelope_mono _ _
      (add_le_add le_rfl (by exact_mod_cast hjk : (j : ℝ) ≤ k))
  have heq (i : Fin n) : singularityEnvelope (θ i).val (u i) =
      uscRegularization (⨆ j, v j i) :=
    singularityEnvelope_eq_uscRegularization_iSup_truncated (θ i).val (u i) (-C i)
  have hP : ∀ i, IsThetaPshPotential (θ i).val (singularityEnvelope (θ i).val (u i)) :=
    fun i => singularityEnvelope_isThetaPshPotential (θ i).val (θ i).property.1
      (θ i).property.2 (hu i).1.hasSmoothLocalPotentials (u i) (hu i)
  have hreg : ∀ i, IsThetaPshPotential (θ i).val (uscRegularization (⨆ j, v j i)) :=
    fun i => heq i ▸ hP i
  have hstage (j : ℕ) : globalMixedMass θ (v j) (fun i => (hv j i).1) =
      globalMixedMass θ u (fun i => (hu i).1) :=
    FiniteGeodesicsFullMassAnyDim.globalMixedMass_eq_of_sameSingularityType omega
      (hv j) hu (fun i =>
        (sameSingularityTypeOn_truncatedSingularityEnvelope (hu i) (hC i) (hlevel i j)).symm)
  have ht := tendsto_integral_mixed_of_monotone_regularized omega hv hm hreg (1 : C(M, ℝ))
  have ht' : Tendsto
      (fun j => (globalMixedMass θ (v j) (fun i => (hv j i).1)).toReal) atTop
      (𝓝 ((globalMixedMass θ (fun i => singularityEnvelope (θ i).val (u i))
        (fun i => (hP i).1)).toReal)) := by
    simpa only [← heq, ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one,
      globalMixedMass, Measure.real_def] using ht
  have hreal : (globalMixedMass θ (fun i => singularityEnvelope (θ i).val (u i))
      (fun i => (hP i).1)).toReal = (globalMixedMass θ u (fun i => (hu i).1)).toReal := by
    simp only [hstage] at ht'
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  exact (ENNReal.toReal_eq_toReal_iff'
    (globalMixedMass_lt_top omega (fun i => (hP i).1)).ne
    (globalMixedMass_lt_top omega (fun i => (hu i).1)).ne).mp hreal

end

end SGPT.Foundations.Analysis.Pending.SingularPEnvelopeMixedMassPreservation
