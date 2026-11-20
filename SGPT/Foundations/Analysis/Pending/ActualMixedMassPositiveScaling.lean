import SGPT.Foundations.Analysis.Pending.MixedMassProductCalculus
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false

/-! # Actual independent positive homogeneity

The singleton-support specialization of the actual mixed polynomial
calculus. Common positive scaling supplies the mass identity used in
SGPT PDF0240, Lemma 6.2.6. No singularity-distance scaling is asserted.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMixedMassPositiveScaling

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar MixedMass
  GlobalMultilinearExpansion MixedMassProductCalculus

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Equality of actual measures under independent positive slot scalings. -/
theorem globalMixedMeasure_positive_smul
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    {c : Fin n → ℝ} (hc : ∀ i, 0 < c i) :
    globalMixedMeasure (fun i => c i • θ i)
      (fun i x => (c i : EReal) * u i x)
      (fun i => (RestrictedApproximantComparison.isThetaPshPotential_smul
        (hu i) (hc i)).1) =
    ENNReal.ofReal (∏ i, c i) • globalMixedMeasure θ u (fun i => (hu i).1) := by
  classical
  have h := globalMixedMeasure_sumPot_slots (T := fun i : Fin n => {i})
    (fun i => Finset.singleton_nonempty i) (w := fun i _ => c i)
    (fun i _ => hc i) (fun i => (hu i).1) (fun i => (hu i).quasiPshPotential)
  have hpi : Fintype.piFinset (fun i : Fin n => ({i} : Finset (Fin n))) =
      {fun i : Fin n => i} := Fintype.piFinset_singleton _
  rw [hpi, Finset.sum_singleton] at h
  simpa only [sumForm_singleton, sumPot_singleton] using h

/-- Extended total-mass homogeneity, before any real-valued conversion. -/
theorem globalMixedMass_positive_smul
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    {c : Fin n → ℝ} (hc : ∀ i, 0 < c i) :
    globalMixedMass (fun i => c i • θ i)
      (fun i x => (c i : EReal) * u i x)
      (fun i => (RestrictedApproximantComparison.isThetaPshPotential_smul
        (hu i) (hc i)).1) =
    ENNReal.ofReal (∏ i, c i) * globalMixedMass θ u (fun i => (hu i).1) := by
  have h := congrArg (fun μ : Measure M => μ univ) (globalMixedMeasure_positive_smul hu hc)
  simpa only [globalMixedMass, Measure.smul_apply, smul_eq_mul] using h

end

end SGPT.Foundations.Analysis.Pending.ActualMixedMassPositiveScaling
