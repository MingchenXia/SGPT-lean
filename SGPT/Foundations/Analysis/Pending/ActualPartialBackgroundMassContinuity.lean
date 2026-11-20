import SGPT.Foundations.Analysis.Pending.ActualPartialBackgroundMassPolynomial
import SGPT.Foundations.Analysis.Pending.ActualNativeMixedMassContinuity
import SGPT.Foundations.Analysis.Pending.PluripolarCapacityDichotomy

set_option autoImplicit false

/-! # Actual original-native mixed-mass limits after selected smooth enlargement

SGPT PDF0238 Corollary 6.2.9. Genuine original and constant smooth slots
produce all coefficient limits before actual background evaluations.
-/

open Set Filter MeasureTheory Polynomial
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualPartialBackgroundMassContinuity

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus MixedMass
  GlobalNonPluripolar MixedMassBoundedDifference KahlerDomination
  SingularCanonicalSingularityDistance ThetaPshL1Topology
  ActualPartialBackgroundMassPolynomial ActualNativeMixedMassContinuity
  PluripolarCapacityDichotomy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual original-native limits, together with the constant genuine smooth
slots, produce actual mixed-mass limits after selected nonnegative enlargement. -/
theorem tendsto_globalMixedMass_partial_background_of_native
    (omega : KahlerBackground n M) {θ : Fin n → ClosedRealOneOneForm n M}
    (hbig : ∀ k, IsBigClass (RealBottChern.ofRepresentative (θ k)))
    {I : Type*} (F : Filter I) {u : I → Fin n → M → EReal} {v : Fin n → M → EReal}
    (hu : ∀ i k, IsThetaPshPotential (θ k).val (u i k))
    (hv : ∀ k, IsThetaPshPotential (θ k).val (v k))
    (hlim : ∀ k, Tendsto (fun i => (⟨u i k, hu i k⟩ : ThetaPshL1 (θ k).val)) F
      (@nhds (ThetaPshL1 (θ k).val)
        (singularityPseudoMetricSpace omega (θ k) (hbig k)).toUniformSpace.toTopologicalSpace
        ⟨v k, hv k⟩)) (S : Finset (Fin n)) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun i => globalMixedMass
      (fun k => θ k + (if k ∈ S then a else 0) • omega.form) (u i)
      (fun k => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hu i k)
        (isSemipositive_smul omega.isSemipositive (by split_ifs <;> first | exact ha | exact le_rfl))).1)) F
      (𝓝 (globalMixedMass (fun k => θ k + (if k ∈ S then a else 0) • omega.form) v
        (fun k => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hv k)
          (isSemipositive_smul omega.isSemipositive (by split_ifs <;> first | exact ha | exact le_rfl))).1))) := by
  classical
  have hbg (o : Option (Fin n)) : IsBigClass (RealBottChern.ofRepresentative (optForm omega θ o)) := by
    cases o with
    | none => exact isBigClass_kahler omega
    | some k => exact hbig k
  have hU (i : I) (o : Option (Fin n)) :
      IsThetaPshPotential (optForm omega θ o).val (optPot (u i) o) := by
    cases o with
    | none => exact isThetaPshPotential_zero omega
    | some k => exact hu i k
  have hV (o : Option (Fin n)) :
      IsThetaPshPotential (optForm omega θ o).val (optPot v o) := by
    cases o with
    | none => exact isThetaPshPotential_zero omega
    | some k => exact hv k
  have hopt (o : Option (Fin n)) : Tendsto
      (fun i => (⟨optPot (u i) o, hU i o⟩ : ThetaPshL1 (optForm omega θ o).val)) F
      (@nhds (ThetaPshL1 (optForm omega θ o).val)
        (singularityPseudoMetricSpace omega (optForm omega θ o) (hbg o)).toUniformSpace.toTopologicalSpace
        ⟨optPot v o, hV o⟩) := by
    cases o with
    | none =>
      let := singularityPseudoMetricSpace omega omega.form (isBigClass_kahler omega)
      let : TopologicalSpace (ThetaPshL1 omega.form.val) :=
        (singularityPseudoMetricSpace omega omega.form
          (isBigClass_kahler omega)).toUniformSpace.toTopologicalSpace
      let z : ThetaPshL1 omega.form.val := ⟨fun _ => 0, isThetaPshPotential_zero omega⟩
      change Tendsto (fun _ : I => z) F
        (@nhds (ThetaPshL1 omega.form.val)
          (singularityPseudoMetricSpace omega omega.form
            (isBigClass_kahler omega)).toUniformSpace.toTopologicalSpace z)
      exact tendsto_const_nhds
    | some k => exact hlim k
  have hg (g : Fin n → Option (Fin n)) : Tendsto
      (fun i => (globalMixedMass (fun k => optForm omega θ (g k))
        (fun k => optPot (u i) (g k)) (fun k => (hU i (g k)).1)).toReal) F
      (𝓝 ((globalMixedMass (fun k => optForm omega θ (g k))
        (fun k => optPot v (g k)) (fun k => (hV (g k)).1)).toReal)) := by
    have hm := tendsto_globalMixedMass_of_native omega (fun k => hbg (g k)) F
      (fun i k => hU i (g k)) (fun k => hV (g k)) (fun k => hopt (g k))
    exact (ENNReal.tendsto_toReal (globalMixedMass_lt_top omega
      (fun k => (hV (g k)).1)).ne).comp hm
  have hp : Tendsto (fun i => (partialBackgroundMassPolynomial omega θ (u i) (hu i) S).eval a) F
      (𝓝 ((partialBackgroundMassPolynomial omega θ v hv S).eval a)) := by
    unfold partialBackgroundMassPolynomial
    simp only [eval_finsetSum, eval_mul, eval_C, eval_prod]
    exact tendsto_finsetSum Finset.univ fun g _ => (hg g).mul_const _
  have hfun : (fun i => (partialBackgroundMassPolynomial omega θ (u i) (hu i) S).eval a) =
      fun i => (globalMixedMass
        (fun k => θ k + (if k ∈ S then a else 0) • omega.form) (u i)
        (fun k => (LocalPotentials.isThetaPshPotential_add_of_semipositive (hu i k)
          (isSemipositive_smul omega.isSemipositive (by split_ifs <;> first | exact ha | exact le_rfl))).1)).toReal :=
    funext fun i => (globalMixedMass_partial_background_toReal_eq_eval omega (hu i) S ha).symm
  rw [hfun, ← globalMixedMass_partial_background_toReal_eq_eval omega hv S ha] at hp
  have hup (i : I) (k : Fin n) : IsThetaPshPotential
      (θ k + (if k ∈ S then a else 0) • omega.form).val (u i k) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive (hu i k)
      (isSemipositive_smul omega.isSemipositive (by split_ifs <;> first | exact ha | exact le_rfl))
  have hvp (k : Fin n) : IsThetaPshPotential
      (θ k + (if k ∈ S then a else 0) • omega.form).val (v k) :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive (hv k)
      (isSemipositive_smul omega.isSemipositive (by split_ifs <;> first | exact ha | exact le_rfl))
  have he := (ENNReal.continuous_ofReal.tendsto _).comp hp
  simpa only [Function.comp_def, ENNReal.ofReal_toReal (globalMixedMass_lt_top omega
      (fun k => (hup _ k).1)).ne,
    ENNReal.ofReal_toReal (globalMixedMass_lt_top omega
      (fun k => (hvp k).1)).ne] using he

end
end SGPT.Foundations.Analysis.Pending.ActualPartialBackgroundMassContinuity
