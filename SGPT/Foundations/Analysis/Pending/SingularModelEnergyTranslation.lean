import SGPT.Foundations.Analysis.Pending.SingularModelEnergyLayout
import SGPT.Foundations.Analysis.Pending.CanonicalWeightConstantShift

set_option autoImplicit false

/-!
# Finite translations of actual singular finite-type energy

Xia SGPT PDF0118, equation (3.31). Actual endpoint mixed measure invariance,
actual same-type mass invariance and canonical weighted integral translation
produce the formula for possibly unbounded genuine same-type potentials.
-/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularModelEnergyTranslation

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar RelativeEnergy
  CanonicalWeightConstantShift GlobalMeasureInvariance

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Finite translation of the first endpoint preserves the actual mixed measure. -/
theorem endpointMixedMeasure_sub_const (θ : ClosedRealOneOneForm n M)
    {φ u : M → EReal} (hφ : IsThetaPshPotential θ.val φ)
    (hu : IsThetaPshPotential θ.val u) (c : ℝ) (j : Fin (n + 1)) :
    endpointMixedMeasure θ φ (fun x => u x - (c : EReal)) hφ (hu.sub_const c) j =
      endpointMixedMeasure θ φ u hφ hu j := by
  let cs : Fin n → ℝ := fun i => if i.val < j.val then c else 0
  have heq : endpointMixedPotential j (fun x => u x - (c : EReal)) φ =
      fun i x => endpointMixedPotential j u φ i x - (cs i : EReal) := by
    funext i x
    simp only [endpointMixedPotential, cs]
    split_ifs <;> simp
  exact (UniformBoundedGlobalMass.globalMixedMeasure_congr_tuple heq _ _).trans
    (globalMixedMeasure_sub_const
      (endpointMixedPotential_thetaPlurisubharmonic θ j u φ hu hφ) cs)

/-- Actual endpoint mixed masses equal the actual diagonal reference mass. -/
theorem endpointMixedMeasure_real_univ_eq (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hutype : SameSingularityTypeOn u φ univ) (j : Fin (n + 1)) :
    (endpointMixedMeasure θ φ u hφ hu j).real univ =
      (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ := by
  have hgen : ∀ i, IsThetaPshPotential θ.val (endpointMixedPotential j u φ i) := by
    intro i
    unfold endpointMixedPotential
    split_ifs
    · exact hu
    · exact hφ
  have htype : ∀ i, SameSingularityTypeOn (endpointMixedPotential j u φ i) φ univ := by
    intro i
    unfold endpointMixedPotential
    split_ifs
    · exact hutype
    · exact SameSingularityTypeOn.refl φ univ
  exact congrArg ENNReal.toReal
    (FiniteGeodesicsFullMassAnyDim.globalMixedMass_eq_of_sameSingularityType
      omega hgen (fun _ => hφ) htype)

/-- Each actual canonical energy term changes by the constant times reference mass. -/
theorem relativeEnergyTerm_sub_const (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hutype : SameSingularityTypeOn u φ univ) (c : ℝ) (j : Fin (n + 1)) :
    relativeEnergyTerm θ φ (fun x => u x - (c : EReal)) hφ (hu.sub_const c) j =
      relativeEnergyTerm θ φ u hφ hu j -
        c * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ := by
  rw [relativeEnergyTerm, endpointMixedMeasure_sub_const]
  have h := integral_canonicalDiff_sub_consts_globalMixedMeasure omega hu hφ hutype
    (endpointMixedPotential_thetaPlurisubharmonic θ j u φ hu hφ) c 0
  simp only [EReal.coe_zero, sub_zero, zero_sub] at h
  change (∫ x, canonicalERealDiffToReal (u x - (c : EReal)) (φ x)
      ∂endpointMixedMeasure θ φ u hφ hu j) =
    relativeEnergyTerm θ φ u hφ hu j +
      (-c) * (endpointMixedMeasure θ φ u hφ hu j).real univ at h
  rw [endpointMixedMeasure_real_univ_eq omega θ hφ hu hutype j] at h
  simpa only [neg_mul, sub_eq_add_neg] using h

/-- The actual energy translation formula for singular same-type potentials. -/
theorem relativeEnergyOfMinimalType_sub_const (omega : KahlerBackground n M)
    (θ : ClosedRealOneOneForm n M) {φ u : M → EReal}
    (hφ : IsThetaPshPotential θ.val φ) (hu : IsThetaPshPotential θ.val u)
    (hutype : SameSingularityTypeOn u φ univ) (c : ℝ) :
    relativeEnergyOfMinimalType θ φ (fun x => u x - (c : EReal)) hφ (hu.sub_const c) =
      relativeEnergyOfMinimalType θ φ u hφ hu -
        c * (globalMixedMeasure (fun _ => θ) (fun _ => φ) (fun _ => hφ.1)).real univ := by
  unfold relativeEnergyOfMinimalType
  simp_rw [relativeEnergyTerm_sub_const omega θ hφ hu hutype c]
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [sub_div, mul_div_cancel_left₀ _ (by positivity)]

end

end SGPT.Foundations.Analysis.Pending.SingularModelEnergyTranslation
