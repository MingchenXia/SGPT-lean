import SGPT.Foundations.Analysis.Pending.SingularPBackgroundMassPolynomial
import SGPT.Foundations.Analysis.Pending.KahlerVolumePositive

set_option autoImplicit false

/-! # Actual positive common backgrounds, including initially zero-mass potentials -/

open Set MeasureTheory

namespace SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere DiagonalMass MixedMass
  GlobalNonPluripolar MixedMassBoundedDifference CanonicalBackgroundPolynomial
  SingularPBackgroundMassPolynomial KahlerVolumePositive PluripolarCapacityDichotomy

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- The all-Kähler term of the actual positive slot polynomial gives positive perturbed mass without any positive original-mass assumption. -/
theorem hasPositivePotentialMass_add_smul (omega : KahlerBackground n M)
    {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {a : ℝ} (ha : 0 < a) :
    HasPositivePotentialMass (θ + a • omega.form) u
      (LocalPotentials.isThetaPshPotential_add_of_semipositive hu
        (KahlerDomination.isSemipositive_smul omega.isSemipositive ha.le)) := by
  classical
  let p : ∀ i : Fin n, IsThetaPshPotential θ.val u := fun _ => hu
  have hexp := globalMixedMass_add_background_toReal_eq_sum omega p ha
  have hnone : (fun _ : Fin n => (none : Option (Fin n))) ∈
      Fintype.piFinset (backgroundChoices (n := n)) := by
    simp [Fintype.mem_piFinset, backgroundChoices]
  have hle : a ^ backgroundDegree (fun _ : Fin n => (none : Option (Fin n))) *
      (globalMixedMass (fun i => optForm omega (fun _ => θ) ((fun _ => none) i))
        (fun i => optPot (fun _ => u) ((fun _ => none) i))
        (fun i => optPot_psh omega p ((fun _ => none) i))).toReal ≤
      ∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)), a ^ backgroundDegree g *
        (globalMixedMass (fun i => optForm omega (fun _ => θ) (g i))
          (fun i => optPot (fun _ => u) (g i)) (fun i => optPot_psh omega p (g i))).toReal := by
    exact Finset.single_le_sum
      (f := fun g => a ^ backgroundDegree g *
        (globalMixedMass (fun i => optForm omega (fun _ => θ) (g i))
          (fun i => optPot (fun _ => u) (g i)) (fun i => optPot_psh omega p (g i))).toReal)
      (fun g _ => mul_nonneg (pow_nonneg ha.le (backgroundDegree g)) ENNReal.toReal_nonneg)
      hnone
  have hdegree : backgroundDegree (fun _ : Fin n => (none : Option (Fin n))) = n := by
    simp [backgroundDegree]
  have hcoeff : globalMixedMass
      (fun i : Fin n => optForm omega (fun _ => θ) ((fun _ => none) i))
      (fun i => optPot (fun _ => u) ((fun _ => none) i))
      (fun i => optPot_psh omega p ((fun _ => none) i)) =
      diagonalPotentialMass omega.form (fun _ => 0) (isThetaPshPotential_zero omega) := rfl
  rw [hdegree, hcoeff, ← hexp] at hle
  have hvol := diagonalPotentialMass_zero_pos omega
  have hfinite : diagonalPotentialMass omega.form (fun _ => 0)
      (isThetaPshPotential_zero omega) < ⊤ := globalMixedMeasure_apply_lt_top omega _ univ
  have hrealpos := lt_of_lt_of_le
    (mul_pos (pow_pos ha n) (ENNReal.toReal_pos hvol.ne' hfinite.ne)) hle
  exact (ENNReal.toReal_pos_iff.mp hrealpos).1

/-- Compact Kähler domination and actual positive perturbation internally construct one positive admissible background for any two genuine quasi-PSH potentials. -/
theorem exists_positive_common_background (omega : KahlerBackground n M)
    (θ σ : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    ∃ τ : ClosedRealOneOneForm n M,
      ∃ huτ : IsThetaPshPotential τ.val u,
      ∃ hvτ : IsThetaPshPotential τ.val v,
        HasPositivePotentialMass τ u huτ ∧ HasPositivePotentialMass τ v hvτ := by
  obtain ⟨C, hC, hsemi⟩ :=
    KahlerDomination.exists_pos_isSemipositive_add_smul omega (θ - σ)
  let η := θ - σ + C • omega.form
  have hvη : IsThetaPshPotential (σ + η).val v :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hv hsemi
  have hC1 : 0 < C + 1 := by linarith
  have hupos := hasPositivePotentialMass_add_smul omega hu hC1
  have hvpos := hasPositivePotentialMass_add_smul omega hvη zero_lt_one
  have hforms : (σ + η) + (1 : ℝ) • omega.form = θ + (C + 1) • omega.form := by
    dsimp only [η]
    module
  refine ⟨θ + (C + 1) • omega.form,
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu
      (KahlerDomination.isSemipositive_smul omega.isSemipositive hC1.le), ?_⟩
  have hvτ : IsThetaPshPotential (θ + (C + 1) • omega.form).val v := by
    simpa only [hforms] using
      LocalPotentials.isThetaPshPotential_add_of_semipositive hvη
        (KahlerDomination.isSemipositive_smul omega.isSemipositive zero_le_one)
  exact ⟨hvτ, hupos, by simpa only [hforms] using hvpos⟩

end

end SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence
