import SGPT.Foundations.Analysis.Pending.BackgroundPolynomialIntegrationByParts

set_option autoImplicit false

/-! # Actual mixed non-pluripolar background mass polynomials and recovery at zero -/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SingularPBackgroundMassPolynomial

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar GlobalDiagonalScaling MixedMass
  GlobalMultilinearExpansion MixedMassProductCalculus MixedMassBoundedDifference
  CanonicalBackgroundPolynomial

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Actual positive slot splitting and genuine finite mass internally produce the real mixed non-pluripolar background mass polynomial with its actual global measure coefficients. -/
theorem globalMixedMass_add_background_toReal_eq_sum (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {N : ℝ} (hN : 0 < N) :
    (globalMixedMass (fun i => θ i + N • omega.form) u
      (fun i => (isThetaPshPotential_add_background omega hu hN.le i).1)).toReal =
      ∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)), N ^ backgroundDegree g *
        (globalMixedMass (fun i => optForm omega θ (g i))
          (fun i => optPot u (g i)) (fun i => optPot_psh omega hu (g i))).toReal := by
  classical
  have hT : ∀ i : Fin n, (backgroundChoices i).Nonempty :=
    fun i => ⟨none, by simp [backgroundChoices]⟩
  have hexp := globalMixedMeasure_sumPot_slots hT
    (fun _ => optWeight_pos (n := n) hN) (optPot_psh omega hu) (optPot_quasiPsh hu)
  rw [globalMixedMeasure_congr (funext (sumForm_backgroundChoices omega θ N))
    (funext (sumPot_backgroundChoices u N)) _
    (fun i => (isThetaPshPotential_add_background omega hu hN.le i).1)] at hexp
  unfold globalMixedMass
  rw [hexp, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_sum fun g _ => ?_]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, prod_optWeight]
    simp only [backgroundDegree, ENNReal.toReal_ofReal (pow_nonneg hN.le _)]
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (globalMixedMeasure_apply_lt_top omega _ univ).ne

/-- Equality of actual perturbed mixed masses on a positive natural tail internally gives a genuine polynomial identity, whose actual original coefficient recovers equality of the original extended nonnegative masses. -/
theorem globalMixedMass_eq_of_add_background_nat_eq (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M} {u v : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i))
    (hv : ∀ i, IsThetaPshPotential (θ i).val (v i))
    (N0 : ℕ) (hN0 : 0 < N0)
    (hm : ∀ N : ℕ, N0 ≤ N →
      globalMixedMass (fun i => θ i + (N : ℝ) • omega.form) u
        (fun i => (isThetaPshPotential_add_background omega hu (Nat.cast_nonneg N) i).1) =
      globalMixedMass (fun i => θ i + (N : ℝ) • omega.form) v
        (fun i => (isThetaPshPotential_add_background omega hv (Nat.cast_nonneg N) i).1)) :
    globalMixedMass θ u (fun i => (hu i).1) =
      globalMixedMass θ v (fun i => (hv i).1) := by
  classical
  let d : (Fin n → Option (Fin n)) → ℝ := fun g =>
    (globalMixedMass (fun i => optForm omega θ (g i))
      (fun i => optPot u (g i)) (fun i => optPot_psh omega hu (g i))).toReal -
    (globalMixedMass (fun i => optForm omega θ (g i))
      (fun i => optPot v (g i)) (fun i => optPot_psh omega hv (g i))).toReal
  have hp (N : ℕ) (hN : N0 ≤ N) :
      ∑ g ∈ Fintype.piFinset (backgroundChoices (n := n)),
        (N : ℝ) ^ backgroundDegree g * d g = 0 := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast (hN0.trans_le hN)
    have hreal := congrArg ENNReal.toReal (hm N hN)
    rw [globalMixedMass_add_background_toReal_eq_sum omega hu hNp,
      globalMixedMass_add_background_toReal_eq_sum omega hv hNp] at hreal
    simp only [d, mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr hreal
  have hc := BackgroundPolynomialIntegrationByParts.original_coefficient_eq_zero d N0 hp
  have hreal : (globalMixedMass θ u (fun i => (hu i).1)).toReal =
      (globalMixedMass θ v (fun i => (hv i).1)).toReal := by
    apply sub_eq_zero.mp
    exact hc
  exact (ENNReal.toReal_eq_toReal_iff' (globalMixedMass_lt_top omega _).ne
    (globalMixedMass_lt_top omega _).ne).mp hreal

end

end SGPT.Foundations.Analysis.Pending.SingularPBackgroundMassPolynomial
