import SGPT.Okounkov.CurrentFlagValuation
import SGPT.Foundations.Analysis.Pending.SourceCurrentFiniteCombinations

set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents NaturalThetaPshGeometricCurrent
open GlobalMultilinearExpansion NaturalThetaPshSourceCurrent

/-- The already-produced full source-current finite combination, converted
to the original theta-current normalization by genuine nonzero 2π cancellation.
No chart distribution or current-linearity proof is repeated. -/
theorem exists_thetaPotentialCurrent_finite_combination {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M]
    {ι : Type*} [Fintype ι] {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i)
    {α : ι → ClosedRealOneOneForm (m + 1) M} {f : ι → M → EReal}
    (hf : ∀ i, IsThetaPshPotential (α i).val (f i)) :
    ∃ hF : IsThetaPshPotential (sumForm Finset.univ c α).val (sumPot Finset.univ c f),
      thetaPotentialCurrent (sumForm Finset.univ c α).val
        (sumPot Finset.univ c f) hF =
        ∑ i, c i • thetaPotentialCurrent (α i).val (f i) (hf i) := by
  classical
  obtain ⟨hF, hcur⟩ := SourceCurrentFiniteCombinations.exists_genuine_sum_and_sourceDCurrent_eq hc hf
  refine ⟨hF, ?_⟩
  rw [sourceDCurrent_scaled_theta_eq
    (sumForm Finset.univ c α) (sumPot Finset.univ c f) hF] at hcur
  have hscaled : (2 * Real.pi) • thetaPotentialCurrent
      (sumForm Finset.univ c α).val (sumPot Finset.univ c f) hF =
      (2 * Real.pi) • (∑ i, c i • thetaPotentialCurrent (α i).val (f i) (hf i)) := by
    rw [Finset.smul_sum]
    exact hcur.trans (Finset.sum_congr rfl fun i _ => by
      rw [sourceDCurrent_scaled_theta_eq (α i) (f i) (hf i)]
      exact smul_comm _ _ _)
  have hpi : 2 * Real.pi ≠ 0 := ne_of_gt (mul_pos (by norm_num) Real.pi_pos)
  have hcancel := congrArg (fun A => (2 * Real.pi)⁻¹ • A) hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hpi, one_smul] using hcancel

/-- Actual genuine theta-PSH sum and literal whole-current addition,
including every divisor-supported coefficient. -/
theorem exists_thetaPotentialCurrent_add {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M]
    {θ σ : ClosedRealOneOneForm (m + 1) M} {u v : M → EReal}
    (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val v) :
    ∃ huv : IsThetaPshPotential (θ + σ).val (fun x => u x + v x),
      thetaPotentialCurrent (θ + σ).val (fun x => u x + v x) huv =
        thetaPotentialCurrent θ.val u hu + thetaPotentialCurrent σ.val v hv := by
  let α : Fin 2 → ClosedRealOneOneForm (m + 1) M := ![θ, σ]
  let f : Fin 2 → M → EReal := ![u, v]
  have hf : ∀ i, IsThetaPshPotential (α i).val (f i) := by
    intro i
    fin_cases i
    · exact hu
    · exact hv
  obtain ⟨hF, hcur⟩ := exists_thetaPotentialCurrent_finite_combination
    (c := fun _ : Fin 2 => (1 : ℝ)) (fun _ => zero_le_one) hf
  have hpot : sumPot Finset.univ (fun _ : Fin 2 => (1 : ℝ)) f =
      (fun x => u x + v x) := by
    funext x
    simp only [sumPot, Fin.sum_univ_two, EReal.coe_one, one_mul,
      f, Matrix.cons_val_zero, Matrix.cons_val_one]
  have huv : IsThetaPshPotential (θ + σ).val (fun x => u x + v x) := by
    simpa only [hpot, sumForm, Fin.sum_univ_two, one_smul,
      EReal.coe_one, one_mul, α, f, Matrix.cons_val_zero, Matrix.cons_val_one] using hF
  refine ⟨huv, ?_⟩
  simpa only [hpot, sumForm, Fin.sum_univ_two, one_smul,
    EReal.coe_one, one_mul, α, f, Matrix.cons_val_zero, Matrix.cons_val_one] using hcur

/-- Every original nonnegative scalar, including zero, gives a genuine
theta-PSH potential and the literal whole scaled current. -/
theorem exists_thetaPotentialCurrent_nonneg_smul {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M]
    {θ : ClosedRealOneOneForm (m + 1) M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) {c : ℝ} (hc : 0 ≤ c) :
    ∃ hcu : IsThetaPshPotential (c • θ).val (fun x => (c : EReal) * u x),
      thetaPotentialCurrent (c • θ).val (fun x => (c : EReal) * u x) hcu =
        c • thetaPotentialCurrent θ.val u hu := by
  obtain ⟨hF, hcur⟩ := exists_thetaPotentialCurrent_finite_combination
    (c := fun _ : Fin 1 => c) (fun _ => hc)
    (α := fun _ => θ) (f := fun _ => u) (fun _ => hu)
  have hpot : sumPot Finset.univ (fun _ : Fin 1 => c) (fun _ => u) =
      (fun x => (c : EReal) * u x) := by
    funext x
    simp only [sumPot, Fin.sum_univ_one]
  have hcu : IsThetaPshPotential (c • θ).val (fun x => (c : EReal) * u x) := by
    simpa only [hpot, sumForm, Fin.sum_univ_one] using hF
  refine ⟨hcu, ?_⟩
  simpa only [hpot, sumForm, Fin.sum_univ_one] using hcur

end SGPT.Okounkov
