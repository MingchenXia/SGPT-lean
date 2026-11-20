import SGPT.Foundations.Analysis.Pending.ActualHilbertSquaredCutoffLevi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option autoImplicit false

/-! # Actual coordinate isometries for different Hilbert-dual kernels -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SGPT.Foundations.Analysis.Pending.ActualFiniteHilbertSquaredCutoffLevi
open FirstPass ConcentrationPotentialLevi

variable {ι : Type*} [Fintype ι] (H : ι → Type*)
  [∀ j, NormedAddCommGroup (H j)] [∀ j, InnerProductSpace ℂ (H j)]

/-- Composition with the actual coordinate projection of the finite Hilbert product. -/
def coordinateDualLift (j : ι) :
    StrongDual ℂ (H j) →L[ℂ] StrongDual ℂ (PiLp 2 H) :=
  (ContinuousLinearMap.compL ℂ (PiLp 2 H) (H j) ℂ).flip (PiLp.proj 2 H j)

/-- The dual coordinate lift preserves the genuine operator norm, including zero summands. -/
theorem norm_coordinateDualLift (j : ι) (L : StrongDual ℂ (H j)) :
    ‖coordinateDualLift H j L‖ = ‖L‖ := by
  classical
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
    intro x
    change ‖L (x j)‖ ≤ ‖L‖ * ‖x‖
    exact (L.le_opNorm (x j)).trans
      (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x j) (norm_nonneg L))
  · apply L.opNorm_le_bound (norm_nonneg (coordinateDualLift H j L))
    intro x
    have h := (coordinateDualLift H j L).le_opNorm (PiLp.single 2 j x)
    simpa [coordinateDualLift] using h

variable [∀ j, CompleteSpace (H j)]

/-- The squared-cutoff Levi estimate applies to the actual heterogeneous
atlas Hilbert-dual kernels through internally isometric coordinate lifts. -/
theorem neg_le_leviForm_log_sum_heterogeneous_dual_of_nonneg
    {n : ℕ} {c : ι → ComplexModel n → ℝ}
    {A : (j : ι) → ComplexModel n → StrongDual ℂ (H j)} {s : ℝ} (hs : 0 ≤ s)
    {z : ComplexModel n}
    (hpos : 0 < ∑ j, c j z ^ 2 * ‖A j z‖ ^ 2 + s)
    (hc : ∀ j, ContDiffAt ℝ 2 (c j) z)
    (hA : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (A j) y)
    (v : ComplexModel n) :
    -(2 * (∑ j, ‖A j z‖ ^ 2 *
        (Complex.normSq (delC (c j) z v) - c j z * leviForm (c j) z v)) /
      (∑ j, c j z ^ 2 * ‖A j z‖ ^ 2 + s)) ≤
      leviForm (fun y => Real.log (∑ j, c j y ^ 2 * ‖A j y‖ ^ 2 + s)) z v := by
  let B : ι → ComplexModel n → StrongDual ℂ (PiLp 2 H) :=
    fun j y => coordinateDualLift H j (A j y)
  have hB : ∀ j, ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (B j) y := by
    intro j
    exact (hA j).mono fun y hy =>
      DifferentiableAt.comp (𝕜 := ℂ) (E := ComplexModel n)
        (F := StrongDual ℂ (H j)) (G := StrongDual ℂ (PiLp 2 H)) y
        (coordinateDualLift H j).differentiableAt hy
  have hnorm : ∀ j y, ‖B j y‖ = ‖A j y‖ := fun j y =>
    norm_coordinateDualLift H j (A j y)
  have hp : 0 < ∑ j, c j z ^ 2 * ‖B j z‖ ^ 2 + s := by
    simpa only [hnorm] using hpos
  have hbound := ActualHilbertSquaredCutoffLevi.neg_le_leviForm_log_sum_dual_of_nonneg
    hs hp hc hB v
  simpa only [hnorm] using hbound

end SGPT.Foundations.Analysis.Pending.ActualFiniteHilbertSquaredCutoffLevi
