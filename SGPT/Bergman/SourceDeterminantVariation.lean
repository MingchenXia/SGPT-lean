import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.WeightVariation

open Matrix
open scoped BigOperators

private theorem exists_moved_except {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (hσ : σ ≠ 1) (i : ι) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra hnone
  have hfix (j : ι) (hj : j ≠ i) : σ j = j := by
    by_contra hm
    exact hnone ⟨j, hj, hm⟩
  have hi : σ i = i := by
    by_contra hm
    exact hm (σ.injective (hfix (σ i) hm))
  apply hσ
  ext j
  by_cases hj : j = i
  · simpa only [hj, Equiv.Perm.one_apply] using hi
  · exact hfix j hj

/-- Jacobi's determinant derivative at the identity, proved from the actual
Leibniz polynomial. The empty index set is retained. -/
theorem hasDerivAt_det_at_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (t₀ : ℝ)
    (hzero : A t₀ = 1)
    (hd : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) t₀) :
    HasDerivAt (fun t => (A t).det) (Matrix.trace A') t₀ := by
  classical
  have hprod (σ : Equiv.Perm ι) :=
    HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hd (σ i) i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ =>
    (hprod σ).const_mul (((Equiv.Perm.sign σ : ℤ) : ℂ)))
  have hvalue : (∑ σ : Equiv.Perm ι, (((Equiv.Perm.sign σ : ℤ) : ℂ)) *
      ∑ i, (∏ j ∈ Finset.univ.erase i, A t₀ (σ j) j) • A' (σ i) i) =
      Matrix.trace A' := by
    rw [hzero]
    have hz (σ : Equiv.Perm ι) (hσ : σ ≠ 1) (i : ι) :
        (∏ j ∈ Finset.univ.erase i, (1 : Matrix ι ι ℂ) (σ j) j) = 0 := by
      obtain ⟨j, hji, hj⟩ := exists_moved_except σ hσ i
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
      simp only [Matrix.one_apply, if_neg hj]
    rw [Finset.sum_eq_single (1 : Equiv.Perm ι)]
    · simp [Matrix.trace, Matrix.diag, Matrix.one_apply]
    · intro σ _ hσ
      simp [hz σ hσ]
    · simp
  simpa only [Matrix.det_apply', hvalue] using hsum

/-- The actual real log determinant has derivative equal to the real trace
at an identity matrix. No positivity or nonzero determinant is supplied:
the needed local nonzero value follows from the identity itself. -/
theorem hasDerivAt_log_re_det_at_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℂ) (A' : Matrix ι ι ℂ) (t₀ : ℝ)
    (hzero : A t₀ = 1)
    (hd : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) t₀) :
    HasDerivAt (fun t => Real.log (A t).det.re) (Matrix.trace A').re t₀ := by
  have h := hasDerivAt_det_at_identity A A' t₀ hzero hd
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t₀ h
  have hne : (A t₀).det.re ≠ 0 := by simp [hzero]
  have hlog := hr.log hne
  change HasDerivAt (fun t => Real.log (A t).det.re)
    ((Matrix.trace A').re / (A t₀).det.re) t₀ at hlog
  simpa only [hzero, Matrix.det_one, Complex.one_re, div_one] using hlog

end SGPT.Bergman.WeightVariation
