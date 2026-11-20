import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Complex.Order

/-!
# Pointwise linear algebra of the Bochner--Kodaira inequality for `(n,1)`-forms

Blueprint `claude-twisted-l2:kahler-antisym`.

Write an `L`-valued `(n,1)`-form through the vector field `W = σ^♯τ` (a `(1,0)`-vector field) and
put `A_{lj} = ∂W_l/∂z̄_j`.  For a Kähler form with coefficient matrix `g` (`σ(W) = W* g W`) the
lowered form is `τ = g W` and, by Kähler lowering (`KahlerLoweringStatement`), the `(0,2)`-form
`∂̄τ` has the antisymmetric coefficient matrix `β = (gA)ᵀ - gA` (`kahlerAntisym`).  Its norm for
`σ` is `|β|²_σ = ½ tr(β* N β Nᵀ)` with `N = g⁻¹` (`zeroTwoNormSq`).  The flat
Morrey--Kohn--Hörmander identity produces the term `Re tr(A Ā)` (`traceMulConj`).  We prove the
pointwise identity

`|∂̄τ|²_σ + Re tr(A Ā) = Re tr(A* g A Nᵀ) = |A|²_σ ≥ 0`

(`zeroTwoNormSq_kahlerAntisym_add`, `re_trace_conjTranspose_mul_mul_nonneg`), hence
`-Re tr(A Ā) ≤ |∂̄τ|²_σ` (`neg_re_traceMulConj_le`).  This is the only pointwise input of the
Bochner--Kodaira--Nakano inequality `‖∂̄*τ‖² + ‖∂̄τ‖² ≥ ∫ Levi(p)(W)` for `(n,1)`-forms on a Kähler
manifold beyond the flat identity: no Kähler normal coordinates and no curvature of `σ` enter.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.TwistedL2

open Matrix
open scoped ComplexOrder

variable {n : ℕ}

/-- The coefficient matrix `β = (gA)ᵀ - gA` of `∂̄(g W)` (`β_{jk} = (gA)_{kj} - (gA)_{jk}`). -/
def kahlerAntisym (g A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (g * A)ᵀ - g * A

/-- The norm `|β|²_σ = ½ tr(β* N β Nᵀ)` of a `(0,2)`-covector with coefficient matrix `β` for the
inverse metric `N = g⁻¹` (in a `σ`-unitary frame, `½ ∑_{j,k} |β_{jk}|²`). -/
def zeroTwoNormSq (N β : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (1 / 2 : ℝ) * (trace (βᴴ * N * β * Nᵀ)).re

/-- `tr(A Ā) = ∑_{j,k} A_{kj} conj(A_{jk})` (`Ā = Aᴴᵀ` is the entrywise conjugate). -/
def traceMulConj (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  trace (A * Aᴴᵀ)

/-- **The trace identity**: for a Hermitian `g` with inverse `N`,
`tr(β* N β Nᵀ) = 2 tr(A* g A Nᵀ) - 2 tr(A Ā)` for `β = (gA)ᵀ - gA`. -/
theorem trace_kahlerAntisym {g N : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ = g) (hNg : N * g = 1)
    (hgN : g * N = 1) (A : Matrix (Fin n) (Fin n) ℂ) :
    trace ((kahlerAntisym g A)ᴴ * N * kahlerAntisym g A * Nᵀ) =
      2 * trace (Aᴴ * g * A * Nᵀ) - 2 * traceMulConj A := by
  have hgTN : gᵀ * Nᵀ = 1 := by rw [← transpose_mul, hNg, transpose_one]
  have hNTgT : Nᵀ * gᵀ = 1 := by rw [← transpose_mul, hgN, transpose_one]
  have h1 : ∀ X : Matrix (Fin n) (Fin n) ℂ, g * (N * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hgN, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin n) (Fin n) ℂ, N * (g * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hNg, Matrix.one_mul]
  -- `βᴴ = gᵀ Ā - Aᴴ g` and `β = Aᵀ gᵀ - g A`
  have hβH : (kahlerAntisym g A)ᴴ = gᵀ * Aᴴᵀ - Aᴴ * g := by
    rw [kahlerAntisym, conjTranspose_sub, conjTranspose_mul, hg,
      conjTranspose_transpose_eq_transpose_conjTranspose, conjTranspose_mul, hg, transpose_mul]
  have hβ : kahlerAntisym g A = Aᵀ * gᵀ - g * A := by
    rw [kahlerAntisym, transpose_mul]
  rw [hβH, hβ]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h1, h2, hgTN, Matrix.mul_one]
  rw [trace_sub, trace_sub, trace_sub]
  -- the four traces
  have t1 : trace (gᵀ * (Aᴴᵀ * (N * Aᵀ))) = trace (Aᴴ * (g * (A * Nᵀ))) := by
    rw [← trace_transpose]
    simp only [transpose_mul, transpose_transpose]
    rw [Matrix.mul_assoc (A * Nᵀ), trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have t2 : trace (gᵀ * (Aᴴᵀ * (A * Nᵀ))) = traceMulConj A := by
    rw [trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hNTgT, Matrix.mul_one,
      trace_mul_comm, traceMulConj]
  have t3 : trace (Aᴴ * Aᵀ) = traceMulConj A := by
    rw [← trace_transpose, transpose_mul, transpose_transpose, traceMulConj]
  rw [t1, t2, t3]
  ring

/-- `re tr(P Q) ≥ 0` for positive semidefinite `P, Q`. -/
theorem re_trace_mul_nonneg_of_posSemidef {P Q : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ (trace (P * Q)).re := by
  classical
  set U : Matrix (Fin n) (Fin n) ℂ := (hQ.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  set d : Fin n → ℂ := RCLike.ofReal ∘ hQ.1.eigenvalues
  have hQ' : Q = U * diagonal d * Uᴴ := by
    have h := hQ.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [h, ← star_eq_conjTranspose, ← Unitary.coe_star]
  have hcyc : trace (P * Q) = trace ((Uᴴ * P * U) * diagonal d) := by
    rw [hQ']
    calc trace (P * (U * diagonal d * Uᴴ)) = trace ((P * U * diagonal d) * Uᴴ) := by
          simp only [Matrix.mul_assoc]
      _ = trace (Uᴴ * (P * U * diagonal d)) := trace_mul_comm _ _
      _ = trace ((Uᴴ * P * U) * diagonal d) := by simp only [Matrix.mul_assoc]
  have hM : (Uᴴ * P * U).PosSemidef := hP.conjTranspose_mul_mul_same U
  rw [hcyc, trace]
  simp only [diag_apply, mul_diagonal, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have hd : d i = ((hQ.1.eigenvalues i : ℝ) : ℂ) := rfl
  rw [hd, Complex.re_mul_ofReal]
  exact mul_nonneg (Complex.nonneg_iff.mp (hM.diag_nonneg (i := i))).1 (hQ.eigenvalues_nonneg i)

/-- `|A|²_σ = re tr(A* g A Nᵀ) ≥ 0` for `g` positive definite and `N = g⁻¹`. -/
theorem re_trace_conjTranspose_mul_mul_nonneg {g : Matrix (Fin n) (Fin n) ℂ} (hg : g.PosDef)
    (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ (trace (Aᴴ * g * A * (g⁻¹)ᵀ)).re :=
  re_trace_mul_nonneg_of_posSemidef (hg.posSemidef.conjTranspose_mul_mul_same A)
    hg.inv.transpose.posSemidef

/-- **The pointwise Kähler identity** `|∂̄τ|²_σ + Re tr(A Ā) = |A|²_σ`. -/
theorem zeroTwoNormSq_kahlerAntisym_add {g : Matrix (Fin n) (Fin n) ℂ} (hg : g.PosDef)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    zeroTwoNormSq g⁻¹ (kahlerAntisym g A) + (traceMulConj A).re =
      (trace (Aᴴ * g * A * (g⁻¹)ᵀ)).re := by
  have hu : IsUnit g.det := (isUnit_iff_isUnit_det g).mp hg.isUnit
  have h := trace_kahlerAntisym hg.1 (nonsing_inv_mul g hu) (mul_nonsing_inv g hu) A
  rw [zeroTwoNormSq, h]
  simp only [Complex.sub_re, Complex.mul_re]
  norm_num
  ring

/-- **The pointwise Bochner--Kodaira inequality** `-Re tr(A Ā) ≤ |∂̄τ|²_σ`. -/
theorem neg_re_traceMulConj_le {g : Matrix (Fin n) (Fin n) ℂ} (hg : g.PosDef)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    -(traceMulConj A).re ≤ zeroTwoNormSq g⁻¹ (kahlerAntisym g A) := by
  have h1 := zeroTwoNormSq_kahlerAntisym_add hg A
  have h2 := re_trace_conjTranspose_mul_mul_nonneg hg A
  linarith

end SGPT.Trace.TwistedL2
