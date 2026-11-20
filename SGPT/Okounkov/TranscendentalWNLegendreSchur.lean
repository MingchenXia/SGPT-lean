import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Complex.Basic

/-!
# The Schur complement of the last diagonal entry (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:schur` (standard linear algebra).  For a square
matrix `H` indexed by `Fin (n + 1)` whose last diagonal entry `c = H_{last,last}` is invertible,
the **Schur complement** of `c` is the `n × n` matrix

  `S_{jk} = H_{jk} - H_{j,last} H_{last,k} / c`,

and `det H = c · det S` (`det_eq_mul_det_lastSchur`).  This is Mathlib's
`Matrix.det_fromBlocks₂₂` after the reindexing `Fin n ⊕ Fin 1 ≃ Fin (n + 1)`.

It computes the Monge–Ampère density of `u(z, τ) = F(z, log |τ|²)` in terms of the
Monge–Ampère densities of the partial Legendre transforms (`tok-wn-leg:smooth-family`).
-/

set_option autoImplicit false

namespace SGPT.Okounkov.TranscendentalWN

open Matrix

variable {n : ℕ} {R : Type*} [Field R]

/-- The Schur complement of the last diagonal entry of `H`. -/
def lastSchur (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) : Matrix (Fin n) (Fin n) R :=
  fun j k => H j.castSucc k.castSucc -
    H j.castSucc (Fin.last n) * H (Fin.last n) k.castSucc / H (Fin.last n) (Fin.last n)

theorem natAdd_zero_eq_last : Fin.natAdd n (0 : Fin 1) = Fin.last n := Fin.ext (by simp)

/-- **`tok-wn-leg:schur`**: `det H = H_{last,last} · det (Schur complement)`. -/
theorem det_eq_mul_det_lastSchur (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hc : H (Fin.last n) (Fin.last n) ≠ 0) :
    H.det = H (Fin.last n) (Fin.last n) * (lastSchur H).det := by
  classical
  set c := H (Fin.last n) (Fin.last n) with hc_def
  set e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
  set M := H.submatrix e e with hM
  have h1 : M.det = H.det := det_submatrix_equiv_self e H
  have hD : M.toBlocks₂₂ = Matrix.of fun _ _ => c := by
    ext i j
    fin_cases i; fin_cases j
    simp [M, e, toBlocks₂₂, c, natAdd_zero_eq_last]
  let X : Matrix (Fin 1) (Fin 1) R := Matrix.of fun _ _ => c⁻¹
  have hXD : X * M.toBlocks₂₂ = 1 := by
    rw [hD]
    ext i j
    fin_cases i; fin_cases j
    simp [X, Matrix.mul_apply, hc]
  have hDX : M.toBlocks₂₂ * X = 1 := by
    rw [hD]
    ext i j
    fin_cases i; fin_cases j
    simp [X, Matrix.mul_apply, hc]
  let _ : Invertible M.toBlocks₂₂ := ⟨X, hXD, hDX⟩
  rw [← h1, ← fromBlocks_toBlocks M, det_fromBlocks₂₂]
  have hdetD : M.toBlocks₂₂.det = c := by
    rw [hD, det_unique]
    rfl
  rw [hdetD]
  congr 1
  congr 1
  ext j k
  have hinv : (⅟M.toBlocks₂₂ : Matrix (Fin 1) (Fin 1) R) = X := rfl
  rw [hinv]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_one,
    toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, Matrix.of_apply, M, submatrix_apply, e,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, X, lastSchur, natAdd_zero_eq_last]
  change _ = H (Fin.castAdd 1 j) (Fin.castAdd 1 k) -
    H (Fin.castAdd 1 j) (Fin.last n) * H (Fin.last n) (Fin.castAdd 1 k) / c
  ring

end SGPT.Okounkov.TranscendentalWN
