import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Polynomial.Expand

/-!
# Two matrix facts for the `L²` Hessian identity

Lane CZ-LP (`claude-cz-lp`, node `czlp:matrix`).

* `two_mul_coeff_two_det_one_add_X_smul`: the second coefficient of `t ↦ det(1 + tM)` is
  `((tr M)² - tr M²)/2`.  (Comparison of the `t²` coefficients of
  `det(1 + tM) det(1 - tM) = det(1 - t²M²)`.)
* `sum_norm_sq_le_re_trace_mul`: for a positive definite `N` and a Hermitian `A`,
  `∑ |A_pq|² ≤ (Re tr N)² · Re tr(N⁻¹AN⁻¹A)` (spectral theorem for `N`).

These are the pointwise algebra of `LapClass3Energy`: the density of `(ω + t ddᶜu)ⁿ/ωⁿ` is
`det(1 + tN⁻¹A)`, its `t²` coefficient integrates to `0`, and `Re tr((N⁻¹A)²)` controls the
Euclidean norm of the complex Hessian `A`.
-/

set_option autoImplicit false

noncomputable section

open Polynomial Matrix
open scoped Matrix ComplexOrder

namespace SGPT.Analysis.CZLp

variable {n : ℕ}

theorem coeff_two_det_one_add_X_smul_neg (M : Matrix (Fin n) (Fin n) ℂ) :
    (det (1 + (X : ℂ[X]) • (-M).map C)).coeff 2 = (det (1 + (X : ℂ[X]) • M.map C)).coeff 2 := by
  rw [coeff_det_one_add_X_smul_eq_sum_minors, coeff_det_one_add_X_smul_eq_sum_minors]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hcard : Fintype.card s = 2 := by
    rw [Fintype.card_coe]
    exact (Finset.mem_powersetCard.mp hs).2
  have hneg : (-M).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n) =
      -(M.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)) := by
    ext i j
    simp
  rw [hneg, Matrix.det_neg, hcard]
  norm_num

theorem coeff_one_det_one_add_X_smul (M : Matrix (Fin n) (Fin n) ℂ) :
    (det (1 + (X : ℂ[X]) • M.map C)).coeff 1 = M.trace :=
  coeff_det_one_add_X_smul_one M

theorem coeff_zero_det_one_add_X_smul (M : Matrix (Fin n) (Fin n) ℂ) :
    (det (1 + (X : ℂ[X]) • M.map C)).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_det]
  simp

/-- **The second coefficient of `det(1 + tM)`**: `2 c₂ = (tr M)² - tr(M²)`. -/
theorem two_mul_coeff_two_det_one_add_X_smul (M : Matrix (Fin n) (Fin n) ℂ) :
    2 * (det (1 + (X : ℂ[X]) • M.map C)).coeff 2 = M.trace ^ 2 - (M * M).trace := by
  set P := det (1 + (X : ℂ[X]) • M.map C) with hP
  set Q := det (1 + (X : ℂ[X]) • (-M).map C) with hQ
  set R := det (1 + (X : ℂ[X]) • (-(M * M)).map C) with hR
  have hmat : (1 + (X : ℂ[X]) • M.map C) * (1 + (X : ℂ[X]) • (-M).map C) =
      (1 + (X : ℂ[X]) • (-(M * M)).map C).map (expand ℂ 2) := by
    have h1 : (1 + (X : ℂ[X]) • (-(M * M)).map C).map (expand ℂ 2) =
        1 + (X ^ 2 : ℂ[X]) • (-(M * M)).map C := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      split_ifs <;> simp
    have hn1 : (-M).map C = -(M.map C) := Matrix.map_neg _ (fun a => map_neg C a) M
    have hn2 : (-(M * M)).map C = -(M.map C * M.map C) := by
      rw [Matrix.map_neg _ (fun a => map_neg C a), Matrix.map_mul]
    rw [h1, hn1, hn2, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, smul_mul_smul_comm,
      smul_neg, mul_neg, smul_neg, pow_two, smul_neg (X * X)]
    abel
  have hprod : P * Q = expand ℂ 2 R := by
    rw [hP, hQ, hR, ← det_mul, hmat]
    exact (RingHom.map_det (expand ℂ 2).toRingHom _).symm
  have hcoeff := congrArg (fun p : ℂ[X] => p.coeff 2) hprod
  rw [coeff_expand (by norm_num : 0 < 2), if_pos (by norm_num : 2 ∣ 2)] at hcoeff
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add] at hcoeff
  norm_num at hcoeff
  rw [hQ, coeff_two_det_one_add_X_smul_neg, coeff_zero_det_one_add_X_smul,
    coeff_zero_det_one_add_X_smul, coeff_one_det_one_add_X_smul, coeff_one_det_one_add_X_smul,
    hR, coeff_one_det_one_add_X_smul, trace_neg, trace_neg] at hcoeff
  rw [← hP] at hcoeff
  linear_combination hcoeff

/-- **Euclidean norm of a Hermitian matrix against the `N`-norm.**  For `N` positive definite and
`A` Hermitian, `∑ |A_pq|² ≤ (Re tr N)² · Re tr(N⁻¹AN⁻¹A)`. -/
theorem sum_norm_sq_le_re_trace_mul {N A : Matrix (Fin n) (Fin n) ℂ} (hN : N.PosDef)
    (hA : A.IsHermitian) :
    ∑ p, ∑ q, ‖A p q‖ ^ 2 ≤ (N.trace.re) ^ 2 * (N⁻¹ * A * N⁻¹ * A).trace.re := by
  classical
  set U : Matrix (Fin n) (Fin n) ℂ := (hN.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hU
  set d : Fin n → ℝ := hN.1.eigenvalues with hd
  have hd0 : ∀ k, 0 < d k := hN.eigenvalues_pos
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun k => (d k : ℂ)) with hD
  set Di : Matrix (Fin n) (Fin n) ℂ := diagonal (fun k => ((d k)⁻¹ : ℂ)) with hDi
  have hspec : N = U * D * star U := by
    have := hN.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hU, hD, Function.comp_def] using this
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    have : (d k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hd0 k).ne'
    field_simp
  have hinv : N⁻¹ = U * Di * star U := by
    refine inv_eq_right_inv ?_
    rw [hspec]
    calc U * D * star U * (U * Di * star U) = U * D * (star U * U) * Di * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, Matrix.mul_assoc U D Di, hDDi, Matrix.mul_one, hUU']
  set B : Matrix (Fin n) (Fin n) ℂ := star U * A * U with hB
  have hBherm : B.IsHermitian := by
    have := isHermitian_conjTranspose_mul_mul U hA
    rwa [← Matrix.star_eq_conjTranspose] at this
  have hprod : N⁻¹ * A * N⁻¹ * A = U * (Di * B * Di * B) * star U := by
    rw [hinv, hB]
    simp only [Matrix.mul_assoc]
    rw [hUU', Matrix.mul_one]
  have htr : (N⁻¹ * A * N⁻¹ * A).trace = (Di * B * Di * B).trace := by
    rw [hprod, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hentry : (Di * B * Di * B).trace = ∑ k, ∑ l, (((d k)⁻¹ * (d l)⁻¹ * ‖B k l‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, hDi, diagonal_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    have hlk : B l k = star (B k l) := by
      have := congrFun (congrFun hBherm.eq l) k
      rw [Matrix.conjTranspose_apply] at this
      exact this.symm
    rw [hlk, Complex.star_def]
    have hc := Complex.mul_conj (B k l)
    rw [Complex.normSq_eq_norm_sq] at hc
    push_cast at hc ⊢
    linear_combination ((d k : ℂ)⁻¹ * (d l : ℂ)⁻¹) * hc
  have htrN : N.trace = ∑ k, (d k : ℂ) := by
    rw [hspec, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, hD,
      trace_diagonal]
  have htrNre : N.trace.re = ∑ k, d k := by
    rw [htrN, Complex.re_sum]
    simp
  have hsumB : ∑ k, ∑ l, ‖B k l‖ ^ 2 = ∑ p, ∑ q, ‖A p q‖ ^ 2 := by
    have hfrob : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        ((∑ p, ∑ q, ‖X p q‖ ^ 2 : ℝ) : ℂ) = (Xᴴ * X).trace := by
      intro X
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
      push_cast
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have h1 := hfrob B
    have h2 := hfrob A
    have hUh : Uᴴ = star U := (Matrix.star_eq_conjTranspose U).symm
    have hsUh : (star U)ᴴ = U := by rw [← hUh, conjTranspose_conjTranspose]
    have h3 : Bᴴ * B = star U * (Aᴴ * A) * U := by
      rw [hB, conjTranspose_mul, conjTranspose_mul, hsUh, hUh]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U (star U), hUU', Matrix.one_mul]
    have h4 : (Bᴴ * B).trace = (Aᴴ * A).trace := by
      rw [h3, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
    exact_mod_cast (h1.trans (h4.trans h2.symm))
  rw [htr, hentry, Complex.re_sum, htrNre, ← hsumB, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [Complex.ofReal_re]
  have hk : d k ≤ ∑ j, d j := Finset.single_le_sum (fun j _ => (hd0 j).le) (Finset.mem_univ k)
  have hl : d l ≤ ∑ j, d j := Finset.single_le_sum (fun j _ => (hd0 j).le) (Finset.mem_univ l)
  have hkl : d k * d l ≤ (∑ j, d j) ^ 2 := by
    rw [pow_two]; exact mul_le_mul hk hl (hd0 l).le ((hd0 k).le.trans hk)
  have hpos : 0 < d k * d l := mul_pos (hd0 k) (hd0 l)
  have hb : 0 ≤ ‖B k l‖ ^ 2 := sq_nonneg _
  calc ‖B k l‖ ^ 2 = (d k * (d k)⁻¹) * (d l * (d l)⁻¹) * ‖B k l‖ ^ 2 := by
        rw [mul_inv_cancel₀ (hd0 k).ne', mul_inv_cancel₀ (hd0 l).ne', one_mul, one_mul]
    _ = (d k * d l) * ((d k)⁻¹ * (d l)⁻¹ * ‖B k l‖ ^ 2) := by ring
    _ ≤ (∑ j, d j) ^ 2 * ((d k)⁻¹ * (d l)⁻¹ * ‖B k l‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hkl (mul_nonneg (mul_nonneg (inv_nonneg.mpr (hd0 k).le)
          (inv_nonneg.mpr (hd0 l).le)) hb)

/-- **Trace against a positive definite matrix**: for `N` positive definite and `P` positive
semidefinite, `Re tr P ≤ Re tr N · Re tr(N⁻¹P)`. -/
theorem re_trace_le_re_trace_mul {N P : Matrix (Fin n) (Fin n) ℂ} (hN : N.PosDef)
    (hP : P.PosSemidef) : P.trace.re ≤ N.trace.re * (N⁻¹ * P).trace.re := by
  classical
  set U : Matrix (Fin n) (Fin n) ℂ := (hN.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hU
  set d : Fin n → ℝ := hN.1.eigenvalues with hd
  have hd0 : ∀ k, 0 < d k := hN.eigenvalues_pos
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun k => (d k : ℂ)) with hD
  set Di : Matrix (Fin n) (Fin n) ℂ := diagonal (fun k => ((d k)⁻¹ : ℂ)) with hDi
  have hspec : N = U * D * star U := by
    have := hN.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hU, hD, Function.comp_def] using this
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    have : (d k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hd0 k).ne'
    field_simp
  have hinv : N⁻¹ = U * Di * star U := by
    refine inv_eq_right_inv ?_
    rw [hspec]
    calc U * D * star U * (U * Di * star U) = U * D * (star U * U) * Di * star U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, Matrix.mul_assoc U D Di, hDDi, Matrix.mul_one, hUU']
  set Q : Matrix (Fin n) (Fin n) ℂ := star U * P * U with hQ
  have hQpsd : Q.PosSemidef := by
    have := hP.conjTranspose_mul_mul_same U
    rwa [← Matrix.star_eq_conjTranspose] at this
  have htrP : P.trace = Q.trace := by
    rw [hQ, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul]
  have htrNP : (N⁻¹ * P).trace = (Di * Q).trace := by
    rw [hinv, hQ]
    have : U * Di * star U * P = U * (Di * (star U * P * U)) * star U := by
      simp only [Matrix.mul_assoc]; rw [hUU', Matrix.mul_one]
    rw [this, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have htrN : N.trace.re = ∑ k, d k := by
    rw [hspec, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul, hD,
      trace_diagonal, Complex.re_sum]
    simp
  have hQkk : ∀ k, 0 ≤ (Q k k).re := fun k => (Complex.nonneg_iff.mp hQpsd.diag_nonneg).1
  have h1 : Q.trace.re = ∑ k, (Q k k).re := by
    simp [Matrix.trace, Complex.re_sum]
  have h2 : (Di * Q).trace.re = ∑ k, (d k)⁻¹ * (Q k k).re := by
    simp only [Matrix.trace, Matrix.diag, hDi, diagonal_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]
  rw [htrP, htrNP, h1, h2, htrN, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : d k ≤ ∑ j, d j := Finset.single_le_sum (fun j _ => (hd0 j).le) (Finset.mem_univ k)
  calc (Q k k).re = (d k * (d k)⁻¹) * (Q k k).re := by rw [mul_inv_cancel₀ (hd0 k).ne', one_mul]
    _ ≤ (∑ j, d j) * (d k)⁻¹ * (Q k k).re := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hk (mul_nonneg (inv_nonneg.mpr (hd0 k).le) (hQkk k))
    _ = (∑ j, d j) * ((d k)⁻¹ * (Q k k).re) := by ring

/-- **Rayleigh bound**: for `P` positive semidefinite, `Re ⟨x, Px⟩ ≤ Re tr P · ∑ |x_i|²`. -/
theorem re_dotProduct_mulVec_le {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef)
    (x : Fin n → ℂ) : (star x ⬝ᵥ (P *ᵥ x)).re ≤ P.trace.re * ∑ i, ‖x i‖ ^ 2 := by
  classical
  set V : Matrix (Fin n) (Fin n) ℂ := (hP.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
    with hV
  set e : Fin n → ℝ := hP.1.eigenvalues with he
  have he0 : ∀ k, 0 ≤ e k := fun k => hP.eigenvalues_nonneg k
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVV' : V * star V = 1 := Unitary.coe_mul_star_self _
  have hspec : P = V * diagonal (fun k => (e k : ℂ)) * star V := by
    have := hP.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    simpa [hV, Function.comp_def] using this
  set y : Fin n → ℂ := star V *ᵥ x with hy
  have hdot : star x ⬝ᵥ (P *ᵥ x) = star y ⬝ᵥ (diagonal (fun k => (e k : ℂ)) *ᵥ y) := by
    rw [hspec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, hy,
      Matrix.star_mulVec, Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose,
      ← Matrix.star_eq_conjTranspose]
  have hnorm : ∑ i, ‖y i‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    have hsq : ∀ z : Fin n → ℂ, ((∑ i, ‖z i‖ ^ 2 : ℝ) : ℂ) = star z ⬝ᵥ z := by
      intro z
      simp only [dotProduct, Pi.star_apply]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    have h1 : star y ⬝ᵥ y = star x ⬝ᵥ x := by
      rw [hy, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose,
        hVV', Matrix.one_mulVec]
    exact_mod_cast (hsq y).trans (h1.trans (hsq x).symm)
  have htr : P.trace.re = ∑ k, e k := by
    rw [hspec, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hVV, Matrix.one_mul, trace_diagonal,
      Complex.re_sum]
    simp
  have hval : (star y ⬝ᵥ (diagonal (fun k => (e k : ℂ)) *ᵥ y)).re = ∑ k, e k * ‖y k‖ ^ 2 := by
    simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : star (y k) * ((e k : ℂ) * y k) = ((e k * ‖y k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, mul_left_comm, Complex.conj_mul']
      push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [hdot, hval, htr, ← hnorm, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  have hyk : ‖y k‖ ^ 2 ≤ ∑ i, ‖y i‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖y i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  exact mul_le_mul_of_nonneg_left hyk (he0 k)

end SGPT.Analysis.CZLp
