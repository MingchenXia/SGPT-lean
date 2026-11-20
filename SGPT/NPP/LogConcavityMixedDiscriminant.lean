import SGPT.Foundations.Analysis.Pending.MixedHessianDivergence
import SGPT.Foundations.Analysis.Pending.MixedCoefficientCongruence
import SGPT.Foundations.Analysis.Pending.MixedCoefficientPositivity
import SGPT.Foundations.Analysis.Pending.MixedCoefficientSlotBound
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalities

/-!
# The geometric-mean inequality for mixed discriminants

Pointwise linear algebra behind the log-concavity of mixed masses (source `thm:logconc`,
Xia, *Singularities in global pluripotential theory*, chapter on non-pluripolar products; the
pointwise input is Xia, *Foundations of pluripotential theory*, `lem:multifactor-mixed-discriminant`,
i.e. Gårding's inequality for the determinant).

For positive definite Hermitian `n × n` matrices `H₀, …, H_{n-1}` let
`mixedCoefficient H = ∑_σ det (row j of H_{σ j})`, the coefficient of `t₀ ⋯ t_{n-1}` in
`det (∑ tᵢ Hᵢ)` (TN's `mixedCoefficient`, which is `n!` times the normalized mixed discriminant).
We prove

`∏ᵢ det Hᵢ ≤ (Re (mixedCoefficient H) / n!)ⁿ`, equivalently
`n! ∏ᵢ (det Hᵢ)^{1/n} ≤ Re (mixedCoefficient H)`.

## Proof

Induction on `n`, by a route different from the source (which uses the signature of the mixed
discriminant form): diagonalize `H₀ = U diag(λ) U*` by a unitary `U`; the mixed coefficient is
invariant under the congruence `Hᵢ ↦ U* Hᵢ U`. Expanding in the first slot,
`mixedCoefficient (diag λ, K) = ∑ₖ λₖ · mixedCoefficient (Kᵢ^{(k)})`, where `K^{(k)}` deletes the
`k`-th row and column (`cofactor_self`). By induction
`∏ᵢ det Kᵢ^{(k)} ≤ (cₖ / (n-1)!)^{n-1}`, and `det Kᵢ^{(k)} = det Kᵢ · (Kᵢ⁻¹)ₖₖ`; Hadamard's
inequality for `Kᵢ⁻¹` gives `∏ₖ det Kᵢ^{(k)} ≥ (det Kᵢ)^{n-1}`; the AM–GM inequality for the
numbers `λₖ cₖ / (n-1)!` concludes.

## Main results

* `det_re_le_prod_diag_re`: Hadamard's inequality for positive definite Hermitian matrices.
* `cofactor_self`: the first-slot cofactor at a diagonal position is a mixed coefficient of
  principal submatrices.
* `prod_det_re_le_mixedCoefficient_re_pow`, `factorial_mul_prod_det_rpow_le_mixedCoefficient_re`:
  the geometric-mean inequality.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NPP.LogConcavity

open Matrix Finset
open scoped ComplexOrder
open SGPT.Foundations.Analysis.FirstPass.MixedMongeAmpere
open SGPT.Foundations.Analysis.Pending.MixedHessian SGPT.Foundations.Analysis.Pending.MixedMongeAmpere

/-! ### Real parts of determinants and diagonal entries -/

section Hermitian

variable {N : ℕ}

/-- The determinant of a positive definite Hermitian matrix is a positive real number. -/
theorem det_re_pos {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosDef) : 0 < P.det.re :=
  (Complex.pos_iff.mp hP.det_pos).1

theorem det_im_eq_zero {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosDef) : P.det.im = 0 :=
  (Complex.pos_iff.mp hP.det_pos).2.symm

theorem det_eq_ofReal_re {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosDef) :
    P.det = (P.det.re : ℂ) :=
  Complex.ext (by simp) (by simp [det_im_eq_zero hP])

/-- Diagonal entries of a positive definite Hermitian matrix are positive reals. -/
theorem diag_re_pos {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosDef) (k : Fin N) :
    0 < (P k k).re := by
  have h := hP.dotProduct_mulVec_pos (x := Pi.single k 1) (by simp)
  have hkk : star (Pi.single k (1 : ℂ)) ⬝ᵥ (P *ᵥ Pi.single k 1) = P k k := by
    simp [mulVec_single, dotProduct, Pi.single_apply]
  rw [hkk] at h
  exact (Complex.pos_iff.mp h).1

theorem diag_eq_ofReal_re {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosDef) (k : Fin N) :
    P k k = ((P k k).re : ℂ) :=
  (hP.isHermitian.coe_re_apply_self k).symm

end Hermitian

/-! ### Hadamard's inequality -/

section Hadamard

variable {N : ℕ}

/-- For a positive definite Hermitian matrix with unit diagonal, `det ≤ 1` (AM–GM for the
eigenvalues). -/
theorem det_re_le_one_of_diag_eq_one {Q : Matrix (Fin N) (Fin N) ℂ} (hQ : Q.PosDef)
    (hdiag : ∀ k, Q k k = 1) : Q.det.re ≤ 1 := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  set μ := hQ.isHermitian.eigenvalues with hμ
  have hμpos : ∀ k, 0 < μ k := fun k => hQ.eigenvalues_pos k
  have hdet : Q.det.re = ∏ k, μ k := by
    rw [hQ.isHermitian.det_eq_prod_eigenvalues]
    norm_cast
  have htr : ∑ k, μ k = N := by
    have h := hQ.isHermitian.trace_eq_sum_eigenvalues
    have h' : Q.trace = N := by
      simp [Matrix.trace, hdiag]
    rw [h'] at h
    have := congrArg Complex.re h
    simp only [Complex.natCast_re] at this
    rw [this]
    norm_cast
  have hamgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin N)) (fun _ => (1 : ℝ)) μ
    (fun _ _ => zero_le_one) (by simp [hN]) (fun k _ => (hμpos k).le)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hamgm
  rw [htr, div_self (by exact_mod_cast hN.ne')] at hamgm
  rw [hdet]
  have hprod : 0 ≤ ∏ k, μ k := Finset.prod_nonneg fun k _ => (hμpos k).le
  have hx : (∏ k, μ k) = ((∏ k, μ k) ^ ((N : ℝ)⁻¹)) ^ N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hprod,
      inv_mul_cancel₀ (by exact_mod_cast hN.ne'), Real.rpow_one]
  rw [hx]
  exact pow_le_one₀ (Real.rpow_nonneg hprod _) hamgm

/-- **Hadamard's inequality**: the determinant of a positive definite Hermitian matrix is at most
the product of its diagonal entries. -/
theorem det_re_le_prod_diag_re {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosDef) :
    P.det.re ≤ ∏ k, (P k k).re := by
  classical
  set d : Fin N → ℝ := fun k => (P k k).re with hd
  have hdpos : ∀ k, 0 < d k := fun k => diag_re_pos hP k
  set s : Fin N → ℝ := fun k => (Real.sqrt (d k))⁻¹ with hs
  have hspos : ∀ k, 0 < s k := fun k => inv_pos.mpr (Real.sqrt_pos.mpr (hdpos k))
  have hs2 : ∀ k, s k * s k * d k = 1 := by
    intro k
    have h1 : Real.sqrt (d k) * Real.sqrt (d k) = d k := Real.mul_self_sqrt (hdpos k).le
    have h2 : Real.sqrt (d k) ≠ 0 := (Real.sqrt_pos.mpr (hdpos k)).ne'
    simp only [hs]
    field_simp
    linarith [h1]
  set D : Matrix (Fin N) (Fin N) ℂ := diagonal fun k => ((s k : ℝ) : ℂ) with hD
  have hDH : Dᴴ = D := by
    rw [hD, diagonal_conjTranspose]
    congr 1
    funext k
    simp
  have hinj : Function.Injective D.mulVec := by
    intro x y hxy
    funext k
    have := congrFun hxy k
    simp only [hD, mulVec_diagonal] at this
    exact mul_left_cancel₀ (by exact_mod_cast (hspos k).ne') this
  have hQ : (Dᴴ * P * D).PosDef := hP.conjTranspose_mul_mul_same hinj
  have hQdiag : ∀ k, (Dᴴ * P * D) k k = 1 := by
    intro k
    rw [hDH, hD, mul_diagonal, diagonal_mul]
    rw [diag_eq_ofReal_re hP k]
    have := hs2 k
    simp only [hd] at this
    rw [show ((s k : ℂ) * ((P k k).re : ℂ) * (s k : ℂ)) = ((s k * s k * (P k k).re : ℝ) : ℂ) by
      push_cast; ring, this]
    simp
  have hle := det_re_le_one_of_diag_eq_one hQ hQdiag
  have hdetQ : (Dᴴ * P * D).det.re = (∏ k, s k) ^ 2 * P.det.re := by
    rw [hDH, det_mul, det_mul, hD, det_diagonal, ← Complex.ofReal_prod]
    rw [det_eq_ofReal_re hP]
    norm_cast
    ring
  rw [hdetQ] at hle
  have hprod : (∏ k, s k) ^ 2 * ∏ k, d k = 1 := by
    rw [sq, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => hs2 k
  have hdprod : 0 < ∏ k, d k := Finset.prod_pos fun k _ => hdpos k
  have hsprod : 0 < (∏ k, s k) ^ 2 := by
    have : 0 < ∏ k, s k := Finset.prod_pos fun k _ => hspos k
    positivity
  have : P.det.re = (∏ k, s k) ^ 2 * P.det.re * ∏ k, d k := by
    rw [mul_comm ((∏ k, s k) ^ 2) _, mul_assoc, mul_comm _ (∏ k, d k), ← mul_assoc, mul_comm _ (∏ k, d k)]
    rw [show (∏ k, d k) * P.det.re * (∏ k, s k) ^ 2 = P.det.re * ((∏ k, s k) ^ 2 * ∏ k, d k) by ring,
      hprod, mul_one]
  rw [this]
  calc (∏ k, s k) ^ 2 * P.det.re * ∏ k, d k ≤ 1 * ∏ k, d k :=
        mul_le_mul_of_nonneg_right hle hdprod.le
    _ = ∏ k, (P k k).re := one_mul _

end Hadamard

/-! ### The first-slot cofactor at a diagonal position -/

section Cofactor

variable {m : ℕ}

/-- Summing over the permutations sending `0` to `k` is summing over `Perm (Fin m)`. -/
theorem sum_perm_ite_apply_zero_eq (k : Fin (m + 1)) (F : Equiv.Perm (Fin (m + 1)) → ℂ) :
    (∑ π : Equiv.Perm (Fin (m + 1)), if π 0 = k then F π else 0) =
      ∑ e : Equiv.Perm (Fin m), F (Equiv.Perm.decomposeFin.symm (k, e)) := by
  classical
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero]
  rw [Finset.sum_eq_single k]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

/-- **The cofactor of a diagonal entry.** The coefficient of the `(k, k)` entry of the first
matrix in the mixed coefficient is the mixed coefficient of the remaining matrices with the
`k`-th row and column deleted (in the order `a ↦ swap 0 k (a + 1)`). -/
theorem cofactor_self (K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (k : Fin (m + 1)) :
    cofactor K k k = mixedCoefficient (fun i => (K i).submatrix
      (fun a => Equiv.swap 0 k a.succ) (fun a => Equiv.swap 0 k a.succ)) := by
  classical
  rw [mixedCoefficient_eq_sum_sum, cofactor]
  have hsplit : ∀ π : Equiv.Perm (Fin (m + 1)),
      (∑ ρ : Equiv.Perm (Fin (m + 1)), if π 0 = k ∧ ρ 0 = k then
        ((Equiv.Perm.sign π : ℂ) * Equiv.Perm.sign ρ) * ∏ i, K i (π i.succ) (ρ i.succ) else 0) =
      if π 0 = k then (∑ ρ : Equiv.Perm (Fin (m + 1)), if ρ 0 = k then
        ((Equiv.Perm.sign π : ℂ) * Equiv.Perm.sign ρ) * ∏ i, K i (π i.succ) (ρ i.succ)
          else 0) else 0 := by
    intro π
    by_cases h : π 0 = k <;> simp [h]
  simp_rw [hsplit]
  rw [sum_perm_ite_apply_zero_eq]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sum_perm_ite_apply_zero_eq]
  refine Finset.sum_congr rfl fun e' _ => ?_
  simp only [Equiv.Perm.decomposeFin.symm_sign, Equiv.Perm.decomposeFin_symm_apply_succ,
    submatrix_apply]
  congr 1
  by_cases hk : k = 0 <;> simp [hk]

end Cofactor

/-! ### Principal submatrices -/

section Minor

variable {m : ℕ}

/-- `det` of the principal submatrix deleting the `k`-th row and column is `det G · (G⁻¹)ₖₖ`. -/
theorem det_submatrix_swap_succ (G : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hG : IsUnit G.det)
    (k : Fin (m + 1)) :
    (G.submatrix (fun a : Fin m => Equiv.swap 0 k a.succ)
      (fun a : Fin m => Equiv.swap 0 k a.succ)).det = G.det * G⁻¹ k k := by
  classical
  set G' := G.submatrix (Equiv.swap 0 k) (Equiv.swap 0 k) with hG'
  have hsub : G.submatrix (fun a : Fin m => Equiv.swap 0 k a.succ)
      (fun a : Fin m => Equiv.swap 0 k a.succ) =
      G'.submatrix Fin.succ Fin.succ := by
    rw [hG', submatrix_submatrix]
    rfl
  have hdet : G'.det = G.det := det_submatrix_equiv_self (Equiv.swap 0 k) G
  have hinv : G'⁻¹ 0 0 = G⁻¹ k k := by
    rw [hG', inv_submatrix_equiv]
    simp
  have hadj : adjugate G' 0 0 = (G'.submatrix Fin.succ Fin.succ).det := by
    rw [adjugate_fin_succ_eq_det_submatrix]
    simp [Fin.succAbove_zero]
  have hG'u : IsUnit G'.det := hdet ▸ hG
  have hentry : G'⁻¹ 0 0 = Ring.inverse G'.det * adjugate G' 0 0 := by
    rw [Matrix.inv_def]
    simp
  rw [hsub, ← hadj, ← hinv, hentry, ← hdet, ← mul_assoc, Ring.mul_inverse_cancel _ hG'u, one_mul]

end Minor

/-! ### AM–GM in power form -/

theorem prod_le_sum_div_pow {N : ℕ} (y : Fin N → ℝ) (hy : ∀ k, 0 ≤ y k) :
    ∏ k, y k ≤ ((∑ k, y k) / N) ^ N := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp
  have hamgm := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin N)) (fun _ => (1 : ℝ)) y
    (fun _ _ => zero_le_one) (by simp [hN]) (fun k _ => hy k)
  simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hamgm
  have hprod : 0 ≤ ∏ k, y k := Finset.prod_nonneg fun k _ => hy k
  have hx : (∏ k, y k) = ((∏ k, y k) ^ ((N : ℝ)⁻¹)) ^ N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hprod,
      inv_mul_cancel₀ (by exact_mod_cast hN.ne'), Real.rpow_one]
  rw [hx]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hprod _) hamgm N

/-! ### The geometric-mean inequality -/

section Main

/-- The induction step of the geometric-mean inequality for mixed coefficients. -/
theorem prod_det_re_le_mixedCoefficient_re_pow_succ {m : ℕ} (hm : 0 < m)
    (IH : ∀ H : Fin m → Matrix (Fin m) (Fin m) ℂ, (∀ i, (H i).PosDef) →
      ∏ i, (H i).det.re ≤ ((mixedCoefficient H).re / m.factorial) ^ m)
    (H : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hH : ∀ i, (H i).PosDef) :
    ∏ i, (H i).det.re ≤ ((mixedCoefficient H).re / (m + 1).factorial) ^ (m + 1) := by
  classical
  have hA := (hH 0).isHermitian
  set U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    (hA.eigenvectorUnitary : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) with hUdef
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  set L : Fin (m + 1) → ℝ := hA.eigenvalues with hLdef
  have hLpos : ∀ k, 0 < L k := fun k => (hH 0).eigenvalues_pos k
  have hspec : H 0 = U * diagonal (fun k => (L k : ℂ)) * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  set G : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := fun i => star U * H i * U
    with hGdef
  have hGmc : mixedCoefficient G = mixedCoefficient H := by
    rw [hGdef, mixedCoefficient_mul_mul, ← det_mul, hUU, det_one, one_mul]
  have hG0 : G 0 = diagonal (fun k => (L k : ℂ)) := by
    simp only [hGdef]
    rw [hspec]
    simp only [← mul_assoc, hUU, one_mul]
    rw [mul_assoc, hUU, mul_one]
  have hinj : Function.Injective U.mulVec := by
    intro x y hxy
    have := congrArg (fun v => (star U).mulVec v) hxy
    simpa [mulVec_mulVec, hUU] using this
  have hGpos : ∀ i, (G i).PosDef := by
    intro i
    have := (hH i).conjTranspose_mul_mul_same hinj
    simpa [hGdef, star_eq_conjTranspose] using this
  have hGdet : ∀ i, (G i).det = (H i).det := by
    intro i
    simp only [hGdef, det_mul]
    rw [mul_comm (det (star U)), mul_assoc, ← det_mul, hUU, det_one, mul_one]
  set K : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := fun i => G i.succ with hKdef
  have hGcons : G = Fin.cons (G 0) K := (Fin.cons_self_tail G).symm
  have hmc : mixedCoefficient H = ∑ k, (L k : ℂ) * cofactor K k k := by
    rw [← hGmc, hGcons, mixedCoefficient_cons, hG0]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [diagonal_apply]
  set M : Fin (m + 1) → Fin m → Matrix (Fin m) (Fin m) ℂ := fun k i =>
    (K i).submatrix (fun a : Fin m => Equiv.swap 0 k a.succ)
      (fun a : Fin m => Equiv.swap 0 k a.succ) with hMdef
  have hcof : ∀ k, cofactor K k k = mixedCoefficient (M k) := fun k => cofactor_self K k
  have hKpos : ∀ i, (K i).PosDef := fun i => hGpos i.succ
  have hMpos : ∀ k i, (M k i).PosDef := by
    intro k i
    exact (hKpos i).submatrix fun a b h => Fin.succ_injective _ ((Equiv.swap 0 k).injective h)
  set c : Fin (m + 1) → ℝ := fun k => (mixedCoefficient (M k)).re with hcdef
  have hc : ∀ k, 0 ≤ c k := fun k =>
    mixedCoefficient_re_nonneg _ fun i => (hMpos k i).posSemidef
  have hIH : ∀ k, ∏ i, (M k i).det.re ≤ (c k / m.factorial) ^ m := fun k => IH (M k) (hMpos k)
  set δ : Fin m → ℝ := fun i => (K i).det.re with hδdef
  have hδ : ∀ i, 0 < δ i := fun i => det_re_pos (hKpos i)
  set e : Fin (m + 1) → Fin m → ℝ := fun k i => ((K i)⁻¹ k k).re with hedef
  have he : ∀ k i, 0 < e k i := fun k i => diag_re_pos (hKpos i).inv k
  have hMdet : ∀ k i, (M k i).det.re = δ i * e k i := by
    intro k i
    have hu : IsUnit (K i).det := isUnit_iff_ne_zero.mpr (hKpos i).det_pos.ne'
    simp only [hMdef]
    rw [det_submatrix_swap_succ (K i) hu k, det_eq_ofReal_re (hKpos i),
      diag_eq_ofReal_re (hKpos i).inv k]
    simp [hδdef, hedef]
  have hHad : ∀ i, 1 ≤ δ i * ∏ k, e k i := by
    intro i
    have h := det_re_le_prod_diag_re (hKpos i).inv
    rw [det_nonsing_inv, Ring.inverse_eq_inv', det_eq_ofReal_re (hKpos i),
      ← Complex.ofReal_inv, Complex.ofReal_re] at h
    calc (1 : ℝ) = δ i * (δ i)⁻¹ := (mul_inv_cancel₀ (hδ i).ne').symm
      _ ≤ δ i * ∏ k, e k i := mul_le_mul_of_nonneg_left h (hδ i).le
  have hmcre : (mixedCoefficient H).re = ∑ k, L k * c k := by
    rw [hmc, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hcof k, Complex.re_ofReal_mul]
  have hdetH : ∏ i, (H i).det.re = (∏ k, L k) * ∏ i, δ i := by
    rw [Fin.prod_univ_succ]
    have h0 : (H 0).det.re = ∏ k, L k := by
      rw [← hGdet 0, hG0, det_diagonal]
      norm_cast
    rw [h0]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← hGdet i.succ]
  set y : Fin (m + 1) → ℝ := fun k => L k * c k / m.factorial with hydef
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hy : ∀ k, 0 ≤ y k := fun k => div_nonneg (mul_nonneg (hLpos k).le (hc k)) hfac.le
  have hamgm := prod_le_sum_div_pow y hy
  have hsum : (∑ k, y k) / ((m + 1 : ℕ) : ℝ) = (∑ k, L k * c k) / ((m + 1).factorial : ℝ) := by
    rw [Nat.factorial_succ, hydef]
    simp only
    rw [← Finset.sum_div]
    push_cast
    rw [div_div, mul_comm ((m : ℝ) + 1)]
  have hlow : (∏ k, L k) * ∏ i, δ i ≤ ∏ k, y k := by
    have hpowle : ((∏ k, L k) * ∏ i, δ i) ^ m ≤ (∏ k, y k) ^ m := by
      calc ((∏ k, L k) * ∏ i, δ i) ^ m = (∏ k, L k) ^ m * ∏ i, δ i ^ m := by
            rw [mul_pow, Finset.prod_pow]
        _ ≤ (∏ k, L k) ^ m * ∏ i, (δ i ^ (m + 1) * ∏ k, e k i) := by
            refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
              (fun i _ => pow_nonneg (hδ i).le m) fun i _ => ?_)
              (pow_nonneg (Finset.prod_nonneg fun k _ => (hLpos k).le) m)
            rw [pow_succ, mul_assoc]
            calc δ i ^ m = δ i ^ m * 1 := (mul_one _).symm
              _ ≤ δ i ^ m * (δ i * ∏ k, e k i) :=
                mul_le_mul_of_nonneg_left (hHad i) (pow_nonneg (hδ i).le m)
        _ = (∏ k, L k) ^ m * ∏ k, ∏ i, (δ i * e k i) := by
            congr 1
            rw [Finset.prod_comm]
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ (∏ k, L k) ^ m * ∏ k, (c k / m.factorial) ^ m := by
            refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod
              (fun k _ => Finset.prod_nonneg fun i _ => (mul_pos (hδ i) (he k i)).le)
              fun k _ => ?_)
              (pow_nonneg (Finset.prod_nonneg fun k _ => (hLpos k).le) m)
            have := hIH k
            simp only [hMdet] at this
            exact this
        _ = (∏ k, y k) ^ m := by
            rw [← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
            refine Finset.prod_congr rfl fun k _ => ?_
            rw [hydef]
            simp only
            rw [← mul_pow, mul_div_assoc]
    exact le_of_pow_le_pow_left₀ hm.ne' (Finset.prod_nonneg fun k _ => hy k) hpowle
  calc ∏ i, (H i).det.re = (∏ k, L k) * ∏ i, δ i := hdetH
    _ ≤ ∏ k, y k := hlow
    _ ≤ ((∑ k, y k) / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) := by
        simpa using hamgm
    _ = ((mixedCoefficient H).re / (m + 1).factorial) ^ (m + 1) := by
        rw [hsum, hmcre]

/-- **Geometric-mean inequality for mixed discriminants** (power form): for positive definite
Hermitian `Hᵢ`, `∏ᵢ det Hᵢ ≤ (Re (mixedCoefficient H) / n!)ⁿ`. -/
theorem prod_det_re_le_mixedCoefficient_re_pow :
    ∀ (n : ℕ) (H : Fin n → Matrix (Fin n) (Fin n) ℂ), (∀ i, (H i).PosDef) →
      ∏ i, (H i).det.re ≤ ((mixedCoefficient H).re / n.factorial) ^ n
  | 0, H, _ => by
      have h0 : mixedCoefficient H = 1 := by
        simp only [mixedCoefficient, Finset.univ_unique, Finset.sum_singleton]
        exact Matrix.det_isEmpty
      simp [h0]
  | 1, H, _ => by
      have hfun : H = fun _ => H 0 := funext fun i => by rw [Subsingleton.elim i 0]
      rw [hfun, mixedCoefficient_diagonal]
      simp
  | m + 2, H, hH =>
      prod_det_re_le_mixedCoefficient_re_pow_succ (Nat.succ_pos m)
        (prod_det_re_le_mixedCoefficient_re_pow (m + 1)) H hH

/-- **Geometric-mean inequality for mixed discriminants** (Gårding's inequality for `det`): for
positive definite Hermitian `n × n` matrices `Hᵢ`,
`n! ∏ᵢ (det Hᵢ)^{1/n} ≤ Re (mixedCoefficient H)`. -/
theorem factorial_mul_prod_det_rpow_le_mixedCoefficient_re (n : ℕ)
    (H : Fin n → Matrix (Fin n) (Fin n) ℂ) (hH : ∀ i, (H i).PosDef) :
    (n.factorial : ℝ) * ∏ i, (H i).det.re ^ ((n : ℝ)⁻¹) ≤ (mixedCoefficient H).re := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : mixedCoefficient H = 1 := by
      simp only [mixedCoefficient, Finset.univ_unique, Finset.sum_singleton]
      exact Matrix.det_isEmpty
    simp [h0]
  have hpow := prod_det_re_le_mixedCoefficient_re_pow n H hH
  have hdet : ∀ i, 0 ≤ (H i).det.re := fun i => (det_re_pos (hH i)).le
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hmc : 0 ≤ (mixedCoefficient H).re :=
    mixedCoefficient_re_nonneg _ fun i => (hH i).posSemidef
  have hq : 0 ≤ (mixedCoefficient H).re / n.factorial := div_nonneg hmc hfac.le
  have hroot : (∏ i, (H i).det.re) ^ ((n : ℝ)⁻¹) ≤ (mixedCoefficient H).re / n.factorial := by
    calc (∏ i, (H i).det.re) ^ ((n : ℝ)⁻¹)
        ≤ (((mixedCoefficient H).re / n.factorial) ^ n) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => hdet i) hpow (by positivity)
      _ = (mixedCoefficient H).re / n.factorial := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hq, mul_inv_cancel₀ (by exact_mod_cast hn.ne'),
            Real.rpow_one]
  rw [Real.finsetProd_rpow _ _ fun i _ => hdet i]
  rw [le_div_iff₀ hfac] at hroot
  linarith [hroot]

end Main

end SGPT.NPP.LogConcavity
