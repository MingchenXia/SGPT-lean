import SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
import SGPT.Foundations.Analysis.Pending.ConcentrationMassComparison
import SGPT.Foundations.Analysis.Pending.TopDegreeDensity

/-!
# The density bound on the contact set, in product coordinates

Blueprint `tok-wn-conv6:inner-density` (chapter `claude-tok-wn-conv6`); source WN21, proof of
Proposition 6.4: on `D_k`, `(θ̃ + ddᶜg_k)^{n+1} ≤ θ̃^{n+1} + (n + 1) θ̃ⁿ ∧ ω_k`.

On `ℂⁿ⁺¹ = ℂⁿ × ℂ` (`prodModelEquiv n 1`) let `ιF : ℂⁿ → ℂⁿ⁺¹` be the inclusion of the first factor.
For real `(1,1)`-forms `B` on `ℂⁿ⁺¹` and `G` on `ℂ`, with `A = B + p₂^*G`:

* `normalizedHermitianMatrix_comp_inclFst`: the coefficient matrix of `ιF^*B` is the upper left
  `n × n` block of that of `B`;
* `normalizedHermitianMatrix_comp_projSnd_apply`: the matrix of `p₂^*G` has the single entry
  `π G(e, ie)` at `(last, last)`;
* `det_add_single_last`: `det(H + t E_{last,last}) = det H + t det H_{zz}` (Laplace expansion);
* `actualTopPowerDensity_le` (`tok-wn-conv6:inner-density`): if `ιF^*B ≥ 0` and the density of
  `G` is `r - r'` with `r' ≥ 0`, then `A^{n+1} ≤ B^{n+1} + (n+1) (ιF^*B)ⁿ · r` as densities.
-/

set_option autoImplicit false

noncomputable section

open Set Matrix
open scoped ComplexOrder

namespace SGPT.Okounkov.TranscendentalWN.Algebra

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open SGPT.Foundations.Analysis.Pending.ProductMixedMeasure
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.TopDegreeDensity

variable {n : ℕ}

/-- The inclusion `ℂⁿ → ℂⁿ⁺¹`, `v ↦ (v, 0)`. -/
def inclFst (n : ℕ) : ComplexModel n →L[ℝ] ComplexModel (n + 1) :=
  (((prodModelEquiv n 1 : (ComplexModel n × ComplexModel 1) →L[ℂ] ComplexModel (n + 1))).comp
    (ContinuousLinearMap.inl ℂ (ComplexModel n) (ComplexModel 1))).restrictScalars ℝ

theorem inclFst_apply (v : ComplexModel n) : inclFst n v = prodModelEquiv n 1 (v, 0) := rfl

theorem inclFst_smul (c : ℂ) (v : ComplexModel n) : inclFst n (c • v) = c • inclFst n v := by
  simp [inclFst_apply, ← map_smul, Prod.smul_mk]

theorem inclFst_coordinateVector (j : Fin n) :
    inclFst n (coordinateVector j) = coordinateVector (Fin.castAdd 1 j) := by
  rw [inclFst_apply, ← prodModelEquiv_symm_coordinateVector_castAdd (m := 1) j,
    ContinuousLinearEquiv.apply_symm_apply]

theorem projSnd_inclFst (v : ComplexModel n) : projSnd n 1 (inclFst n v) = 0 := by
  rw [projSnd_apply, inclFst_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- **The matrix of `ιF^*B` is the upper left block.** -/
theorem normalizedHermitianMatrix_comp_inclFst (B : CoordinateRealTwoForm (n + 1)) :
    normalizedHermitianMatrix (B.compContinuousLinearMap (inclFst n)) =
      (normalizedHermitianMatrix B).submatrix Fin.castSucc Fin.castSucc := by
  ext j k
  simp only [normalizedHermitianMatrix, submatrix_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, comp_vec, inclFst_smul,
    inclFst_coordinateVector]
  rfl

theorem castAdd_eq_castSucc (j : Fin n) : Fin.castAdd 1 j = Fin.castSucc j := rfl

theorem natAdd_zero_eq_last : Fin.natAdd n (0 : Fin 1) = Fin.last n := by
  ext; simp

/-- **The matrix of `p₂^*G`**: the single entry `H(G)₀₀` at `(last, last)`. -/
theorem normalizedHermitianMatrix_comp_projSnd_apply (G : CoordinateRealTwoForm 1)
    (i j : Fin (n + 1)) :
    normalizedHermitianMatrix (G.compContinuousLinearMap (projSnd n 1)) i j =
      if i = Fin.last n ∧ j = Fin.last n then normalizedHermitianMatrix G 0 0 else 0 := by
  have hcast : ∀ a : Fin n, projSnd n 1 (coordinateVector (Fin.castAdd 1 a)) = 0 :=
    fun a => projSnd_castAdd a
  have hlast : projSnd n 1 (coordinateVector (Fin.last n)) = coordinateVector (0 : Fin 1) := by
    rw [← natAdd_zero_eq_last]; exact projSnd_natAdd 0
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [normalizedHermitianMatrix, ContinuousAlternatingMap.compContinuousLinearMap_apply,
        comp_vec, projSnd_smul, hlast, and_self, if_true]
    | cast j =>
      have hj : Fin.castAdd 1 j ≠ Fin.last n := Fin.castSucc_ne_last j
      simp only [normalizedHermitianMatrix, ContinuousAlternatingMap.compContinuousLinearMap_apply,
        comp_vec, projSnd_smul, ← castAdd_eq_castSucc, hcast, smul_zero, apply_vec_zero_right,
        Complex.ofReal_zero, mul_zero, sub_zero, hj, and_false, if_false]
  | cast i =>
    have hi : Fin.castAdd 1 i ≠ Fin.last n := Fin.castSucc_ne_last i
    simp only [normalizedHermitianMatrix, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      comp_vec, projSnd_smul, ← castAdd_eq_castSucc, hcast, apply_vec_zero_left,
      Complex.ofReal_zero, mul_zero, sub_zero, hi, false_and, if_false]

theorem normalizedHermitianMatrix_add (A B : CoordinateRealTwoForm n) :
    normalizedHermitianMatrix (A + B) = normalizedHermitianMatrix A + normalizedHermitianMatrix B := by
  ext j k
  simp only [normalizedHermitianMatrix, ContinuousAlternatingMap.add_apply, Matrix.add_apply,
    Complex.ofReal_add]
  ring

/-- **Laplace expansion along the last row**: `det(H + t E_{last,last}) = det H + t det H_{zz}`. -/
theorem det_add_single_last (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (t : ℂ) :
    (H + Matrix.of fun i j => if i = Fin.last n ∧ j = Fin.last n then t else 0).det =
      H.det + t * (H.submatrix Fin.castSucc Fin.castSucc).det := by
  set E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun i j => if i = Fin.last n ∧ j = Fin.last n then t else 0 with hE
  have hrow : H + E = H.updateRow (Fin.last n) (H (Fin.last n) + Pi.single (Fin.last n) t) := by
    ext i j
    by_cases hi : i = Fin.last n
    · subst hi
      simp only [Matrix.add_apply, hE, Matrix.of_apply, true_and, updateRow_self, Pi.add_apply]
      by_cases hj : j = Fin.last n
      · subst hj; simp
      · simp [hj]
    · simp [hE, hi]
  rw [hrow, det_updateRow_add, updateRow_eq_self]
  congr 1
  rw [det_succ_row _ (Fin.last n)]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp only [updateRow_self, Pi.single_eq_same, Fin.val_last, Fin.succAbove_last]
    have hsub : (H.updateRow (Fin.last n) (Pi.single (Fin.last n) t)).submatrix Fin.castSucc
        Fin.castSucc = H.submatrix Fin.castSucc Fin.castSucc := by
      ext i j
      simp
    rw [hsub, ← two_mul, pow_mul]
    simp
  · intro j _ hj
    simp [updateRow_self, hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem isOneOne_add {A B : CoordinateRealTwoForm n} (hA : IsOneOne A) (hB : IsOneOne B) :
    IsOneOne (A + B) := fun u v => by
  simp only [ContinuousAlternatingMap.add_apply, hA u v, hB u v]

/-- The `(0,0)` entry of the matrix of a `(1,1)`-form on `ℂ` is `π` times its density. -/
theorem normalizedHermitianMatrix_one (G : CoordinateRealTwoForm 1) :
    normalizedHermitianMatrix G 0 0 = ((Real.pi * actualTopPowerDensity G : ℝ) : ℂ) := by
  have h0 : G ![coordinateVector (0 : Fin 1), coordinateVector (0 : Fin 1)] = 0 :=
    G.map_eq_zero_of_eq _ (i := 0) (j := 1) (by simp) (by decide)
  rw [actualTopPowerDensity_one]
  simp only [normalizedHermitianMatrix, h0, Complex.ofReal_zero, mul_zero, sub_zero,
    Complex.ofReal_mul]

/-- **`tok-wn-conv6:inner-density`**: if `ιF^*B ≥ 0` and the density of `G` is `r - r'` with
`r' ≥ 0`, then `(B + p₂^*G)^{n+1} ≤ B^{n+1} + (n + 1) (ιF^*B)ⁿ · r`. -/
theorem actualTopPowerDensity_le (B : CoordinateRealTwoForm (n + 1)) (G : CoordinateRealTwoForm 1)
    (hB : IsOneOne B) (hG : IsOneOne G)
    (hpos : CoefficientSemipositive (B.compContinuousLinearMap (inclFst n))) {r r' : ℝ}
    (hr' : 0 ≤ r') (hGr : actualTopPowerDensity G = r - r') :
    actualTopPowerDensity (B + G.compContinuousLinearMap (projSnd n 1)) ≤
      actualTopPowerDensity B +
        ((n + 1 : ℕ) : ℝ) * actualTopPowerDensity (B.compContinuousLinearMap (inclFst n)) * r := by
  have hGp : IsOneOne (G.compContinuousLinearMap (projSnd n 1)) := isOneOne_comp_projSnd hG
  have hBi : IsOneOne (B.compContinuousLinearMap (inclFst n)) :=
    ProductTestForms.isOneOne_compContinuousLinearMap hB _ fun v => inclFst_smul Complex.I v
  rw [ConcentrationMassComparison.actualTopPowerDensity_eq_det (isOneOne_add hB hGp),
    ConcentrationMassComparison.actualTopPowerDensity_eq_det hB,
    ConcentrationMassComparison.actualTopPowerDensity_eq_det hBi,
    normalizedHermitianMatrix_add]
  have hmat : normalizedHermitianMatrix (G.compContinuousLinearMap (projSnd n 1)) =
      Matrix.of fun i j => if i = Fin.last n ∧ j = Fin.last n then
        ((Real.pi * actualTopPowerDensity G : ℝ) : ℂ) else 0 := by
    ext i j
    rw [normalizedHermitianMatrix_comp_projSnd_apply, normalizedHermitianMatrix_one]
    rfl
  rw [hmat, det_add_single_last, ← normalizedHermitianMatrix_comp_inclFst]
  set S := normalizedHermitianMatrix (B.compContinuousLinearMap (inclFst n))
  have hS : 0 ≤ S.det := (normalizedHermitianMatrix_posSemidef ⟨hBi, hpos⟩).det_nonneg
  have hSre : 0 ≤ S.det.re := (Complex.le_def.mp hS).1
  have hSim : S.det.im = 0 := ((Complex.le_def.mp hS).2).symm
  rw [Complex.add_re, Complex.re_ofReal_mul, hGr]
  have hpi := Real.pi_pos
  have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [hfac, pow_succ]
  push_cast
  have key : (n + 1 : ℝ) * n.factorial / (Real.pi ^ n * Real.pi) * (Real.pi * (r - r') * S.det.re) =
      (n + 1 : ℝ) * (n.factorial / Real.pi ^ n * S.det.re) * (r - r') := by
    field_simp
  rw [mul_add, key]
  have h1 : 0 ≤ (n.factorial : ℝ) / Real.pi ^ n * S.det.re := by positivity
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ n + 1) h1) hr']

end SGPT.Okounkov.TranscendentalWN.Algebra
