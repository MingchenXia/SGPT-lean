import SGPT.Foundations.Analysis.Pending.BlowupMonomialCharts
import SGPT.Foundations.Analysis.Pending.DivisorialChangeOfVariables
import SGPT.Foundations.Analysis.Pending.CoordinateDensityGeneral

set_option autoImplicit false

/-!
# Actual differential and determinant of the existing monomial blowup map

The finite-coordinate determinant is computed on all points, including
the exceptional hyperplane.  This is a geometric primitive for the
existing finite smooth-centre blowup charts, not a factorization of
arbitrary modifications or an intrinsic all-prime-divisor dictionary.
-/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.BlowupMonomialJacobian

open FirstPass BlowupMonomialCharts DivisorialChangeOfVariables

/-- The actual complex derivative of the existing monomial map is
computed coordinatewise without a nonzero normal-coordinate assumption. -/
theorem fderiv_monomial_apply {n : ℕ} (k : ℕ) (j : Fin n)
    (w v : ComplexModel n) (i : Fin n) :
    (fderiv ℂ (monomial k j) w v) i =
      if k ≤ i.1 ∧ i ≠ j then v i * w j + w i * v j else v i := by
  classical
  let pr (a : Fin n) : ComplexModel n →L[ℂ] ℂ := EuclideanSpace.proj a
  have hF := (contDiff_monomial k j).differentiable (by simp) w
  have hcomp : HasFDerivAt (fun z => monomial k j z i)
      ((pr i).comp (fderiv ℂ (monomial k j) w)) w :=
    (pr i).hasFDerivAt.comp w hF.hasFDerivAt
  by_cases hi : k ≤ i.1 ∧ i ≠ j
  · have heq : (fun z => monomial k j z i) = (fun z : ComplexModel n => z i * z j) := by
      funext z
      simp [monomial_apply, hi]
    rw [heq] at hcomp
    have hp : HasFDerivAt (fun z : ComplexModel n => z i * z j)
        (w i • pr j + w j • pr i) w := (pr i).hasFDerivAt.mul (pr j).hasFDerivAt
    have hval := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v) (hcomp.unique hp)
    simpa [pr, hi, mul_comm, add_comm] using hval
  · have heq : (fun z => monomial k j z i) = (fun z : ComplexModel n => z i) := by
      funext z
      simp [monomial_apply, hi]
    rw [heq] at hcomp
    have hval := congrArg (fun L : ComplexModel n →L[ℂ] ℂ => L v)
      (hcomp.unique (pr i).hasFDerivAt)
    simpa [pr, hi] using hval

private theorem exists_moved_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin n)
    (hσ : σ ≠ 1) : ∃ a : Fin n, a ≠ j ∧ σ a ≠ a := by
  classical
  by_contra hnot
  have hfix (a : Fin n) (ha : a ≠ j) : σ a = a := by
    by_contra hmove
    exact hnot ⟨a, ha, hmove⟩
  have hj : σ j = j := by
    by_cases hh : σ j = j
    · exact hh
    · exact σ.injective (hfix (σ j) hh)
  apply hσ
  apply Equiv.ext
  intro a
  by_cases ha : a = j
  · simpa [ha] using hj
  · exact hfix a ha

private theorem card_multiplied_coordinates {n : ℕ} (k : ℕ) (j : Fin n) (hj : k ≤ j.1) :
    (Finset.univ.filter (fun i : Fin n => k ≤ i.1 ∧ i ≠ j)).card = n - k - 1 := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter (fun i => k ≤ i.1)
  have hT : T.card = n - k := by
    let e : T ≃ Fin (n - k) :=
      { toFun := fun i => ⟨i.val.val - k, by
          have hi := (Finset.mem_filter.mp i.property).2
          have hilt := i.val.isLt
          omega⟩
        invFun := fun a => ⟨⟨a.val + k, by
          have halt := a.isLt
          have hjlt := j.isLt
          omega⟩, by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, by change k ≤ a.val + k; omega⟩⟩
        left_inv := fun i => by
          apply Subtype.ext
          apply Fin.ext
          have hi := (Finset.mem_filter.mp i.property).2
          change i.val.val - k + k = i.val.val
          omega
        right_inv := fun a => by
          apply Fin.ext
          change a.val + k - k = a.val
          omega }
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_congr e
  have hjT : j ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have heq : Finset.univ.filter (fun i : Fin n => k ≤ i.1 ∧ i ≠ j) = T.erase j := by
    ext i
    simp [T, and_comm]
  rw [heq, Finset.card_erase_of_mem hjT, hT]

/-- The exact actual Jacobian of the existing blowup monomial chart.
No division by the normal coordinate is used, so the formula includes
the exceptional hyperplane and codimension-one identity chart. -/
theorem complexJacobian_monomial {n : ℕ} (k : ℕ) (j : Fin n)
    (hj : k ≤ j.1) (w : ComplexModel n) :
    complexJacobian (monomial k j) w = w j ^ (n - k - 1) := by
  classical
  let M := FirstPass.MongeAmpere.standardMatrix
    (fderiv ℂ (monomial k j) w).toLinearMap
  have hoff (a b : Fin n) (hb : b ≠ j) (hab : a ≠ b) : M a b = 0 := by
    change FirstPass.MongeAmpere.standardMatrix
      (fderiv ℂ (monomial k j) w).toLinearMap a b = 0
    rw [FirstPass.MongeAmpere.standardMatrix_apply]
    change (fderiv ℂ (monomial k j) w (FirstPass.MongeAmpere.coordinateVector b)) a = 0
    rw [fderiv_monomial_apply]
    split_ifs <;> simp [FirstPass.MongeAmpere.coordinateVector, hab, hb.symm]
  have hdiag (a : Fin n) : M a a = if k ≤ a.1 ∧ a ≠ j then w j else 1 := by
    change FirstPass.MongeAmpere.standardMatrix
      (fderiv ℂ (monomial k j) w).toLinearMap a a = _
    rw [FirstPass.MongeAmpere.standardMatrix_apply]
    change (fderiv ℂ (monomial k j) w (FirstPass.MongeAmpere.coordinateVector a)) a = _
    rw [fderiv_monomial_apply]
    by_cases ha : k ≤ a.1 ∧ a ≠ j
    · simp [ha, FirstPass.MongeAmpere.coordinateVector, ha.2.symm]
    · simp [ha, FirstPass.MongeAmpere.coordinateVector]
  have hdet : M.det = ∏ a : Fin n, M a a := by
    rw [Matrix.det_apply]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp
    · intro σ _ hσ
      obtain ⟨a, haj, hmove⟩ := exists_moved_ne σ j hσ
      have hz : ∏ i : Fin n, M (σ i) i = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        exact hoff (σ a) a haj hmove
      rw [hz, smul_zero]
    · simp
  have hJ : complexJacobian (monomial k j) w = M.det := by
    exact (FirstPass.MongeAmpere.det_standardMatrix
      (fderiv ℂ (monomial k j) w).toLinearMap).symm
  rw [hJ, hdet]
  simp_rw [hdiag]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  rw [card_multiplied_coordinates k j hj]

end SGPT.Foundations.Analysis.Pending.BlowupMonomialJacobian
