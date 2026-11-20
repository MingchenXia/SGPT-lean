import SGPT.Toric.ToricFaceFiniteGenerators
import Mathlib.Analysis.Convex.Combination

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set
open scoped BigOperators

/-- A genuine extreme face contains every positive-weight term of an actual
finite convex combination in it. The remaining normalized point is produced
inside the original convex set; no face-membership certificate is supplied. -/
theorem mem_extreme_of_sum_smul_mem
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P F : Set E} (hP : Convex ℝ P) (hF : IsExtreme ℝ P F)
    {I : Type*} [Fintype I] (w : I → ℝ) (p : I → E)
    (hw : ∀ j, 0 ≤ w j) (hws : ∑ j, w j = 1) (hp : ∀ j, p j ∈ P)
    (hz : (∑ j, w j • p j) ∈ F) (i : I) (hi : 0 < w i) : p i ∈ F := by
  classical
  have hwle : w i ≤ 1 := by
    rw [← hws]
    exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  have hsum : (∑ j ∈ Finset.univ.erase i, w j) = 1 - w i := by
    have heq := Finset.sum_erase_add Finset.univ w (Finset.mem_univ i)
    rw [hws] at heq
    linarith
  by_cases hwi : w i = 1
  · have hrest : ∀ j ∈ Finset.univ.erase i, w j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw j)).mp (by simpa [hwi] using hsum)
    have hrestp : (∑ j ∈ Finset.univ.erase i, w j • p j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hrest j hj, zero_smul]
    have heq := Finset.sum_erase_add Finset.univ (fun j => w j • p j) (Finset.mem_univ i)
    rw [hrestp, hwi, one_smul, zero_add] at heq
    rwa [← heq] at hz
  · have hbi : 0 < 1 - w i := sub_pos.mpr (lt_of_le_of_ne hwle hwi)
    let q := (Finset.univ.erase i).centerMass w p
    have hq : q ∈ P := hP.centerMass_mem (fun j _ => hw j)
      (by rw [hsum]; exact hbi) (fun j _ => hp j)
    have hqeq : (1 - w i) • q = ∑ j ∈ Finset.univ.erase i, w j • p j := by
      dsimp only [q, Finset.centerMass]
      rw [hsum, smul_smul, mul_inv_cancel₀ hbi.ne', one_smul]
    apply hF.left_mem_of_mem_openSegment (hp i) hq hz
    refine ⟨w i, 1 - w i, hi, hbi, by ring, ?_⟩
    rw [hqeq]
    exact (Finset.add_sum_erase Finset.univ (fun j => w j • p j) (Finset.mem_univ i))

end SGPT.Toric
