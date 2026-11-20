import SGPT.AlmostSemigroup.Basic

/-! Actual finite zero slice forces original positive height.
Blueprint: okounkov-finite-zero-slice.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SGPT.Okounkov.BodyFromGrowth
open Set SGPT.AlmostSemigroup

/-- Finiteness of the SAME actual zero slice rules out nonzero original height-zero points. -/
theorem zero_height_eq_zero_of_finite_slice {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hfinite : (slice (S : Set ((Fin n → ℤ) × ℤ)) 0).Finite)
    {z : (Fin n → ℤ) × ℤ} (hz : z ∈ S) (hz0 : z.2 = 0) : z = 0 := by
  classical
  rcases z with ⟨x,d⟩
  dsimp at hz0
  subst d
  have hx : x = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i : Fin n, x i ≠ 0 := by
      by_contra h
      apply hne
      ext i
      simpa using not_exists.mp h i
    let g : ℕ → (Fin n → ℤ) := fun k => (k+1) • x
    have hmem (k : ℕ) : (g k,0) ∈ S := by
      induction k with
      | zero => simpa only [g, zero_add, one_nsmul] using hz
      | succ k ih =>
        have hadd := S.add_mem ih hz
        simpa only [g, Prod.mk_add_mk, add_zero, succ_nsmul] using hadd
    have hinj : Function.Injective g := by
      intro k l hkl
      have heq := congrFun hkl i
      change (k+1) • x i = (l+1) • x i at heq
      simp only [nsmul_eq_mul] at heq
      have heq' := mul_right_cancel₀ hi heq
      exact Nat.succ.inj (by exact_mod_cast heq')
    exact (Set.infinite_range_of_injective hinj) (hfinite.subset (by
      rintro _ ⟨k,rfl⟩
      exact hmem k))
  exact Prod.ext hx rfl

/-- Actual nonnegative degrees and a finite original zero slice manufacture positive original height. -/
theorem positiveHeight_of_nonnegative_finiteZeroSlice {n : ℕ}
    (S : AddSubsemigroup ((Fin n → ℤ) × ℤ))
    (hnonneg : ∀ z ∈ S, 0 ≤ z.2)
    (hfinite : (slice (S : Set ((Fin n → ℤ) × ℤ)) 0).Finite) :
    ∀ z ∈ S, z = 0 ∨ 0 < z.2 := by
  intro z hz
  by_cases hz0 : z.2 = 0
  · exact Or.inl (zero_height_eq_zero_of_finite_slice S hfinite hz hz0)
  · exact Or.inr (lt_of_le_of_ne (hnonneg z hz) (Ne.symm hz0))

end SGPT.Okounkov.BodyFromGrowth
