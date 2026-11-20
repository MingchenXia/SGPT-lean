import SGPT.AlmostSemigroup.Basic

/-! Genuine norm cone for EACH actual finite original positive source set.
Blueprint: okounkov-finite-norm-cone.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Okounkov.BodyFromGrowth
open Set SGPT.AlmostSemigroup
open scoped BigOperators

/-- The actual norm inequality manufactures ALL original admissible-cone fields. -/
def originalNormCone (n : ℕ) (M : ℝ) : AdmissibleCone n where
  cone := {
    carrier := {z | ‖z.1‖ ≤ M*z.2 ∧ 0 ≤ z.2}
    smul_mem' := by
      rintro c hc z ⟨hn,ht⟩
      constructor
      · change ‖c • z.1‖ ≤ M*(c*z.2)
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc]
        nlinarith
      · change 0 ≤ c*z.2
        exact mul_nonneg hc.le ht
    add_mem' := by
      rintro x ⟨hx,hxt⟩ y ⟨hy,hyt⟩
      constructor
      · change ‖x.1+y.1‖ ≤ M*(x.2+y.2)
        exact (norm_add_le _ _).trans (by nlinarith)
      · exact add_nonneg hxt hyt }
  closed := by
    change IsClosed {z : (Fin n → ℝ) × ℝ | ‖z.1‖ ≤ M*z.2 ∧ 0 ≤ z.2}
    exact (isClosed_le continuous_fst.norm (continuous_const.mul continuous_snd)).inter
      (isClosed_le continuous_const continuous_snd)
  nonnegativeHeight := fun _ h => h.2
  zeroHeight := by
    intro x hx
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa only [mul_zero] using hx.1) (norm_nonneg x)

/-- The bound uses only the SAME actual finite original spatial coordinates. -/
def finiteSourceNormBound {n : ℕ} (R : Finset ((Fin n → ℤ) × ℤ)) : ℝ :=
  ∑ z ∈ R, ‖fun j : Fin n => (z.1 j : ℝ)‖

/-- The SAME genuine finite norm sum is nonnegative. -/
theorem finiteSourceNormBound_nonneg {n : ℕ} (R : Finset ((Fin n → ℤ) × ℤ)) :
    0 ≤ finiteSourceNormBound R := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- The ENTIRE actual generated finite original semigroup lies in its manufactured actual norm cone. -/
theorem finiteGenerated_le_normCone {n : ℕ} (R : Finset ((Fin n → ℤ) × ℤ))
    (hR : ∀ z ∈ R, 0 < z.2) :
    AddSubsemigroup.closure (R : Set ((Fin n → ℤ) × ℤ)) ≤
      latticePoints (originalNormCone n (finiteSourceNormBound R)).cone := by
  apply AddSubsemigroup.closure_le.mpr
  intro z hz
  change ‖fun j : Fin n => (z.1 j : ℝ)‖ ≤ finiteSourceNormBound R * (z.2 : ℝ) ∧ 0 ≤ (z.2 : ℝ)
  have hdZ : (1:ℤ) ≤ z.2 := hR z hz
  have hd : (1:ℝ) ≤ (z.2:ℝ) := by exact_mod_cast hdZ
  refine ⟨?_, le_trans zero_le_one hd⟩
  calc ‖fun j : Fin n => (z.1 j : ℝ)‖ ≤ finiteSourceNormBound R :=
      by
        exact Finset.single_le_sum
          (f := fun w : (Fin n → ℤ) × ℤ => ‖fun j : Fin n => (w.1 j : ℝ)‖)
          (fun _ _ => norm_nonneg _) hz
    _ ≤ finiteSourceNormBound R * (z.2:ℝ) :=
      le_mul_of_one_le_right (finiteSourceNormBound_nonneg R) hd

end SGPT.Okounkov.BodyFromGrowth
