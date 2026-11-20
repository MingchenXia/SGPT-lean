import SGPT.PSH.LocalRationalDivisorGrouping

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.Pending

/-- ORIGINAL finite positive rational weights and a prescribed positive
integer factor internally produce a LOCAL denominator multiple and literal
logarithm product identity, including every pole and the empty family. -/
theorem exists_finite_rational_logarithmic_product_grouping_multiple {ι : Type*}
    (s : Finset ι) (w : ι → ℚ) (hw : ∀ i ∈ s, 0 < w i) (d : ℕ) (hd : 0 < d) :
    ∃ (k : ℕ) (a : ι → ℕ), 0 < k ∧
      (∀ i ∈ s, 0 < a i ∧ w i = (a i : ℚ) / ((d * k : ℕ) : ℚ)) ∧
      ∀ h : ι → ℂ,
        (∑ i : {i // i ∈ s}, ((w i.val : ℝ) : EReal) * logNormSq (h i.val)) =
          (((1 / ((d * k : ℕ) : ℚ) : ℚ) : ℝ) : EReal) *
            logNormSq (∏ i : {i // i ∈ s}, h i.val ^ a i.val) := by
  classical
  obtain ⟨k, a, hk, ha, hlog⟩ := exists_finite_rational_logarithmic_product_grouping s
    (fun i => (d : ℚ) * w i) (fun i hi => mul_pos (by exact_mod_cast hd) (hw i hi))
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have hc : 0 ≤ ((1 / (d : ℚ) : ℚ) : ℝ) := by positivity
  have hscale (i : ι) :
      (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) * ((((d : ℚ) * w i : ℚ) : ℝ) : EReal) =
        ((w i : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    have hQ : (1 / (d : ℚ)) * ((d : ℚ) * w i) = w i := by
      rw [one_div, ← mul_assoc, inv_mul_cancel₀ hdQ, one_mul]
    exact_mod_cast hQ
  have hcoef : (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) *
      (((1 / (k : ℚ) : ℚ) : ℝ) : EReal) =
        (((1 / ((d * k : ℕ) : ℚ) : ℚ) : ℝ) : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    have hQ : (1 / (d : ℚ)) * (1 / (k : ℚ)) = 1 / ((d * k : ℕ) : ℚ) := by
      push_cast
      field_simp
    exact_mod_cast hQ
  refine ⟨k, a, hk, ?_, ?_⟩
  · intro i hi
    refine ⟨(ha i hi).1, ?_⟩
    apply (eq_div_iff (by exact_mod_cast Nat.mul_ne_zero hd.ne' hk.ne')).mpr
    have h := (eq_div_iff hkQ).mp (ha i hi).2
    push_cast
    calc
      w i * ((d : ℚ) * (k : ℚ)) = ((d : ℚ) * w i) * (k : ℚ) := by ring
      _ = (a i : ℚ) := h
  · intro h
    calc
      (∑ i : {i // i ∈ s}, ((w i.val : ℝ) : EReal) * logNormSq (h i.val)) =
          (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) *
            (∑ i : {i // i ∈ s}, ((((d : ℚ) * w i.val : ℚ) : ℝ) : EReal) *
              logNormSq (h i.val)) := by
        rw [MeteredDivisorSingleGenerator.coe_mul_finsetSum hc]
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_assoc, hscale]
      _ = (((1 / (d : ℚ) : ℚ) : ℝ) : EReal) *
          ((((1 / (k : ℚ) : ℚ) : ℝ) : EReal) *
            logNormSq (∏ i : {i // i ∈ s}, h i.val ^ a i.val)) := by rw [hlog h]
      _ = _ := by rw [← mul_assoc, hcoef]

end SGPT.PSH
