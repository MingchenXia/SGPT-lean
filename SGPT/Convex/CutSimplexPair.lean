import SGPT.Convex.CutSimplexDirections
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex.CutSimplex
open Set
variable {ι : Type*} [Fintype ι]

/-- The literal source two-node barycentric vector, including degenerate
endpoint weights (strict interior eligibility is imposed separately). -/
def pairWeights (τ : ι → ℝ) (s : ℝ) (i j : ι) : ι → ℝ :=
  ((s - τ j) / (τ i - τ j)) • basis i + ((τ i - s) / (τ i - τ j)) • basis j

theorem sum_pairWeights (τ : ι → ℝ) (s : ℝ) {i j : ι} (hτ : τ i ≠ τ j) :
    ∑ k, pairWeights τ s i j k = 1 := by
  simp only [pairWeights, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, sum_basis, mul_one]
  field_simp [sub_ne_zero.mpr hτ]
  ring

theorem objective_pairWeights (τ : ι → ℝ) (s : ℝ) {i j : ι} (hτ : τ i ≠ τ j) :
    objective τ (pairWeights τ s i j) = s := by
  simp only [pairWeights, map_add, map_smul, smul_eq_mul, objective_basis]
  field_simp [sub_ne_zero.mpr hτ]
  ring

theorem pairWeights_mem_cut (τ : ι → ℝ) {s : ℝ} {i j : ι}
    (hij : τ j < τ i) (hlo : τ j ≤ s) (hhi : s ≤ τ i) :
    pairWeights τ s i j ∈ cut τ s := by
  have hd : 0 < τ i - τ j := sub_pos.mpr hij
  have ha : 0 ≤ (s - τ j) / (τ i - τ j) := div_nonneg (sub_nonneg.mpr hlo) hd.le
  have hb : 0 ≤ (τ i - s) / (τ i - τ j) := div_nonneg (sub_nonneg.mpr hhi) hd.le
  refine ⟨⟨?_, sum_pairWeights τ s hij.ne'⟩, ?_⟩
  · intro k
    have hki : 0 ≤ basis i k := by classical simp only [basis]; split_ifs <;> norm_num
    have hkj : 0 ≤ basis j k := by classical simp only [basis]; split_ifs <;> norm_num
    exact add_nonneg (mul_nonneg ha hki) (mul_nonneg hb hkj)
  · exact (objective_pairWeights τ s hij.ne').ge

theorem pairWeights_eq_of_supported (τ : ι → ℝ) (s : ℝ)
    {i j : ι} (hij : i ≠ j) (hτ : τ i ≠ τ j) {w : ι → ℝ}
    (hw : w ∈ cut τ s) (hb : objective τ w = s)
    (hs : ∀ k, k ≠ i → k ≠ j → w k = 0) : w = pairWeights τ s i j := by
  classical
  have he : w = w i • basis i + w j • basis j := by
    funext k
    by_cases hki : k = i
    · subst k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basis_self,
        basis_other hij, mul_one, mul_zero, add_zero]
    by_cases hkj : k = j
    · subst k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basis_self,
        basis_other hij.symm, mul_one, mul_zero, zero_add]
    · simp only [hs k hki hkj, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        basis_other hki, basis_other hkj, mul_zero, add_zero]
  have hm : w i + w j = 1 := by
    have h := congrArg (fun v : ι → ℝ => ∑ k, v k) he
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_basis, mul_one, hw.1.2] at h
    exact h.symm
  have ht : w i * τ i + w j * τ j = s := by
    have h := congrArg (objective τ) he
    simp only [map_add, map_smul, smul_eq_mul, objective_basis, hb] at h
    exact h.symm
  have hd : τ i - τ j ≠ 0 := sub_ne_zero.mpr hτ
  have hi : w i = (s - τ j) / (τ i - τ j) := by
    apply (eq_div_iff hd).mpr
    linear_combination ht - τ j * hm
  have hj : w j = (τ i - s) / (τ i - τ j) := by
    apply (eq_div_iff hd).mpr
    linear_combination τ i * hm - ht
  simpa only [pairWeights, hi, hj] using he

/-- The actual active barycentre boundary is extreme inside the cut. -/
def boundary (τ : ι → ℝ) (s : ℝ) : Set (ι → ℝ) :=
  {w ∈ cut τ s | objective τ w = s}

theorem boundary_isExtreme (τ : ι → ℝ) (s : ℝ) : IsExtreme ℝ (cut τ s) (boundary τ s) := by
  refine ⟨fun _ hw => hw.1, ?_⟩
  intro u hu v hv w hw hseg
  rcases hseg with ⟨a, b, ha, hb, hab, he⟩
  refine ⟨hu, ?_⟩
  have hbar := congrArg (objective τ) he
  simp only [map_add, map_smul, smul_eq_mul, hw.2] at hbar
  have hbase : a * s + b * s = s := by rw [← add_mul, hab, one_mul]
  apply le_antisymm _ hu.2
  by_contra h
  have hpos : 0 < a * (objective τ u - s) := mul_pos ha (sub_pos.mpr (lt_of_not_ge h))
  have hnonneg : 0 ≤ b * (objective τ v - s) := mul_nonneg hb.le (sub_nonneg.mpr hv.2)
  nlinarith

omit [Fintype ι] in
/-- Both endpoint and interior pair weights vary affinely in the real
parameter as ACTUAL weight vectors, before any EReal node is evaluated. -/
theorem pairWeights_affine (τ : ι → ℝ) (s t a b : ℝ) (hab : a + b = 1) (i j : ι) :
    pairWeights τ (a * s + b * t) i j = a • pairWeights τ s i j + b • pairWeights τ t i j := by
  funext k
  simp only [pairWeights, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hnumleft : a * s + b * t - τ j = a * (s - τ j) + b * (t - τ j) := by
    calc
      a * s + b * t - τ j = a * s + b * t - (a + b) * τ j := by rw [hab, one_mul]
      _ = a * (s - τ j) + b * (t - τ j) := by ring
  have hnumright : τ i - (a * s + b * t) = a * (τ i - s) + b * (τ i - t) := by
    calc
      τ i - (a * s + b * t) = (a + b) * τ i - (a * s + b * t) := by rw [hab, one_mul]
      _ = a * (τ i - s) + b * (τ i - t) := by ring
  have hleft : (a * s + b * t - τ j) / (τ i - τ j) =
      a * ((s - τ j) / (τ i - τ j)) + b * ((t - τ j) / (τ i - τ j)) := by
    rw [hnumleft, add_div, mul_div_assoc, mul_div_assoc]
  have hright : (τ i - (a * s + b * t)) / (τ i - τ j) =
      a * ((τ i - s) / (τ i - τ j)) + b * ((τ i - t) / (τ i - τ j)) := by
    rw [hnumright, add_div, mul_div_assoc, mul_div_assoc]
  rw [hleft, hright]
  ring

end SGPT.Convex.CutSimplex
