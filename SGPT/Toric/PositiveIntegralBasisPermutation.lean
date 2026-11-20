import SGPT.Toric.ToricNativeVertexFace

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set SGPT.AlmostSemigroup.Counting
open scoped BigOperators

/-- Two actual integral bases with nonnegative coordinates in both
directions differ only by a genuine permutation. Positivity and inverse
reconstruction prove this; no basis-vector correspondence is supplied. -/
theorem exists_basis_vector_eq_of_nonneg_coordinates
    {n : ℕ} (b c : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (hbc : ∀ i j, 0 ≤ b.repr (c j) i)
    (hcb : ∀ j i, 0 ≤ c.repr (b i) j) (j : Fin n) :
    ∃ i, b i = c j := by
  have hsum (k : Fin n) :
      (∑ i, b.repr (c j) i * c.repr (b i) k) = if j = k then 1 else 0 := by
    have heq := congrArg (fun m : Fin n → ℤ => c.repr m k) (b.sum_repr (c j))
    simpa only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      Module.Basis.repr_self_apply] using heq
  have hsumone : (∑ i, b.repr (c j) i * c.repr (b i) j) = 1 := by simpa using hsum j
  obtain ⟨i, _, hpos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => mul_nonneg (hbc i j) (hcb j i))).mp
      (show 0 < ∑ i, b.repr (c j) i * c.repr (b i) j by rw [hsumone]; decide)
  have hle : b.repr (c j) i * c.repr (b i) j ≤ 1 := by
    rw [← hsumone]
    exact Finset.single_le_sum (fun l _ => mul_nonneg (hbc l j) (hcb j l)) (Finset.mem_univ i)
  have hbpos : 0 < b.repr (c j) i := by nlinarith [hbc i j, hcb j i]
  have hcpos : 0 < c.repr (b i) j := by nlinarith [hbc i j, hcb j i]
  have hb1 : b.repr (c j) i = 1 := by nlinarith [hbpos, hcpos]
  have hc1 : c.repr (b i) j = 1 := by nlinarith [hbpos, hcpos]
  refine ⟨i, ?_⟩
  apply c.repr.injective
  ext k
  by_cases hjk : j = k
  · subst k
    simp only [Module.Basis.repr_self_apply, if_true, hc1]
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l (_ : l ∈ Finset.univ) => mul_nonneg (hbc l j) (hcb k l))).mp
        (by simpa only [if_neg hjk] using hsum k) i (Finset.mem_univ i)
    rw [hb1, one_mul] at hz
    simpa only [Module.Basis.repr_self_apply, if_neg hjk] using hz

/-- Both genuine correspondence directions assemble an actual permutation
of the integral basis index, including the empty index. -/
def positiveIntegralBasisPermutation
    {n : ℕ} (b c : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (hbc : ∀ i j, 0 ≤ b.repr (c j) i)
    (hcb : ∀ j i, 0 ≤ c.repr (b i) j) : Fin n ≃ Fin n where
  toFun j := (exists_basis_vector_eq_of_nonneg_coordinates b c hbc hcb j).choose
  invFun i := (exists_basis_vector_eq_of_nonneg_coordinates c b hcb hbc i).choose
  left_inv j := by
    apply c.injective
    exact (exists_basis_vector_eq_of_nonneg_coordinates c b hcb hbc _).choose_spec.trans
      (exists_basis_vector_eq_of_nonneg_coordinates b c hbc hcb j).choose_spec
  right_inv i := by
    apply b.injective
    exact (exists_basis_vector_eq_of_nonneg_coordinates b c hbc hcb _).choose_spec.trans
      (exists_basis_vector_eq_of_nonneg_coordinates c b hcb hbc i).choose_spec

/-- The permutation is the literal original vector readback. -/
theorem positiveIntegralBasisPermutation_apply
    {n : ℕ} (b c : Module.Basis (Fin n) ℤ (Fin n → ℤ))
    (hbc : ∀ i j, 0 ≤ b.repr (c j) i)
    (hcb : ∀ j i, 0 ≤ c.repr (b i) j) (j : Fin n) :
    b (positiveIntegralBasisPermutation b c hbc hcb j) = c j :=
  (exists_basis_vector_eq_of_nonneg_coordinates b c hbc hcb j).choose_spec

end SGPT.Toric
