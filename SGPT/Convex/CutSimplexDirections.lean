import SGPT.Convex.CutSimplexPerturbation

/-! Actual two- and three-coordinate directions in the source finite LP.
The coefficient identities are computed and feasible non-extremeness is
proved from the original cut simplex, including degenerate node counts. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Convex.CutSimplex
open Set
variable {ι : Type*} [Fintype ι]

/-- The genuine standard basis vector. -/
def basis (i : ι) : ι → ℝ := by
  classical
  exact fun j => if j = i then 1 else 0

omit [Fintype ι] in
@[simp] theorem basis_self (i : ι) : basis i i = 1 := by classical simp [basis]

omit [Fintype ι] in
@[simp] theorem basis_other {i j : ι} (h : j ≠ i) : basis i j = 0 := by classical simp [basis, h]

@[simp] theorem sum_basis (i : ι) : ∑ j, basis i j = 1 := by classical simp [basis]

@[simp] theorem objective_basis (τ : ι → ℝ) (i : ι) : objective τ (basis i) = τ i := by
  classical
  simp [objective_apply, basis]

theorem basis_mem_cut (τ : ι → ℝ) (s : ℝ) (i : ι) (hi : s ≤ τ i) : basis i ∈ cut τ s := by
  classical
  refine ⟨⟨fun j => ?_, sum_basis i⟩, ?_⟩
  · simp only [basis]
    split_ifs <;> norm_num
  · simpa only [mem_ofPred_eq, objective_basis] using hi

/-- A concrete two-coordinate, total-mass-preserving direction. -/
def twoDirection (i j : ι) : ι → ℝ := basis i - basis j

theorem sum_twoDirection (i j : ι) : ∑ k, twoDirection i j k = 0 := by
  simp only [twoDirection, Pi.sub_apply, Finset.sum_sub_distrib, sum_basis, sub_self]

omit [Fintype ι] in
theorem twoDirection_ne_zero {i j : ι} (hij : i ≠ j) : twoDirection i j ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp only [twoDirection, Pi.sub_apply, basis_self, basis_other hij, Pi.zero_apply] at hi
  norm_num at hi

omit [Fintype ι] in
theorem twoDirection_supported {w : ι → ℝ} {i j : ι} (hi : 0 < w i) (hj : 0 < w j) :
    ∀ k, twoDirection i j k ≠ 0 → 0 < w k := by
  classical
  intro k hk
  by_cases hki : k = i
  · simpa only [hki] using hi
  by_cases hkj : k = j
  · simpa only [hkj] using hj
  exact (hk (by simp only [twoDirection, Pi.sub_apply, basis_other hki, basis_other hkj, sub_self])).elim

/-- A slack extreme point cannot have two positive coordinates. -/
theorem extreme_slack_no_two (τ : ι → ℝ) (s : ℝ) {w : ι → ℝ}
    (hw : w ∈ (cut τ s).extremePoints ℝ) (hslack : s < objective τ w)
    {i j : ι} (hij : i ≠ j) (hi : 0 < w i) (hj : 0 < w j) : False :=
  not_extreme_of_supported_direction τ s hw.1 (twoDirection_ne_zero hij)
    (sum_twoDirection i j) (twoDirection_supported hi hj) (Or.inr hslack) hw

/-- Nonempty positive support is an output of the actual simplex equation. -/
theorem exists_positive_coordinate {τ : ι → ℝ} {s : ℝ} {w : ι → ℝ}
    (hw : w ∈ cut τ s) : ∃ i, 0 < w i := by
  by_contra h
  have hz : ∀ i, w i = 0 := by
    intro i
    apply le_antisymm _ (hw.1.1 i)
    exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
  have hs := hw.1.2
  simp only [hz, Finset.sum_const_zero] at hs
  norm_num at hs

/-- Hence every slack extreme point is an ACTUAL eligible basis vector. -/
theorem extreme_slack_eq_basis (τ : ι → ℝ) (s : ℝ) {w : ι → ℝ}
    (hw : w ∈ (cut τ s).extremePoints ℝ) (hslack : s < objective τ w) :
    ∃ i, s ≤ τ i ∧ w = basis i := by
  classical
  obtain ⟨i, hi⟩ := exists_positive_coordinate hw.1
  have hzero : ∀ j, j ≠ i → w j = 0 := by
    intro j hji
    apply le_antisymm _ (hw.1.1.1 j)
    exact le_of_not_gt (fun hj => extreme_slack_no_two τ s hw hslack hji hj hi)
  have hsum : (∑ j, w j) = w i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact hzero j hji
    · simp
  have hwi : w i = 1 := hsum.symm.trans hw.1.1.2
  have heq : w = basis i := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [hwi, basis_self]
    · simp only [hzero j hji, basis_other hji]
  refine ⟨i, ?_, heq⟩
  simpa only [mem_ofPred_eq, heq, objective_basis] using hw.1.2

/-- A concrete kernel direction for the mass and barycentre equations. -/
def threeDirection (τ : ι → ℝ) (i j k : ι) : ι → ℝ :=
  (τ j - τ k) • basis i + (τ k - τ i) • basis j + (τ i - τ j) • basis k

theorem sum_threeDirection (τ : ι → ℝ) (i j k : ι) : ∑ l, threeDirection τ i j k l = 0 := by
  simp only [threeDirection, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum, sum_basis, mul_one]
  ring

theorem objective_threeDirection (τ : ι → ℝ) (i j k : ι) :
    objective τ (threeDirection τ i j k) = 0 := by
  simp only [threeDirection, map_add, map_smul, smul_eq_mul, objective_basis]
  ring

omit [Fintype ι] in
theorem threeDirection_ne_zero (τ : ι → ℝ) (hτ : Function.Injective τ)
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : threeDirection τ i j k ≠ 0 := by
  intro h
  have he : threeDirection τ i j k i = τ j - τ k := by
    simp only [threeDirection, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      basis_self, basis_other hij, basis_other hik, mul_one, mul_zero, add_zero]
  have hz : τ j - τ k = 0 := by
    simpa only [he, Pi.zero_apply] using congrFun h i
  exact hjk (hτ (sub_eq_zero.mp hz))

omit [Fintype ι] in
theorem threeDirection_supported (τ : ι → ℝ) {w : ι → ℝ} {i j k : ι}
    (hi : 0 < w i) (hj : 0 < w j) (hk : 0 < w k) :
    ∀ l, threeDirection τ i j k l ≠ 0 → 0 < w l := by
  intro l hl
  by_cases hli : l = i
  · simpa only [hli] using hi
  by_cases hlj : l = j
  · simpa only [hlj] using hj
  by_cases hlk : l = k
  · simpa only [hlk] using hk
  exact (hl (by simp only [threeDirection, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    basis_other hli, basis_other hlj, basis_other hlk, mul_zero, add_zero])).elim

/-- Every original extreme point has at most two positive support
coordinates; this excludes a genuine feasible midpoint using an explicit
three-coordinate kernel direction, without a sparsity assumption. -/
theorem extreme_no_three (τ : ι → ℝ) (hτ : Function.Injective τ) (s : ℝ) {w : ι → ℝ}
    (hw : w ∈ (cut τ s).extremePoints ℝ) {i j k : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : 0 < w i) (hj : 0 < w j) (hk : 0 < w k) : False :=
  not_extreme_of_supported_direction τ s hw.1 (threeDirection_ne_zero τ hτ hij hik hjk)
    (sum_threeDirection τ i j k) (threeDirection_supported τ hi hj hk)
    (Or.inl (objective_threeDirection τ i j k)) hw

end SGPT.Convex.CutSimplex
