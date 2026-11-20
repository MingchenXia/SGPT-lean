import SGPT.Convex.CutSimplexPair

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex.CutSimplex
open Set
variable {ι : Type*} [Fintype ι]

theorem eq_basis_of_supported {τ : ι → ℝ} {s : ℝ} {w : ι → ℝ}
    (hw : w ∈ cut τ s) (i : ι) (hz : ∀ j, j ≠ i → w j = 0) : w = basis i := by
  classical
  have hsum : (∑ j, w j) = w i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      exact hz j hji
    · simp
  have hi : w i = 1 := hsum.symm.trans hw.1.2
  funext j
  by_cases hji : j = i
  · subst j
    simp only [hi, basis_self]
  · simp only [hz j hji, basis_other hji]

theorem basis_isExtreme (τ : ι → ℝ) (s : ℝ) (i : ι) (hi : s ≤ τ i) :
    basis i ∈ (cut τ s).extremePoints ℝ := by
  classical
  have heq : coordinateFace τ s {i} = {basis i} := by
    ext w
    constructor
    · intro hw
      apply mem_singleton_iff.mpr
      apply eq_basis_of_supported hw.1 i
      intro j hji
      exact hw.2 j (by simpa only [Finset.mem_singleton] using hji)
    · intro hw
      rcases mem_singleton_iff.mp hw with rfl
      refine ⟨basis_mem_cut τ s i hi, ?_⟩
      intro j hj
      exact basis_other (by simpa only [Finset.mem_singleton] using hj)
  have h := coordinateFace_isExtreme τ s ({i} : Finset ι)
  rw [heq] at h
  exact h.mem_extremePoints

def pairSupport (i j : ι) : Finset ι := by classical exact {i, j}

theorem pairWeights_isExtreme (τ : ι → ℝ) (s : ℝ) {i j : ι}
    (hlo : τ j < s) (hhi : s < τ i) :
    pairWeights τ s i j ∈ (cut τ s).extremePoints ℝ := by
  classical
  have htime : τ j < τ i := hlo.trans hhi
  have hij : i ≠ j := by
    intro h
    subst j
    exact (lt_irrefl _) htime
  have hfeas := pairWeights_mem_cut τ htime hlo.le hhi.le
  have heq : coordinateFace τ s (pairSupport i j) ∩ boundary τ s = {pairWeights τ s i j} := by
    ext w
    constructor
    · intro hw
      apply mem_singleton_iff.mpr
      apply pairWeights_eq_of_supported τ s hij htime.ne' hw.1.1 hw.2.2
      intro k hki hkj
      exact hw.1.2 k (by simp only [pairSupport, Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hki, hkj⟩)
    · intro hw
      rcases mem_singleton_iff.mp hw with rfl
      refine ⟨⟨hfeas, ?_⟩, hfeas, objective_pairWeights τ s htime.ne'⟩
      intro k hk
      have hkp : k ≠ i ∧ k ≠ j := by
        simpa only [pairSupport, Finset.mem_insert, Finset.mem_singleton, not_or] using hk
      simp only [pairWeights, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        basis_other hkp.1, basis_other hkp.2, mul_zero, add_zero]
  have h := (coordinateFace_isExtreme τ s (pairSupport i j)).inter (boundary_isExtreme τ s)
  rw [heq] at h
  exact h.mem_extremePoints

/-- Positive support and an active barycentre force the strict source
parameter inequalities for the displayed actual pair. -/
theorem strict_bounds_of_supported_pair (τ : ι → ℝ) (s : ℝ)
    {i j : ι} (hij : i ≠ j) (htime : τ j < τ i) {w : ι → ℝ}
    (hw : w ∈ cut τ s) (hb : objective τ w = s)
    (hs : ∀ k, k ≠ i → k ≠ j → w k = 0) (hi : 0 < w i) (hj : 0 < w j) :
    τ j < s ∧ s < τ i ∧ w = pairWeights τ s i j := by
  have heq := pairWeights_eq_of_supported τ s hij htime.ne' hw hb hs
  have hwi : w i = (s - τ j) / (τ i - τ j) := by
    have h := congrFun heq i
    simpa only [pairWeights, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basis_self,
      basis_other hij, mul_one, mul_zero, add_zero] using h
  have hwj : w j = (τ i - s) / (τ i - τ j) := by
    have h := congrFun heq j
    simpa only [pairWeights, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basis_self,
      basis_other hij.symm, mul_one, mul_zero, zero_add] using h
  have hd : 0 < τ i - τ j := sub_pos.mpr htime
  have himul := (eq_div_iff hd.ne').mp hwi
  have hjmul := (eq_div_iff hd.ne').mp hwj
  refine ⟨sub_pos.mp ?_, sub_pos.mp ?_, heq⟩
  · rw [← himul]
    exact mul_pos hi hd
  · rw [← hjmul]
    exact mul_pos hj hd

/-- EXACT actual extreme-point classification. Sparsity and the active
barycentre are proved from supported perturbations, never caller data. -/
theorem extreme_eq_basis_or_pair (τ : ι → ℝ) (hτ : Function.Injective τ) (s : ℝ)
    {w : ι → ℝ} (hw : w ∈ (cut τ s).extremePoints ℝ) :
    (∃ i, s ≤ τ i ∧ w = basis i) ∨
      (∃ i j, τ j < s ∧ s < τ i ∧ w = pairWeights τ s i j) := by
  classical
  by_cases hslack : s < objective τ w
  · exact Or.inl (extreme_slack_eq_basis τ s hw hslack)
  have hb : objective τ w = s := le_antisymm (le_of_not_gt hslack) hw.1.2
  obtain ⟨i, hi⟩ := exists_positive_coordinate hw.1
  by_cases hex : ∃ j, j ≠ i ∧ 0 < w j
  · obtain ⟨j, hji, hj⟩ := hex
    have hij : i ≠ j := hji.symm
    have hs : ∀ k, k ≠ i → k ≠ j → w k = 0 := by
      intro k hki hkj
      apply le_antisymm _ (hw.1.1.1 k)
      exact le_of_not_gt (fun hk => extreme_no_three τ hτ s hw hij hki.symm hkj.symm hi hj hk)
    have hτij : τ i ≠ τ j := fun h => hij (hτ h)
    by_cases htime : τ j < τ i
    · exact Or.inr ⟨i, j, strict_bounds_of_supported_pair τ s hij htime hw.1 hb hs hi hj⟩
    · have htime' : τ i < τ j := by
        rcases lt_or_eq_of_le (le_of_not_gt htime) with h | h
        · exact h
        · exact (hτij h).elim
      exact Or.inr ⟨j, i, strict_bounds_of_supported_pair τ s hji htime' hw.1 hb
        (fun k hkj hki => hs k hki hkj) hj hi⟩
  · have hz : ∀ j, j ≠ i → w j = 0 := by
      intro j hji
      apply le_antisymm _ (hw.1.1.1 j)
      exact le_of_not_gt (fun hj => hex ⟨j, hji, hj⟩)
    have heq := eq_basis_of_supported hw.1 i hz
    refine Or.inl ⟨i, ?_, heq⟩
    simpa only [mem_ofPred_eq, heq, objective_basis] using hw.1.2

/-- A finite, genuine parameter-dependent index for exactly those vertices. -/
def VertexIndex (τ : ι → ℝ) (s : ℝ) :=
  {i : ι // s ≤ τ i} ⊕ {p : ι × ι // τ p.2 < s ∧ s < τ p.1}

instance vertexIndex_finite (τ : ι → ℝ) (s : ℝ) : Finite (VertexIndex τ s) := by
  unfold VertexIndex
  infer_instance

def vertexVector (τ : ι → ℝ) (s : ℝ) : VertexIndex τ s → (ι → ℝ)
  | Sum.inl i => basis i.val
  | Sum.inr p => pairWeights τ s p.val.1 p.val.2

theorem vertexVector_isExtreme (τ : ι → ℝ) (s : ℝ) (v : VertexIndex τ s) :
    vertexVector τ s v ∈ (cut τ s).extremePoints ℝ := by
  cases v with
  | inl i => exact basis_isExtreme τ s i.val i.property
  | inr p => exact pairWeights_isExtreme τ s p.property.1 p.property.2

theorem extremePoints_eq_range (τ : ι → ℝ) (hτ : Function.Injective τ) (s : ℝ) :
    (cut τ s).extremePoints ℝ = Set.range (vertexVector τ s) := by
  ext w
  constructor
  · intro hw
    rcases extreme_eq_basis_or_pair τ hτ s hw with ⟨i, hi, heq⟩ | ⟨i, j, hi, hj, heq⟩
    · exact ⟨Sum.inl ⟨i, hi⟩, heq.symm⟩
    · exact ⟨Sum.inr ⟨(i, j), hi, hj⟩, heq.symm⟩
  · rintro ⟨v, rfl⟩
    exact vertexVector_isExtreme τ s v

/-- Actual coordinate-face optimizer is one of the exact original vertices. -/
theorem exists_vertex_coordinateFace_max (τ : ι → ℝ) (hτ : Function.Injective τ)
    (c : ι → ℝ) (s : ℝ) (J : Finset ι) (hne : (coordinateFace τ s J).Nonempty) :
    ∃ v : VertexIndex τ s, vertexVector τ s v ∈ coordinateFace τ s J ∧
      ∀ w ∈ coordinateFace τ s J, objective c w ≤ objective c (vertexVector τ s v) := by
  obtain ⟨w, hw, hext, hmax⟩ := exists_coordinateFace_extreme_max τ c s J hne
  rw [extremePoints_eq_range τ hτ s] at hext
  obtain ⟨v, rfl⟩ := hext
  exact ⟨v, hw, hmax⟩

end SGPT.Convex.CutSimplex
