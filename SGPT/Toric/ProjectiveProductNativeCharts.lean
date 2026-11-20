import SGPT.Toric.ProjectiveProductBoundaryPole
import SGPT.Foundations.Analysis.FirstPass.ComplexAnalyticSubvarieties
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetNull

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped Topology Manifold

/-- The binary original quotient charts exhaust the actual native atlas. -/
theorem mem_projectiveProductNativeAtlas_iff : (n : ℕ) →
    (e : OpenPartialHomeomorph (projectiveProductSpace n) (ComplexModel n)) →
    e ∈ atlas (ComplexModel n) (projectiveProductSpace n) ↔
      ∃ ε : Fin n → Bool, e = (projectiveProductNativeChart n ε).val
  | 0, e => by
    change e ∈ ({OpenPartialHomeomorph.refl (ComplexModel 0)} : Set _) ↔ _
    simp only [mem_singleton_iff]
    constructor
    · intro h
      exact ⟨fun i => Fin.elim0 i, h⟩
    · rintro ⟨ε, h⟩
      exact h
  | n + 1, e => by
    constructor
    · intro he
      change e ∈ image2 prodChart (atlas (ComplexModel n) (projectiveProductSpace n))
        (atlas (ComplexModel 1) (Projectivization ℂ (Fin 2 → ℂ))) at he
      obtain ⟨a, ha, b, hb, rfl⟩ := he
      obtain ⟨ε, rfl⟩ := (mem_projectiveProductNativeAtlas_iff n a).mp ha
      obtain ⟨c, rfl⟩ := (mem_projectiveNativeAtlas_iff b).mp hb
      refine ⟨Fin.snoc ε c, ?_⟩
      simp only [projectiveProductNativeChart, Fin.init_snoc, Fin.snoc_last]
      rfl
    · rintro ⟨ε, rfl⟩
      exact (projectiveProductNativeChart (n + 1) ε).property

/-- Every actual native complex chart is literally an original binary chart. -/
theorem projectiveProductNativeChart_exhaustive {n : ℕ}
    (e : ComplexChart n (projectiveProductSpace n)) :
    ∃ ε : Fin n → Bool, e = projectiveProductNativeChart n ε := by
  obtain ⟨ε, hε⟩ := (mem_projectiveProductNativeAtlas_iff n e.val).mp e.property
  exact ⟨ε, Subtype.ext hε⟩

/-- Every binary chart sees the original torus as all nonzero coordinates. -/
theorem projectiveProductTorus_chart_symm : (n : ℕ) → (ε : Fin n → Bool) →
    (z : ComplexModel n) →
    (projectiveProductNativeChart n ε).val.symm z ∈ projectiveProductTorus n ↔
      z ∈ complexTorus n
  | 0, _, _ => by simp [projectiveProductTorus, complexTorus]
  | n + 1, ε, z => by
    change (((projectiveProductNativeChart n (Fin.init ε)).val.symm
        ((prodModelEquiv n 1).symm z).1 ∈ projectiveProductTorus n) ∧
      (projectiveNativeChart (ε (Fin.last n))).val.symm
        ((prodModelEquiv n 1).symm z).2 ∉ projectiveToricBoundary) ↔ _
    rw [projectiveProductTorus_chart_symm,
      show ((projectiveNativeChart (ε (Fin.last n))).val.symm
          ((prodModelEquiv n 1).symm z).2 ∉ projectiveToricBoundary) ↔
          ((prodModelEquiv n 1).symm z).2 ∈ complexTorus 1 from
        projectiveToricBoundary_chart_off_iff _ _]
    constructor
    · intro h i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact h.2 0
      · exact h.1 j
    · intro h
      exact ⟨fun i => h i.castSucc, fun i => h (Fin.natAdd n i)⟩

/-- The actual original product boundary has its literal entire polynomial equation.
The empty coordinate product is one, so this includes dimension zero. -/
theorem projectiveProductBoundary_chart_iff (n : ℕ) (ε : Fin n → Bool)
    (z : ComplexModel n) :
    (projectiveProductNativeChart n ε).val.symm z ∈ (projectiveProductTorus n)ᶜ ↔
      ∏ i : Fin n, z i = 0 := by
  rw [mem_compl_iff, projectiveProductTorus_chart_symm]
  change (¬ ∀ i : Fin n, z i ≠ 0) ↔ _
  have h : (∏ i : Fin n, z i) ≠ 0 ↔ ∀ i : Fin n, z i ≠ 0 := by
    simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left]
  simpa only [not_not] using (not_congr h).symm

private theorem differentiable_coordinate_product (n : ℕ) :
    Differentiable ℂ (fun z : ComplexModel n => ∏ i : Fin n, z i) := by
  have h : ContDiff ℂ 1 (fun z : ComplexModel n => ∏ i : Fin n, z i) := by
    apply contDiff_prod
    intro i _
    fun_prop
  exact h.differentiable (by norm_num)

/-- The actual original boundary is null in every whole binary coordinate chart,
by the genuine holomorphic zero-set theorem, including the empty product. -/
theorem projectiveProductBoundary_chart_volume_eq_zero (n : ℕ) (ε : Fin n → Bool) :
    volume {z : ComplexModel n |
      (projectiveProductNativeChart n ε).val.symm z ∈ (projectiveProductTorus n)ᶜ} = 0 := by
  have h := Pending.HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero volume
    isOpen_univ (convex_univ : Convex ℝ (univ : Set (ComplexModel n)))
    (differentiable_coordinate_product n).differentiableOn
    (x₁ := WithLp.toLp 2 (fun _ : Fin n => (1 : ℂ))) (mem_univ _) (by simp)
  have heq : {z : ComplexModel n |
      (projectiveProductNativeChart n ε).val.symm z ∈ (projectiveProductTorus n)ᶜ} =
      univ ∩ (fun z : ComplexModel n => ∏ i : Fin n, z i) ⁻¹' {0} := by
    ext z
    simpa only [mem_ofPred_eq, mem_inter_iff, mem_univ, true_and, mem_preimage,
      mem_singleton_iff] using projectiveProductBoundary_chart_iff n ε z
  rwa [heq]

/-- Genuine finite holomorphic presentations of the actual boundary, in the
actual preferred native chart at every point. -/
theorem isComplexAnalyticSubset_projectiveProductBoundary (n : ℕ) :
    IsComplexAnalyticSubset (n := n) (projectiveProductTorus n)ᶜ := by
  intro p
  obtain ⟨ε, hε⟩ := projectiveProductNativeChart_exhaustive (complexChartAt (n := n) p)
  refine ⟨{ generatorCount := 1
            generator := fun _ z => ∏ i : Fin n, z i
            coordinateNeighborhood := univ
            isOpen_coordinateNeighborhood := isOpen_univ
            center_mem_coordinateNeighborhood := mem_univ _
            coordinateNeighborhood_subset_target := ?_
            generator_holomorphic := fun _ => (differentiable_coordinate_product n).differentiableOn
            zeroLocus := ?_ }⟩
  · rw [hε, projectiveProductNativeChart_target]
  · intro y hy _
    have h := projectiveProductBoundary_chart_iff n ε
      ((projectiveProductNativeChart n ε).val y)
    rw [(projectiveProductNativeChart n ε).val.left_inv (hε ▸ hy)] at h
    simpa only [hε, Fin.forall_fin_one] using h

end SGPT.Toric
