import SGPT.Unibranch.PrimeNov16AnalyticNormalizationLocalGraph

/-! Actual original finite germ decomposition realized on ONE original ambient ball.
Blueprint: prime-nov16-analytic-normalization-original-branch-window.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchWindow
open AnalyticGermDecomposition
open PrimeNov16AnalyticNormalizationLocalGraph

theorem exists_original_branch_window {n : ℕ} {Z N : Set (ComplexModel n)}
    (hZ : IsAnalyticGerm Z) (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ (k : ℕ) (B : Fin k → Set (ComplexModel n)) (r : ℝ),
      0<r ∧ ball (0 : ComplexModel n) r ⊆ N ∧
      (∀ i,IsIrreducibleGerm (B i)) ∧
      IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z} ∧
      (∀ i,IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ B i}) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,z ∈ Z ↔ ∃ i,z ∈ B i) ∧
      (∀ i,∀ z ∈ ball (0 : ComplexModel n) r,z ∈ B i → z ∈ Z) ∧
      Pairwise (fun i j => ¬ (B i ≤ᶠ[𝓝 0] B j)) := by
  obtain ⟨k,B,hB,_hBZ,hcover,hpair⟩ := exists_irreducible_decomposition_euclidean hZ
  obtain ⟨r0,hr0,hC0⟩ := exists_analytic_ball hZ
  choose ri hri hCi using fun i => exists_analytic_ball (hB i).1
  have hballs : ∀ᶠ z in 𝓝 (0 : ComplexModel n),∀ i,z ∈ ball 0 (ri i) :=
    eventually_all.mpr fun i => ball_mem_nhds 0 (hri i)
  have heq : ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ Z ↔ ∃ i,z ∈ B i := by
    filter_upwards [eventuallyEq_set.mp hcover] with z hz
    simpa only [mem_iUnion] using hz
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff_ball.mp
    ((eventually_of_mem hN fun _ hz => hz).and
      ((eventually_of_mem (ball_mem_nhds 0 hr0) fun _ hz => hz).and (hballs.and heq)))
  have hU0 : ballDomain (n := n) r ≤ ballDomain (n := n) r0 := fun z hz => (hs z hz).2.1
  have hUi (i : Fin k) : ballDomain (n := n) r ≤ ballDomain (n := n) (ri i) :=
    fun z hz => (hs z hz).2.2.1 i
  refine ⟨k,B,r,hr,fun z hz => (hs z hz).1,hB,?_,?_,?_,?_,hpair⟩
  · exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_inclusion hU0) hC0
  · intro i
    exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (contMDiff_inclusion (hUi i)) (hCi i)
  · intro z hz
    exact (hs z hz).2.2.2
  · intro i z hz hi
    exact ((hs z hz).2.2.2).mpr ⟨i,hi⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchWindow
