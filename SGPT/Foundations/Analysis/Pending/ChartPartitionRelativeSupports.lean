import SGPT.Foundations.Analysis.Pending.ChartPartition

set_option autoImplicit false

/-! # Genuine relative chart supports of the actual global partition

All mathematical statements and complete proofs were written before this file.
-/

noncomputable section

open Set TopologicalSpace Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ChartPartitionRelativeSupports

open FirstPass ChartPartition

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual scalar coordinate function, zero outside the whole chart target. -/
def chartWeight (e : ComplexChart n M) (χ : M → ℝ) : ComplexModel n → ℝ :=
  e.val.target.indicator (fun z => χ (e.val.symm z))

/-- Genuine global support produces continuity and the relative chart support. -/
theorem chartWeight_relativeSupport (e : ComplexChart n M) (χ : M → ℝ)
    (hχ : ChartSmooth (n := n) χ) (S : Opens M) (hsupp : tsupport χ ⊆ S)
    (hnonneg : ∀ x, 0 ≤ χ x) :
    ContinuousOn (chartWeight e χ) e.val.target ∧
    (∀ z, 0 ≤ chartWeight e χ z) ∧
    IsOpen (e.val.target ∩ e.val.symm ⁻¹' (S : Set M)) ∧
    tsupport (chartWeight e χ) ∩ e.val.target ⊆
      e.val.target ∩ e.val.symm ⁻¹' (S : Set M) := by
  refine ⟨(hχ e).continuousOn.congr (fun z hz => ?_), ?_,
    e.val.symm.isOpen_inter_preimage S.isOpen, ?_⟩
  · exact indicator_of_mem hz _
  · intro z
    by_cases hz : z ∈ e.val.target
    · simp only [chartWeight, indicator_of_mem hz]
      exact hnonneg _
    · simp only [chartWeight, indicator_of_notMem hz]
      exact le_rfl
  · intro z hz
    refine ⟨hz.2, ?_⟩
    by_contra hnot
    have hx : e.val.symm z ∉ tsupport χ := fun hx => hnot (hsupp hx)
    have hc : ContinuousAt e.val.symm z := e.val.continuousAt_symm hz.2
    have he := hc.eventually (notMem_tsupport_iff_eventuallyEq.mp hx)
    have hzero : chartWeight e χ =ᶠ[𝓝 z] 0 := by
      filter_upwards [he, e.val.open_target.mem_nhds hz.2] with y hy hyV
      simp only [chartWeight, indicator_of_mem hyV, hy, Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hz.1

/-- The actual finite partition supplies all chart support inputs internally. -/
theorem exists_chartSmooth_partition_relativeSupports [CompactSpace M]
    {ι : Type*} (S : ι → Opens M) (hcover : ∀ x : M, ∃ i, x ∈ S i) :
    ∃ (m : ℕ) (χ : Fin m → M → ℝ) (idx : Fin m → ι),
      (∀ a, ChartSmooth (n := n) (χ a)) ∧ (∀ a x, 0 ≤ χ a x) ∧
      (∀ a, tsupport (χ a) ⊆ (S (idx a) : Set M)) ∧
      (∀ a, IsCompact (tsupport (χ a))) ∧ (∀ x, ∑ a, χ a x = 1) ∧
      ∀ a (e : ComplexChart n M),
        ContinuousOn (chartWeight e (χ a)) e.val.target ∧
        (∀ z, 0 ≤ chartWeight e (χ a) z) ∧
        IsOpen (e.val.target ∩ e.val.symm ⁻¹' (S (idx a) : Set M)) ∧
        tsupport (chartWeight e (χ a)) ∩ e.val.target ⊆
          e.val.target ∩ e.val.symm ⁻¹' (S (idx a) : Set M) := by
  obtain ⟨m, χ, idx, hsm, hnonneg, hsupp, hcompact, hsum⟩ :=
    exists_chartSmooth_partitionOfUnity (n := n) S hcover
  exact ⟨m, χ, idx, hsm, hnonneg, hsupp, hcompact, hsum,
    fun a e => chartWeight_relativeSupport e (χ a) (hsm a) (S (idx a)) (hsupp a)
      (hnonneg a)⟩

end SGPT.Foundations.Analysis.Pending.ChartPartitionRelativeSupports
