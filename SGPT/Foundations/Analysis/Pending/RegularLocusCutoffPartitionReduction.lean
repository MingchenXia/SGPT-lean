import SGPT.Foundations.Analysis.Pending.ChartPartition
import SGPT.Foundations.Analysis.Pending.RegularPieceExhaustion

set_option autoImplicit false

/-!
# Finite compact cutoffs on a regular-locus exhaustion

The finite-cutoff part of the positive-dimensional Stokes argument is purely
topological.  For a compact set `K` and a finite ambient open cover of `K`, a
global finite chart-smooth partition of unity can be split into terms supported
in the chosen cover and terms supported in `Kᶜ`.  The latter vanish on `K`, so
the retained finite sum is one on `K`.

Together with the existing regular-piece exhaustion, this supplies a single
stage covering `K`.  It deliberately does not construct a current, identify a
weighted pushforward measure, or assert a Stokes cancellation: those remain
analytic-current inputs.
-/

open Set Filter Topology TopologicalSpace MeasureTheory
open scoped Topology ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.RegularLocusCutoffPartitionReduction

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.NumericalRestrictedVolumeScaffold
open RegularPieceExhaustion

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A finite chart-smooth partition which is subordinate to a finite cover on a
compact set.  Terms marked `none` are supported in the complement of that compact
set and hence do not contribute to the displayed sum on the compact set. -/
structure CompactCutoffPartition {r : ℕ} (K : Set M) (U : Fin r → Opens M) where
  size : ℕ
  cutoff : Fin size → M → ℝ
  index : Fin size → Option (Fin r)
  smooth : ∀ a, ChartSmooth (n := n) (cutoff a)
  nonneg : ∀ a x, 0 ≤ cutoff a x
  compact_support : ∀ a, IsCompact (tsupport (cutoff a))
  support_some : ∀ a i, index a = some i → tsupport (cutoff a) ⊆ (U i : Set M)
  support_none : ∀ a, index a = none → tsupport (cutoff a) ⊆ Kᶜ
  sum_eq_one_on : ∀ x ∈ K,
    (∑ a ∈ Finset.univ.filter (fun a => (index a).isSome), cutoff a x) = 1

/-- A finite ambient open cover of a compact set admits a compactly supported
chart-smooth partition whose active terms sum to one on that set. -/
theorem exists_compactCutoffPartition [CompactSpace M] {r : ℕ} (K : Set M)
    (hKclosed : IsClosed K) (U : Fin r → Opens M)
    (hcover : K ⊆ ⋃ i, (U i : Set M)) :
    Nonempty (CompactCutoffPartition (n := n) K U) := by
  classical
  let S : Option (Fin r) → Opens M := fun j =>
    match j with
    | some i => U i
    | none => ⟨Kᶜ, hKclosed.isOpen_compl⟩
  have hScover : ∀ x : M, ∃ j, x ∈ S j := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hx)
      exact ⟨some i, hxi⟩
    · exact ⟨none, hx⟩
  obtain ⟨m, χ, idx, hχsmooth, hχnonneg, hχsupp, hχcompact, hχsum⟩ :=
    ChartPartition.exists_chartSmooth_partitionOfUnity (n := n) S hScover
  refine ⟨⟨m, χ, idx, hχsmooth, hχnonneg, hχcompact, ?_, ?_, ?_⟩⟩
  · intro a i hai
    simpa [S, hai] using hχsupp a
  · intro a hai
    simpa [S, hai] using hχsupp a
  · intro x hx
    calc
      (∑ a ∈ Finset.univ.filter (fun a => (idx a).isSome), χ a x) =
          ∑ a ∈ Finset.univ, χ a x := by
        apply Finset.sum_subset
        · exact Finset.filter_subset _ _
        · intro a _ ha
          have hnone : idx a = none := by
            cases hidx : idx a with
            | none => rfl
            | some i => simp [hidx] at ha
          have hsupp : tsupport (χ a) ⊆ Kᶜ := by
            simpa [S, hnone] using hχsupp a
          by_contra hzero
          exact (hsupp (subset_tsupport _ hzero)) hx
      _ = 1 := hχsum x

/-- The topological cutoff partition and the finite regular-piece exhaustion
can be chosen at the same stage for any compact subset of the regular locus.
This packages exactly the data a later local current argument may consume. -/
theorem exists_exhaustionStage_and_compactCutoffPartition [CompactSpace M]
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    {H : ℕ → RegularPieceFamily V (∅ : Set M)}
    (hexh : ∀ K : Set M, IsCompact K →
      K ⊆ regularLocus (n := n) V.carrier V.dim → ∃ m,
        K ⊆ coveredRegion (H m))
    {K : Set M} (hKcompact : IsCompact K)
    (hKregular : K ⊆ regularLocus (n := n) V.carrier V.dim)
    (hKclosed : IsClosed K) {r : ℕ} (U : Fin r → Opens M)
    (hcover : K ⊆ ⋃ i, (U i : Set M)) :
    ∃ m, K ⊆ coveredRegion (H m) ∧
      Nonempty (CompactCutoffPartition (n := n) K U) := by
  obtain ⟨m, hm⟩ := hexh K hKcompact hKregular
  exact ⟨m, hm, exists_compactCutoffPartition K hKclosed U hcover⟩

end

end SGPT.Foundations.Analysis.Pending.RegularLocusCutoffPartitionReduction
