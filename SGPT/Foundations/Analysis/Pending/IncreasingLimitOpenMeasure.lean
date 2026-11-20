import SGPT.Foundations.Analysis.Pending.IncreasingLimitMass

set_option autoImplicit false

/-!
# The increasing-limit semicontinuity inequality on open sets

`Pending.IncreasingLimitMass` proves the local statement

  `θ^n_{sup* u_j} G ≤ liminf_j θ^n_{u_j} G`   for `G` open inside a chart patch,

and turns it into a bound on the TOTAL mass by a partition of unity
(`measure_univ_le_liminf_of_local`).  Xia's Corollary 2.4.1
(`xia-sgpt:page-0075`) is used in the proofs of Theorem 3.1.1 and Corollary
3.1.1 (`xia-sgpt:page-0101`) as a statement about *measures*, not just about
total masses, so the same local input has to reach every open set of the
manifold and not only `univ`.

No new analysis is needed: restricting both sides to a fixed open set `G`
turns an open set of the manifold into `univ` for the restricted measures, and
the local hypothesis is stable under that restriction because `H ∩ G` is again
open and still inside the patch.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.IncreasingLimitOpenMeasure

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.IncreasingLimitMass

noncomputable section

/-- The open-set form of `measure_univ_le_liminf_of_local`: a measure which is
locally below the lower limit of a sequence of measures on the open subsets of
a neighbourhood of every point is below it on **every** open set. -/
theorem measure_isOpen_le_liminf_of_local {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) (nu : ℕ → Measure X)
    (h : ∀ x : X, ∃ O : Set X, IsOpen O ∧ x ∈ O ∧
      ∀ G : Set X, IsOpen G → G ⊆ O → mu G ≤ liminf (fun j => nu j G) atTop)
    {G : Set X} (hG : IsOpen G) :
    mu G ≤ liminf (fun j => nu j G) atTop := by
  have key := measure_univ_le_liminf_of_local (mu.restrict G)
    (fun j => (nu j).restrict G) ?_
  · simpa only [Measure.restrict_apply_univ] using key
  · intro x
    obtain ⟨O, hO, hxO, hlim⟩ := h x
    refine ⟨O, hO, hxO, fun H hH hHO => ?_⟩
    simp only [Measure.restrict_apply' hG.measurableSet]
    exact hlim (H ∩ G) (hH.inter hG) (inter_subset_left.trans hHO)

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Xia, Corollary 2.4.1 in measure form, on open sets.**  The diagonal
non-pluripolar measure of the regularized limit of an increasing sequence of
`theta`-PSH potentials is, on every open set, at most the lower limit of the
measures of the sequence. -/
theorem diagonalPotentialMeasure_isOpen_le_liminf
    {theta : ClosedRealOneOneForm n M} (u : ℕ → M → EReal)
    (hu : ∀ j, IsThetaPshPotential theta.val (u j)) (hmono : Monotone u)
    (hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, u j)))
    {G : Set M} (hG : IsOpen G) :
    diagonalPotentialMeasure theta (uscRegularization (⨆ j, u j)) hU G ≤
      liminf (fun j => diagonalPotentialMeasure theta (u j) (hu j) G) atTop :=
  measure_isOpen_le_liminf_of_local _ _
    (exists_nhds_diagonalPotentialMeasure_le_liminf u hu hmono hU) hG

end Manifold

end

end SGPT.Foundations.Analysis.Pending.IncreasingLimitOpenMeasure
