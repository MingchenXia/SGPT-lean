import SGPT.Foundations.Analysis.Pending.AnalyticModificationPositiveCriticalFibres
import SGPT.Foundations.Analysis.Pending.HolomorphicIntrinsicExceptionalAnalytic
import SGPT.Foundations.Analysis.Pending.AnalyticImageDimension
import SGPT.Foundations.Analysis.Pending.ProperMappingTheorem
import SGPT.Foundations.Analysis.Pending.ThinDimensionDrop

set_option autoImplicit false

/-!
# No divisor lies in the intrinsic exceptional image

The actual differential exceptional locus is analytic and thin.  Every actual
fibre meeting it is wholly contained in it and has positive local dimension.
Remmert and the image-dimension bound therefore exclude every whole codimension
one irreducible subvariety from the intrinsic exceptional image.  Chosen enlarged
exceptional witnesses are used only to prove thinness of the intrinsic locus.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalImageCodimension

open FirstPass FirstPass.BlowupSequences AnalyticModificationLocalDiscrepancy
  AnalyticDimensionBasics

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Properness and the actual analytic critical locus give analyticity of its image. -/
theorem isComplexAnalyticSubset_image_exceptionalLocus
    {g : Y → X} (hg : IsAnalyticModification (n := n) g) :
    IsComplexAnalyticSubset (n := n) (g '' exceptionalLocus n g) := by
  have hEa := HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hg.1
  exact ProperMappingTheorem.isComplexAnalyticSubset_image hg.1 hEa fun K hK =>
    (hg.2.1.isCompact_preimage hK).inter_left hEa.isClosed

/-- The regular-point dimension inequality retains the empty-image conclusion
in dimensions zero and one, without a truncated codimension-two bound. -/
theorem add_one_le_pred_of_regularAtDim_image
    {g : Y → X} (hg : IsAnalyticModification (n := n) g) {x : X} {d : ℕ}
    (hx : RegularAtDim (n := n) (g '' exceptionalLocus n g) x d) : d + 1 ≤ n - 1 := by
  obtain ⟨A, _, _, hAi, _, hnon⟩ := exists_analytic_exceptional_set_of_isAnalyticModification hg
  have hEA : exceptionalLocus n g ⊆ A := by
    intro y hy
    by_contra hyA
    exact (hnon y hyA) hy
  have hthin : ∀ O : Set Y, IsOpen O → O ∩ univ ⊆ exceptionalLocus n g → O ∩ univ = ∅ := by
    intro O hO hOE
    have hOA : O ⊆ A := fun y hy => hEA (hOE ⟨hy, mem_univ y⟩)
    have hOi : O ⊆ interior A := interior_maximal hOA hO
    rw [hAi] at hOi
    simpa only [inter_univ] using subset_empty_iff.mp hOi
  have hdimY : DimLE (n := n) (univ : Set Y) n := by
    intro y k hy
    exact (RegularPointDimension.eq_of_regularAtDim hy
      (AnalyticIrreducibleComponents.regularAtDim_univ y)).le
  have hdimE : DimLE (n := n) (exceptionalLocus n g) (n - 1) :=
    ThinDimensionDrop.dimLE_pred_of_thin isComplexAnalyticSubset_univ (subset_univ _)
      hthin hdimY
  have hfib : ∀ y ∈ exceptionalLocus n g,
      LocDimGE (n := n) (exceptionalLocus n g ∩ g ⁻¹' {g y}) y 1 := by
    intro y hy
    have heq : exceptionalLocus n g ∩ g ⁻¹' {g y} = g ⁻¹' ({g y} : Set X) := by
      refine Subset.antisymm inter_subset_right ?_
      intro z hz
      have hzE : z ∈ g ⁻¹' (g '' exceptionalLocus n g) := ⟨y, hy, hz.symm⟩
      rw [AnalyticModificationExceptionalFibres.preimage_image_exceptionalLocus hg] at hzE
      exact ⟨hzE, hz⟩
    rw [heq]
    exact AnalyticModificationPositiveCriticalFibres.locDimGE_fibre_of_mem_exceptionalLocus hg hy
  exact AnalyticImageDimension.add_le_of_regularAtDim_image hg.1
    (HolomorphicIntrinsicExceptionalAnalytic.isComplexAnalyticSubset_exceptionalLocus hg.1)
    hdimE hfib hx

/-- Every specified whole codimension-one prime, including a singular prime,
meets the complement of the intrinsic exceptional image. -/
theorem not_subset_image_exceptionalLocus_of_codim_one
    {g : Y → X} (hg : IsAnalyticModification (n := n) g)
    (V : ClosedIrreducibleAnalyticSubvariety n X) (hVdim : V.dim + 1 = n) :
    ¬ V.carrier ⊆ g '' exceptionalLocus n g := by
  intro hsub
  obtain ⟨x, _, hx⟩ := V.exists_regular_point
  obtain ⟨z, _, d, hd, hz⟩ :=
    DimensionMonotone.locDimGE_of_regularAtDim_subset
      (isComplexAnalyticSubset_image_exceptionalLocus hg) hsub hx univ univ_mem
  have hbound := add_one_le_pred_of_regularAtDim_image hg hz
  omega

end SGPT.Foundations.Analysis.Pending.AnalyticModificationExceptionalImageCodimension
