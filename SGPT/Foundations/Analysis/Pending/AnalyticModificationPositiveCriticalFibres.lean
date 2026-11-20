import SGPT.Foundations.Analysis.Pending.AnalyticModificationSingletonFibreInverse
import SGPT.Foundations.Analysis.Pending.FibreDimensionLowerBound
import SGPT.Foundations.Analysis.Pending.AnalyticDimensionBasics

set_option autoImplicit false

/-!
# Positive local dimension of intrinsic critical fibres

Actual connected fibres and the internally constructed singleton-fibre inverse
show that every point of the differential exceptional locus is an accumulation
point of its actual fibre.  Analytic dimension-zero isolation then gives local
complex dimension at least one.  No codimension claim is made for the enlarged
exceptional witnesses in the modification definition.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace SGPT.Foundations.Analysis.Pending.AnalyticModificationPositiveCriticalFibres

open FirstPass FirstPass.BlowupSequences AnalyticModificationLocalDiscrepancy
  AnalyticDimensionBasics

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Every actual critical point of a proper holomorphic modification lies
on an actual analytic fibre of positive local complex dimension. -/
theorem locDimGE_fibre_of_mem_exceptionalLocus
    {g : Y → X} (hg : IsAnalyticModification (n := n) g) {y : Y}
    (hy : y ∈ exceptionalLocus n g) :
    LocDimGE (n := n) (g ⁻¹' ({g y} : Set X)) y 1 := by
  let F : Set Y := g ⁻¹' ({g y} : Set X)
  have hacc : AccPt y (𝓟 F) := by
    by_contra hnot
    rw [accPt_iff_nhds] at hnot
    push Not at hnot
    obtain ⟨U, hU, huniqU⟩ := hnot
    obtain ⟨O, hOU, hOo, hyO⟩ := _root_.mem_nhds_iff.mp hU
    have hunique : ∀ z : Y, g z = g y → z = y := by
      intro z hzF
      by_contra hz
      have hcover : F ⊆ O ∪ ({y} : Set Y)ᶜ := by
        intro w _
        by_cases hw : w = y
        · exact Or.inl (hw ▸ hyO)
        · exact Or.inr hw
      have hconn := (AnalyticModificationConnectedFibres.isConnected_fibre hg (g y)).1
      obtain ⟨w, hwF, hwO, hwn⟩ := hconn.isPreconnected O ({y} : Set Y)ᶜ hOo
        isOpen_compl_singleton hcover ⟨y, rfl, hyO⟩ ⟨z, hzF, hz⟩
      have hwEq : w = y := huniqU w ⟨hOU hwO, hwF⟩
      exact hwn (by simpa only [mem_singleton_iff] using hwEq)
    exact (AnalyticModificationSingletonFibreInverse.not_mem_exceptionalLocus_of_unique_fibre
      hg y hunique) hy
  have hFa : IsComplexAnalyticSubset (n := n) F :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hg.1
      (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (g y))
  intro U hU
  by_contra hnot
  have h0 : LocDimLE (n := n) F y 0 := by
    refine ⟨U, hU, fun z hz k hreg => ?_⟩
    have hkn : ¬ 1 ≤ k := fun hk => hnot ⟨z, hz, k, hk, hreg⟩
    omega
  exact (not_accPt_of_locDimLE_zero hFa rfl h0) hacc

end SGPT.Foundations.Analysis.Pending.AnalyticModificationPositiveCriticalFibres
