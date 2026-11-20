import SGPT.Checks.Comparison.TraceNARationalSlices

/-! The actual original hull restriction detects the actual trace cutoff.
Blueprint: `trace-rational-hull-slices.tex`, cutoff node. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison

open Set Filter
open SGPT.NAPotential.Berkovich SGPT.NAPotential.Berkovich.PiecewiseLinearData
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision
open SGPT.NAPotential.Berkovich.PiecewiseLinearData.SimplexRevision.WholeHull
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open SourceTraceRepresentativeDefinition
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.NATrace

universe u
variable {n k : ℕ} {M V : Type u}
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [ConnectedSpace V]
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n M)}

/-- Literal nontriviality of the original hull restriction gives the actual
generic Lelong condition for its ACTUAL NA component, in every dimension. -/
theorem originalHull_sliceTraceable_of_nontrivial_restriction
    (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M) {ι : V → M} (s : ℝ)
    (hs : s < ((hullNAPotential D).component κ).val.max)
    (hne : ∃ y, uscRegularization (D.pointwiseUpperConcaveEnvelope s) (ι y) ≠ ⊥) :
    SliceTraceable ι (hullNAPotential D) κ s := by
  have hI := originalHull_iEquivalent_component D κ s hs
  have hu : IsThetaPshPotential (atlasClosedFormToNative (sourceNAComponentBackground θ κ)).val
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s)) := by
    rw [uscRegularization_pointwiseUpperConcaveEnvelope_eq_simplexValue]
    exact (isThetaPSH_iff_nativeThetaPotential _ _).mp (simplexValue_componentPSH D κ hs.le)
  have hg : sourceGenericLelongNumber (n := n) ι
      (uscRegularization (D.pointwiseUpperConcaveEnvelope s)) = 0 := by
    by_cases hn : n = 0
    · exact sourceGenericLelongNumber_zero_dimension hn ι _
    · obtain ⟨y, hy⟩ := hne
      have hzero : lelongNumber (n := n)
          (uscRegularization (D.pointwiseUpperConcaveEnvelope s)) (ι y) = 0 := by
        by_contra h
        exact hy (eq_bot_of_lelongNumber_pos (Nat.pos_of_ne_zero hn) hu.1 (pos_iff_ne_zero.mpr h))
      apply (nativeGeneric_zero_iff_source hn ι _).mp
      exact le_antisymm ((iInf_le _ y).trans_eq hzero) bot_le
  exact ⟨hs, SGPT.Trace.sourceGenericLelongNumber_eq_zero_of_iOrder hu
    ((sourceIOrder_iff_native hI.1.1 hI.1.2.1).mp hI.1) hg⟩

/-- Above the ACTUAL trace cutoff, the literal original regularized hull
restriction is identically minus infinity. No vanishing premise is assumed. -/
theorem originalHull_restriction_eq_bot_of_traceCutoff_lt
    (D : PiecewiseLinearData θ) (κ : SourceKahlerForm n M) {ι : V → M} (s : ℝ)
    (hs : s < ((hullNAPotential D).component κ).val.max)
    (hcut : traceCutoff ι (hullNAPotential D) κ < s) (y : V) :
    uscRegularization (D.pointwiseUpperConcaveEnvelope s) (ι y) = ⊥ := by
  by_contra hy
  have ht := originalHull_sliceTraceable_of_nontrivial_restriction D κ s hs ⟨y, hy⟩
  have hle : s ≤ traceCutoff ι (hullNAPotential D) κ :=
    le_csSup (traceCutoff_set_bddAbove ι (hullNAPotential D) κ) ht
  exact (not_le_of_gt hcut) hle

end SGPT.NAPotential.TraceComparison
