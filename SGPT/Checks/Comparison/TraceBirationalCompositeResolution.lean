import SGPT.Checks.Comparison.TraceBirationalStrictTransform

/-! L655 actual compatible resolution geometry: the composite of EVERY
actual strict-transform resolution with the ORIGINAL actual modification
is an ACTUAL downstairs resolution, with original geometry produced.
No Hironaka implementation or supplied common-model certificate.
Blueprint: trace-birational-strict-transform.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
namespace SGPT.NAPotential.TraceComparison.BirationalGeometry
open Set Filter
open SGPT.Trace.Trace2Resolution
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.FirstPass.NonKahlerLocus
open AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) X] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n X] [IsComplexManifold n Y]
  {π : Y → X} (hπ : IsAnalyticModification (n := n) π)

include hπ in
/-- Genuine composite resolution of ORIGINAL downstairs Z. Carrier/image,
actual thin inverse locus and injectivity are all derived internally. -/
theorem isResolutionOf_comp_of_originalStrictTransform
    (Z : ClosedIrreducibleAnalyticSubvariety n X)
    (hZ : ¬ Z.carrier ⊆ π '' exceptionalLocus n π)
    (W : ClosedIrreducibleAnalyticSubvariety n Y)
    (hW : W.carrier = strictTransform n π Z.carrier) (RW : ResolutionTarget W) :
    IsResolutionOf Z (π ∘ RW.ι) := by
  let f := π ∘ RW.ι
  have hf : ContMDiff 𝓘(ℂ, ComplexModel W.dim) 𝓘(ℂ, ComplexModel n) ∞ f :=
    hπ.1.comp RW.contMDiff
  have himage := RawProperStrictTransformLelongReader.image_eq_of_strictTransform
    hπ.1 hπ.2.1 Z W hW
  have hrange : range f = Z.carrier := by
    rw [range_comp,RW.isResolutionOf.range_eq,himage]
  obtain ⟨BW,hBW,_hWsing,hinjW,hdW⟩ := RW.isResolutionOf.exists_isoLocus
  let T := π '' exceptionalLocus n π
  have hTa : IsComplexAnalyticSubset (n := n) T :=
    AnalyticModificationExceptionalImageCodimension.isComplexAnalyticSubset_image_exceptionalLocus hπ
  have hIa : IsComplexAnalyticSubset (n := n) (π '' BW) :=
    ProperMappingTheorem.isComplexAnalyticSubset_image hπ.1 hBW fun K hK =>
      (hπ.2.1.isCompact_preimage hK).inter_left hBW.isClosed
  have hSa : IsComplexAnalyticSubset (n := n) (singularLocus Z) := by
    exact StokesSingularLocusAnalytic.isComplexAnalyticSubset_singularLocus Z
  let B := T ∪ π '' BW ∪ singularLocus Z
  have hBa : IsComplexAnalyticSubset (n := n) B :=
    ConstantRankImage.IsComplexAnalyticSubset.union
      (ConstantRankImage.IsComplexAnalyticSubset.union hTa hIa) hSa
  let A₀ := f ⁻¹' T
  let A₁ := RW.ι ⁻¹' BW
  let A₂ := f ⁻¹' singularLocus Z
  have hA₀a := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hTa
  have hA₂a := AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hf hSa
  have hA₀ : interior A₀ = ∅ := by
    obtain ⟨z,hzZ,hzT⟩ := not_subset.mp hZ
    have hz : z ∈ range f := hrange.symm ▸ hzZ
    obtain ⟨v,hv⟩ := hz
    apply SGPT.Trace.P5Wire.interior_eq_empty_of_not_mem hA₀a (v := v)
    change f v ∉ T
    rw [hv]
    exact hzT
  have hA₁ : interior A₁ = ∅ := by
    rw [interior_eq_empty_iff_dense_compl,← preimage_compl]
    exact hdW
  have hA₂ : interior A₂ = ∅ := by
    obtain ⟨z,hzreg⟩ := Z.regularLocus_nonempty
    have hzZ : z ∈ Z.carrier := hzreg.2.1
    have hz : z ∈ range f := hrange.symm ▸ hzZ
    obtain ⟨v,hv⟩ := hz
    apply SGPT.Trace.P5Wire.interior_eq_empty_of_not_mem hA₂a (v := v)
    change f v ∉ singularLocus Z
    rw [hv]
    exact fun hzsing => hzsing.2 hzreg
  have hA₀c : IsClosed A₀ := hTa.isClosed.preimage hf.continuous
  have hA₁c : IsClosed A₁ := hBW.isClosed.preimage RW.contMDiff.continuous
  have hunion : interior (A₀ ∪ A₁ ∪ A₂) = ∅ := by
    rw [interior_union_isClosed_of_interior_empty (hA₀c.union hA₁c) hA₂,
      interior_union_isClosed_of_interior_empty hA₀c hA₁,hA₀]
  have hsub : f ⁻¹' B ⊆ A₀ ∪ A₁ ∪ A₂ := by
    intro v hv
    rcases hv with (hvT | hvBW) | hvS
    · exact Or.inl (Or.inl hvT)
    · by_cases hvT : f v ∈ T
      · exact Or.inl (Or.inl hvT)
      · obtain ⟨y,hyBW,hyf⟩ := hvBW
        have hnot : RW.ι v ∉ exceptionalLocus n π :=
          fun he => hvT ⟨RW.ι v,he,rfl⟩
        have heq : y = RW.ι v :=
          AnalyticModificationExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hπ hnot hyf
        exact Or.inl (Or.inr (show RW.ι v ∈ BW from heq ▸ hyBW))
    · exact Or.inr hvS
  have hthin : interior (f ⁻¹' B) = ∅ :=
    subset_empty_iff.mp ((interior_mono hsub).trans hunion.subset)
  refine ⟨hrange,B,hBa,fun _ h => Or.inr h,?_,?_⟩
  · intro v hv w hw hEq
    have hwT : f w ∉ T := fun h => hw (Or.inl (Or.inl h))
    have hnot : RW.ι w ∉ exceptionalLocus n π := fun h => hwT ⟨RW.ι w,h,rfl⟩
    have heq : RW.ι v = RW.ι w :=
      AnalyticModificationExceptionalFibres.eq_of_apply_eq_of_not_mem_exceptionalLocus hπ hnot hEq
    apply hinjW _ _ heq
    · exact fun h => hv (Or.inl (Or.inr ⟨RW.ι v,h,rfl⟩))
    · exact fun h => hw (Or.inl (Or.inr ⟨RW.ι w,h,rfl⟩))
  · rw [preimage_compl]
    exact interior_eq_empty_iff_dense_compl.mp hthin

/-- The ACTUAL downstairs resolution uses SAME V, SAME atlas/model index,
SAME original target Kahler form. Original Z and source avoidance alone
produce W; no common-model or dimension-cast certificate is input. -/
def compositeResolutionTarget (Z : ClosedIrreducibleAnalyticSubvariety n X)
    (hZ : ¬ Z.carrier ⊆ π '' exceptionalLocus n π)
    (RW : ResolutionTarget (originalStrictTransform hπ Z hZ)) : ResolutionTarget Z where
  V := RW.V
  topologicalSpace := RW.topologicalSpace
  chartedSpace := RW.chartedSpace
  isComplexManifold := RW.isComplexManifold
  compactSpace := RW.compactSpace
  connectedSpace := RW.connectedSpace
  ι := π ∘ RW.ι
  contMDiff := by
    let : ChartedSpace (ComplexModel Z.dim) RW.V := RW.chartedSpace
    exact hπ.1.comp RW.contMDiff
  isResolutionOf := isResolutionOf_comp_of_originalStrictTransform hπ Z hZ
    (originalStrictTransform hπ Z hZ) (originalStrictTransform_carrier hπ Z hZ) RW
  kahler := RW.kahler

end SGPT.NAPotential.TraceComparison.BirationalGeometry
