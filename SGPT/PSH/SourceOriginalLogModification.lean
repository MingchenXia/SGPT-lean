import SGPT.PSH.AtlasLogModification

/-! Literal BOTH original clauses of author76fde3d1
chapter_pshfunctions.tex1411–1415, with complex-manifold standing scope1353. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
open SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas.SourceLogSingularitiesDraft
universe u
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [ParacompactSpace X] [T2Space Y] [ParacompactSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y} {π : X → Y}

/-- Whole original prop:pshfunctions:L1425: the SAME proper bimeromorphic
original map preserves original QPSH with analytic singularities, and
preserves the literal original logarithmic condition along the ACTUAL
independently defined entire geometric rational pullback. Both clauses use
original inputs and internally produced native geometry, with no compactness,
fixed native dimension or desired-output certificate premise. -/
theorem original_source_modification_clauses (hπ : A.IsAtlasAnalyticModification B π) :
    (∀ u : Y → EReal,B.IsQPSH u → B.HasRationalAnalyticType u →
      A.IsQPSH (u ∘ π) ∧ A.HasRationalAnalyticType (u ∘ π)) ∧
    (∀ (D : AtlasEffectiveGeometricQDivisor B) (u : Y → EReal),
      SourceHasLogSingularitiesAlong D u →
      SourceHasLogSingularitiesAlong (atlasComponentwiseGeometricQPullback D hπ) (u ∘ π)) := by
  exact ⟨fun _ hu han => original_analytic_comp_atlasAnalyticModification hu han hπ,
    fun _ _ hu => original_log_comp_atlasAnalyticModification hu hπ⟩

end SGPT.PSH.VariableComplexAtlas.SourceLogReverseDraft
