import SGPT.Hodge.BDivChainZeroWeilDraft

/-!
# Zero-dimensional cofinality of actual model systems

This narrow zero-dimensional argument does not assume Chow's
lemma. It does not establish cofinality in positive dimensions or identify
`volumeAny` with any previously undefined zero-dimensional source volume.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace SGPT.Hodge.BDivChain.NativeDraft

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.Pending SGPT.BDivisor

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel 0) X]
  [IsComplexManifold 0 X] [CompactSpace X] [ConnectedSpace X]

omit [CompactSpace X] in
/-- Every actual analytic modification of a connected zero-dimensional
manifold is dominated by the actual root. -/
theorem modification_le_root_zero (π : Modification 0 X) : π ≤ Modification.root := by
  let : Subsingleton X := SGPT.NPP.subsingleton_of_dim_zero
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨y, _hy⟩ :=
    AnalyticModificationStrongPullback.surjective_of_isAnalyticModification
      π.isAnalyticModification x
  refine ⟨fun _ => y, contMDiff_const, ?_⟩
  funext z
  change π.map y = z
  exact Subsingleton.elim _ _

omit [CompactSpace X] in
/-- In dimension zero every actual model system is cofinal among ALL actual
analytic modifications, since each system contains the root. -/
theorem modelSystem_isCofinal_zero (S : ModelSystem 0 X) : S.IsCofinal := by
  intro π
  exact ⟨ModelSystem.Model.root, modification_le_root_zero π⟩

/-- In particular, the book's actual finite-blowup model system is cofinal in
dimension zero, independently of the unsettled general-dimensional comparison. -/
theorem blowup_isCofinal_zero : (ModelSystem.blowup 0 X).IsCofinal :=
  modelSystem_isCofinal_zero (ModelSystem.blowup 0 X)

end SGPT.Hodge.BDivChain.NativeDraft
