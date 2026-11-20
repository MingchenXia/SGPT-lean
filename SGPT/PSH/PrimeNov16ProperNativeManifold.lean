import SGPT.PSH.PrimeNov16SecondCountableNativeModel

/-! Actual proper domination internally supplies native countability and a
full n-manifold model, including disconnected original smooth sources.
Blueprint first: `prime-nov16-noncompact-common-model.tex`.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.PrimeNov16ProperNativeManifold
open Set CategoryTheory
open SGPT.Unibranch SourceReducedComplexSpace
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open scoped Topology Manifold ContDiff

/-- A proper map to an actual manifold manufactures second countability of
the SAME uniform native source, then its full original n-manifold model. -/
theorem exists_native_manifold_of_proper_map
    {R : SourceReducedComplexSpace} {n m : ℕ} {M : Type}
    [TopologicalSpace M] [ChartedSpace (ComplexModel m) M] [IsComplexManifold m M]
    (h : PrimeNov16SecondCountableNativeModel.UniformSmoothModels R n)
    (f : R.obj.left → M) (hf : IsProperMap f) :
    ∃ N : BlowupTowers.CMfd.{0} n,
      Nonempty (OriginalNativeModification.wholeModel (n := n) N ≅ R) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (ComplexModel m) M
  let : SigmaCompactSpace M := inferInstance
  let : SigmaCompactSpace R.obj.left := ⟨⟨fun i => f ⁻¹' compactCovering M i,
    fun i => hf.isCompact_preimage (isCompact_compactCovering M i), by
      rw [← preimage_iUnion, iUnion_compactCovering, preimage_univ]⟩⟩
  let := PrimeNov16SecondCountableNativeModel.nativeChartedSpace h
  let : SecondCountableTopology R.obj.left :=
    ChartedSpace.secondCountable_of_sigmaCompact (ComplexModel n) R.obj.left
  exact PrimeNov16SecondCountableNativeModel.exists_native_manifold_model_of_uniform h

end SGPT.PSH.PrimeNov16ProperNativeManifold
