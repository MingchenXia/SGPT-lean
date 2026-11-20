import SGPT.Bergman.SourceOriginalGramTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (φ : X → EReal)

/-- Literal restriction of the actual original global test function to K. -/
def sourceBergmanTestRestriction (u : C(X, ℝ)) : C(W.carrier, ℝ) :=
  u.comp ⟨Subtype.val, continuous_subtype_val⟩

omit [CompactSpace X] [ConnectedSpace X] in
/-- Exact original global Bergman test integral, retaining the original
zero-extension/push-forward measure on X and the same included mu. -/
theorem integral_sourcePartialBergmanMeasure (u : C(X, ℝ)) :
    (∫ x, u x ∂sourcePartialBergmanMeasure L T W μ k φ) =
      ∫ x, sourceBergmanTestRestriction W u x
        ∂sourcePartialBergmanMeasureOnK L T W μ k φ := by
  rw [sourcePartialBergmanMeasure,
    integral_map measurable_subtype_coe.aemeasurable u.continuous.aestronglyMeasurable]
  rfl

/-- Actual original global test formula for the normalized log Gram
variation. The density is the original literal-Gamma unit-ball supremum
and the measure is precisely beta^k on the original X. -/
theorem hasDerivAt_normalized_log_Gram_eq_global_Bergman (u : C(X, ℝ)) :
    HasDerivAt (fun t => -((n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
        Real.log (sourceOriginalGram L T W μ hBM k hk φ
          (sourceBergmanTestRestriction W u) t).det.re)
      (∫ x, u x ∂sourcePartialBergmanMeasure L T W μ k φ) 0 := by
  rw [integral_sourcePartialBergmanMeasure L T W μ k φ]
  exact hasDerivAt_normalized_log_Gram_eq_BergmanOnK L T W μ hBM k hk φ
    (sourceBergmanTestRestriction W u)

end SGPT.Bergman.SingularWeightedHilbert
