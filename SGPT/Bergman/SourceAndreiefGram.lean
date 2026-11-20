import SGPT.Bergman.SourceWeightedAndreief
import SGPT.Bergman.SourceEvaluationPairing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal ComplexConjugate
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

/-- The true tilted scalar evaluation Gram integral is EXACTLY the
original same-section, same-metric Gram family. No dictionary is supplied. -/
theorem integralGram_sourceBasisEvaluation_tilt (u : C(W.carrier, ℝ)) (t : ℝ) :
    SGPT.Bergman.Andreief.integralGram μ
      (SGPT.Bergman.Andreief.tiltedEvaluations
        (sourceBasisEvaluation L T W μ hBM k hk φ) u (-(k : ℝ)) t) =
      sourceOriginalGram L T W μ hBM k hk φ u t := by
  ext i j
  change (∫ x, conj (SGPT.Bergman.Andreief.tiltedEvaluations
      (sourceBasisEvaluation L T W μ hBM k hk φ) u (-(k : ℝ)) t i x) *
      SGPT.Bergman.Andreief.tiltedEvaluations
        (sourceBasisEvaluation L T W μ hBM k hk φ) u (-(k : ℝ)) t j x ∂μ) = _
  simp_rw [SGPT.Bergman.Andreief.tilted_pair]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    dsimp only [sourceOriginalGram]
    rw [RCLike.real_smul_eq_coe_mul]
    congr 1
    exact sourceWeightedEvaluation_pairing L T W μ hBM k hk φ _ _ x)

/-- Actual original Andreief identity: the true determinant of the
original physical Gram family is a real Laplace integral of the genuine
nonnegative evaluation determinant density. Empty Gamma is retained. -/
theorem sourceOriginalGram_andreief (u : C(W.carrier, ℝ)) (t : ℝ) :
    (∫ x : sourceGramIndex L T W μ hBM k hk φ → W.carrier,
      Real.exp (-(k : ℝ) * t * ∑ j, u (x j)) *
        sourceEvaluationDeterminantDensity L T W μ hBM k hk φ x
      ∂Measure.pi (fun _ : sourceGramIndex L T W μ hBM k hk φ => μ)) =
      ((Module.finrank ℂ (SourceHilbertSections L T W μ hBM k hk φ)).factorial : ℝ) *
        (sourceOriginalGram L T W μ hBM k hk φ u t).det.re := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  let : IsProbabilityMeasure μ := hBM.1
  have h := SGPT.Bergman.Andreief.integral_weighted_squaredEvaluationDet μ
    (sourceBasisEvaluation L T W μ hBM k hk φ)
    (sourceBasisEvaluation_pair_continuous L T W μ hBM k hk φ) u (-(k : ℝ)) t
  rw [integralGram_sourceBasisEvaluation_tilt] at h
  simpa only [sourceGramIndex, Fintype.card_fin, sourceEvaluationDeterminantDensity] using! h

end SGPT.Bergman.SingularWeightedHilbert
