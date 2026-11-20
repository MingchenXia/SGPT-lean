import SGPT.Bergman.SourcePerturbedHilbert
import SGPT.Bergman.SourceComplexGramNormVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.Bergman.QuantizationFrontier SGPT.Bergman.PartialDonaldson

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (φ : X → EReal)

local instance sourceOriginalBaseHilbertMeasurable :
    MeasurableSpace (SourceHilbertSections L T W μ hBM k hk φ) := borel _
local instance sourceOriginalBaseHilbertBorel :
    BorelSpace (SourceHilbertSections L T W μ hBM k hk φ) := ⟨rfl⟩

/-- The actual whole-section identity equivalence is continuous in both
genuine finite-dimensional norm topologies, internally. -/
def sourceBaseHilbertGammaContinuousEquiv :
    SourceHilbertSections L T W μ hBM k hk φ ≃L[ℂ] idealSections L T k φ :=
  (sourceHilbertOriginalEquiv L T W μ hBM k hk φ).toContinuousLinearEquiv

/-- A genuine original Lebesgue/Haar measure on the book's ENTIRE original
ideal-Gamma space, manufactured by the actual whole-section equivalence. -/
def sourceOriginalGammaHaar : Measure (idealSections L T k φ) :=
  Measure.map (sourceBaseHilbertGammaContinuousEquiv L T W μ hBM k hk φ)
    (Measure.addHaar : Measure (SourceHilbertSections L T W μ hBM k hk φ))

/-- The produced original section-space measure really is Haar; this is
proved from actual finite-dimensional continuous maps in both directions. -/
instance sourceOriginalGammaHaarIsAddHaar :
    (sourceOriginalGammaHaar L T W μ hBM k hk φ).IsAddHaarMeasure :=
  (sourceHilbertOriginalEquiv L T W μ hBM k hk φ).toAddEquiv.isAddHaarMeasure_map
    Measure.addHaar
    (sourceBaseHilbertGammaContinuousEquiv L T W μ hBM k hk φ).continuous
    (sourceBaseHilbertGammaContinuousEquiv L T W μ hBM k hk φ).symm.continuous

/-- Literal original norm-ball volume is the actual Hilbert norm-ball
preimage measure, through the genuine identity on EVERY original section. -/
theorem sourceOriginalGammaHaar_normball_preimage (u : C(W.carrier, ℝ)) (t : ℝ) :
    sourceOriginalGammaHaar L T W μ hBM k hk φ
      (normUnitBall (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t)) =
      (Measure.addHaar : Measure (SourceHilbertSections L T W μ hBM k hk φ))
        {s | ‖sourceOriginalToPerturbedHilbert L T W μ hBM k hk φ u t s‖ ≤ 1} := by
  rw [sourceOriginalGammaHaar, Measure.map_apply
    (sourceBaseHilbertGammaContinuousEquiv L T W μ hBM k hk φ).continuous.measurable
    (normUnitBall_isCompact _).measurableSet]
  rfl

/-- Exact physical original norm-ball Haar volume / original Gram
determinant identity, with no volume or Gram dictionary as an input. -/
theorem sourceOriginalGammaHaar_normball_volume (u : C(W.carrier, ℝ)) (t : ℝ) :
    sourceOriginalGammaHaar L T W μ hBM k hk φ
      (normUnitBall (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t)) =
      ENNReal.ofReal ((sourceOriginalGram L T W μ hBM k hk φ u t).det.re)⁻¹ *
        (Measure.addHaar : Measure (SourceHilbertSections L T W μ hBM k hk φ))
          (closedBall 0 1) := by
  rw [sourceOriginalGammaHaar_normball_preimage,
    SGPT.Bergman.GramNormVolume.measure_normball_eq_gram Measure.addHaar
      (sourceOrthonormalBasis L T W μ hBM k hk φ)
      (sourceOriginalToPerturbedHilbert L T W μ hBM k hk φ u t),
    sourceOriginalToPerturbedHilbert_gram]

/-- At the base weight the actual original ball has precisely the native
base-Hilbert unit-ball Haar volume, including zero section dimension. -/
theorem sourceOriginalGammaHaar_normball_zero (u : C(W.carrier, ℝ)) :
    sourceOriginalGammaHaar L T W μ hBM k hk φ
      (normUnitBall (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u 0)) =
      (Measure.addHaar : Measure (SourceHilbertSections L T W μ hBM k hk φ))
        (closedBall 0 1) := by
  rw [sourceOriginalGammaHaar_normball_volume, sourceOriginalGram_zero]
  simp only [Matrix.det_one, Complex.one_re, ENNReal.ofReal_one, inv_one, one_mul]

/-- Genuine original real norm-ball log ratio equals the original Gram
log determinant. The positive finite Haar volumes and determinant needed
by the real logarithm are internally established. -/
theorem sourceOriginalGammaHaar_log_normball_ratio (u : C(W.carrier, ℝ)) (t : ℝ) :
    Real.log ((sourceOriginalGammaHaar L T W μ hBM k hk φ).real
        (normUnitBall (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t)) /
      (sourceOriginalGammaHaar L T W μ hBM k hk φ).real
        (normUnitBall (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u 0))) =
      -Real.log (sourceOriginalGram L T W μ hBM k hk φ u t).det.re := by
  change Real.log ((sourceOriginalGammaHaar L T W μ hBM k hk φ
        (normUnitBall (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t))).toReal /
      (sourceOriginalGammaHaar L T W μ hBM k hk φ
        (normUnitBall (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u 0))).toReal) = _
  rw [sourceOriginalGammaHaar_normball_preimage, sourceOriginalGammaHaar_normball_zero]
  have h := SGPT.Bergman.GramNormVolume.log_real_normball_ratio_eq_neg_log_gram
    (Measure.addHaar : Measure (SourceHilbertSections L T W μ hBM k hk φ))
    (sourceOrthonormalBasis L T W μ hBM k hk φ)
    (sourceOriginalToPerturbedHilbert L T W μ hBM k hk φ u t)
  rw [sourceOriginalToPerturbedHilbert_gram] at h
  exact h

end SGPT.Bergman.SingularWeightedHilbert
