import SGPT.Bergman.SourceAndreiefGram
import Mathlib.MeasureTheory.Measure.WithDensity

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

/-- The actual determinant-density measure on ORIGINAL point tuples,
manufactured from the true internally produced original evaluation basis. -/
def sourceDeterminantTupleMeasure :
    Measure (sourceGramIndex L T W μ hBM k hk φ → W.carrier) :=
  (Measure.pi (fun _ : sourceGramIndex L T W μ hBM k hk φ => μ)).withDensity
    (fun x => ENNReal.ofReal (sourceEvaluationDeterminantDensity L T W μ hBM k hk φ x))

/-- Genuine compact determinant continuity and the original BM probability
produce finite measure; no tuple-density integrability bound is supplied. -/
instance sourceDeterminantTupleMeasureFinite :
    IsFiniteMeasure (sourceDeterminantTupleMeasure L T W μ hBM k hk φ) := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  let : IsProbabilityMeasure μ := hBM.1
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((sourceEvaluationDeterminantDensity_continuous L T W μ hBM k hk φ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall (sourceEvaluationDeterminantDensity_nonneg L T W μ hBM k hk φ))]
  exact ENNReal.ofReal_ne_top

/-- Literal original test weight summed over the actual point tuple. -/
def sourceDeterminantTuplePotential (u : C(W.carrier, ℝ)) :
    C((sourceGramIndex L T W μ hBM k hk φ → W.carrier), ℝ) :=
  ⟨fun x => -(k : ℝ) * ∑ j, u (x j),
    continuous_const.mul (continuous_finsetSum _
      (fun j _ => u.continuous.comp (continuous_apply j)))⟩

/-- Exact real integral against the actual tuple determinant measure. -/
theorem integral_sourceDeterminantTupleMeasure
    (g : (sourceGramIndex L T W μ hBM k hk φ → W.carrier) → ℝ) :
    (∫ x, g x ∂sourceDeterminantTupleMeasure L T W μ hBM k hk φ) =
      ∫ x, sourceEvaluationDeterminantDensity L T W μ hBM k hk φ x * g x
        ∂Measure.pi (fun _ : sourceGramIndex L T W μ hBM k hk φ => μ) := by
  unfold sourceDeterminantTupleMeasure
  have hread := integral_withDensity_eq_integral_toReal_smul
    (μ := Measure.pi (fun _ : sourceGramIndex L T W μ hBM k hk φ => μ))
    (f := fun x => ENNReal.ofReal (sourceEvaluationDeterminantDensity L T W μ hBM k hk φ x))
    ((ENNReal.continuous_ofReal.comp
      (sourceEvaluationDeterminantDensity_continuous L T W μ hBM k hk φ)).measurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) g
  simpa only [ENNReal.toReal_ofReal
    (sourceEvaluationDeterminantDensity_nonneg L T W μ hBM k hk φ _), smul_eq_mul] using! hread

/-- Native original Gram determinant / actual Laplace measure reader.
All tuple density, pairing, product measure and normalization data are
internally produced; there is no incoming Andreief/Laplace certificate. -/
theorem sourceOriginalGram_laplace (u : C(W.carrier, ℝ)) (t : ℝ) :
    (∫ x, Real.exp (t * sourceDeterminantTuplePotential L T W μ hBM k hk φ u x)
      ∂sourceDeterminantTupleMeasure L T W μ hBM k hk φ) =
      ((Module.finrank ℂ (SourceHilbertSections L T W μ hBM k hk φ)).factorial : ℝ) *
        (sourceOriginalGram L T W μ hBM k hk φ u t).det.re := by
  rw [integral_sourceDeterminantTupleMeasure]
  calc
    _ = ∫ x : sourceGramIndex L T W μ hBM k hk φ → W.carrier,
        Real.exp (-(k : ℝ) * t * ∑ j, u (x j)) *
          sourceEvaluationDeterminantDensity L T W μ hBM k hk φ x
        ∂Measure.pi (fun _ : sourceGramIndex L T W μ hBM k hk φ => μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only [sourceDeterminantTuplePotential, ContinuousMap.coe_mk]
        rw [mul_comm]
        congr 1
        congr 1
        ring)
    _ = _ := sourceOriginalGram_andreief L T W μ hBM k hk φ u t

end SGPT.Bergman.SingularWeightedHilbert
