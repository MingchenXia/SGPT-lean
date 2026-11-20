import SGPT.Bergman.SourceAndreiefIntegral
import SGPT.Bergman.SourceOriginalGramTrace

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

/-- The actual preferred-frame scalar evaluation preserves the ORIGINAL
physical Hermitian pairing pointwise. It is proved by genuine section
polarization and the already proved exact evaluation norm, not supplied
as a pairing/frame certificate. -/
theorem sourceWeightedEvaluation_pairing (s r : SourceHilbertSections L T W μ hBM k hk φ)
    (x : W.carrier) :
    conj (sourceWeightedEvaluation L T W μ hBM k hk φ x s) *
        sourceWeightedEvaluation L T W μ hBM k hk φ x r =
      weightedHermitianPairing L T W k
        (sourceOriginalSectionLinear L T W μ hBM k hk φ s)
        (sourceOriginalSectionLinear L T W μ hBM k hk φ r) x := by
  let E := sourceWeightedEvaluation L T W μ hBM k hk φ x
  have hn (q : SourceHilbertSections L T W μ hBM k hk φ) :
      (‖E q‖ : ℂ) ^ 2 = (weightedQuadraticDensity L T W k
        (sourceOriginalSectionLinear L T W μ hBM k hk φ q) x : ℂ) := by
    rw [sourceWeightedEvaluation_continuous_norm]
    exact (Complex.ofReal_pow _ _).symm
  have hadd : E s + E r = E (s + r) := (map_add E s r).symm
  have hsub : E s - E r = E (s - r) := (map_sub E s r).symm
  have hmi : E s - Complex.I * E r = E (s - Complex.I • r) := by
    rw [map_sub, map_smul, smul_eq_mul]
  have hpi : E s + Complex.I * E r = E (s + Complex.I • r) := by
    rw [map_add, map_smul, smul_eq_mul]
  change conj (E s) * E r = _
  rw [← RCLike.inner_apply']
  rw [inner_eq_sum_norm_sq_div_four]
  change (((‖E s + E r‖ : ℂ) ^ 2 - (‖E s - E r‖ : ℂ) ^ 2 +
    ((‖E s - Complex.I * E r‖ : ℂ) ^ 2 - (‖E s + Complex.I * E r‖ : ℂ) ^ 2) *
      Complex.I) / 4) = _
  rw [hadd, hsub, hmi, hpi, hn (s + r), hn (s - r), hn (s - Complex.I • r),
    hn (s + Complex.I • r), weightedHermitianPairing_polarization]
  simp only [map_add, map_sub, map_smul]

/-- The entire original ON basis's genuine preferred-frame evaluations;
the family is manufactured internally on the literal same Gamma space. -/
def sourceBasisEvaluation : sourceGramIndex L T W μ hBM k hk φ → W.carrier → ℂ :=
  fun i x => sourceWeightedEvaluation L T W μ hBM k hk φ x
    (sourceOrthonormalBasis L T W μ hBM k hk φ i)

/-- True pair continuity follows from the exact physical identity. No
global continuity/measurability of a preferred frame is assumed. -/
theorem sourceBasisEvaluation_pair_continuous
    (i j : sourceGramIndex L T W μ hBM k hk φ) :
    Continuous (fun x => conj (sourceBasisEvaluation L T W μ hBM k hk φ i x) *
      sourceBasisEvaluation L T W μ hBM k hk φ j x) := by
  have heq : (fun x => conj (sourceBasisEvaluation L T W μ hBM k hk φ i x) *
      sourceBasisEvaluation L T W μ hBM k hk φ j x) =
      weightedHermitianPairing L T W k
        (sourceOriginalSectionLinear L T W μ hBM k hk φ
          (sourceOrthonormalBasis L T W μ hBM k hk φ i))
        (sourceOriginalSectionLinear L T W μ hBM k hk φ
          (sourceOrthonormalBasis L T W μ hBM k hk φ j)) :=
    funext (fun x => sourceWeightedEvaluation_pairing L T W μ hBM k hk φ _ _ x)
  rw [heq]
  exact weightedHermitianPairing_continuous L T W k _ _

/-- Actual determinant density on tuples of ORIGINAL K points, including
the true empty determinant when the original section space is zero. -/
def sourceEvaluationDeterminantDensity
    (x : sourceGramIndex L T W μ hBM k hk φ → W.carrier) : ℝ :=
  SGPT.Bergman.Andreief.squaredEvaluationDet (sourceBasisEvaluation L T W μ hBM k hk φ) x

/-- Intrinsic pointwise positivity; no determinant-density bound/certificate. -/
theorem sourceEvaluationDeterminantDensity_nonneg
    (x : sourceGramIndex L T W μ hBM k hk φ → W.carrier) :
    0 ≤ sourceEvaluationDeterminantDensity L T W μ hBM k hk φ x :=
  Complex.normSq_nonneg _

/-- Genuine compact tuple continuity is derived from actual same-fiber
pairing products rather than a measurable-trivialization assumption. -/
theorem sourceEvaluationDeterminantDensity_continuous :
    Continuous (sourceEvaluationDeterminantDensity L T W μ hBM k hk φ) := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  exact SGPT.Bergman.Andreief.squaredEvaluationDet_continuous _
    (sourceBasisEvaluation_pair_continuous L T W μ hBM k hk φ)

end SGPT.Bergman.SingularWeightedHilbert
