import SGPT.Bergman.SourcePerturbedL2Norm
import SGPT.Bergman.SourceOriginalGramTrace
import Mathlib.Analysis.InnerProductSpace.GramMatrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory
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

/-- Actual perturbed norm parallelogram, internally derived from the true
same-fiber quadratic integrals. No Hilbert certificate is supplied. -/
theorem sourcePerturbedPartialL2Norm_parallelogram (u : C(W.carrier, ℝ)) (t : ℝ)
    (s r : idealSections L T k φ) :
    ((sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t).toAddGroupNorm (s + r)) ^ 2 +
      ((sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t).toAddGroupNorm (s - r)) ^ 2 =
      2 * (((sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t).toAddGroupNorm s) ^ 2 +
        ((sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t).toAddGroupNorm r) ^ 2) := by
  let : IsProbabilityMeasure μ := hBM.1
  simp_rw [sourcePerturbedPartialL2Norm_sq_integral]
  have hi (q : twistedSections L T k) :=
    weightedQuadraticDensity_integrable L T (sourcePerturbedWeightedSubset W u t) k μ q
  dsimp only [sourcePerturbedWeightedSubset] at hi ⊢
  rw [← integral_add
      (hi (s + r).val) (hi (s - r).val),
    ← integral_add (hi s.val) (hi r.val),
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (weightedQuadraticDensity_parallelogram L T (sourcePerturbedWeightedSubset W u t) k s.val r.val)

/-- The genuine varying norm wrapper retains EVERY original ideal section. -/
abbrev SourcePerturbedPartialHilbert (u : C(W.carrier, ℝ)) (t : ℝ) :=
  WithComplexNorm (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t)

/-- Jordan--von Neumann produces the actual compatible complex inner
product from the internally established physical norm parallelogram. -/
instance sourcePerturbedPartialHilbertInner (u : C(W.carrier, ℝ)) (t : ℝ) :
    InnerProductSpace ℂ (SourcePerturbedPartialHilbert L T W μ hBM k hk φ u t) :=
  InnerProductSpace.ofNorm ℂ (fun s r => by
    simpa only [← sq] using!
      sourcePerturbedPartialL2Norm_parallelogram L T W μ hBM k hk φ u t s.val r.val)

/-- Completeness is manufactured from genuine finite original Gamma
dimension and the actual norm, never supplied by the caller. -/
instance sourcePerturbedPartialHilbertComplete (u : C(W.carrier, ℝ)) (t : ℝ) :
    CompleteSpace (SourcePerturbedPartialHilbert L T W μ hBM k hk φ u t) :=
  FiniteDimensional.complete ℂ _

/-- Actual identity-on-section maps in both directions from the original
base BM Hilbert space to the produced perturbed physical Hilbert space. -/
def sourceOriginalToPerturbedHilbert (u : C(W.carrier, ℝ)) (t : ℝ) :
    SourceHilbertSections L T W μ hBM k hk φ ≃ₗ[ℂ]
      SourcePerturbedPartialHilbert L T W μ hBM k hk φ u t :=
  (sourceHilbertOriginalEquiv L T W μ hBM k hk φ).trans
    (complexNormOriginalEquiv (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t)).symm

/-- Every actual perturbed-Hilbert vector retains the true same-section
squared integral, with the original physical weight v+t*u and original mu. -/
theorem sourcePerturbedPartialHilbert_norm_sq_integral (u : C(W.carrier, ℝ)) (t : ℝ)
    (s : SourcePerturbedPartialHilbert L T W μ hBM k hk φ u t) :
    ‖s‖ ^ 2 = ∫ x, weightedQuadraticDensity L T
      (sourcePerturbedWeightedSubset W u t) k s.val.val x ∂μ :=
  sourcePerturbedPartialL2Norm_sq_integral L T W μ hBM k hk φ u t s.val

/-- The manufactured varying Hilbert pairing is EXACTLY the original
physical same-fiber Hermitian integral, with original measure retained. -/
theorem sourcePerturbedPartialHilbert_inner_eq_integral (u : C(W.carrier, ℝ)) (t : ℝ)
    (s r : SourcePerturbedPartialHilbert L T W μ hBM k hk φ u t) :
    inner ℂ s r = ∫ x, weightedHermitianPairing L T
      (sourcePerturbedWeightedSubset W u t) k s.val.val r.val.val x ∂μ := by
  let : IsProbabilityMeasure μ := hBM.1
  have hp := integral_weightedHermitianPairing_polarization L T
    (sourcePerturbedWeightedSubset W u t) k μ s.val.val r.val.val
  dsimp only [sourcePerturbedWeightedSubset] at hp
  rw [inner_eq_sum_norm_sq_div_four]
  dsimp only [sourcePerturbedWeightedSubset]
  rw [hp]
  have hn (a : SourcePerturbedPartialHilbert L T W μ hBM k hk φ u t) :
      (‖a‖ : ℂ) ^ 2 = Complex.ofReal (∫ x, weightedQuadraticDensity L T
        (sourcePerturbedWeightedSubset W u t) k a.val.val x ∂μ) := by
    exact_mod_cast sourcePerturbedPartialHilbert_norm_sq_integral L T W μ hBM k hk φ u t a
  dsimp only [sourcePerturbedWeightedSubset] at hn
  change (((‖s + r‖ : ℂ) ^ 2 - (‖s - r‖ : ℂ) ^ 2 +
    ((‖s - Complex.I • r‖ : ℂ) ^ 2 - (‖s + Complex.I • r‖ : ℂ) ^ 2) * Complex.I) / 4) = _
  rw [hn (s + r), hn (s - r), hn (s - Complex.I • r), hn (s + Complex.I • r)]
  rfl

/-- The genuine Gram matrix of the actual original-to-perturbed Hilbert
equivalence is the already defined original physical Gram integral. -/
theorem sourceOriginalToPerturbedHilbert_gram (u : C(W.carrier, ℝ)) (t : ℝ) :
    Matrix.gram ℂ (fun i => sourceOriginalToPerturbedHilbert L T W μ hBM k hk φ u t
      (sourceOrthonormalBasis L T W μ hBM k hk φ i)) =
      sourceOriginalGram L T W μ hBM k hk φ u t := by
  ext i j
  rw [Matrix.gram_apply, sourcePerturbedPartialHilbert_inner_eq_integral]
  change (∫ x, weightedHermitianPairing L T (sourcePerturbedWeightedSubset W u t) k
      (sourceOriginalSectionLinear L T W μ hBM k hk φ
        (sourceOrthonormalBasis L T W μ hBM k hk φ i))
      (sourceOriginalSectionLinear L T W μ hBM k hk φ
        (sourceOrthonormalBasis L T W μ hBM k hk φ j)) x ∂μ) = _
  simp_rw [weightedHermitianPairing_perturbed]
  rfl

end SGPT.Bergman.SingularWeightedHilbert
