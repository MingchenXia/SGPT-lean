import SGPT.Bergman.SourceDeterminantTupleMeasure
import SGPT.Bergman.SourceLogLaplaceConvex
import SGPT.Bergman.SourcePartialDonaldsonDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
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

/-- Actual original log-Gram convexity, produced from the true evaluation
determinant integral and actual centered-square log-Laplace derivative.
No caller log-convexity, determinant-density or moment certificate enters. -/
theorem sourceOriginalGram_log_convex (u : C(W.carrier, ℝ)) :
    ConvexOn ℝ univ (fun t : ℝ => Real.log
      (sourceOriginalGram L T W μ hBM k hk φ u t).det.re) := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  let d := Module.finrank ℂ (SourceHilbertSections L T W μ hBM k hk φ)
  have hd : 0 < (d.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos d)
  have hpos (t : ℝ) : 0 < (sourceOriginalGram L T W μ hBM k hk φ u t).det.re := by
    have h := SGPT.Bergman.GramNormVolume.gram_det_re_pos
      (sourceOrthonormalBasis L T W μ hBM k hk φ)
      (sourceOriginalToPerturbedHilbert L T W μ hBM k hk φ u t)
    rw [sourceOriginalToPerturbedHilbert_gram] at h
    exact h
  have hconv := SGPT.Bergman.LogLaplace.convexOn_log_integral_exp
    (sourceDeterminantTupleMeasure L T W μ hBM k hk φ)
    (sourceDeterminantTuplePotential L T W μ hBM k hk φ u)
  have heq : (fun t : ℝ => Real.log (sourceOriginalGram L T W μ hBM k hk φ u t).det.re) =
      (fun t : ℝ => Real.log (∫ x,
        Real.exp (t * sourceDeterminantTuplePotential L T W μ hBM k hk φ u x)
          ∂sourceDeterminantTupleMeasure L T W μ hBM k hk φ)) +
        (fun _ => -Real.log (d.factorial : ℝ)) := by
    funext t
    dsimp only [Pi.add_apply]
    rw [sourceOriginalGram_laplace, Real.log_mul hd.ne' (hpos t).ne']
    ring
  rw [heq]
  exact hconv.add_const _

/-- Genuine concavity of the ACTUAL original partial Donaldson functional
of the ACTUAL varying original ideal-Gamma L2 norms. Base BM alone gives
faithfulness; no all-t BM, concavity, derivative or asymptotic certificate
is a source premise. The empty original section space is retained. -/
theorem sourcePartialDonaldson_concave
    (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1)
    (u : C(W.carrier, ℝ)) :
    ConcaveOn ℝ univ (fun t : ℝ => partialDonaldsonFunctional L T omega hmass k hk φ
      (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t)) := by
  let c : ℝ := (n.factorial : ℝ) / (k : ℝ) ^ (n + 1)
  let L₀ := partialDonaldsonFunctional L T omega hmass k hk φ
    (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u 0)
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hneg : ConcaveOn ℝ univ (fun t : ℝ =>
      -Real.log (sourceOriginalGram L T W μ hBM k hk φ u t).det.re) :=
    (sourceOriginalGram_log_convex L T W μ hBM k hk φ u).neg
  have hconc := (ConcaveOn.smul hc hneg).add_const L₀
  have heq : (fun t : ℝ => partialDonaldsonFunctional L T omega hmass k hk φ
      (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t)) =
      (fun t : ℝ => c • (-Real.log (sourceOriginalGram L T W μ hBM k hk φ u t).det.re)) +
        (fun _ => L₀) := by
    funext t
    dsimp only [Pi.add_apply, smul_eq_mul, c, L₀]
    have h := sourcePartialDonaldson_sub_eq_log_Gram L T W μ hBM k hk φ omega hmass u t
    simp only [neg_mul] at h
    rw [mul_neg]
    linarith
  rw [heq]
  exact hconc

end SGPT.Bergman.SingularWeightedHilbert
