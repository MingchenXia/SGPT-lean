import SGPT.Bergman.SourceOriginalNormBallVolume
import SGPT.Bergman.SourceGlobalBergmanGramVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
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

/-- The reference ball cancels in the ACTUAL original partial Donaldson
functional. Real positive finite original norm-ball Haar volumes justify
the logarithms internally; no functional difference reader is supplied. -/
theorem partialDonaldsonFunctional_sub_eq_normball_log_ratio
    (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1)
    (H H₀ : ComplexNorm (idealSections L T k φ))
    (vol : Measure (idealSections L T k φ)) [vol.IsAddHaarMeasure] :
    partialDonaldsonFunctional L T omega hmass k hk φ H -
      partialDonaldsonFunctional L T omega hmass k hk φ H₀ =
      ((n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
        Real.log (vol.real (normUnitBall H) / vol.real (normUnitBall H₀)) := by
  have hR := normUnitBall_real_pos vol (referenceNorm L T omega hmass k hk φ)
  have hH := normUnitBall_real_pos vol H
  have hH₀ := normUnitBall_real_pos vol H₀
  rw [partialDonaldsonFunctional_eq_haar L T omega hmass k hk φ H vol,
    partialDonaldsonFunctional_eq_haar L T omega hmass k hk φ H₀ vol,
    Real.log_div hH.ne' hR.ne', Real.log_div hH₀.ne' hR.ne',
    Real.log_div hH.ne' hH₀.ne']
  ring

/-- Exact original partial Donaldson functional / original physical Gram
dictionary. All norms, Hilbert structures, Haar measure and Gram entries
are internally manufactured on the whole original multiplier ideal. -/
theorem sourcePartialDonaldson_sub_eq_log_Gram
    (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1)
    (u : C(W.carrier, ℝ)) (t : ℝ) :
    partialDonaldsonFunctional L T omega hmass k hk φ
        (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t) -
      partialDonaldsonFunctional L T omega hmass k hk φ
        (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u 0) =
      -((n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
        Real.log (sourceOriginalGram L T W μ hBM k hk φ u t).det.re := by
  rw [partialDonaldsonFunctional_sub_eq_normball_log_ratio L T k hk φ omega hmass
    _ _ (sourceOriginalGammaHaar L T W μ hBM k hk φ),
    sourceOriginalGammaHaar_log_normball_ratio]
  ring

/-- Actual original finite-degree partial Donaldson derivative against
the genuine original beta measure on X. No norm-volume, density,
derivative, perturbed-BM or convergence certificate is an input. -/
theorem hasDerivAt_sourcePartialDonaldson_eq_global_Bergman
    (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1)
    (u : C(X, ℝ)) :
    HasDerivAt (fun t => partialDonaldsonFunctional L T omega hmass k hk φ
        (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ
          (sourceBergmanTestRestriction W u) t))
      (∫ x, u x ∂sourcePartialBergmanMeasure L T W μ k φ) 0 := by
  let uK := sourceBergmanTestRestriction W u
  let L₀ := partialDonaldsonFunctional L T omega hmass k hk φ
    (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ uK 0)
  have heq : (fun t => partialDonaldsonFunctional L T omega hmass k hk φ
      (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ uK t)) =
      (fun t => L₀ + -((n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
        Real.log (sourceOriginalGram L T W μ hBM k hk φ uK t).det.re) := by
    funext t
    have h := sourcePartialDonaldson_sub_eq_log_Gram L T W μ hBM k hk φ omega hmass uK t
    dsimp only [L₀]
    linarith
  change HasDerivAt (fun t => partialDonaldsonFunctional L T omega hmass k hk φ
      (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ uK t)) _ 0
  rw [heq]
  simpa only [uK, Pi.add_apply, zero_add] using! (hasDerivAt_const 0 L₀).add
    (hasDerivAt_normalized_log_Gram_eq_global_Bergman L T W μ hBM k hk φ u)

end SGPT.Bergman.SingularWeightedHilbert
