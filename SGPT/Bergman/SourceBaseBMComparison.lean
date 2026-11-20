import SGPT.Bergman.SourcePartialDonaldsonDerivative

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
open SGPT.Bergman.PolynomialH0Growth

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (φ : X → EReal)

/-- Exact base-value dictionary for the ORIGINAL functional: the actual
varying norm at zero has the SAME whole-Gamma unit ball as original N2.
No functional-value equality or norm-volume certificate is supplied. -/
theorem sourcePartialDonaldson_perturbed_zero_eq_l2
    (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1)
    (u : C(W.carrier, ℝ)) :
    partialDonaldsonFunctional L T omega hmass k hk φ
        (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u 0) =
      partialDonaldsonFunctional L T omega hmass k hk φ (l2Norm L T W μ hBM k hk φ) := by
  have hball : normUnitBall (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u 0) =
      normUnitBall (l2Norm L T W μ hBM k hk φ) := by
    ext s
    change (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u 0).toAddGroupNorm s ≤ 1 ↔
      (l2Norm L T W μ hBM k hk φ).toAddGroupNorm s ≤ 1
    rw [sourcePerturbedPartialL2Norm_zero_apply]
  unfold partialDonaldsonFunctional sourceDonaldsonFunctional normBallVolumeRatio
  rw [hball]

/-- Genuine BASE-WEIGHT-ONLY BM comparison for the actual varying family.
This consumes the accepted whole lma:BML and does not claim a second
completion of that book item or assume BM at any perturbed weight. -/
theorem tendsto_partialDonaldson_sup_sub_perturbed_zero
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1)
    (u : C(W.carrier, ℝ)) :
    Tendsto (fun degree : ℕ => if hdegree : 0 < degree then
      partialDonaldsonFunctional L T omega hmass degree hdegree φ (supNorm L T W degree φ) -
        partialDonaldsonFunctional L T omega hmass degree hdegree φ
          (sourcePerturbedPartialL2Norm L T W μ hBM degree hdegree φ u 0)
      else 0) atTop (𝓝 0) := by
  have heq : (fun degree : ℕ => if hdegree : 0 < degree then
      partialDonaldsonFunctional L T omega hmass degree hdegree φ (supNorm L T W degree φ) -
        partialDonaldsonFunctional L T omega hmass degree hdegree φ
          (sourcePerturbedPartialL2Norm L T W μ hBM degree hdegree φ u 0)
      else 0) = (fun degree : ℕ => if hdegree : 0 < degree then
      partialDonaldsonFunctional L T omega hmass degree hdegree φ (supNorm L T W degree φ) -
        partialDonaldsonFunctional L T omega hmass degree hdegree φ
          (l2Norm L T W μ hBM degree hdegree φ)
      else 0) := by
    funext degree
    by_cases hdegree : 0 < degree
    · simp only [dif_pos hdegree, sourcePartialDonaldson_perturbed_zero_eq_l2]
    · simp only [dif_neg hdegree]
  rw [heq]
  exact tendsto_partialDonaldson_sup_sub_l2 L T hL hT omega hmass W μ hBM φ

end SGPT.Bergman.SingularWeightedHilbert
