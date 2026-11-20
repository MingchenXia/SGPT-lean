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

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (φ : X → EReal)

/-- Actual original probability gives the true L2<=sup comparison at EVERY
perturbed weight. No perturbed Bernstein--Markov property is required. -/
theorem sourcePerturbedPartialL2Norm_le_supNorm (u : C(W.carrier, ℝ)) (t : ℝ)
    (s : idealSections L T k φ) :
    (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t).toAddGroupNorm s ≤
      (supNorm L T (sourcePerturbedWeightedSubset W u t) k φ).toAddGroupNorm s := by
  let : IsProbabilityMeasure μ := hBM.1
  apply (ENNReal.ofReal_le_ofReal_iff (apply_nonneg _ _)).mp
  rw [sourcePerturbedPartialL2Norm_ofReal, supNorm_ofReal]
  exact SGPT.Bergman.BernsteinMarkov.weightedL2Norm_le_weightedSupNorm
    (twistedPower L T k).Fiber k (sourcePerturbedWeightedSubset W u t).erealWeight μ
    (by simp [SGPT.Bergman.WeightedSubset.WeightedSubset.erealWeight]) s.val

/-- The ACTUAL original sup-norm Donaldson functional is a lower
approximant for the ACTUAL original L2 functional at EVERY parameter.
Unit-ball inclusion, finite positive Haar volumes and real-log order are
proved internally from the genuine probability norm comparison. -/
theorem sourcePartialDonaldson_sup_le_perturbedL2
    (omega : KahlerBackground n X)
    (hmass : IntegrationCurrent.kahlerVolume omega univ = 1)
    (u : C(W.carrier, ℝ)) (t : ℝ) :
    partialDonaldsonFunctional L T omega hmass k hk φ
        (supNorm L T (sourcePerturbedWeightedSubset W u t) k φ) ≤
      partialDonaldsonFunctional L T omega hmass k hk φ
        (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t) := by
  let vol : Measure (idealSections L T k φ) := Measure.addHaar
  let Q := sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t
  let S := supNorm L T (sourcePerturbedWeightedSubset W u t) k φ
  let R := referenceNorm L T omega hmass k hk φ
  have hN : ∀ s, Q.toAddGroupNorm s ≤ S.toAddGroupNorm s :=
    sourcePerturbedPartialL2Norm_le_supNorm L T W μ hBM k hk φ u t
  have hvol : vol.real (normUnitBall S) ≤ vol.real (normUnitBall Q) :=
    measureReal_mono (normUnitBall_antitone Q S hN) (normUnitBall_measure_ne_top vol Q)
  have hlog := Real.log_le_log (normUnitBall_real_pos vol S) hvol
  apply sub_nonpos.mp
  change sourceDonaldsonFunctional vol n k S R - sourceDonaldsonFunctional vol n k Q R ≤ 0
  rw [sourceDonaldsonFunctional_difference]
  exact mul_nonpos_of_nonneg_of_nonpos (sourceDonaldsonNormalization_nonneg n k)
    (sub_nonpos.mpr hlog)

end SGPT.Bergman.SingularWeightedHilbert
