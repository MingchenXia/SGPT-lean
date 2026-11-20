import SGPT.Bergman.SourceSmoothMetricPolynomialBound
import SGPT.Bergman.SourceGeneralBergmanTransport
import SGPT.Bergman.SourcePartialBergmanTrace

/-!
# PolynomialSectionDimension

Polynomial growth `dim H⁰(X, L^k ⊗ T ⊗ I(kφ)) ≤ C kⁿ`, uniformly in `φ`, from the trace of the Bergman kernel.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Bundle Set MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.BernsteinMarkov SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]

set_option backward.isDefEq.respectTransparency false in
/-- Genuine trace of the actual source unit-ball kernel gives a polynomial
bound for literal tensor-ideal Γ, uniformly in EVERY potential/domain.
The constant comes from actual smooth source metrics and an independent
auxiliary geometric probability volume; no growth/asymptotic input occurs. -/
theorem exists_literal_multiplier_dimension_bound (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (μ0 : Measure X) [IsProbabilityMeasure μ0] (hμ0 : IsSmoothPositiveVolume (n := n) μ0) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k → ∀ φ : X → EReal,
      (Module.finrank ℂ (LiteralTwistedMultiplierSections L T k φ) : ℝ) ≤ C * (k : ℝ) ^ n := by
  obtain ⟨C, hC, hb⟩ := exists_global_polynomial_section_bound L T hL hT μ0 hμ0
  let W := wholeWeightedSubset (n := n) (0 : C(X, ℝ))
  let μ := μ0.comap (Subtype.val : W.carrier → X)
  have hBM := smoothPositiveProbabilityVolume_general_BM L T (0 : C(X, ℝ)) μ0 hμ0
  have hp : IsProbabilityMeasure μ := hBM.1
  let := hp
  refine ⟨C, hC, fun k hk φ => ?_⟩
  have hkernel (x : W.carrier) : sourcePartialBergmanDensity L T W μ k φ x ≤
      ENNReal.ofReal (C * (k : ℝ) ^ n) := by
    unfold sourcePartialBergmanDensity
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    let t := (literalTwistedMultiplierSectionEquiv L T k φ s).val
    have hN : (∫⁻ z, ENNReal.ofReal (‖t z‖ ^ 2) ∂μ0) ^ (1 / 2 : ℝ) ≤ 1 := by
      change weightedL2Norm (twistedPower L T k).Fiber k (univRealWeight (0 : C(X, ℝ)))
        (μ0.comap (Subtype.val : ↥(univ : Set X) → X)) t ≤ 1 at hs
      rw [weightedL2Norm_univ] at hs
      simpa only [realWeightedSectionDensity, ContinuousMap.zero_apply, mul_zero, neg_zero,
        Real.exp_zero, mul_one] using hs
    have hI : (∫⁻ z, ENNReal.ofReal (‖t z‖ ^ 2) ∂μ0) ≤ 1 :=
      (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp
        (by simpa only [ENNReal.one_rpow] using hN)
    have hpoint := (hb k hk t x.val).trans (mul_le_mul' le_rfl hI)
    change weightedSectionDensity (twistedPower L T k).Fiber k
      (univRealWeight (0 : C(X, ℝ))) t ⟨x.val, mem_univ x.val⟩ ≤ _
    rw [weightedSectionDensity_univ L T (0 : C(X, ℝ)) k t]
    simpa only [mul_one, realWeightedSectionDensity,
      ContinuousMap.zero_apply, mul_zero, neg_zero, Real.exp_zero] using hpoint
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC.le (pow_nonneg (Nat.cast_nonneg _) _))).mp
  calc
    _ = ∫⁻ x, sourcePartialBergmanDensity L T W μ k φ x ∂μ :=
      (lintegral_sourcePartialBergmanDensity L T W μ hBM k hk φ).symm
    _ ≤ ∫⁻ _, ENNReal.ofReal (C * (k : ℝ) ^ n) ∂μ := lintegral_mono hkernel
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end SGPT.Bergman.PolynomialH0Growth
