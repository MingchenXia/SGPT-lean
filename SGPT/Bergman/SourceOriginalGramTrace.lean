import SGPT.Bergman.SourceOriginalGramVariation
import SGPT.Bergman.SourceDeterminantVariation

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

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The actual physical Hermitian pairing for v+t*u is exactly the
integrand defining the original Gram family. -/
theorem weightedHermitianPairing_perturbed (u : C(W.carrier, ℝ)) (t : ℝ)
    (s r : twistedSections L T k) (x : W.carrier) :
    weightedHermitianPairing L T (sourcePerturbedWeightedSubset W u t) k s r x =
      Real.exp (-(k : ℝ) * t * u x) • weightedHermitianPairing L T W k s r x := by
  simp only [weightedHermitianPairing, RCLike.real_smul_eq_coe_mul]
  change (Real.exp (-((k : ℝ) * (W.weight x + t * u x))) : ℂ) *
    inner ℂ (s x.val) (r x.val) = _
  rw [show -((k : ℝ) * (W.weight x + t * u x)) =
    -(k : ℝ) * t * u x + -((k : ℝ) * W.weight x) by ring, Real.exp_add]
  simp only [Complex.ofReal_mul]
  exact mul_assoc _ _ _

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Original diagonal fiber pairing, retaining actual original h^k tensor h_T. -/
theorem weightedHermitianPairing_self (s : twistedSections L T k) (x : W.carrier) :
    weightedHermitianPairing L T W k s s x =
      (weightedQuadraticDensity L T W k s x : ℂ) := by
  rw [weightedHermitianPairing, inner_self_eq_norm_sq_to_K,
    weightedQuadraticDensity_eq_norm_sq_weight]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  exact mul_comm _ _

/-- The actual first variation matrix at the original weight. -/
def sourceOriginalGramFirstVariation (u : C(W.carrier, ℝ)) :
    Matrix (sourceGramIndex L T W μ hBM k hk φ)
      (sourceGramIndex L T W μ hBM k hk φ) ℂ :=
  fun i j => ∫ x, (-(k : ℝ) * u x) • weightedHermitianPairing L T W k
    (sourceOriginalSectionLinear L T W μ hBM k hk φ
      (sourceOrthonormalBasis L T W μ hBM k hk φ i))
    (sourceOriginalSectionLinear L T W μ hBM k hk φ
      (sourceOrthonormalBasis L T W μ hBM k hk φ j)) x ∂μ

/-- Same original Gram entries, true first variation at zero. -/
theorem hasDerivAt_sourceOriginalGram_zero_entry (u : C(W.carrier, ℝ))
    (i j : sourceGramIndex L T W μ hBM k hk φ) :
    HasDerivAt (fun t => sourceOriginalGram L T W μ hBM k hk φ u t i j)
      (sourceOriginalGramFirstVariation L T W μ hBM k hk φ u i j) 0 := by
  simpa only [mul_zero, zero_mul, Real.exp_zero, mul_one,
    sourceOriginalGramFirstVariation] using
    hasDerivAt_sourceOriginalGram_entry L T W μ hBM k hk φ u 0 i j

/-- Trace against the actual internally produced original ON basis, with
the integral/sum interchange justified by compact continuous densities. -/
theorem trace_sourceOriginalGramFirstVariation (u : C(W.carrier, ℝ)) :
    Matrix.trace (sourceOriginalGramFirstVariation L T W μ hBM k hk φ u) =
      Complex.ofReal (-(k : ℝ) * ∫ x,
        u x * sourceBasisDensityReal L T W μ hBM k hk φ x ∂μ) := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  let : IsProbabilityMeasure μ := hBM.1
  have hint (i : sourceGramIndex L T W μ hBM k hk φ) :
      Integrable (fun x => (-(k : ℝ) * u x) * weightedQuadraticDensity L T W k
        (sourceOriginalSectionLinear L T W μ hBM k hk φ
          (sourceOrthonormalBasis L T W μ hBM k hk φ i)) x) μ := by
    exact ((continuous_const.mul u.continuous).mul
      (weightedQuadraticDensity_continuous L T W k _)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  change (∑ i, ∫ x, (-(k : ℝ) * u x) • weightedHermitianPairing L T W k
    (sourceOriginalSectionLinear L T W μ hBM k hk φ
      (sourceOrthonormalBasis L T W μ hBM k hk φ i))
    (sourceOriginalSectionLinear L T W μ hBM k hk φ
      (sourceOrthonormalBasis L T W μ hBM k hk φ i)) x ∂μ) = _
  have hconvert (i : sourceGramIndex L T W μ hBM k hk φ) :
      (∫ x, (-(k : ℝ) * u x) • weightedHermitianPairing L T W k
        (sourceOriginalSectionLinear L T W μ hBM k hk φ
          (sourceOrthonormalBasis L T W μ hBM k hk φ i))
        (sourceOriginalSectionLinear L T W μ hBM k hk φ
          (sourceOrthonormalBasis L T W μ hBM k hk φ i)) x ∂μ) =
      Complex.ofReal (∫ x, (-(k : ℝ) * u x) * weightedQuadraticDensity L T W k
        (sourceOriginalSectionLinear L T W μ hBM k hk φ
          (sourceOrthonormalBasis L T W μ hBM k hk φ i)) x ∂μ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      dsimp only
      rw [weightedHermitianPairing_self, RCLike.real_smul_eq_coe_mul]
      exact (Complex.ofReal_mul _ _).symm)
  simp_rw [hconvert]
  rw [← Complex.ofReal_sum]
  congr 1
  rw [← integral_finsetSum _ (fun i _ => hint i), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [sourceBasisDensityReal, Finset.mul_sum, mul_assoc])

/-- The trace uses the TRUE original unit-ball supremum, via the genuine
source supremum/basis theorem. No caller density identity appears. -/
theorem trace_sourceOriginalGramFirstVariation_eq_supremum
    (u : C(W.carrier, ℝ)) :
    Matrix.trace (sourceOriginalGramFirstVariation L T W μ hBM k hk φ u) =
      Complex.ofReal (-(k : ℝ) * ∫ x, u x *
        (sourcePartialBergmanDensity L T W μ k φ x).toReal ∂μ) := by
  rw [trace_sourceOriginalGramFirstVariation]
  simp only [sourcePartialBergmanDensity_eq_produced_basis L T W μ hBM k hk φ,
    ENNReal.toReal_ofReal (sourceBasisDensityReal_nonneg L T W μ hBM k hk φ _)]

/-- Original Gram log determinant derivative is internally derived from
the actual original sections and their real continuous perturbation. -/
theorem hasDerivAt_log_re_sourceOriginalGram_det (u : C(W.carrier, ℝ)) :
    HasDerivAt (fun t => Real.log
        (sourceOriginalGram L T W μ hBM k hk φ u t).det.re)
      (-(k : ℝ) * ∫ x, u x *
        (sourcePartialBergmanDensity L T W μ k φ x).toReal ∂μ) 0 := by
  have h := SGPT.Bergman.WeightVariation.hasDerivAt_log_re_det_at_identity
    (sourceOriginalGram L T W μ hBM k hk φ u)
    (sourceOriginalGramFirstVariation L T W μ hBM k hk φ u) 0
    (sourceOriginalGram_zero L T W μ hBM k hk φ u)
    (hasDerivAt_sourceOriginalGram_zero_entry L T W μ hBM k hk φ u)
  rw [trace_sourceOriginalGramFirstVariation_eq_supremum] at h
  simpa only [Complex.ofReal_re] using h

include hBM hk in
/-- Real test integral of the ACTUAL original normalized Bergman measure
on K. The zero extension/global map is already defined in the source API. -/
theorem integral_sourcePartialBergmanMeasureOnK (u : C(W.carrier, ℝ)) :
    (∫ x, u x ∂sourcePartialBergmanMeasureOnK L T W μ k φ) =
      ((n.factorial : ℝ) / (k : ℝ) ^ n) *
        ∫ x, u x * (sourcePartialBergmanDensity L T W μ k φ x).toReal ∂μ := by
  rw [sourcePartialBergmanMeasureOnK, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul
      (sourcePartialBergmanDensity_measurable L T W μ hBM k hk φ)
      (Filter.Eventually.of_forall (fun x => by
        rw [sourcePartialBergmanDensity_eq_produced_basis L T W μ hBM k hk φ]
        exact ENNReal.ofReal_lt_top))]
  simp only [sourceBergmanNormalization, ENNReal.toReal_ofReal (by positivity :
    0 ≤ (n.factorial : ℝ) / (k : ℝ) ^ n), smul_eq_mul]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => mul_comm _ _))

/-- Genuine normalized log-Gram derivative equals the integral against
the ACTUAL original partial Bergman measure, including zero section space. -/
theorem hasDerivAt_normalized_log_Gram_eq_BergmanOnK (u : C(W.carrier, ℝ)) :
    HasDerivAt (fun t => -((n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
        Real.log (sourceOriginalGram L T W μ hBM k hk φ u t).det.re)
      (∫ x, u x ∂sourcePartialBergmanMeasureOnK L T W μ k φ) 0 := by
  have h := (hasDerivAt_log_re_sourceOriginalGram_det L T W μ hBM k hk φ u).const_mul
    (-((n.factorial : ℝ) / (k : ℝ) ^ (n + 1)))
  rw [integral_sourcePartialBergmanMeasureOnK L T W μ hBM k hk φ]
  have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have heq : -((n.factorial : ℝ) / (k : ℝ) ^ (n + 1)) *
      (-(k : ℝ) * ∫ x, u x *
        (sourcePartialBergmanDensity L T W μ k φ x).toReal ∂μ) =
      ((n.factorial : ℝ) / (k : ℝ) ^ n) *
        ∫ x, u x * (sourcePartialBergmanDensity L T W μ k φ x).toReal ∂μ := by
    rw [pow_succ]
    field_simp
  rwa [heq] at h

end SGPT.Bergman.SingularWeightedHilbert
