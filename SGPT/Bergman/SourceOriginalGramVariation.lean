import SGPT.Bergman.SourceCompactWeightIntegral
import SGPT.Bergman.SourcePartialBergmanTrace
import Mathlib.LinearAlgebra.Matrix.Trace

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
/-- Continuity of the SAME original fiber pairing is produced by actual
section polarization, with no assumed kernel family or pairing certificate. -/
theorem weightedHermitianPairing_continuous (s t : twistedSections L T k) :
    Continuous (weightedHermitianPairing L T W k s t) := by
  have hq (r : twistedSections L T k) :
      Continuous (fun x => (weightedQuadraticDensity L T W k r x : ℂ)) :=
    Complex.continuous_ofReal.comp (weightedQuadraticDensity_continuous L T W k r)
  have h := (((hq (s + t)).sub (hq (s - t))).add
    (((hq (s - Complex.I • t)).sub (hq (s + Complex.I • t))).mul_const Complex.I)).div_const 4
  exact h.congr (fun x => (weightedHermitianPairing_polarization L T W k s t x).symm)

/-- A genuine continuous perturbation of the ORIGINAL weight, on the SAME
original K. The multiplier ideal, bundles and measure are unchanged. -/
def sourcePerturbedWeightedSubset (u : C(W.carrier, ℝ)) (t : ℝ) :
    SGPT.Bergman.WeightedSubset.WeightedSubset n X :=
  { W with weight := W.weight + t • u }

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Exact physical density for the actual weight v+t*u, not a replacement
finite-family density. -/
theorem weightedQuadraticDensity_perturbed (u : C(W.carrier, ℝ)) (t : ℝ)
    (s : twistedSections L T k) (x : W.carrier) :
    weightedQuadraticDensity L T (sourcePerturbedWeightedSubset W u t) k s x =
      Real.exp (-(k : ℝ) * t * u x) * weightedQuadraticDensity L T W k s x := by
  rw [weightedQuadraticDensity_eq_norm_sq_weight,
    weightedQuadraticDensity_eq_norm_sq_weight]
  change ‖s x.val‖ ^ 2 * Real.exp (-((k : ℝ) * (W.weight x + t * u x))) = _
  rw [show -((k : ℝ) * (W.weight x + t * u x)) =
    -(k : ℝ) * t * u x + -((k : ℝ) * W.weight x) by ring, Real.exp_add]
  ring

include hBM in
omit [ConnectedSpace X] in
/-- Genuine derivative of the original quadratic L2 integral under a
continuous change of the actual source weight, at EVERY real parameter. -/
theorem hasDerivAt_original_quadratic_integral (u : C(W.carrier, ℝ))
    (s : twistedSections L T k) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x,
        weightedQuadraticDensity L T (sourcePerturbedWeightedSubset W u t) k s x ∂μ)
      (∫ x, (-(k : ℝ) * u x * Real.exp (-(k : ℝ) * t₀ * u x)) *
        weightedQuadraticDensity L T W k s x ∂μ) t₀ := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  let : IsProbabilityMeasure μ := hBM.1
  simpa only [weightedQuadraticDensity_perturbed, smul_eq_mul] using!
    SGPT.Bergman.WeightVariation.hasDerivAt_weighted_integral μ
      ⟨weightedQuadraticDensity L T W k s, weightedQuadraticDensity_continuous L T W k s⟩
      u (k : ℝ) t₀

/-- The index set is that of the INTERNALLY produced orthonormal basis of
the actual original ideal-section Hilbert space, including dimension zero. -/
abbrev sourceGramIndex :=
  Fin (Module.finrank ℂ (SourceHilbertSections L T W μ hBM k hk φ))

/-- Actual Gram matrix of the original sections with the physical weight
v+t*u. Its entries are original SAME-fiber Hermitian integrals. -/
def sourceOriginalGram (u : C(W.carrier, ℝ)) (t : ℝ) :
    Matrix (sourceGramIndex L T W μ hBM k hk φ)
      (sourceGramIndex L T W μ hBM k hk φ) ℂ :=
  fun i j => ∫ x, Real.exp (-(k : ℝ) * t * u x) •
    weightedHermitianPairing L T W k
      (sourceOriginalSectionLinear L T W μ hBM k hk φ
        (sourceOrthonormalBasis L T W μ hBM k hk φ i))
      (sourceOriginalSectionLinear L T W μ hBM k hk φ
        (sourceOrthonormalBasis L T W μ hBM k hk φ j)) x ∂μ

/-- Actual entrywise derivative, with all domination and measurability
manufactured from genuine compact continuous section data. -/
theorem hasDerivAt_sourceOriginalGram_entry (u : C(W.carrier, ℝ)) (t₀ : ℝ)
    (i j : sourceGramIndex L T W μ hBM k hk φ) :
    HasDerivAt (fun t => sourceOriginalGram L T W μ hBM k hk φ u t i j)
      (∫ x, (-(k : ℝ) * u x * Real.exp (-(k : ℝ) * t₀ * u x)) •
        weightedHermitianPairing L T W k
          (sourceOriginalSectionLinear L T W μ hBM k hk φ
            (sourceOrthonormalBasis L T W μ hBM k hk φ i))
          (sourceOriginalSectionLinear L T W μ hBM k hk φ
            (sourceOrthonormalBasis L T W μ hBM k hk φ j)) x ∂μ) t₀ := by
  let : CompactSpace W.carrier := isCompact_iff_compactSpace.mp W.isClosed_carrier.isCompact
  let : IsProbabilityMeasure μ := hBM.1
  exact SGPT.Bergman.WeightVariation.hasDerivAt_weighted_integral μ
    ⟨_, weightedHermitianPairing_continuous L T W k _ _⟩ u (k : ℝ) t₀

/-- The actual original ON basis makes the actual Gram matrix the identity
at zero. No chosen Gram-identity field is an input. -/
theorem sourceOriginalGram_zero (u : C(W.carrier, ℝ)) :
    sourceOriginalGram L T W μ hBM k hk φ u 0 = 1 := by
  let : IsProbabilityMeasure μ := hBM.1
  ext i j
  simp only [sourceOriginalGram, mul_zero, zero_mul, Real.exp_zero, one_smul]
  change (∫ x, weightedHermitianPairing L T W k
      (sourceHilbertOriginalEquiv L T W μ hBM k hk φ
        (sourceOrthonormalBasis L T W μ hBM k hk φ i)).val
      (sourceHilbertOriginalEquiv L T W μ hBM k hk φ
        (sourceOrthonormalBasis L T W μ hBM k hk φ j)).val x ∂μ) = _
  rw [← sourceHilbert_inner_eq_original_integral]
  exact (sourceOrthonormalBasis L T W μ hBM k hk φ).inner_eq_ite i j

end SGPT.Bergman.SingularWeightedHilbert
