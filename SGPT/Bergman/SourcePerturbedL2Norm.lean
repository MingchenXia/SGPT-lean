import SGPT.Bergman.SourceOriginalGramVariation
import SGPT.Bergman.SourcePartialDonaldsonFunctional

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

include hBM hk in
omit [CompactSpace X] in
/-- Faithfulness of the perturbed physical L2 integral follows from the
original BM norm and positivity of the exponential. The perturbed weight
is NOT assumed Bernstein--Markov. -/
theorem perturbed_weightedL2Norm_eq_zero_iff (u : C(W.carrier, ℝ)) (t : ℝ)
    (s : twistedSections L T k) :
    weightedL2Norm (twistedPower L T k).Fiber k
      (sourcePerturbedWeightedSubset W u t).erealWeight μ s = 0 ↔ s = 0 := by
  constructor
  · intro hz
    rw [weightedL2Norm_eq_eLpNorm,
      eLpNorm_eq_zero_iff (weightedPointNorm_continuous (twistedPower L T k).Fiber
        (sourcePerturbedWeightedSubset W u t) k s).aestronglyMeasurable (by norm_num)] at hz
    have hbase : weightedPointNorm (twistedPower L T k).Fiber W k s =ᵐ[μ] 0 := by
      filter_upwards [hz] with x hx
      change ‖s x.val‖ * Real.exp _ = 0 at hx
      have hn : ‖s x.val‖ = 0 := (mul_eq_zero.mp hx).resolve_right (Real.exp_pos _).ne'
      change ‖s x.val‖ * Real.exp _ = 0
      rw [hn, zero_mul]
    apply (bernsteinMarkov_weightedL2Norm_eq_zero_iff L T W μ hBM k hk s).mp
    rw [weightedL2Norm_eq_eLpNorm]
    exact (eLpNorm_eq_zero_iff (weightedPointNorm_continuous
      (twistedPower L T k).Fiber W k s).aestronglyMeasurable (by norm_num)).mpr hbase
  · rintro rfl
    exact weightedL2Norm_zero (twistedPower L T k).Fiber
      (sourcePerturbedWeightedSubset W u t) k μ

/-- Genuine varying norm on ALL original tensor sections. Only the base
BM assumption is used for definiteness, with no BM hypothesis at v+t*u. -/
def sourcePerturbedWholeL2Norm (u : C(W.carrier, ℝ)) (t : ℝ) :
    AddGroupNorm (twistedSections L T k) := by
  let : IsProbabilityMeasure μ := hBM.1
  refine {
    toAddGroupSeminorm := weightedL2Seminorm (twistedPower L T k).Fiber
      (sourcePerturbedWeightedSubset W u t) k μ
    eq_zero_of_map_eq_zero' := fun s hs => ?_ }
  apply (perturbed_weightedL2Norm_eq_zero_iff L T W μ hBM k hk u t s).mp
  exact ((ENNReal.toReal_eq_zero_iff _).mp hs).resolve_right
    (weightedL2Norm_ne_top (twistedPower L T k).Fiber
      (sourcePerturbedWeightedSubset W u t) k μ s)

/-- Exact finite reader of the ORIGINAL perturbed L2 norm on every section. -/
theorem sourcePerturbedWholeL2Norm_ofReal (u : C(W.carrier, ℝ)) (t : ℝ)
    (s : twistedSections L T k) :
    ENNReal.ofReal (sourcePerturbedWholeL2Norm L T W μ hBM k hk u t s) =
      weightedL2Norm (twistedPower L T k).Fiber k
        (sourcePerturbedWeightedSubset W u t).erealWeight μ s := by
  let : IsProbabilityMeasure μ := hBM.1
  exact weightedL2Seminorm_ofReal (twistedPower L T k).Fiber
    (sourcePerturbedWeightedSubset W u t) k μ s

/-- Complex homogeneity is inherited from the genuine original L2 integral. -/
theorem sourcePerturbedWholeL2Norm_smul (u : C(W.carrier, ℝ)) (t : ℝ)
    (c : ℂ) (s : twistedSections L T k) :
    sourcePerturbedWholeL2Norm L T W μ hBM k hk u t (c • s) =
      ‖c‖ * sourcePerturbedWholeL2Norm L T W μ hBM k hk u t s := by
  let : IsProbabilityMeasure μ := hBM.1
  exact weightedL2Seminorm_smul (twistedPower L T k).Fiber
    (sourcePerturbedWeightedSubset W u t) k μ c s

/-- The actual physical varying norm on the SAME entire original
multiplier-ideal Gamma space used by the partial Donaldson functional. -/
def sourcePerturbedPartialL2Norm (u : C(W.carrier, ℝ)) (t : ℝ) :
    ComplexNorm (idealSections L T k φ) :=
  restrictNorm φ (sourcePerturbedWholeL2Norm L T W μ hBM k hk u t)
    (sourcePerturbedWholeL2Norm_smul L T W μ hBM k hk u t)

/-- Exact physical readback on the SAME original ideal section space. -/
theorem sourcePerturbedPartialL2Norm_ofReal (u : C(W.carrier, ℝ)) (t : ℝ)
    (s : idealSections L T k φ) :
    ENNReal.ofReal ((sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t).toAddGroupNorm s) =
      weightedL2Norm (twistedPower L T k).Fiber k
        (sourcePerturbedWeightedSubset W u t).erealWeight μ s.val :=
  sourcePerturbedWholeL2Norm_ofReal L T W μ hBM k hk u t s.val

/-- At the original weight, the produced family has EXACTLY the source
partial L2 norm's values. The family is not a mere equivalent norm. -/
theorem sourcePerturbedPartialL2Norm_zero_apply (u : C(W.carrier, ℝ))
    (s : idealSections L T k φ) :
    (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u 0).toAddGroupNorm s =
      (l2Norm L T W μ hBM k hk φ).toAddGroupNorm s := by
  apply (ENNReal.ofReal_eq_ofReal_iff (apply_nonneg _ _) (apply_nonneg _ _)).mp
  rw [sourcePerturbedPartialL2Norm_ofReal, l2Norm_ofReal]
  congr 2
  cases W
  simp only [sourcePerturbedWeightedSubset, zero_smul, add_zero]

/-- Actual squared norm integral, internally proved also when no BM
property is available for the perturbed weight. -/
theorem sourcePerturbedPartialL2Norm_sq_integral (u : C(W.carrier, ℝ)) (t : ℝ)
    (s : idealSections L T k φ) :
    ((sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t).toAddGroupNorm s) ^ 2 =
      ∫ x, weightedQuadraticDensity L T
        (sourcePerturbedWeightedSubset W u t) k s.val x ∂μ := by
  let : IsProbabilityMeasure μ := hBM.1
  have hN := apply_nonneg
    (sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t).toAddGroupNorm s
  apply (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (integral_nonneg (weightedQuadraticDensity_nonneg L T
      (sourcePerturbedWeightedSubset W u t) k s.val))).mp
  rw [ENNReal.ofReal_pow hN, sourcePerturbedPartialL2Norm_ofReal,
    ofReal_integral_eq_lintegral_ofReal
      (weightedQuadraticDensity_integrable L T (sourcePerturbedWeightedSubset W u t) k μ s.val)
      (Filter.Eventually.of_forall (weightedQuadraticDensity_nonneg L T
        (sourcePerturbedWeightedSubset W u t) k s.val))]
  unfold weightedL2Norm
  simp_rw [weightedSectionDensity_eq_pointNorm_sq]
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  norm_num
  rfl

/-- Genuine native derivative of the squared ORIGINAL varying L2 norm on
EVERY original multiplier-ideal section, at EVERY real parameter. -/
theorem hasDerivAt_sourcePerturbedPartialL2Norm_sq (u : C(W.carrier, ℝ))
    (s : idealSections L T k φ) (t₀ : ℝ) :
    HasDerivAt (fun t =>
        ((sourcePerturbedPartialL2Norm L T W μ hBM k hk φ u t).toAddGroupNorm s) ^ 2)
      (∫ x, (-(k : ℝ) * u x * Real.exp (-(k : ℝ) * t₀ * u x)) *
        weightedQuadraticDensity L T W k s.val x ∂μ) t₀ := by
  simpa only [sourcePerturbedPartialL2Norm_sq_integral] using
    hasDerivAt_original_quadratic_integral L T W μ hBM k u s.val t₀

end SGPT.Bergman.SingularWeightedHilbert
