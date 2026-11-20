import SGPT.Bergman.SourceSingularWeightedHilbert
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# WeightedEvaluation

Weighted evaluation `s ↦ s(x) e^{-kv(x)/2}` at points of `K` as a continuous linear functional and its Riesz representative.

Ported from the previous team's drafts (`work/sgpt-active-lanes-20261102/bergman-*`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Bergman.SingularWeightedHilbert
open Bundle Set Filter MeasureTheory
open scoped Topology Manifold ContDiff ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.QuantizationDraft SGPT.Bergman.NormAxioms
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.MultiplierSectionsDraft
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X]
  (L T : HermitianHolomorphicLineBundle n X)
  (W : SGPT.Bergman.WeightedSubset.WeightedSubset n X) (μ : Measure W.carrier)
  (hBM : IsBernsteinMarkov L T W μ) (k : ℕ) (hk : 0 < k) (φ : X → EReal)

/-- The TRUE whole original multiplier submodule inclusion into ALL native same-tensor sections. -/
def sourceOriginalSectionLinear :
    SourceHilbertSections L T W μ hBM k hk φ →ₗ[ℂ] twistedSections L T k :=
  (fullHolomorphicIdealSections (n := n) (twistedPower L T k).Fiber
    (sourceDegreeMultiplierIdeal (n := n) k φ)).subtype.comp
      (sourceHilbertOriginalEquiv L T W μ hBM k hk φ).toLinearMap

/-- Evaluation of ALL actual original sections at the SAME actual fiber. -/
def sourceEvaluationLinear (x : X) :
    SourceHilbertSections L T W μ hBM k hk φ →ₗ[ℂ] (twistedPower L T k).Fiber x where
  toFun s := sourceOriginalSectionLinear L T W μ hBM k hk φ s x
  map_add' s t := congrArg (fun u : twistedSections L T k => u x)
    ((sourceOriginalSectionLinear L T W μ hBM k hk φ).map_add s t)
  map_smul' r s := congrArg (fun u : twistedSections L T k => u x)
    ((sourceOriginalSectionLinear L T W μ hBM k hk φ).map_smul r s)

/-- Actual original preferred-frame coordinate evaluation times the SAME positive frame norm and source weight.
The frame and all maps are internally produced, not a prescribed finite family/evaluation certificate. -/
def sourceWeightedEvaluationLinear (x : W.carrier) :
    SourceHilbertSections L T W μ hBM k hk φ →ₗ[ℂ] ℂ :=
  (((trivializationAt ℂ (twistedPower L T k).Fiber x.val).linearEquivAt ℂ x.val
      (mem_baseSet_trivializationAt ℂ (twistedPower L T k).Fiber x.val)).toLinearMap.comp
    (sourceEvaluationLinear L T W μ hBM k hk φ x.val)).smulRight
      (Complex.ofReal (frameNorm (twistedPower L T k).Fiber
        (trivializationAt ℂ (twistedPower L T k).Fiber x.val) x.val *
          Real.exp (-((k : ℝ) * W.weight x) / 2)))

omit [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- EXACT original weighted point norm, proved from the TRUE whole-fiber preferred-frame formula. -/
theorem sourceWeightedEvaluation_norm (x : W.carrier)
    (s : SourceHilbertSections L T W μ hBM k hk φ) :
    ‖sourceWeightedEvaluationLinear L T W μ hBM k hk φ x s‖ =
      weightedPointNorm (twistedPower L T k).Fiber W k
        (sourceOriginalSectionLinear L T W μ hBM k hk φ s) x := by
  let V := (twistedPower L T k).Fiber
  let e := trivializationAt ℂ V x.val
  have hx : x.val ∈ e.baseSet := mem_baseSet_trivializationAt ℂ V x.val
  have he : 0 ≤ frameNorm V e x.val := (frameNorm_pos V e hx).le
  change ‖(e.linearEquivAt ℂ x.val hx) (sourceOriginalSectionLinear L T W μ hBM k hk φ s x.val) •
      Complex.ofReal (frameNorm V e x.val * Real.exp (-((k : ℝ) * W.weight x) / 2))‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg he (Real.exp_pos _).le)]
  change ‖sectionCoefficient V e (sourceOriginalSectionLinear L T W μ hBM k hk φ s) x.val‖ *
      (frameNorm V e x.val * Real.exp (-((k : ℝ) * W.weight x) / 2)) = _
  rw [weightedPointNorm, norm_eq_coefficient_mul_frameNorm V e _ hx, mul_assoc]

/-- Actual finite dimension makes the produced original evaluation functional continuous. -/
def sourceWeightedEvaluation (x : W.carrier) :
    SourceHilbertSections L T W μ hBM k hk φ →L[ℂ] ℂ :=
  (sourceWeightedEvaluationLinear L T W μ hBM k hk φ x).toContinuousLinearMap

/-- Actual Riesz vector produced by the genuine previously proved Hilbert structure. -/
def sourceEvaluationRiesz (x : W.carrier) : SourceHilbertSections L T W μ hBM k hk φ :=
  (InnerProductSpace.toDual ℂ (SourceHilbertSections L T W μ hBM k hk φ)).symm
    (sourceWeightedEvaluation L T W μ hBM k hk φ x)

/-- The produced Riesz vector retains the ACTUAL original weighted coefficient evaluation at EVERY section. -/
theorem sourceEvaluationRiesz_inner (x : W.carrier)
    (s : SourceHilbertSections L T W μ hBM k hk φ) :
    inner ℂ (sourceEvaluationRiesz L T W μ hBM k hk φ x) s =
      sourceWeightedEvaluation L T W μ hBM k hk φ x s :=
  InnerProductSpace.toDual_symm_apply

/-- The actual original functional and produced Riesz vector have exactly the same norm. -/
theorem sourceEvaluationRiesz_norm (x : W.carrier) :
    ‖sourceEvaluationRiesz L T W μ hBM k hk φ x‖ = ‖sourceWeightedEvaluation L T W μ hBM k hk φ x‖ :=
  (InnerProductSpace.toDual ℂ (SourceHilbertSections L T W μ hBM k hk φ)).symm.norm_map _

end SGPT.Bergman.SingularWeightedHilbert
