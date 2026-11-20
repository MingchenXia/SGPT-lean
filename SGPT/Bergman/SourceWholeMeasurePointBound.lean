import SGPT.Bergman.SourcePartialBergmanTrace
import SGPT.Bergman.SourceGeneralBergmanTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.ContactConcentration

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.GeneralBMTransport SGPT.Bergman.SingularWeightedHilbert
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]

omit [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- Elementary EXACT source measure transport of a pointwise bound on a
measurable set. This helper retains the ACTUAL normalization, whole-X
subtype/comap, raw mu and entire original kernel. It needs no BM or
probability, basis or source-density measurability certificate. -/
theorem sourceWholeMeasure_apply_le_of_pointwise
    (L T : HermitianHolomorphicLineBundle n X) (v : C(X, ℝ)) (mu : Measure X)
    (k : ℕ) (phi : X → EReal) (S : Set X) (hS : MeasurableSet S) (b : ℝ≥0∞)
    (hb : ∀ x : (wholeWeightedSubset (n := n) v).carrier, x.val ∈ S →
      sourcePartialBergmanDensity L T (wholeWeightedSubset v)
        (mu.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k phi x ≤ b) :
    sourcePartialBergmanMeasure L T (wholeWeightedSubset v)
        (mu.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k phi S ≤
      sourceBergmanNormalization (n := n) k * b * mu S := by
  let W := wholeWeightedSubset (n := n) v
  let muK := mu.comap (Subtype.val : W.carrier → X)
  have hpre : MeasurableSet ((Subtype.val : W.carrier → X) ⁻¹' S) := measurable_subtype_coe hS
  have hmap : Measure.map (Subtype.val : W.carrier → X) muK = mu := by
    dsimp only [muK, W, wholeWeightedSubset]
    rw [map_comap_subtype_coe MeasurableSet.univ, Measure.restrict_univ]
  have hmass := congrArg (fun z : Measure X => z S) hmap
  rw [Measure.map_apply measurable_subtype_coe hS] at hmass
  change (Measure.map (Subtype.val : W.carrier → X)
    (sourcePartialBergmanMeasureOnK L T W muK k phi)) S ≤ _
  rw [Measure.map_apply measurable_subtype_coe hS, sourcePartialBergmanMeasureOnK,
    Measure.smul_apply, smul_eq_mul, withDensity_apply _ hpre]
  calc
    _ ≤ sourceBergmanNormalization (n := n) k *
        ∫⁻ x in (Subtype.val : W.carrier → X) ⁻¹' S, b ∂muK := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hpre] with x hx
      exact hb x hx
    _ = sourceBergmanNormalization (n := n) k *
        (b * muK ((Subtype.val : W.carrier → X) ⁻¹' S)) := by
      rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    _ = _ := by rw [hmass, mul_assoc]

end SGPT.Bergman.ContactConcentration
