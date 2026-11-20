import SGPT.Bergman.SourceSmoothWeightedBergmanBound
import SGPT.Bergman.SourcePartialBergmanTrace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.TensorDictionaryDraft
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]

omit [ConnectedSpace X] in
/-- Actual normalized original global beta is dominated by ONE constant
times the SAME raw smooth-positive volume, for every positive degree and
every multiplier ideal. All point-density estimates and measure transport
are produced internally; no limiting measure or bound certificate enters. -/
theorem exists_source_smooth_weighted_measure_bound
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ) :
    ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ, 0 < k → ∀ φ : X → EReal,
      sourcePartialBergmanMeasure L T (wholeWeightedSubset v)
          (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ ≤
        ENNReal.ofReal D • μ := by
  obtain ⟨C, hC, hb⟩ := exists_source_smooth_weighted_Bergman_bound L T hL hT v hv μ hμ
  refine ⟨(n.factorial : ℝ) * C, mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos n)) hC,
    fun k hk φ => ?_⟩
  let W := wholeWeightedSubset (n := n) v
  let μK := μ.comap (Subtype.val : W.carrier → X)
  have hpoint : μK.withDensity (sourcePartialBergmanDensity L T W μK k φ) ≤
      μK.withDensity (fun _ => ENNReal.ofReal (C * (k : ℝ) ^ n)) :=
    withDensity_mono (Filter.Eventually.of_forall (hb k hk φ))
  have hfactor : sourceBergmanNormalization (n := n) k *
      ENNReal.ofReal (C * (k : ℝ) ^ n) = ENNReal.ofReal ((n.factorial : ℝ) * C) := by
    have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    rw [sourceBergmanNormalization, ← ENNReal.ofReal_mul
      (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))]
    congr 1
    field_simp
  have hK : sourcePartialBergmanMeasureOnK L T W μK k φ ≤
      ENNReal.ofReal ((n.factorial : ℝ) * C) • μK := by
    calc
      _ ≤ sourceBergmanNormalization (n := n) k •
          μK.withDensity (fun _ => ENNReal.ofReal (C * (k : ℝ) ^ n)) := by
        dsimp only [sourcePartialBergmanMeasureOnK]
        gcongr
      _ = _ := by rw [withDensity_const, smul_smul, hfactor]
  change Measure.map (Subtype.val : W.carrier → X)
    (sourcePartialBergmanMeasureOnK L T W μK k φ) ≤ _
  calc
    _ ≤ Measure.map (Subtype.val : W.carrier → X)
        (ENNReal.ofReal ((n.factorial : ℝ) * C) • μK) :=
      Measure.map_mono hK measurable_subtype_coe
    _ = ENNReal.ofReal ((n.factorial : ℝ) * C) • μ := by
      dsimp only [μK, W, wholeWeightedSubset]
      rw [Measure.map_smul, map_comap_subtype_coe MeasurableSet.univ, Measure.restrict_univ]

end SGPT.Bergman.PolynomialH0Growth
