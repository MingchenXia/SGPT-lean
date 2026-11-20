import SGPT.Bergman.SourceSmoothWeightedPolynomialBound
import SGPT.Bergman.SourceGeneralBergmanTransport
import SGPT.Bergman.SourcePartialBergmanDensity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.PolynomialH0Growth
open Bundle Set Filter Metric MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.BernsteinMarkov
open SGPT.Bergman.SingularWeightedHilbert SGPT.Bergman.GeneralBMTransport
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]

omit [BorelSpace X] [CompactSpace X] [ConnectedSpace X] in
/-- The literal original squared-L2 admissibility gives the actual whole-X
quadratic lower-integral bound, even before a Hilbert or BM structure.
Both the raw smooth-volume normalization and source weight are retained. -/
theorem integral_realWeightedSectionDensity_le_one_of_admissible
    (L T : HermitianHolomorphicLineBundle n X) (v : C(X, ℝ))
    (μ : Measure X) (k : ℕ) (s : twistedSections L T k)
    (hs : weightedL2Norm (twistedPower L T k).Fiber k
      (wholeWeightedSubset (n := n) v).erealWeight
      (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) s ≤ 1) :
    (∫⁻ x, ENNReal.ofReal (realWeightedSectionDensity L T v k s x) ∂μ) ≤ 1 := by
  rw [whole_weightedL2Norm, weightedL2Norm_univ] at hs
  have hh := ENNReal.rpow_le_rpow hs (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul] at hh
  norm_num at hh
  exact hh

omit [ConnectedSpace X] in
/-- Genuine original smooth-weight Bergman point bound. One C precedes
EVERY positive degree, EVERY multiplier potential and EVERY point. The
supremum is over the original literal sheaf-tensor Gamma, with no basis,
density, peak section, BM or asymptotic certificate from the caller.
The actual raw smooth positive volume is unchanged. -/
theorem exists_source_smooth_weighted_Bergman_bound
    (L T : HermitianHolomorphicLineBundle n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 0 < k → ∀ φ : X → EReal,
      ∀ x : (wholeWeightedSubset (n := n) v).carrier,
        sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            (μ.comap (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ x ≤
          ENNReal.ofReal (C * (k : ℝ) ^ n) := by
  obtain ⟨C, hC, hb⟩ := exists_global_weighted_polynomial_section_bound L T hL hT v hv μ hμ
  refine ⟨C, hC, fun k hk φ x => ?_⟩
  unfold sourcePartialBergmanDensity
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  change weightedSectionDensity (twistedPower L T k).Fiber k (univRealWeight v)
    (literalTwistedMultiplierSectionEquiv L T k φ s).val x ≤ _
  rw [weightedSectionDensity_univ L T v k
    (literalTwistedMultiplierSectionEquiv L T k φ s).val x]
  have hI := integral_realWeightedSectionDensity_le_one_of_admissible L T v μ k
    (literalTwistedMultiplierSectionEquiv L T k φ s).val hs
  exact (hb k hk (literalTwistedMultiplierSectionEquiv L T k φ s).val x.val).trans
    (by simpa only [mul_one] using mul_le_mul' (le_refl (ENNReal.ofReal (C * (k : ℝ) ^ n))) hI)

end SGPT.Bergman.PolynomialH0Growth
