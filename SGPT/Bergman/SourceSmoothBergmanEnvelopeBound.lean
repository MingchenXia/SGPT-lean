import SGPT.Bergman.SourceGammaPartialEnvelope
import SGPT.Bergman.SourceSectionEnvelopeExponential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.MultiplierSectionSingularity

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.GeneralBMTransport SGPT.Bergman.BernsteinMarkov
open SGPT.Bergman.SingularWeightedHilbert
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]

/-- The actual source924-925 exponential partial-Bergman envelope bound.
The internally manufactured alpha, C and threshold work on the ENTIRE
original tensor-sheaf Gamma unit ball. Actual zero sections, empty Gamma,
n=0 and both infinite envelope values are included. The SAME raw original
Kahler volume and exact C*k^n prefactor are retained throughout. -/
theorem exists_source_smooth_Bergman_envelope_bound
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (hφan : (ofFixedModel n X).HasRationalAnalyticChartType φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ α : ℕ → ℝ, StrictMono α ∧ (∀ k, 0 < α k ∧ α k < 1) ∧ Tendsto α atTop (𝓝 1) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ∀ x : (wholeWeightedSubset (n := n) v).carrier,
          sourcePartialBergmanDensity L T (wholeWeightedSubset v)
            ((IntegrationCurrent.kahlerVolume omega).comap
              (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k φ x ≤
          ENNReal.ofReal (C * (k : ℝ) ^ n) *
            EReal.exp (((k : ℝ) : EReal) *
              (partialEnvelope
                (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL + ε • omega.form))
                (fun y => ((α k : ℝ) : EReal) * φ y) univ
                (fun y : ↥(univ : Set X) => (v y.val : EReal)) x.val - (v x.val : EReal))) := by
  obtain ⟨α, hmono, hα, hlim, C, hC, k₀, hk₀, henv⟩ :=
    exists_alpha_source_section_le_partialEnvelope omega L T hL hT v hv hφ hφan hε
  refine ⟨α, hmono, hα, hlim, C, hC, k₀, hk₀, fun k hk x => ?_⟩
  have hkpos : 0 < k := lt_of_lt_of_le hk₀ hk
  unfold sourcePartialBergmanDensity
  refine iSup₂_le fun s hs => ?_
  change weightedSectionDensity (twistedPower L T k).Fiber k (univRealWeight v)
    (literalTwistedMultiplierSectionEquiv L T k φ s).val x ≤ _
  rw [weightedSectionDensity_univ]
  by_cases hs0 : s = 0
  · subst s
    simp only [map_zero, ZeroMemClass.coe_zero, realWeightedSectionDensity,
      ContMDiffSection.coe_zero, Pi.zero_apply, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, ENNReal.ofReal_zero]
    exact zero_le
  exact weightedDensity_le_exp_of_normalizedLog_le
    ((literalTwistedMultiplierSectionEquiv L T k φ s).val x.val) (v x.val)
    (C * (k : ℝ) ^ n) (mul_pos hC (pow_pos (Nat.cast_pos.mpr hkpos) n)) k hkpos _
    (henv k hk s hs0 hs x.val)

end SGPT.Bergman.MultiplierSectionSingularity
