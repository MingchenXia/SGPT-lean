import SGPT.Bergman.SourceEnvelopeContactSets
import SGPT.Bergman.SourceWholeMeasurePointBound
import SGPT.Bergman.SourceSmoothBergmanEnvelopeBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.ContactConcentration

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.GeneralBMTransport SGPT.Bergman.SingularWeightedHilbert
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.PartialEnvelope
open SGPT.Bergman.MultiplierSectionSingularity SGPT.PSH.VariableComplexAtlas
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]

/-- Original fixed-m open contact gaps have an ACTUAL exponentially small
source beta mass, with ONE internally produced alpha/C/threshold. Full
Gamma, raw Kahler volume and exact n! coefficient are retained. Compact
QPSH upper bounds produce reference monotonicity internally, with no
phi normalization, desired point/measure bound, BM or weak-limit input. -/
theorem exists_source_fixedContactGap_exponential_bound
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (v : C(X, ℝ)) (hv : ChartSmooth (n := n) v)
    {phi : X → EReal} (hphi : IsGlobalQuasiPshPotential (n := n) phi)
    (han : (ofFixedModel n X).HasRationalAnalyticChartType phi)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ alpha : ℕ → ℝ, StrictMono alpha ∧ (∀ k, 0 < alpha k ∧ alpha k < 1) ∧
      Tendsto alpha atTop (𝓝 1) ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧
        ∀ m : ℕ, ∀ delta : ℝ, 0 < delta → ∀ k : ℕ, N ≤ k → m ≤ k →
          sourcePartialBergmanMeasure L T (wholeWeightedSubset v)
            ((IntegrationCurrent.kahlerVolume omega).comap
              (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k phi
            (sourceEnvelopeGap
              (nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL + eps • omega.form))
              (fun x => ((alpha m : ℝ) : EReal) * phi x) v delta) ≤
          ENNReal.ofReal ((n.factorial : ℝ) * C * Real.exp (-((k : ℝ) * delta))) *
            IntegrationCurrent.kahlerVolume omega univ := by
  obtain ⟨alpha, hmono, ha, hlim, C, hC, N, hN, hkernel⟩ :=
    exists_source_smooth_Bergman_envelope_bound omega L T hL hT v hv hphi han heps
  refine ⟨alpha, hmono, ha, hlim, C, hC, N, hN, fun m delta _hdelta k hk hmk => ?_⟩
  let theta := nativeClosedFormToAtlas (sourceNativeFirstChernForm L hL + eps • omega.form)
  let F := sourceEnvelopeGap theta (fun x => ((alpha m : ℝ) : EReal) * phi x) v delta
  have hF : MeasurableSet F := (sourceEnvelopeGap_isOpen theta _ v delta).measurableSet
  have hanti := sourceScaledReferenceEnvelopes_antitone theta phi hphi v alpha hmono.monotone
    (fun j => (ha j).1)
  have hkpos : 0 < k := lt_of_lt_of_le hN hk
  have hpoint : ∀ x : (wholeWeightedSubset (n := n) v).carrier, x.val ∈ F →
      sourcePartialBergmanDensity L T (wholeWeightedSubset v)
        ((IntegrationCurrent.kahlerVolume omega).comap
          (Subtype.val : (wholeWeightedSubset (n := n) v).carrier → X)) k phi x ≤
      ENNReal.ofReal (C * (k : ℝ) ^ n) * ENNReal.ofReal (Real.exp (-((k : ℝ) * delta))) := by
    intro x hx
    have hgap := (hanti hmk x.val).trans_lt hx
    have hsub : partialEnvelope theta (fun y => ((alpha k : ℝ) : EReal) * phi y)
        univ (fun y : ↥(univ : Set X) => (v y.val : EReal)) x.val - (v x.val : EReal) ≤
        ((-delta : ℝ) : EReal) := by
      calc
        _ ≤ (((v x.val - delta : ℝ) : EReal) - (v x.val : EReal)) :=
          EReal.sub_le_sub hgap.le le_rfl
        _ = _ := by rw [← EReal.coe_sub]; congr 1; ring
    have hexp := EReal.exp_monotone
      (mul_le_mul_of_nonneg_left hsub (EReal.coe_nonneg.mpr (Nat.cast_nonneg k)))
    rw [← EReal.coe_mul, EReal.exp_coe] at hexp
    have hexp' : EReal.exp (((k : ℝ) : EReal) *
        (partialEnvelope theta (fun y => ((alpha k : ℝ) : EReal) * phi y) univ
          (fun y : ↥(univ : Set X) => (v y.val : EReal)) x.val - (v x.val : EReal))) ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * delta))) := by
      simpa only [mul_neg] using hexp
    exact (hkernel k hk x).trans (mul_le_mul' le_rfl hexp')
  have hmass := sourceWholeMeasure_apply_le_of_pointwise L T v
    (IntegrationCurrent.kahlerVolume omega) k phi F hF
    (ENNReal.ofReal (C * (k : ℝ) ^ n) * ENNReal.ofReal (Real.exp (-((k : ℝ) * delta)))) hpoint
  have hfactor : sourceBergmanNormalization (n := n) k *
      ENNReal.ofReal (C * (k : ℝ) ^ n) = ENNReal.ofReal ((n.factorial : ℝ) * C) := by
    have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hkpos
    rw [sourceBergmanNormalization, ← ENNReal.ofReal_mul
      (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))]
    congr 1
    field_simp
  calc
    _ ≤ sourceBergmanNormalization (n := n) k *
        (ENNReal.ofReal (C * (k : ℝ) ^ n) * ENNReal.ofReal (Real.exp (-((k : ℝ) * delta)))) *
        IntegrationCurrent.kahlerVolume omega F := hmass
    _ = ENNReal.ofReal ((n.factorial : ℝ) * C * Real.exp (-((k : ℝ) * delta))) *
        IntegrationCurrent.kahlerVolume omega F := by
      rw [← mul_assoc, hfactor, ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hC.le)]
    _ ≤ _ := mul_le_mul' le_rfl (measure_mono (subset_univ F))

end SGPT.Bergman.ContactConcentration
