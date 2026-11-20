import SGPT.Trace.BertiniDiscExhaustion
import SGPT.Trace.OptimalNativeNormalCorrection

/-!
# Actual original full-pencil sharp weighted correction

All domain and normal geometry is produced for the SAME original native
full incidence over its actual open parameter disc. No supplied
pseudoconvexity or resulting analytic data/extension estimate.
Blueprint: work/sgpt-resume-20261114/bert-e2-pencil-correction/blueprint/bert-e2-pencil-correction.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniPencilSharpCorrection
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Okounkov.TranscendentalRelGen
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini
open SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniNormalMetric SGPT.Trace.BertiniDiscExhaustion
open SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass SGPT.Trace.OptimalNormalRegularization
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalDatum
open SGPT.Trace.OptimalNativeNormalBackground SGPT.Trace.OptimalNativeNormalCorrection

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)

/-- SAME original full native pencil, actual metric and actual exhaustion.
Both singular and sharp gain estimates retain the SAME physical section. -/
theorem exists_actual_pencil_sharp_correction {ρ ε σ δ : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : parameterDisc ρ, IsSmoothHypersurfaceMember n p (pencilParameter i a v t.val))
    (omega : KahlerBackground n X) :
    letI := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
    haveI := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
    ∀ (B : HermitianHolomorphicLineBundle.{0, 0} n (familyIncidence p i a v (parameterDisc ρ)))
      (μ : Measure (familyIncidence p i a v (parameterDisc ρ))),
      IsSmoothPositiveVolume (n := n) μ → IsSourceSmoothHermitianMetric B →
      ∀ φ₀ : familyIncidence p i a v (parameterDisc ρ) → ℝ, ChartSmooth (n := n) φ₀ →
      (∀ (c : ComplexChart n (familyIncidence p i a v (parameterDisc ρ))) (e : AtlasFrame B)
        (d : ComplexModel n → ℝ), IsChartDensity μ c d → ∀ z ∈ chartFrameDomain B c e,
        ∀ w : ComplexModel n, w ≠ 0 → 0 < leviForm (SGPT.Trace.TwistedL2.localWeight B c e d φ₀) z w) →
      ∀ F : (q : familyIncidence p i a v (parameterDisc ρ)) → B.Fiber q,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) B.Fiber F univ →
      ∃ S : (q : familyIncidence p i a v (parameterDisc ρ)) → B.Fiber q,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) B.Fiber S univ ∧
      (∫⁻ q, ENNReal.ofReal (‖cutoffSection B (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) ε F q - S q‖ ^ 2 /
        (nativeTwist (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) ε σ δ q +
          nativeCorrection (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) ε σ δ q)) *
        multiplierWeight 1 (optimalNativeWeight (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) φ₀ ε σ δ q) ∂μ) ≤
      (∫⁻ q, ENNReal.ofReal (curvatureDatum B (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) ε F q) *
        multiplierWeight 1 (optimalNativeWeight (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) φ₀ ε σ δ q) ∂μ) ∧
      (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
        (normalTime ε (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q)) *
        ‖cutoffSection B (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) ε F q - S q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ) ≤
      (∫⁻ q, ENNReal.ofReal ((windowMass σ + δ) *
        normalKernel ε (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q) *
        ‖F q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ) := by
  let := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
  have := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
  intro B μ hμ hB φ₀ hφ hbase F hF
  have hExh := actual_pencil_disc_exhaustion p i a v hρ hp hsm
  exact exists_actual_native_sharp_weighted_correction B
    (familyKahlerBackground p i a v (parameterDisc ρ) hp hsm omega)
    (fun q => ballExhaustion 0 ρ q.val.1.val) hExh.1 hExh.2.1 hExh.2.2 μ hμ hB hφ
    (contMDiff_normalizedPencilNormal p i a v (parameterDisc ρ) hp hsm ρ)
    (surjective_mfderiv_normalizedPencilNormal p i a v (parameterDisc ρ) hp hsm hρ)
    (actual_pencil_normal_radius_lt_one p i a v hρ) hε hσ hδ hρ
    (fun c z hz w => norm_sq_scaled_normal_deriv_le p i a v (parameterDisc ρ) hp hsm omega hρ c z hz w)
    hbase hF

end SGPT.Trace.BertiniPencilSharpCorrection
