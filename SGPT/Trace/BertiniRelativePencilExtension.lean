import SGPT.Trace.BertiniDiscExhaustion
import SGPT.Trace.OptimalRelativeNormalCurvature
import SGPT.Trace.BertiniRelativeBasePositivity
import SGPT.Trace.BertiniCriticalFibreCorrection

/-!
# Actual original relative pencil sharp correction and central interpolation

The original quantitative X curvature comparison is converted using the
actual joint native metric. No strict pulled-X parameter curvature premise.
Blueprint: work/sgpt-resume-20261114/bert-e2-relative-pencil/blueprint/bert-e2-relative-pencil.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniRelativePencilExtension
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
open SGPT.Trace.OptimalRelativeNormalCurvature SGPT.Trace.BertiniRelativeBasePositivity
open SGPT.Trace.BertiniCriticalFibreCorrection

variable {n N : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)

/-- SAME original full native pencil, actual metric and actual exhaustion.
Both singular and sharp gain estimates retain the SAME physical section. -/
theorem exists_actual_relative_pencil_sharp_correction {ρ ε σ δ κ : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ) (hκ : 0 < κ)
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
        ∀ w : ComplexModel n, κ * familyXQuad p i a v (parameterDisc ρ) hp hsm omega c z w ≤
          leviForm (SGPT.Trace.TwistedL2.localWeight B c e d φ₀) z w) →
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
  apply exists_actual_relative_sharp_weighted_correction B
    (familyKahlerBackground p i a v (parameterDisc ρ) hp hsm omega)
    (fun q => ballExhaustion 0 ρ q.val.1.val) hExh.1 hExh.2.1 hExh.2.2 μ hμ hB hφ
    (contMDiff_normalizedPencilNormal p i a v (parameterDisc ρ) hp hsm ρ)
    (surjective_mfderiv_normalizedPencilNormal p i a v (parameterDisc ρ) hp hsm hρ)
    (actual_pencil_normal_radius_lt_one p i a v hρ) hε hσ hδ hρ
    (fun c z hz w => norm_sq_scaled_normal_deriv_le p i a v (parameterDisc ρ) hp hsm omega hρ c z hz w)
    ?_ ?_ hF
  · intro c e d hd z hz w
    exact (relative_base_levi_conditions p i a v (parameterDisc ρ) hp hsm omega hρ hκ c z hz.1
      (SGPT.Trace.TwistedL2.localWeight B c e d φ₀) (hbase c e d hd z hz)).1 w
  · intro c e d hd z hz w hw hdf
    exact (relative_base_levi_conditions p i a v (parameterDisc ρ) hp hsm omega hρ hκ c z hz.1
      (SGPT.Trace.TwistedL2.localWeight B c e d φ₀) (hbase c e d hd z hz)).2 w hw hdf


section PositiveDimension
variable {m : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (pY : Y → ComplexProjectiveSpace N) (iY : Fin (N + 1)) (aY vY : ComplexModel N)

/-- Actual fixed-epsilon full-pencil extension. Only the ORIGINAL
preliminary F kernel energy is assumed finite, not any output estimate. -/
theorem exists_actual_relative_pencil_epsilon_extension {ρ ε σ δ κ : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ) (hκ : 0 < κ)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel N) ∞ pY)
    (hsm : ∀ t : parameterDisc ρ, IsSmoothHypersurfaceMember (m + 1) pY (pencilParameter iY aY vY t.val))
    (omega : KahlerBackground (m + 1) Y) :
    letI := familyChartedSpace pY iY aY vY (parameterDisc ρ) hp hsm
    haveI := isComplexManifold_family pY iY aY vY (parameterDisc ρ) hp hsm
    ∀ (B : HermitianHolomorphicLineBundle.{0, 0} (m + 1) (familyIncidence pY iY aY vY (parameterDisc ρ)))
      (μ : Measure (familyIncidence pY iY aY vY (parameterDisc ρ))),
      IsSmoothPositiveVolume (n := m + 1) μ → IsSourceSmoothHermitianMetric B →
      ∀ φ₀ : familyIncidence pY iY aY vY (parameterDisc ρ) → ℝ, ChartSmooth (n := m + 1) φ₀ →
      (∀ (c : ComplexChart (m + 1) (familyIncidence pY iY aY vY (parameterDisc ρ))) (e : AtlasFrame B)
        (d : ComplexModel (m + 1) → ℝ), IsChartDensity μ c d → ∀ z ∈ chartFrameDomain B c e,
        ∀ w : ComplexModel (m + 1), κ * familyXQuad pY iY aY vY (parameterDisc ρ) hp hsm omega c z w ≤
          leviForm (SGPT.Trace.TwistedL2.localWeight B c e d φ₀) z w) →
      ∀ F : (q : familyIncidence pY iY aY vY (parameterDisc ρ)) → B.Fiber q,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) B.Fiber F univ →
      (∫⁻ q, ENNReal.ofReal ((windowMass σ + δ) *
        normalKernel ε (nativeRadius (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) q) *
        ‖F q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ) ≠ ⊤ →
      ∃ S : (q : familyIncidence pY iY aY vY (parameterDisc ρ)) → B.Fiber q,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) B.Fiber S univ ∧
      (∀ q, normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ q = 0 → S q = F q) ∧
      (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
        (normalTime ε (nativeRadius (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) q)) *
        ‖cutoffSection B (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) ε F q - S q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ) ≤
      (∫⁻ q, ENNReal.ofReal ((windowMass σ + δ) *
        normalKernel ε (nativeRadius (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) q) *
        ‖F q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ) := by
  let := familyChartedSpace pY iY aY vY (parameterDisc ρ) hp hsm
  have := isComplexManifold_family pY iY aY vY (parameterDisc ρ) hp hsm
  intro B μ hμ hB φ₀ hφ hbase F hF hIKernel
  obtain ⟨S, hShol, hRaw, hGain⟩ := exists_actual_relative_pencil_sharp_correction pY iY aY vY hρ hε hσ hδ hκ hp hsm
    omega B μ hμ hB φ₀ hφ hbase F hF
  have hf := contMDiff_normalizedPencilNormal pY iY aY vY (parameterDisc ρ) hp hsm ρ
  have hsub := surjective_mfderiv_normalizedPencilNormal pY iY aY vY (parameterDisc ρ) hp hsm hρ
  have hR := actual_pencil_normal_radius_lt_one pY iY aY vY hρ
  have hzero := measure_eq_zero_of_isLocallyAnalyticNull hμ (isLocallyAnalyticNull_native_zeroSet hf hsub)
  have hae : ∀ᵐ q ∂μ, normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ q ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  have hData : (∫⁻ q, ENNReal.ofReal (curvatureDatum B
        (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) ε F q) *
        multiplierWeight 1 (optimalNativeWeight (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) φ₀ ε σ δ q) ∂μ) ≤
      ∫⁻ q, ENNReal.ofReal ((windowMass σ + δ) *
        normalKernel ε (nativeRadius (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) q) *
        ‖F q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with q hq
    exact actual_data_energy_comparison B _ φ₀ hε hσ hδ F hq (hR q)
  have hRawFinite := ne_top_of_le_ne_top hIKernel (hRaw.trans hData)
  refine ⟨S, hShol, ?_, hGain⟩
  exact fibre_agreement_of_finite_original_error B hB hμ hf hsub hR hφ hε hσ hδ hF hShol hRawFinite

end PositiveDimension

end SGPT.Trace.BertiniRelativePencilExtension
