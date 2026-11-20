import SGPT.Trace.BertiniDiscExhaustion
import SGPT.Trace.OptimalRelativeNormalCurvature
import SGPT.Trace.BertiniRelativeBasePositivity
import SGPT.Trace.BertiniCriticalFibreCorrection
import SGPT.Trace.OptimalNormalEpsilonLimit
import SGPT.Trace.BertiniRelativePencilExtension
import SGPT.Trace.BertiniRelativePencilLimit
import SGPT.Trace.OptimalSingularWeightLimit

/-!
# Actual original singular sharp extension on the full native pencil

Raw original curvature-preserving real approximants and preliminary kernel
limits produce all approximate and limiting sections internally. Original
native metric/volume/residue normalization is a separate source producer.
Blueprint: work/sgpt-resume-20261114/bert-e2-singular-pencil/blueprint/bert-e2-singular-pencil.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniSingularPencilLimit
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
open SGPT.Trace.OptimalNormalEpsilonLimit SGPT.Trace.BertiniRelativePencilExtension
open SGPT.Trace.BertiniRelativePencilLimit SGPT.Trace.OptimalSingularWeightLimit
open SGPT.Trace.OptimalGainCompactBounds

variable {m N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (p : Y → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)

theorem exists_actual_singular_pencil_sharp_extension {ρ σ δ κ : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hδ : 0 < δ) (hκ : 0 < κ)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : parameterDisc ρ, IsSmoothHypersurfaceMember (m + 1) p (pencilParameter i a v t.val))
    (omega : KahlerBackground (m + 1) Y) :
    letI := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
    haveI := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
    ∀ (B : HermitianHolomorphicLineBundle.{0, 0} (m + 1) (familyIncidence p i a v (parameterDisc ρ)))
      (μ : Measure (familyIncidence p i a v (parameterDisc ρ))),
      IsSmoothPositiveVolume (n := m + 1) μ → IsSourceSmoothHermitianMetric B →
      ∀ φj : ℕ → familyIncidence p i a v (parameterDisc ρ) → ℝ,
      (∀ j, ChartSmooth (n := m + 1) (φj j)) →
      (∀ q, Antitone (fun j => φj j q)) →
      ∀ φ : familyIncidence p i a v (parameterDisc ρ) → EReal,
      (∀ q, Tendsto (fun j => (φj j q : EReal)) atTop (𝓝 (φ q))) →
      (∀ j (c : ComplexChart (m + 1) (familyIncidence p i a v (parameterDisc ρ))) (e : AtlasFrame B)
        (d : ComplexModel (m + 1) → ℝ), IsChartDensity μ c d → ∀ z ∈ chartFrameDomain B c e,
        ∀ w : ComplexModel (m + 1), κ * familyXQuad p i a v (parameterDisc ρ) hp hsm omega c z w ≤
          leviForm (SGPT.Trace.TwistedL2.localWeight B c e d (φj j)) z w) →
      ∀ F : (q : familyIncidence p i a v (parameterDisc ρ)) → B.Fiber q,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) B.Fiber F univ →
      ∀ ε : ℕ → ℝ, (∀ k, 0 < ε k) → Tendsto ε atTop (𝓝 0) →
      ∀ C : ℕ → ℝ≥0∞,
      (∀ j, Tendsto (fun k => actualPreliminaryKernelEnergy B μ
        (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) (φj j) (ε k) σ δ F) atTop (𝓝 (C j))) →
      ∀ I : ℝ≥0∞, I < ⊤ → (∀ j, C j ≤ I) →
      ∃ S : (q : familyIncidence p i a v (parameterDisc ρ)) → B.Fiber q,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) B.Fiber S univ ∧
      (∀ q, normalizedPencilNormal p i a v (parameterDisc ρ) ρ q = 0 → S q = F q) ∧
      (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
        (-Real.log (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q)) *
        ‖S q‖ ^ 2) * multiplierWeight 1 (φ q) ∂μ) ≤ I := by
  let := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
  have := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
  intro B μ hμ hB φj hφj hmono φ hφlim hbase F hF ε hεpos hε C hClim I hI hCbound
  choose T hT htrace hgain using fun j =>
    exists_actual_relative_pencil_limit_extension p i a v hρ hσ hδ hκ hp hsm omega
      B μ hμ hB (φj j) (hφj j) (hbase j) F hF ε hεpos hε (C j)
        ((hCbound j).trans_lt hI) (hClim j)
  apply exists_actual_normal_gain_limit_of_real_weight_approximation B hμ
    (contMDiff_normalizedPencilNormal p i a v (parameterDisc ρ) hp hsm ρ).continuous
    hδ φj hφj hmono φ hφlim T hT F htrace hI
  intro j
  have heq : (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
        (-Real.log (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q)) *
        ‖T j q‖ ^ 2) * multiplierWeight 1 (φj j q : EReal) ∂μ) =
      (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
        (-Real.log (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q)) *
        ‖T j q‖ ^ 2 * Real.exp (-φj j q)) ∂μ) := by
    apply lintegral_congr_ae
    filter_upwards [] with q
    simp only [multiplierWeight_coe, one_mul]
    exact (ENNReal.ofReal_mul (mul_nonneg
      (hδ.le.trans (slack_le_actual_annular_gain σ δ _)) (sq_nonneg _))).symm
  rw [heq]
  exact (hgain j).trans (hCbound j)

end SGPT.Trace.BertiniSingularPencilLimit
