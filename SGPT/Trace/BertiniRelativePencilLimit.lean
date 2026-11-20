import SGPT.Trace.BertiniDiscExhaustion
import SGPT.Trace.OptimalRelativeNormalCurvature
import SGPT.Trace.BertiniRelativeBasePositivity
import SGPT.Trace.BertiniCriticalFibreCorrection
import SGPT.Trace.OptimalNormalEpsilonLimit
import SGPT.Trace.BertiniRelativePencilExtension

/-!
# Actual original relative-pencil limit extension

A finite ORIGINAL preliminary kernel-energy limit internally supplies its
bounded tail and all actual extension sections. No MEP or limiting extension
output is a hypothesis. Intrinsic Hodge normalization remains a separate gap.
Blueprint: work/sgpt-resume-20261114/bert-e2-relative-limit/blueprint/bert-e2-relative-limit.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniRelativePencilLimit
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

theorem exists_uniform_finite_tail_of_finite_limit {J : ℕ → ℝ≥0∞} {C : ℝ≥0∞}
    (hC : C < ⊤) (hlim : Tendsto J atTop (𝓝 C)) :
    ∃ (N : ℕ) (I : ℝ≥0∞), I < ⊤ ∧ (∀ j, J (j + N) ≤ I) ∧
      Tendsto (fun j => J (j + N)) atTop (𝓝 C) := by
  have hCI : C < C + 1 := ENNReal.lt_add_right hC.ne one_ne_zero
  have hevent : ∀ᶠ j in atTop, J j < C + 1 :=
    eventually_lt_of_limsup_lt (hlim.limsup_eq.trans_lt hCI)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨N, C + 1, ENNReal.add_lt_top.mpr ⟨hC, by norm_num⟩,
    fun j => (hN _ (Nat.le_add_left N j)).le, hlim.comp (tendsto_add_atTop_nat N)⟩

variable {m N : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (pY : Y → ComplexProjectiveSpace N) (iY : Fin (N + 1)) (aY vY : ComplexModel N)

/-- Actual fixed-epsilon full-pencil extension. Only the ORIGINAL
preliminary F kernel energy is assumed finite, not any output estimate. -/
theorem exists_actual_relative_pencil_limit_extension {ρ σ δ κ : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hδ : 0 < δ) (hκ : 0 < κ)
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
      ∀ ε : ℕ → ℝ, (∀ j, 0 < ε j) → Tendsto ε atTop (𝓝 0) →
      ∀ C : ℝ≥0∞, C < ⊤ →
      Tendsto (fun j => actualPreliminaryKernelEnergy B μ
        (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) φ₀ (ε j) σ δ F) atTop (𝓝 C) →
      ∃ S : (q : familyIncidence pY iY aY vY (parameterDisc ρ)) → B.Fiber q,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) B.Fiber S univ ∧
      (∀ q, normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ q = 0 → S q = F q) ∧
      (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
        (-Real.log (nativeRadius (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) q)) *
        ‖S q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ) ≤ C := by
  let := familyChartedSpace pY iY aY vY (parameterDisc ρ) hp hsm
  have := isComplexManifold_family pY iY aY vY (parameterDisc ρ) hp hsm
  intro B μ hμ hB φ₀ hφ hbase F hF ε hεpos hε C hC hlim
  obtain ⟨N₀, I, hI, hbound, hlimtail⟩ := exists_uniform_finite_tail_of_finite_limit hC hlim
  let η : ℕ → ℝ := fun j => ε (j + N₀)
  have hηpos : ∀ j, 0 < η j := fun j => hεpos _
  have hη : Tendsto η atTop (𝓝 0) := hε.comp (tendsto_add_atTop_nat N₀)
  have hfinite : ∀ j, actualPreliminaryKernelEnergy B μ
      (normalizedPencilNormal pY iY aY vY (parameterDisc ρ) ρ) φ₀ (η j) σ δ F ≠ ⊤ :=
    fun j => ((hbound j).trans_lt hI).ne
  choose T hT htrace hgain using fun j =>
    exists_actual_relative_pencil_epsilon_extension pY iY aY vY hρ (hηpos j) hσ hδ hκ hp hsm
      omega B μ hμ hB φ₀ hφ hbase F hF (hfinite j)
  exact exists_actual_epsilon_gain_limit B hμ (continuous_of_chartSmooth' hφ)
    (contMDiff_normalizedPencilNormal pY iY aY vY (parameterDisc ρ) hp hsm ρ)
    (surjective_mfderiv_normalizedPencilNormal pY iY aY vY (parameterDisc ρ) hp hsm hρ)
    hF hδ hηpos hη T hT htrace hgain hI hbound hlimtail

end SGPT.Trace.BertiniRelativePencilLimit
