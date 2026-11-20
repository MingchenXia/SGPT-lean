import SGPT.PSH.GlobalL2BergmanUpper
import SGPT.Bergman.SourceTwistedMultiplierSections
import SGPT.PSH.SingularityOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.MultiplierSectionSingularity

open Bundle Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
  SGPT.Foundations.Analysis.FirstPass.AnalyticGluingData SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.MultiplierSectionsDraft SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle SGPT.PSH.GlobalL2
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [BorelSpace X] in
/-- Actual normalization of the SAME finite-integral full holomorphic section
into the TRUE singular-weight Bergman unit ball. No density, basis or
normalization certificate is supplied. Zero sections and all poles remain. -/
theorem exists_normalizedLogNormSq_le_bergmanSeq
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (φ : X → EReal) (k : ℕ) (hk : 0 < k) (s : twistedSections L T k)
    (hfin : (∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
      ∂(IntegrationCurrent.kahlerVolume omega)) < ⊤) :
    ∃ C : ℝ, ∀ x : X,
      (((k : ℝ)⁻¹ : ℝ) : EReal) * logNormSq (s x) ≤
        bergmanSeq omega L T φ k x + (C : EReal) := by
  set I : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal (‖s y‖ ^ 2) *
    multiplierWeight (k : ℝ) (φ y) ∂(IntegrationCurrent.kahlerVolume omega) with hI
  set M : ℝ := I.toReal + 1 with hM
  have hM0 : 0 < M := by positivity
  have hIM : I ≤ ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_toReal hfin.ne]
    exact ENNReal.ofReal_le_ofReal (by dsimp only [M]; linarith)
  set c : ℝ := Real.sqrt M⁻¹ with hc
  have hc2 : c ^ 2 = M⁻¹ := Real.sq_sqrt (by positivity)
  set t : twistedSections L T k := (c : ℂ) • s with ht
  have hty : ∀ y, ‖t y‖ ^ 2 = M⁻¹ * ‖s y‖ ^ 2 := by
    intro y
    rw [ht, ContMDiffSection.coe_smul, Pi.smul_apply, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hc2]
  have hunit : (∫⁻ y, ENNReal.ofReal (‖t y‖ ^ 2) *
      multiplierWeight (k : ℝ) (φ y) ∂(IntegrationCurrent.kahlerVolume omega)) ≤ 1 := by
    calc
      _ = ENNReal.ofReal M⁻¹ * I := by
        rw [hI, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        apply lintegral_congr
        intro y
        rw [hty, ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal M⁻¹ * ENNReal.ofReal M := mul_le_mul' le_rfl hIM
      _ = 1 := by
        rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hM0.ne', ENNReal.ofReal_one]
  refine ⟨(k : ℝ)⁻¹ * Real.log M, fun x => ?_⟩
  have hsup : ENNReal.ofReal (‖t x‖ ^ 2) ≤
      ⨆ a : twistedSections L T k,
        ⨆ (_ : ∫⁻ y, ENNReal.ofReal (‖a y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
          ∂(IntegrationCurrent.kahlerVolume omega) ≤ 1), ENNReal.ofReal (‖a x‖ ^ 2) :=
    le_iSup₂ (f := fun (a : twistedSections L T k)
      (_ : ∫⁻ y, ENNReal.ofReal (‖a y‖ ^ 2) * multiplierWeight (k : ℝ) (φ y)
        ∂(IntegrationCurrent.kahlerVolume omega) ≤ 1) => ENNReal.ofReal (‖a x‖ ^ 2)) t hunit
  have hrecover : ENNReal.ofReal (‖s x‖ ^ 2) =
      ENNReal.ofReal (‖t x‖ ^ 2) * ENNReal.ofReal M := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _), hty]
    congr 1
    field_simp
  have hlog := ENNReal.log_monotone (mul_le_mul' hsup (le_refl (ENNReal.ofReal M)))
  rw [← hrecover, ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hM0] at hlog
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have h := mul_le_mul_of_nonneg_left hlog (EReal.coe_nonneg.mpr (inv_nonneg.mpr hkp.le))
  rw [SGPT.PSH.MultiplierIdealInf.coe_mul_add_coe (inv_pos.mpr hkp)] at h
  simpa only [bergmanSeq, one_div, logNormSq] using h

/-- The actual original ideal-stalk Gamma automatically has the finite
singular-weight integral needed by the genuine normalization above. -/
theorem literalGamma_normalizedLogNormSq_singularityLE_bergmanSeq
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (k : ℕ) (hk : 0 < k) (s : LiteralTwistedMultiplierSections L T k φ) :
    SGPT.PSH.SingularityLE
      (fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) *
        logNormSq ((literalTwistedMultiplierSectionEquiv L T k φ s).val x))
      (bergmanSeq omega L T φ k) := by
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  have hfin := (fullHolomorphicDegreeIdealSections_iff_finite_integral (n := n)
    (twistedPower L T k).Fiber k hφ
    (literalTwistedMultiplierSectionEquiv L T k φ s).val hμ).mp
      (literalTwistedMultiplierSectionEquiv L T k φ s).property
  apply (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr
  apply exists_normalizedLogNormSq_le_bergmanSeq omega L T φ k hk
  simpa only [originalSectionDensity] using hfin

/-- ONE genuine alpha sequence, internally produced from the original
multiplier-ideal approximation, controls ALL original Gamma sections. -/
theorem exists_alpha_literalGamma_normalizedLogNormSq_singularityLE
    (omega : KahlerBackground n X) (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    {φ : X → EReal} (hφ : IsGlobalQuasiPshPotential (n := n) φ)
    (hφan : (SGPT.PSH.VariableComplexAtlas.ofFixedModel n X).HasRationalAnalyticChartType φ) :
    ∃ α : ℕ → ℝ, StrictMono α ∧ (∀ k, 0 < α k ∧ α k < 1) ∧ Tendsto α atTop (𝓝 1) ∧
      ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ∀ s : LiteralTwistedMultiplierSections L T k φ,
          SGPT.PSH.SingularityLE
            (fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) *
              logNormSq ((literalTwistedMultiplierSectionEquiv L T k φ s).val x))
            (fun x => ((α k : ℝ) : EReal) * φ x) := by
  obtain ⟨α, hmono, hα, hlim, k₀, hupper⟩ := bergmanSeq_upper omega L T hφ hφan
  refine ⟨α, hmono, hα, hlim, max k₀ 1, by omega, fun k hk s => ?_⟩
  apply SGPT.PSH.singularityLE_trans
    (literalGamma_normalizedLogNormSq_singularityLE_bergmanSeq omega L T hφ k (by omega) s)
  exact (SGPT.PSH.singularityLE_iff_exists_real _ _).mpr (hupper k (by omega))

end SGPT.Bergman.MultiplierSectionSingularity
