import SGPT.Trace.OptimalCriticalNormalVanishing
import SGPT.Trace.BertiniPencilSharpCorrection

/-!
# The actual corrected section retains the original fibre

The retained genuine singular error estimate forces pointwise agreement by
actual physical critical-normal vanishing. The final theorem assumes only
finiteness of the ORIGINAL preliminary section's kernel data energy.
Blueprint: work/sgpt-resume-20261114/bert-e2-fibre-correction/blueprint/bert-e2-fibre-correction.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniCriticalFibreCorrection
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass
open SGPT.Trace.OptimalNormalRegularization SGPT.Trace.OptimalNativeNormalWeight
open SGPT.Trace.OptimalNativeNormalDatum SGPT.Trace.OptimalNativeNormalBackground
open SGPT.Trace.OptimalNativeNormalCorrection SGPT.Trace.OptimalCriticalNormalVanishing
open SGPT.Trace.BertiniPencilFamily SGPT.Trace.BertiniDiscExhaustion
open SGPT.Trace.BertiniPencilSharpCorrection
open SGPT.Projective SGPT.Projective.ComplexProjectiveSpace SGPT.Trace.Bertini

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
  (L : HermitianHolomorphicLineBundle.{0, 0} (m + 1) X)

/-- The true critical ordinary quotient is pointwise bounded by the SAME
original singular error density, retaining the original pole convention. -/
theorem critical_error_energy_le_original (f : X → ℂ) (φ₀ : X → ℝ)
    {ε σ δ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ)
    (x : X) (hR1 : nativeRadius f x < 1) (u : L.Fiber x) :
    ENNReal.ofReal (‖u‖ ^ 2 * annularDensity σ δ (normalTime ε (nativeRadius f x)) *
      Real.exp (-φ₀ x) / ‖f x‖ ^ 2) ≤
    ENNReal.ofReal (‖u‖ ^ 2 / (nativeTwist f ε σ δ x + nativeCorrection f ε σ δ x)) *
      multiplierWeight 1 (optimalNativeWeight f φ₀ ε σ δ x) := by
  by_cases hfx : f x = 0
  · simp only [hfx, norm_zero, zero_pow (by decide : 2 ≠ 0), div_zero, ENNReal.ofReal_zero]
    exact bot_le
  have hc : optimalNativeWeight f φ₀ ε σ δ x =
      ((Real.log (nativeRadius f x) + φ₀ x +
        potential (annularDensity σ δ) (normalTime ε (nativeRadius f x)) : ℝ) : EReal) := by
    unfold optimalNativeWeight normalWeight
    rw [logNormSq_of_ne_zero hfx, ← EReal.coe_add]
    congr 1
    unfold nativeRadius
    ring
  have hbot : optimalNativeWeight f φ₀ ε σ δ x ≠ ⊥ := by rw [hc]; exact EReal.coe_ne_bot _
  have htop : optimalNativeWeight f φ₀ ε σ δ x ≠ ⊤ := by rw [hc]; exact EReal.coe_ne_top _
  rw [← ofReal_mul_exp_neg_toReal _ hbot htop, hc, EReal.toReal_coe]
  apply ENNReal.ofReal_le_ofReal
  have hr : 0 < nativeRadius f x := sq_pos_of_pos (norm_pos_iff.mpr hfx)
  have heq := optimalErrorFactor_eq (contDiff_annularDensity σ δ)
    (fun t _ => annularDensity_pos σ hδ t)
    ((antitone_annularDensity hσ hδ.le).antitoneOn (Ici 0)) hε hr hR1
  have hm := congrArg (fun r => r * ‖u‖ ^ 2 * Real.exp (-φ₀ x)) heq
  unfold optimalErrorFactor at hm
  unfold nativeTwist nativeCorrection
  rw [show -(Real.log (nativeRadius f x) + φ₀ x +
    potential (annularDensity σ δ) (normalTime ε (nativeRadius f x))) =
      (-Real.log (nativeRadius f x) - potential (annularDensity σ δ)
        (normalTime ε (nativeRadius f x))) + (-φ₀ x) by ring, Real.exp_add]
  apply le_of_eq
  convert hm.symm using 1 <;> unfold nativeRadius <;> first | rfl | ring

variable [MeasurableSpace X] [BorelSpace X]

/-- Any SAME original actual finite-singular-error correction retains the
true fibre, by the proved actual physical critical-normal vanishing. -/
theorem fibre_agreement_of_finite_original_error (hL : IsSourceSmoothHermitianMetric L)
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := m + 1) μ) {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) ∞ f)
    (hsub : ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ℂ) f x))
    (hR : ∀ x, nativeRadius f x < 1) {φ₀ : X → ℝ} (hφ : ChartSmooth (n := m + 1) φ₀)
    {ε σ δ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ)
    {F S : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) L.Fiber F univ)
    (hS : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) L.Fiber S univ)
    (hfin : (∫⁻ x, ENNReal.ofReal (‖cutoffSection L f ε F x - S x‖ ^ 2 /
      (nativeTwist f ε σ δ x + nativeCorrection f ε σ δ x)) *
      multiplierWeight 1 (optimalNativeWeight f φ₀ ε σ δ x) ∂μ) ≠ ⊤) :
    ∀ x, f x = 0 → S x = F x := by
  let U : (x : X) → L.Fiber x := fun x => cutoffSection L f ε F x - S x
  let W : X → ℝ := fun x => annularDensity σ δ (normalTime ε (nativeRadius f x)) * Real.exp (-φ₀ x)
  have hU : IsSmoothSectionOn L U univ := SGPT.Trace.OTExt5.isSmoothSectionOn_sub L
    (isSmooth_cutoffSection L hf hε hF) (SGPT.Trace.OTExt5.isSmoothSectionOn_of_holomorphic L hS)
  have hW : Continuous W := ((contDiff_annularDensity σ δ).continuous.comp
    (continuous_of_chartSmooth' (chartSmooth_nativeTime hf hε))).mul
      (Real.continuous_exp.comp (continuous_of_chartSmooth' hφ).neg)
  have hWpos : ∀ x, 0 < W x := fun x =>
    mul_pos (annularDensity_pos σ hδ _) (Real.exp_pos _)
  have hcrit : (∫⁻ x, ENNReal.ofReal (‖U x‖ ^ 2 * W x / ‖f x‖ ^ 2) ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin (lintegral_mono fun x => ?_)
    simpa only [U, W, mul_assoc] using critical_error_energy_le_original L f φ₀ hε hσ hδ x (hR x) (U x)
  intro x hx
  have hzero := physical_section_eq_zero_of_finite_critical_normal_energy L hL hμ hf
    (hsub x) hx hU hW (hWpos x) hcrit
  have heq : cutoffSection L f ε F x = S x := sub_eq_zero.mp hzero
  exact heq.symm.trans (cutoffSection_eq_on_zero L hε F hx)

variable {N : ℕ} [CompactSpace X]
  (p : X → ComplexProjectiveSpace N) (i : Fin (N + 1)) (a v : ComplexModel N)

/-- Actual fixed-epsilon full-pencil extension. Only the ORIGINAL
preliminary F kernel energy is assumed finite, not any output estimate. -/
theorem exists_actual_pencil_epsilon_extension {ρ ε σ δ : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ)
    (hp : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel N) ∞ p)
    (hsm : ∀ t : parameterDisc ρ, IsSmoothHypersurfaceMember (m + 1) p (pencilParameter i a v t.val))
    (omega : KahlerBackground (m + 1) X) :
    letI := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
    haveI := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
    ∀ (B : HermitianHolomorphicLineBundle.{0, 0} (m + 1) (familyIncidence p i a v (parameterDisc ρ)))
      (μ : Measure (familyIncidence p i a v (parameterDisc ρ))),
      IsSmoothPositiveVolume (n := m + 1) μ → IsSourceSmoothHermitianMetric B →
      ∀ φ₀ : familyIncidence p i a v (parameterDisc ρ) → ℝ, ChartSmooth (n := m + 1) φ₀ →
      (∀ (c : ComplexChart (m + 1) (familyIncidence p i a v (parameterDisc ρ))) (e : AtlasFrame B)
        (d : ComplexModel (m + 1) → ℝ), IsChartDensity μ c d → ∀ z ∈ chartFrameDomain B c e,
        ∀ w : ComplexModel (m + 1), w ≠ 0 → 0 < leviForm (SGPT.Trace.TwistedL2.localWeight B c e d φ₀) z w) →
      ∀ F : (q : familyIncidence p i a v (parameterDisc ρ)) → B.Fiber q,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) B.Fiber F univ →
      (∫⁻ q, ENNReal.ofReal ((windowMass σ + δ) *
        normalKernel ε (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q) *
        ‖F q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ) ≠ ⊤ →
      ∃ S : (q : familyIncidence p i a v (parameterDisc ρ)) → B.Fiber q,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := m + 1) B.Fiber S univ ∧
      (∀ q, normalizedPencilNormal p i a v (parameterDisc ρ) ρ q = 0 → S q = F q) ∧
      (∫⁻ q, ENNReal.ofReal (gain (annularDensity σ δ)
        (normalTime ε (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q)) *
        ‖cutoffSection B (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) ε F q - S q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ) ≤
      (∫⁻ q, ENNReal.ofReal ((windowMass σ + δ) *
        normalKernel ε (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q) *
        ‖F q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ) := by
  let := familyChartedSpace p i a v (parameterDisc ρ) hp hsm
  have := isComplexManifold_family p i a v (parameterDisc ρ) hp hsm
  intro B μ hμ hB φ₀ hφ hbase F hF hIKernel
  obtain ⟨S, hShol, hRaw, hGain⟩ := exists_actual_pencil_sharp_correction p i a v hρ hε hσ hδ hp hsm
    omega B μ hμ hB φ₀ hφ hbase F hF
  have hf := contMDiff_normalizedPencilNormal p i a v (parameterDisc ρ) hp hsm ρ
  have hsub := surjective_mfderiv_normalizedPencilNormal p i a v (parameterDisc ρ) hp hsm hρ
  have hR := actual_pencil_normal_radius_lt_one p i a v hρ
  have hzero := measure_eq_zero_of_isLocallyAnalyticNull hμ (isLocallyAnalyticNull_native_zeroSet hf hsub)
  have hae : ∀ᵐ q ∂μ, normalizedPencilNormal p i a v (parameterDisc ρ) ρ q ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  have hData : (∫⁻ q, ENNReal.ofReal (curvatureDatum B
        (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) ε F q) *
        multiplierWeight 1 (optimalNativeWeight (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) φ₀ ε σ δ q) ∂μ) ≤
      ∫⁻ q, ENNReal.ofReal ((windowMass σ + δ) *
        normalKernel ε (nativeRadius (normalizedPencilNormal p i a v (parameterDisc ρ) ρ) q) *
        ‖F q‖ ^ 2 * Real.exp (-φ₀ q)) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with q hq
    exact actual_data_energy_comparison B _ φ₀ hε hσ hδ F hq (hR q)
  have hRawFinite := ne_top_of_le_ne_top hIKernel (hRaw.trans hData)
  refine ⟨S, hShol, ?_, hGain⟩
  exact fibre_agreement_of_finite_original_error B hB hμ hf hsub hR hφ hε hσ hδ hF hShol hRawFinite

end SGPT.Trace.BertiniCriticalFibreCorrection
