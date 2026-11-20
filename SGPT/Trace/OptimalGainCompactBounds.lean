import SGPT.Trace.OptimalNativeNormalDatum
import SGPT.Trace.TwistedL2SingularLocalL2

/-!
# Uniform compact physical L2 bounds from the actual annular gain

Positive finite slack controls actual error norms uniformly in epsilon.
No local boundedness or normal-family outcome is supplied.
Blueprint: work/sgpt-resume-20261114/bert-e2-gain-compact/blueprint/bert-e2-gain-compact.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalGainCompactBounds
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalNormalRegularization
open SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalDatum

theorem slack_le_actual_annular_gain (σ δ t : ℝ) : δ ≤ gain (annularDensity σ δ) t := by
  rw [gain_annularDensity]
  exact le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (annularWindow_nonneg σ t))

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L : HermitianHolomorphicLineBundle.{0, 0} n X)

theorem norm_actual_cutoff_le (f : X → ℂ) {ε : ℝ} (hε : 0 < ε)
    (F : (x : X) → L.Fiber x) (x : X) : ‖cutoffSection L f ε F x‖ ≤ ‖F x‖ := by
  have hden : 0 < ε + nativeRadius f x := add_pos_of_pos_of_nonneg hε (sq_nonneg _)
  have hq : 0 ≤ normalCutoff ε (nativeRadius f x) := div_nonneg hε.le hden.le
  have hq1 : normalCutoff ε (nativeRadius f x) ≤ 1 :=
    (div_le_one hden).mpr (le_add_of_nonneg_right (sq_nonneg _))
  rw [cutoffSection, norm_smul, Complex.norm_real, Real.norm_of_nonneg hq]
  exact mul_le_of_le_one_left (norm_nonneg _) hq1

variable [MeasurableSpace X] [BorelSpace X]

theorem exists_uniform_compact_sq_bound_of_actual_gain
    {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    {φ₀ : X → ℝ} (hφ : Continuous φ₀) {f : X → ℂ}
    {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ)
    {δ : ℝ} (hδ : 0 < δ) (σ : ℝ) {K : Set X} (hK : IsCompact K)
    {I : ℝ≥0∞} (hI : I < ⊤) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∀ S : (x : X) → L.Fiber x,
      (∫⁻ x, ENNReal.ofReal (gain (annularDensity σ δ) (normalTime ε (nativeRadius f x)) *
        ‖cutoffSection L f ε F x - S x‖ ^ 2 * Real.exp (-φ₀ x)) ∂μ) ≤ I →
      (∫⁻ x in K, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ) ≤ B := by
  have hloc : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_of_isSmoothPositiveVolume hμ
  have hKμ : μ K < ⊤ := hK.measure_lt_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_norm_of_holomorphic L hF).mono (subset_univ K))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hφ.continuousOn
  let A : ℝ := 2 * Real.exp M / δ
  let B : ℝ≥0∞ := ENNReal.ofReal (2 * C ^ 2) * μ K + ENNReal.ofReal A * I
  refine ⟨B, ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKμ,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI⟩, ?_⟩
  intro ε hε S hS
  let E : X → ℝ := fun x => gain (annularDensity σ δ) (normalTime ε (nativeRadius f x)) *
    ‖cutoffSection L f ε F x - S x‖ ^ 2 * Real.exp (-φ₀ x)
  have hpt : ∀ x ∈ K, ENNReal.ofReal (‖S x‖ ^ 2) ≤
      ENNReal.ofReal (2 * C ^ 2) + ENNReal.ofReal A * ENNReal.ofReal (E x) := by
    intro x hx
    have hg := slack_le_actual_annular_gain σ δ (normalTime ε (nativeRadius f x))
    have hE : 0 ≤ E x := mul_nonneg (mul_nonneg (hδ.le.trans hg) (sq_nonneg _)) (Real.exp_pos _).le
    have hA : 0 ≤ A := by dsimp [A]; positivity
    rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_add (by positivity) (mul_nonneg hA hE)]
    apply ENNReal.ofReal_le_ofReal
    have hFbound : ‖F x‖ ≤ C := (le_abs_self _).trans (hC x hx)
    have hGbound : ‖cutoffSection L f ε F x‖ ≤ C := (norm_actual_cutoff_le L f hε F x).trans hFbound
    have hφbound : φ₀ x ≤ M := (le_abs_self _).trans (hM x hx)
    have hcancel : Real.exp (φ₀ x) * Real.exp (-φ₀ x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hid : Real.exp (φ₀ x) * E x = gain (annularDensity σ δ) (normalTime ε (nativeRadius f x)) *
        ‖cutoffSection L f ε F x - S x‖ ^ 2 := by
      dsimp [E]
      calc _ = (Real.exp (φ₀ x) * Real.exp (-φ₀ x)) *
          (gain (annularDensity σ δ) (normalTime ε (nativeRadius f x)) *
            ‖cutoffSection L f ε F x - S x‖ ^ 2) := by ring
        _ = _ := by rw [hcancel, one_mul]
    have herr0 : δ * ‖cutoffSection L f ε F x - S x‖ ^ 2 ≤ Real.exp M * E x := by
      calc _ ≤ gain (annularDensity σ δ) (normalTime ε (nativeRadius f x)) *
          ‖cutoffSection L f ε F x - S x‖ ^ 2 := mul_le_mul_of_nonneg_right hg (sq_nonneg _)
        _ = Real.exp (φ₀ x) * E x := hid.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hφbound) hE
    have herr : ‖cutoffSection L f ε F x - S x‖ ^ 2 ≤ Real.exp M / δ * E x := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using herr0)
    have hnorm : ‖S x‖ ≤ ‖cutoffSection L f ε F x‖ + ‖cutoffSection L f ε F x - S x‖ := by
      calc ‖S x‖ = ‖cutoffSection L f ε F x - (cutoffSection L f ε F x - S x)‖ := by rw [sub_sub_cancel]
        _ ≤ _ := norm_sub_le _ _
    have hG2 := pow_le_pow_left₀ (norm_nonneg _) hGbound 2
    have hsq : ‖S x‖ ^ 2 ≤ 2 * ‖cutoffSection L f ε F x‖ ^ 2 +
        2 * ‖cutoffSection L f ε F x - S x‖ ^ 2 := by
      nlinarith [norm_nonneg (S x), norm_nonneg (cutoffSection L f ε F x),
        norm_nonneg (cutoffSection L f ε F x - S x),
        sq_nonneg (‖cutoffSection L f ε F x‖ - ‖cutoffSection L f ε F x - S x‖)]
    calc _ ≤ 2 * ‖cutoffSection L f ε F x‖ ^ 2 + 2 * ‖cutoffSection L f ε F x - S x‖ ^ 2 := hsq
      _ ≤ 2 * C ^ 2 + 2 * (Real.exp M / δ * E x) := by gcongr
      _ = 2 * C ^ 2 + A * E x := by dsimp [A]; ring
  calc (∫⁻ x in K, ENNReal.ofReal (‖S x‖ ^ 2) ∂μ)
      ≤ ∫⁻ x in K, ENNReal.ofReal (2 * C ^ 2) + ENNReal.ofReal A * ENNReal.ofReal (E x) ∂μ :=
        setLIntegral_mono' hK.isClosed.measurableSet hpt
    _ = ENNReal.ofReal (2 * C ^ 2) * μ K + ENNReal.ofReal A *
        ∫⁻ x in K, ENNReal.ofReal (E x) ∂μ := by
      rw [lintegral_add_left measurable_const, setLIntegral_const,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ B := by
      dsimp [B]
      gcongr
      exact (lintegral_mono_set (subset_univ K)).trans (by
        simpa only [Measure.restrict_univ, E] using hS)

end SGPT.Trace.OptimalGainCompactBounds
