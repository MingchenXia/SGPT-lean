import SGPT.Trace.OptimalGainCompactBounds
import SGPT.Trace.OptimalPhysicalSectionMontel
import SGPT.Trace.OptimalNativeNormalCorrection

/-!
# Actual epsilon limit for the same original physical normal extension

All local bounds, subsequence, genuine original section gluing and Fatou
estimate are produced. Only ORIGINAL preliminary kernel normalization is
still an input, rather than a resulting extension or Hodge certificate.
Blueprint: work/sgpt-resume-20261114/bert-e2-epsilon-limit/blueprint/bert-e2-epsilon-limit.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalNormalEpsilonLimit
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass
open SGPT.Trace.OptimalNormalRegularization SGPT.Trace.OptimalNativeNormalWeight
open SGPT.Trace.OptimalNativeNormalDatum SGPT.Trace.OptimalGainCompactBounds
open SGPT.Trace.OptimalPhysicalSectionMontel

theorem tendsto_actual_normalTime {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun j => normalTime (ε j) r) atTop (𝓝 (-Real.log r)) := by
  have h1 := ((hε.add_const r).log (by simpa using hr.ne'))
  have h2 := ((tendsto_const_nhds.add hε).log (by norm_num : (1 : ℝ) + 0 ≠ 0))
  simpa only [normalTime, normalLog, zero_add, add_zero, Real.log_one, sub_zero] using (h1.sub h2).neg

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L : HermitianHolomorphicLineBundle.{0, 0} n X)

theorem tendsto_actual_cutoffSection {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (f : X → ℂ) (F : (x : X) → L.Fiber x) {x : X} (hx : f x ≠ 0) :
    Tendsto (fun j => cutoffSection L f (ε j) F x) atTop (𝓝 (0 : L.Fiber x)) := by
  have hr : 0 < nativeRadius f x := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hq : Tendsto (fun j => normalCutoff (ε j) (nativeRadius f x)) atTop (𝓝 0) := by
    convert hε.div (hε.add_const (nativeRadius f x)) (by simpa using hr.ne') using 1 <;>
      first | rfl | simp only [zero_add, zero_div]
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hq
  simpa only [cutoffSection, Function.comp_apply, Complex.ofReal_zero, zero_smul] using hc.smul_const (F x)

variable [MeasurableSpace X] [BorelSpace X]

def actualPreliminaryKernelEnergy (μ : Measure X) (f : X → ℂ) (φ₀ : X → ℝ)
    (ε σ δ : ℝ) (F : (x : X) → L.Fiber x) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((windowMass σ + δ) * normalKernel ε (nativeRadius f x) *
    ‖F x‖ ^ 2 * Real.exp (-φ₀ x)) ∂μ

theorem exists_actual_epsilon_gain_limit {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {φ₀ : X → ℝ} (hφ : Continuous φ₀)
    {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hsub : ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f x))
    {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ)
    {σ δ : ℝ} (hδ : 0 < δ) {ε : ℕ → ℝ} (hεpos : ∀ j, 0 < ε j)
    (hε : Tendsto ε atTop (𝓝 0))
    (T : ℕ → (x : X) → L.Fiber x)
    (hT : ∀ j, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber (T j) univ)
    (htrace : ∀ j x, f x = 0 → T j x = F x)
    (hgain : ∀ j, (∫⁻ x, ENNReal.ofReal (gain (annularDensity σ δ)
      (normalTime (ε j) (nativeRadius f x)) * ‖cutoffSection L f (ε j) F x - T j x‖ ^ 2 *
      Real.exp (-φ₀ x)) ∂μ) ≤ actualPreliminaryKernelEnergy L μ f φ₀ (ε j) σ δ F)
    {I C : ℝ≥0∞} (hI : I < ⊤)
    (hbound : ∀ j, actualPreliminaryKernelEnergy L μ f φ₀ (ε j) σ δ F ≤ I)
    (hlim : Tendsto (fun j => actualPreliminaryKernelEnergy L μ f φ₀ (ε j) σ δ F) atTop (𝓝 C)) :
    ∃ S : (x : X) → L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
      (∀ x, f x = 0 → S x = F x) ∧
      (∫⁻ x, ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (nativeRadius f x)) *
        ‖S x‖ ^ 2 * Real.exp (-φ₀ x)) ∂μ) ≤ C := by
  have hL2 : ∀ K : Set X, IsCompact K → ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ j, (∫⁻ x in K, ENNReal.ofReal (‖T j x‖ ^ 2) ∂μ) ≤ B := by
    intro K hK
    obtain ⟨B, hB, hcontrol⟩ := exists_uniform_compact_sq_bound_of_actual_gain L hμ hφ hF hδ σ hK hI
    exact ⟨B, hB, fun j => hcontrol (ε j) (hεpos j) (T j) ((hgain j).trans (hbound j))⟩
  obtain ⟨k, S, hk, hS, hnorm, hcentral⟩ := exists_original_global_holomorphic_limit hμ L T hT hL2
    {x | f x = 0} F htrace
  let E : ℕ → X → ℝ≥0∞ := fun j x => ENNReal.ofReal (gain (annularDensity σ δ)
    (normalTime (ε (k j)) (nativeRadius f x)) * ‖cutoffSection L f (ε (k j)) F x - T (k j) x‖ ^ 2 *
    Real.exp (-φ₀ x))
  have hcontGain : Continuous (gain (annularDensity σ δ)) :=
    Real.continuous_exp.mul (contDiff_annularDensity σ δ).continuous
  have hmeas : ∀ j, AEMeasurable (E j) μ := by
    intro j
    have hn : Continuous (fun x => ‖cutoffSection L f (ε (k j)) F x - T (k j) x‖) :=
      continuousOn_univ.mp (continuousOn_norm_sub_of_holomorphic L
        (isSmooth_cutoffSection L hf (hεpos (k j)) hF) isOpen_univ (hT (k j)))
    have ht : Continuous (fun x => normalTime (ε (k j)) (nativeRadius f x)) :=
      continuous_of_chartSmooth' (chartSmooth_nativeTime hf (hεpos (k j)))
    exact (ENNReal.continuous_ofReal.comp
      (((hcontGain.comp ht).mul (hn.pow 2)).mul (Real.continuous_exp.comp hφ.neg))).measurable.aemeasurable
  have hae : ∀ᵐ x ∂μ, f x ≠ 0 := measure_eq_zero_iff_ae_notMem.mp
    (measure_eq_zero_of_isLocallyAnalyticNull hμ (isLocallyAnalyticNull_native_zeroSet hf hsub))
  have heps : Tendsto (fun j => ε (k j)) atTop (𝓝 0) := hε.comp hk.tendsto_atTop
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun j => E j x) atTop
      (𝓝 (ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (nativeRadius f x)) *
        ‖S x‖ ^ 2 * Real.exp (-φ₀ x)))) := by
    filter_upwards [hae] with x hx
    have hzero : Tendsto (fun j => ‖T (k j) x - S x‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [norm_sub_rev, sub_self, norm_zero] using hnorm S x
    have hvec : Tendsto (fun j => T (k j) x) atTop (𝓝 (S x)) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hzero
    have hcut := tendsto_actual_cutoffSection L heps f F hx
    have hdist : Tendsto (fun j => ‖cutoffSection L f (ε (k j)) F x - T (k j) x‖ ^ 2) atTop
        (𝓝 (‖S x‖ ^ 2)) := by
      simpa only [zero_sub, norm_neg] using (hcut.sub hvec).norm.pow 2
    have htime := tendsto_actual_normalTime heps (sq_pos_of_pos (norm_pos_iff.mpr hx))
    exact ENNReal.tendsto_ofReal (((hcontGain.continuousAt.tendsto.comp htime).mul hdist).mul_const _)
  refine ⟨S, hS, hcentral, ?_⟩
  calc (∫⁻ x, ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (nativeRadius f x)) *
          ‖S x‖ ^ 2 * Real.exp (-φ₀ x)) ∂μ)
      ≤ ∫⁻ x, liminf (fun j => E j x) atTop ∂μ :=
        lintegral_mono_ae (hconv.mono fun x hx => hx.liminf_eq.ge)
    _ ≤ liminf (fun j => ∫⁻ x, E j x ∂μ) atTop := lintegral_liminf_le' hmeas
    _ ≤ liminf (fun j => actualPreliminaryKernelEnergy L μ f φ₀ (ε (k j)) σ δ F) atTop :=
      liminf_le_liminf (Filter.Eventually.of_forall fun j => hgain (k j))
    _ = C := (hlim.comp hk.tendsto_atTop).liminf_eq

end SGPT.Trace.OptimalNormalEpsilonLimit
