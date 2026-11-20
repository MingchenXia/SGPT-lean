import SGPT.Trace.OptimalGainCompactBounds
import SGPT.Trace.OptimalPhysicalSectionMontel

/-!
# Actual singular-weight limit in the same original physical bundle

Original EReal poles and 0*infinity are retained. Actual local bounds,
physical Montel and sharp singular Fatou limit are produced; a source
geometric curvature-preserving approximation producer is still separate.
Blueprint: work/sgpt-resume-20261114/bert-e2-singular-limit/blueprint/bert-e2-singular-limit.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalSingularWeightLimit
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalNativeNormalWeight
open SGPT.Trace.OptimalGainCompactBounds SGPT.Trace.OptimalPhysicalSectionMontel

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X]
  (L : HermitianHolomorphicLineBundle.{0, 0} n X)

theorem uniform_compact_sq_bound_of_original_upper_weight
    (μ : Measure X) {G φbar : X → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hG : ∀ x, δ ≤ G x) (hbar : Continuous φbar)
    (φj : ℕ → X → ℝ) (hupper : ∀ j x, φj j x ≤ φbar x)
    (T : ℕ → (x : X) → L.Fiber x) {I : ℝ≥0∞} (hI : I < ⊤)
    (hbound : ∀ j, (∫⁻ x, ENNReal.ofReal (G x * ‖T j x‖ ^ 2) *
      multiplierWeight 1 (φj j x : EReal) ∂μ) ≤ I)
    {K : Set X} (hK : IsCompact K) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ j, (∫⁻ x in K, ENNReal.ofReal (‖T j x‖ ^ 2) ∂μ) ≤ B := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hbar.continuousOn
  let A : ℝ := Real.exp M / δ
  refine ⟨ENNReal.ofReal A * I, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI, ?_⟩
  intro j
  have hpt : ∀ x ∈ K, ENNReal.ofReal (‖T j x‖ ^ 2) ≤ ENNReal.ofReal A *
      (ENNReal.ofReal (G x * ‖T j x‖ ^ 2) * multiplierWeight 1 (φj j x : EReal)) := by
    intro x hx
    have hφ : φj j x ≤ M := (hupper j x).trans ((le_abs_self _).trans (hM x hx))
    have hG0 : 0 ≤ G x := hδ.le.trans (hG x)
    have hE0 : 0 ≤ G x * ‖T j x‖ ^ 2 * Real.exp (-φj j x) := by positivity
    simp only [multiplierWeight_coe, one_mul]
    rw [← ENNReal.ofReal_mul (mul_nonneg hG0 (sq_nonneg _)),
      ← ENNReal.ofReal_mul (by dsimp [A]; positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hid : Real.exp (φj j x) * (G x * ‖T j x‖ ^ 2 * Real.exp (-φj j x)) =
        G x * ‖T j x‖ ^ 2 := by
      calc _ = (Real.exp (φj j x) * Real.exp (-φj j x)) * (G x * ‖T j x‖ ^ 2) := by ring
        _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    have he : δ * ‖T j x‖ ^ 2 ≤ Real.exp M *
        (G x * ‖T j x‖ ^ 2 * Real.exp (-φj j x)) := by
      calc _ ≤ G x * ‖T j x‖ ^ 2 := mul_le_mul_of_nonneg_right (hG x) (sq_nonneg _)
        _ = _ := hid.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hφ) hE0
    dsimp [A]
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using he)
  calc (∫⁻ x in K, ENNReal.ofReal (‖T j x‖ ^ 2) ∂μ)
      ≤ ∫⁻ x in K, ENNReal.ofReal A * (ENNReal.ofReal (G x * ‖T j x‖ ^ 2) *
          multiplierWeight 1 (φj j x : EReal)) ∂μ := setLIntegral_mono' hK.isClosed.measurableSet hpt
    _ = ENNReal.ofReal A * ∫⁻ x in K, ENNReal.ofReal (G x * ‖T j x‖ ^ 2) *
          multiplierWeight 1 (φj j x : EReal) ∂μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((lintegral_mono_set (subset_univ K)).trans (by simpa only [Measure.restrict_univ] using hbound j)) zero_le

theorem exists_original_singular_weight_physical_limit {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {G φbar : X → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hG0 : ∀ x, δ ≤ G x) (hG : Measurable G) (hbar : Continuous φbar)
    (φj : ℕ → X → ℝ) (hφj : ∀ j, Measurable (φj j)) (hupper : ∀ j x, φj j x ≤ φbar x)
    (φ : X → EReal) (hφlim : ∀ x, Tendsto (fun j => (φj j x : EReal)) atTop (𝓝 (φ x)))
    (T : ℕ → (x : X) → L.Fiber x)
    (hT : ∀ j, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber (T j) univ)
    (A : Set X) (F : (x : X) → L.Fiber x) (htrace : ∀ j x, x ∈ A → T j x = F x)
    {I : ℝ≥0∞} (hI : I < ⊤)
    (hbound : ∀ j, (∫⁻ x, ENNReal.ofReal (G x * ‖T j x‖ ^ 2) *
      multiplierWeight 1 (φj j x : EReal) ∂μ) ≤ I) :
    ∃ S : (x : X) → L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
      (∀ x ∈ A, S x = F x) ∧
      (∫⁻ x, ENNReal.ofReal (G x * ‖S x‖ ^ 2) * multiplierWeight 1 (φ x) ∂μ) ≤ I := by
  have hL2 := fun K hK => uniform_compact_sq_bound_of_original_upper_weight L μ hδ hG0 hbar
    φj hupper T hI hbound (K := K) hK
  obtain ⟨k, S, hk, hS, hnorm, hcentral⟩ := exists_original_global_holomorphic_limit hμ L T hT hL2 A F htrace
  have hmeas : ∀ j, Measurable (fun x => ENNReal.ofReal (G x * ‖T (k j) x‖ ^ 2) *
      multiplierWeight 1 (φj (k j) x : EReal)) := by
    intro j
    have hN : Continuous (fun x => ‖T (k j) x‖) := continuousOn_univ.mp (continuousOn_norm_of_holomorphic L (hT (k j)))
    exact (ENNReal.measurable_ofReal.comp (hG.mul (hN.pow 2).measurable)).mul
      ((continuous_multiplierWeight_coe 1).measurable.comp (hφj (k j)))
  have hliminf : ∀ x, ENNReal.ofReal (G x * ‖S x‖ ^ 2) * multiplierWeight 1 (φ x) ≤
      liminf (fun j => ENNReal.ofReal (G x * ‖T (k j) x‖ ^ 2) *
        multiplierWeight 1 (φj (k j) x : EReal)) atTop := by
    intro x
    by_cases hzero : ‖S x‖ = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), mul_zero, ENNReal.ofReal_zero, zero_mul]
      exact zero_le
    have hN : Tendsto (fun j => ‖T (k j) x‖ ^ 2) atTop (𝓝 (‖S x‖ ^ 2)) := by
      simpa only [zero_sub, norm_neg] using (hnorm (fun x => (0 : L.Fiber x)) x).pow 2
    have hn := ENNReal.tendsto_ofReal (hN.const_mul (G x))
    have hw := ((continuous_multiplierWeight one_pos).tendsto (φ x)).comp ((hφlim x).comp hk.tendsto_atTop)
    have hpos : ENNReal.ofReal (G x * ‖S x‖ ^ 2) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (mul_pos (hδ.trans_le (hG0 x)) (sq_pos_of_ne_zero hzero))).ne'
    exact (ENNReal.Tendsto.mul hn (Or.inl hpos) hw (Or.inr ENNReal.ofReal_ne_top)).liminf_eq.ge
  refine ⟨S, hS, hcentral, ?_⟩
  calc (∫⁻ x, ENNReal.ofReal (G x * ‖S x‖ ^ 2) * multiplierWeight 1 (φ x) ∂μ)
      ≤ ∫⁻ x, liminf (fun j => ENNReal.ofReal (G x * ‖T (k j) x‖ ^ 2) *
          multiplierWeight 1 (φj (k j) x : EReal)) atTop ∂μ := lintegral_mono hliminf
    _ ≤ liminf (fun j => ∫⁻ x, ENNReal.ofReal (G x * ‖T (k j) x‖ ^ 2) *
          multiplierWeight 1 (φj (k j) x : EReal) ∂μ) atTop := lintegral_liminf_le hmeas
    _ ≤ I := liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun j => hbound (k j))

theorem exists_actual_normal_gain_limit_of_real_weight_approximation {μ : Measure X}
    (hμ : IsSmoothPositiveVolume (n := n) μ) {f : X → ℂ} (hf : Continuous f)
    {σ δ : ℝ} (hδ : 0 < δ) (φj : ℕ → X → ℝ) (hφj : ∀ j, ChartSmooth (n := n) (φj j))
    (hmono : ∀ x, Antitone (fun j => φj j x))
    (φ : X → EReal) (hφlim : ∀ x, Tendsto (fun j => (φj j x : EReal)) atTop (𝓝 (φ x)))
    (T : ℕ → (x : X) → L.Fiber x)
    (hT : ∀ j, SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber (T j) univ)
    (F : (x : X) → L.Fiber x) (htrace : ∀ j x, f x = 0 → T j x = F x)
    {I : ℝ≥0∞} (hI : I < ⊤)
    (hbound : ∀ j, (∫⁻ x, ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (nativeRadius f x)) *
      ‖T j x‖ ^ 2) * multiplierWeight 1 (φj j x : EReal) ∂μ) ≤ I) :
    ∃ S : (x : X) → L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
      (∀ x, f x = 0 → S x = F x) ∧
      (∫⁻ x, ENNReal.ofReal (gain (annularDensity σ δ) (-Real.log (nativeRadius f x)) *
        ‖S x‖ ^ 2) * multiplierWeight 1 (φ x) ∂μ) ≤ I := by
  have hg : Continuous (gain (annularDensity σ δ)) :=
    Real.continuous_exp.mul (contDiff_annularDensity σ δ).continuous
  have hgm : Measurable (fun x => gain (annularDensity σ δ) (-Real.log (nativeRadius f x))) :=
    hg.measurable.comp (Real.measurable_log.comp (hf.norm.pow 2).measurable).neg
  exact exists_original_singular_weight_physical_limit L hμ hδ
    (fun x => slack_le_actual_annular_gain σ δ _) hgm (continuous_of_chartSmooth' (hφj 0))
    φj (fun j => (continuous_of_chartSmooth' (hφj j)).measurable) (fun j x => hmono x (Nat.zero_le j))
    φ hφlim T hT {x | f x = 0} F htrace hI hbound

end SGPT.Trace.OptimalSingularWeightLimit
