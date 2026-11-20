import SGPT.Trace.OptimalNativeNormalCorrection

/-!
# Strict actual normal curvature from original relative positivity

The original X pullback need not be strict in pure parameter directions.
The SAME actual rank-one normal Levi supplies the missing positivity.
Frozen strict-base stages remain unchanged.
Blueprint: work/sgpt-resume-20261114/bert-e2-relative-curvature/blueprint/bert-e2-relative-curvature.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalRelativeNormalCurvature
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OTExt2 SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass
open SGPT.Trace.OptimalNormalRegularization SGPT.Trace.OptimalTwistedExhaustion
open SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalDatum
open SGPT.Trace.OptimalNativeNormalBackground SGPT.Trace.OptimalNativeNormalEnergy
open SGPT.Trace.OptimalNativeNormalCorrection

/-- Exact original rank-one normal curvature, off its true zero fibre. -/
theorem leviForm_normalLog_eq_holo_derivative {n : ℕ} {f : ComplexModel n → ℂ}
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O)
    {z : ComplexModel n} (hz : z ∈ O) (hfz : f z ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (v : ComplexModel n) :
    leviForm (fun y => normalLog ε (normalRadius f y)) z v =
      ε / (ε + normalRadius f z) ^ 2 * ‖fderiv ℂ f z v‖ ^ 2 := by
  have hR := contDiffAt_normalRadius hO hf hz
  have hr : 0 < normalRadius f z := sq_pos_of_pos (norm_pos_iff.mpr hfz)
  have hlog := SGPT.Trace.OTExt5.leviForm_log_norm_sq_eq_zero
    (by filter_upwards [hO.mem_nhds hz] with y hy
        exact (hf y hy).differentiableAt (hO.mem_nhds hy)) hfz v
  change leviForm (fun y => Real.log (normalRadius f y)) z v = 0 at hlog
  have hcalc := leviForm_log_add (hR.of_le (WithTop.coe_le_coe.mpr le_top)) hr hε v
  rw [hlog, mul_zero, zero_add] at hcalc
  have hscalar := holDerivSq_original_scalar_radius
    ((hf z hz).differentiableAt (hO.mem_nhds hz)) v
  change holDerivSq (normalRadius f) z v = normalRadius f z * ‖fderiv ℂ f z v‖ ^ 2 at hscalar
  have hD := holDerivSq_eq_sq_mul_holDerivSq_log (hR.differentiableAt (by simp)) (add_pos hε hr) v
  rw [hscalar] at hD
  have hDval : holDerivSq (fun y => Real.log (ε + normalRadius f y)) z v =
      normalRadius f z * ‖fderiv ℂ f z v‖ ^ 2 / (ε + normalRadius f z) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2 (add_pos hε hr).ne')).mpr
    nlinarith [hD]
  rw [leviForm_normalLog (hR.of_le (WithTop.coe_le_coe.mpr le_top)) hε hr.le, hcalc, hDval]
  field_simp [hr.ne', (add_pos hε hr).ne']

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- Actual strict H needs only ORIGINAL semipositivity plus strictness on
ker of the SAME original normal derivative. No strict base parameter input. -/
theorem actual_native_twistedCurvature_pos_relative {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hL : IsSourceSmoothHermitianMetric L) {φ₀ : X → ℝ} (hφ : ChartSmooth (n := n) φ₀)
    (c : ComplexChart n X) (e : AtlasFrame L) {ρ : ComplexModel n → ℝ}
    {z : ComplexModel n} (hz : z ∈ chartFrameDomain L c e)
    (hρ : ContDiffAt ℝ ∞ ρ z) (hρ0 : 0 < ρ z)
    (hfz : f (c.val.symm z) ≠ 0) {ε σ δ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ) (hR1 : nativeRadius f (c.val.symm z) < 1)
    (v : ComplexModel n) (hbase0 : 0 ≤ leviForm (SGPT.Trace.TwistedL2.localWeight L c e ρ φ₀) z v)
    (hbaseKer : fderiv ℂ (fun y => f (c.val.symm y)) z v = 0 →
      0 < leviForm (SGPT.Trace.TwistedL2.localWeight L c e ρ φ₀) z v) :
    0 < twistedCurvature (fun y => nativeTwist f ε σ δ (c.val.symm y))
      (fun y => nativeCorrection f ε σ δ (c.val.symm y))
      (SGPT.Trace.TwistedL2.localWeight L c e ρ fun x => (optimalNativeWeight f φ₀ ε σ δ x).toReal) z v := by
  rw [actual_native_twistedCurvature L hf hL hφ c e hz hρ hρ0 hfz hε hσ hδ hR1 v]
  have ha : 0 < nativeTwist f ε σ δ (c.val.symm z) :=
    twist_pos (contDiff_annularDensity σ δ).continuous
      (fun t _ => annularDensity_pos σ hδ t) (normalTime_pos hε (sq_nonneg _) hR1)
  by_cases hdf : fderiv ℂ (fun y => f (c.val.symm y)) z v = 0
  · exact add_pos_of_pos_of_nonneg (mul_pos ha (hbaseKer hdf))
      (leviForm_actual_normalLog_nonneg c.val.open_target
        (differentiableOn_native_normal_chart hf c) hz.1 hfz hε v)
  · have hV : 0 < leviForm (fun y => normalLog ε (nativeRadius f (c.val.symm y))) z v := by
      change 0 < leviForm (fun y => normalLog ε (normalRadius (fun w => f (c.val.symm w)) y)) z v
      rw [leviForm_normalLog_eq_holo_derivative c.val.open_target
        (differentiableOn_native_normal_chart hf c) hz.1 hfz hε v]
      exact mul_pos (div_pos hε (pow_pos (add_pos_of_pos_of_nonneg hε (sq_nonneg _)) 2))
        (sq_pos_of_pos (norm_pos_iff.mpr hdf))
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le hbase0) hV

theorem exists_actual_relative_sharp_weighted_correction [MeasurableSpace X] [BorelSpace X]
    (omega : KahlerBackground n X) (Ψ : X → ℝ) (hΨ : ChartSmooth (n := n) Ψ)
    (hΨpsh : ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      ∀ v : ComplexModel n, 0 ≤ leviForm (fun y => Ψ (c.val.symm y)) z v)
    (hΨc : ∀ t : ℝ, IsCompact {x | Ψ x ≤ t})
    (μ : Measure X) (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hL : IsSourceSmoothHermitianMetric L) {φ₀ : X → ℝ} (hφ : ChartSmooth (n := n) φ₀)
    {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hsub : ∀ x, Function.Surjective (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) f x))
    (hR : ∀ x, nativeRadius f x < 1) {ε σ δ ρ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hdf : ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target →
      ∀ v : ComplexModel n, ‖fderiv ℂ (fun y => f (c.val.symm y)) z v‖ ^ 2 ≤
        kahlerQuad omega c z v / ρ ^ 2)
    (hbase0 : ∀ (c : ComplexChart n X) (e : AtlasFrame L) (d : ComplexModel n → ℝ),
      IsChartDensity μ c d → ∀ z ∈ chartFrameDomain L c e, ∀ v : ComplexModel n,
        0 ≤ leviForm (SGPT.Trace.TwistedL2.localWeight L c e d φ₀) z v)
    (hbaseKer : ∀ (c : ComplexChart n X) (e : AtlasFrame L) (d : ComplexModel n → ℝ),
      IsChartDensity μ c d → ∀ z ∈ chartFrameDomain L c e, ∀ v : ComplexModel n, v ≠ 0 →
        fderiv ℂ (fun y => f (c.val.symm y)) z v = 0 →
        0 < leviForm (SGPT.Trace.TwistedL2.localWeight L c e d φ₀) z v)
    {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ) :
    ∃ S : (x : X) → L.Fiber x,
      SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber S univ ∧
      (∫⁻ x, ENNReal.ofReal (‖cutoffSection L f ε F x - S x‖ ^ 2 /
        (nativeTwist f ε σ δ x + nativeCorrection f ε σ δ x)) *
        multiplierWeight 1 (optimalNativeWeight f φ₀ ε σ δ x) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (curvatureDatum L f ε F x) *
        multiplierWeight 1 (optimalNativeWeight f φ₀ ε σ δ x) ∂μ) ∧
      (∫⁻ x, ENNReal.ofReal (gain (annularDensity σ δ) (normalTime ε (nativeRadius f x)) *
        ‖cutoffSection L f ε F x - S x‖ ^ 2 * Real.exp (-φ₀ x)) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal ((windowMass σ + δ) * normalKernel ε (nativeRadius f x) *
        ‖F x‖ ^ 2 * Real.exp (-φ₀ x)) ∂μ) := by
  obtain ⟨ha, hb, ha0, hb0, M, hM⟩ := actual_native_normal_twist_data hf hε hσ hδ hR
  have hψ : IsAdmissibleSingularWeight (n := n) (optimalNativeWeight f φ₀ ε σ δ) :=
    isAdmissible_actual_native_annular_weight hf hsub hφ hε hδ hR
  have hk : ChartSmooth (n := n) (fun x => φ₀ x +
      potential (annularDensity σ δ) (normalTime ε (nativeRadius f x))) := fun c =>
    (hφ c).add (chartSmooth_nativeOptimalPotential hf hε hδ hR c)
  have hfnot : ∀ x, optimalNativeWeight f φ₀ ε σ δ x ≠ ⊥ → f x ≠ 0 := by
    intro x hx hzero
    exact hx ((normalWeight_eq_bot_iff f _ x).mpr hzero)
  obtain ⟨S, hShol, hS⟩ := global_correction_of_locally_positive_twists omega Ψ hΨ hΨpsh hΨc μ hμ
    L hL (optimalNativeWeight f φ₀ ε σ δ) hψ (nativeTwist f ε σ δ) (nativeCorrection f ε σ δ)
    ha hb ha0 hb0 ⟨M, hM⟩
    (fun c e d hd z hz hfinite v hv => actual_native_twistedCurvature_pos_relative L hf hL hφ c e hz
      (hd.1.contDiffAt (c.val.open_target.mem_nhds hz.1)) (hd.2.1 z hz.1)
      (hfnot _ hfinite) hε hσ hδ (hR _) v (hbase0 c e d hd z hz v) (hbaseKer c e d hd z hz v hv))
    (cutoffSection L f ε F) (isSmooth_cutoffSection L hf hε hF)
    (curvatureDatum L f ε F) (backgroundDatum L f ε ρ F)
    (fun c e d hd z hz hfinite v => actual_physical_curvature_datum L hf hL hφ hF c e hz
      (hd.1.contDiffAt (c.val.open_target.mem_nhds hz.1)) (hd.2.1 z hz.1)
      (hfnot _ hfinite) hε hσ hδ (hR _) v (hbase0 c e d hd z hz v))
    (fun c e z hz _ v => physical_background_datum_of_original_normal_bound L hf hF omega c e hz
      hε hρ v (hdf c z hz.1 v))
    (fun K hK => finite_background_energy_on_compact L hμ hf hL hF hk hε hρ hK)
  have hzero : μ {x | f x = 0} = 0 :=
    measure_eq_zero_of_isLocallyAnalyticNull hμ (isLocallyAnalyticNull_native_zeroSet hf hsub)
  have hae : ∀ᵐ x ∂μ, f x ≠ 0 := measure_eq_zero_iff_ae_notMem.mp hzero
  refine ⟨S, hShol, hS, ?_⟩
  have hleft : (∫⁻ x, ENNReal.ofReal (gain (annularDensity σ δ) (normalTime ε (nativeRadius f x)) *
      ‖cutoffSection L f ε F x - S x‖ ^ 2 * Real.exp (-φ₀ x)) ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (‖cutoffSection L f ε F x - S x‖ ^ 2 /
        (nativeTwist f ε σ δ x + nativeCorrection f ε σ δ x)) *
        multiplierWeight 1 (optimalNativeWeight f φ₀ ε σ δ x) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    exact actual_correction_energy_comparison L f φ₀ hε hσ hδ hx (hR x) _
  refine hleft.trans (hS.trans ?_)
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with x hx
  exact actual_data_energy_comparison L f φ₀ hε hσ hδ F hx (hR x)

end SGPT.Trace.OptimalRelativeNormalCurvature
