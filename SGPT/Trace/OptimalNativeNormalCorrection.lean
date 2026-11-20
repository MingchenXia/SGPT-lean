import SGPT.Trace.OptimalNativeNormalEnergy

/-!
# Actual native sharp weighted correction from original geometric inputs

Analytic engine only: its raw original exhaustion/normal metric/bundle-curvature
inputs have separate actual-pencil/tube producers, whose native open-bundle
instantiation is still explicit work. No resulting analytic datum is assumed.
Blueprint: work/sgpt-resume-20261114/bert-e2-native-correction/blueprint/bert-e2-native-correction.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalNativeNormalCorrection
open Set Filter MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass
open SGPT.Trace.OptimalNormalRegularization SGPT.Trace.OptimalTwistedExhaustion
open SGPT.Trace.OptimalNativeNormalWeight SGPT.Trace.OptimalNativeNormalDatum
open SGPT.Trace.OptimalNativeNormalBackground SGPT.Trace.OptimalNativeNormalEnergy

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  (L : HermitianHolomorphicLineBundle.{0, 0} n X)

/-- The actual correction multiplier dominates the SAME physical gain energy. -/
theorem actual_correction_energy_comparison (f : X → ℂ) (φ₀ : X → ℝ)
    {ε σ δ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ)
    {x : X} (hfx : f x ≠ 0) (hR1 : nativeRadius f x < 1) (u : L.Fiber x) :
    ENNReal.ofReal (gain (annularDensity σ δ) (normalTime ε (nativeRadius f x)) *
      ‖u‖ ^ 2 * Real.exp (-φ₀ x)) ≤
    ENNReal.ofReal (‖u‖ ^ 2 / (nativeTwist f ε σ δ x + nativeCorrection f ε σ δ x)) *
      multiplierWeight 1 (optimalNativeWeight f φ₀ ε σ δ x) := by
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
  have hcomp := gain_le_optimalErrorFactor (contDiff_annularDensity σ δ)
    (fun t _ => annularDensity_pos σ hδ t)
    ((antitone_annularDensity hσ hδ.le).antitoneOn (Ici 0)) hε hr hR1
  have hm := mul_le_mul_of_nonneg_right hcomp (mul_nonneg (sq_nonneg ‖u‖) (Real.exp_pos (-φ₀ x)).le)
  unfold optimalErrorFactor at hm
  unfold nativeTwist nativeCorrection
  rw [show -(Real.log (nativeRadius f x) + φ₀ x +
    potential (annularDensity σ δ) (normalTime ε (nativeRadius f x))) =
      (-Real.log (nativeRadius f x) - potential (annularDensity σ δ)
        (normalTime ε (nativeRadius f x))) + (-φ₀ x) by ring, Real.exp_add]
  convert hm using 1 <;> first | rfl | ring

/-- The original physical data multiplier has the sharp literal kernel bound. -/
theorem actual_data_energy_comparison (f : X → ℂ) (φ₀ : X → ℝ)
    {ε σ δ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ)
    (F : (x : X) → L.Fiber x) {x : X} (hfx : f x ≠ 0) (hR1 : nativeRadius f x < 1) :
    ENNReal.ofReal (curvatureDatum L f ε F x) * multiplierWeight 1 (optimalNativeWeight f φ₀ ε σ δ x) ≤
      ENNReal.ofReal ((windowMass σ + δ) * normalKernel ε (nativeRadius f x) *
        ‖F x‖ ^ 2 * Real.exp (-φ₀ x)) := by
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
  have hm := mul_le_mul_of_nonneg_right
    (sharp_physical_normal_data_energy_bound L hε hσ hδ F hfx hR1) (Real.exp_pos (-φ₀ x)).le
  rw [show -(Real.log (nativeRadius f x) + φ₀ x +
    potential (annularDensity σ δ) (normalTime ε (nativeRadius f x))) =
      (-Real.log (nativeRadius f x) - potential (annularDensity σ δ)
        (normalTime ε (nativeRadius f x))) + (-φ₀ x) by ring, Real.exp_add]
  convert hm using 1 <;> first | rfl | ring

/-- The completed global engine applies to ALL actual produced analytic
hypotheses, keeping only raw original geometric inputs. Both the singular
pre-comparison estimate and the sharp gain estimate are retained. -/
theorem exists_actual_native_sharp_weighted_correction [MeasurableSpace X] [BorelSpace X]
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
    (hbase : ∀ (c : ComplexChart n X) (e : AtlasFrame L) (d : ComplexModel n → ℝ),
      IsChartDensity μ c d → ∀ z ∈ chartFrameDomain L c e, ∀ v : ComplexModel n, v ≠ 0 →
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
    (fun c e d hd z hz hfinite v hv => actual_native_twistedCurvature_pos L hf hL hφ c e hz
      (hd.1.contDiffAt (c.val.open_target.mem_nhds hz.1)) (hd.2.1 z hz.1)
      (hfnot _ hfinite) hε hσ hδ (hR _) v (hbase c e d hd z hz v hv))
    (cutoffSection L f ε F) (isSmooth_cutoffSection L hf hε hF)
    (curvatureDatum L f ε F) (backgroundDatum L f ε ρ F)
    (fun c e d hd z hz hfinite v => actual_physical_curvature_datum L hf hL hφ hF c e hz
      (hd.1.contDiffAt (c.val.open_target.mem_nhds hz.1)) (hd.2.1 z hz.1)
      (hfnot _ hfinite) hε hσ hδ (hR _) v (by
        by_cases hv : v = 0
        · subst v
          simp only [leviForm_zero, le_refl]
        · exact (hbase c e d hd z hz v hv).le))
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

end SGPT.Trace.OptimalNativeNormalCorrection
