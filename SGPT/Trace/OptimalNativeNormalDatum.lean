import SGPT.Trace.OptimalNativeNormalWeight
import SGPT.Trace.OTExt5Step

/-!
# The actual physical normal cutoff and optimal curvature datum

All sections, frame coefficients, norms, local weights and derivatives are
those of the SAME original Hermitian holomorphic line bundle.
Blueprint: work/sgpt-resume-20261114/bert-e2-native-datum/blueprint/bert-e2-native-datum.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.OptimalNativeNormalDatum
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open HermitianHolomorphicLineBundle
open SGPT.Trace.TwistedL2 SGPT.Trace.OptimalExtensionODE SGPT.Trace.OptimalExtensionGainMass
open SGPT.Trace.OptimalExtensionCurvature SGPT.Trace.OptimalNormalRegularization
open SGPT.Trace.OptimalNativeNormalWeight

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

def nativeTwist (f : X → ℂ) (ε σ δ : ℝ) (x : X) : ℝ :=
  twist (annularDensity σ δ) (normalTime ε (nativeRadius f x))

def nativeCorrection (f : X → ℂ) (ε σ δ : ℝ) (x : X) : ℝ :=
  (correction (annularDensity σ δ) (normalTime ε (nativeRadius f x)))⁻¹

def optimalNativeWeight (f : X → ℂ) (φ₀ : X → ℝ) (ε σ δ : ℝ) : X → EReal :=
  normalWeight f fun x => φ₀ x + potential (annularDensity σ δ) (normalTime ε (nativeRadius f x))

variable (L : HermitianHolomorphicLineBundle.{0, 0} n X)

def cutoffSection (f : X → ℂ) (ε : ℝ) (F : (x : X) → L.Fiber x) (x : X) : L.Fiber x :=
  (normalCutoff ε (nativeRadius f x) : ℂ) • F x

def curvatureDatum (f : X → ℂ) (ε : ℝ) (F : (x : X) → L.Fiber x) (x : X) : ℝ :=
  normalDataFactor ε (nativeRadius f x) * ‖F x‖ ^ 2

theorem cutoffSection_eq_on_zero {f : X → ℂ} {ε : ℝ} (hε : 0 < ε)
    (F : (x : X) → L.Fiber x) {x : X} (hx : f x = 0) :
    cutoffSection L f ε F x = F x := by
  simp only [cutoffSection, nativeRadius, hx, norm_zero, zero_pow (by decide : 2 ≠ 0),
    normalCutoff_zero hε, Complex.ofReal_one, one_smul]

theorem chartCoeff_cutoffSection (f : X → ℂ) (ε : ℝ) (F : (x : X) → L.Fiber x)
    (c : ComplexChart n X) (e : AtlasFrame L) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain L c e) :
    chartCoeff L c e (cutoffSection L f ε F) z =
      chartCoeff L c e F z * (normalCutoff ε (nativeRadius f (c.val.symm z)) : ℂ) := by
  change (e.val ⟨c.val.symm z, (normalCutoff ε (nativeRadius f (c.val.symm z)) : ℂ) •
    F (c.val.symm z)⟩).2 = _
  rw [frameCoeff_smul_apply e hz.2]
  exact mul_comm _ _

theorem chartCoeff_cutoffSection_eventuallyEq (f : X → ℂ) (ε : ℝ)
    (F : (x : X) → L.Fiber x) (c : ComplexChart n X) (e : AtlasFrame L)
    {z : ComplexModel n} (hz : z ∈ chartFrameDomain L c e) :
    chartCoeff L c e (cutoffSection L f ε F) =ᶠ[𝓝 z]
      fun y => chartCoeff L c e F y * (normalCutoff ε (nativeRadius f (c.val.symm y)) : ℂ) := by
  filter_upwards [(isOpen_chartFrameDomain L c e).mem_nhds hz] with y hy
  exact chartCoeff_cutoffSection L f ε F c e hy

theorem differentiableOn_original_section_coefficient {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ)
    (c : ComplexChart n X) (e : AtlasFrame L) :
    DifferentiableOn ℂ (chartCoeff L c e F) (chartFrameDomain L c e) := by
  have := e.property
  have hd := SGPT.PSH.GlobalL2.differentiableOn_coord_of_holomorphicSectionOn e.val c isOpen_univ hF
  simp only [univ_inter] at hd
  refine hd.congr fun z hz => ?_
  exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℂ) e.val hz.2 _).symm

theorem isSmooth_cutoffSection {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f) {ε : ℝ} (hε : 0 < ε)
    {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ) :
    IsSmoothSectionOn L (cutoffSection L f ε F) univ := by
  intro c e z hz
  have hFs := SGPT.Trace.OTExt5.isSmoothSectionOn_of_holomorphic L hF c e
  have hFz := hFs.contDiffAt (by
    rw [preimage_univ, inter_univ]
    exact (isOpen_chartFrameDomain L c e).mem_nhds hz.1)
  have hq := (chartSmooth_nativeCutoff hf hε c).contDiffAt
    (c.val.open_target.mem_nhds hz.1.1)
  exact ((hFz.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp z hq)).congr_of_eventuallyEq
    (chartCoeff_cutoffSection_eventuallyEq L f ε F c e hz.1)).contDiffWithinAt

/-- Smoothness of the ORIGINAL local weight is produced from the actual
metric, same physical frame, original smooth base weight and volume density. -/
theorem contDiffAt_original_localWeight (hL : IsSourceSmoothHermitianMetric L)
    {φ₀ : X → ℝ} (hφ : ChartSmooth (n := n) φ₀)
    (c : ComplexChart n X) (e : AtlasFrame L) {ρ : ComplexModel n → ℝ}
    {z : ComplexModel n} (hz : z ∈ chartFrameDomain L c e)
    (hρ : ContDiffAt ℝ ∞ ρ z) (hρ0 : 0 < ρ z) :
    ContDiffAt ℝ 2 (SGPT.Trace.TwistedL2.localWeight L c e ρ φ₀) z := by
  have hmetric := (hL c e).contDiffAt ((isOpen_chartFrameDomain L c e).mem_nhds hz)
  exact (((hmetric.log (frameNormSq_pos e hz.2).ne').neg.add
    ((hφ c).contDiffAt (c.val.open_target.mem_nhds hz.1))).sub (hρ.log hρ0.ne')).of_le
      (WithTop.coe_le_coe.mpr le_top)

/-- The true regularized logarithmic normal has nonnegative Levi off its
original zero set; no Levi certificate is supplied. -/
theorem leviForm_actual_normalLog_nonneg {f : ComplexModel n → ℂ}
    {O : Set (ComplexModel n)} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O)
    {z : ComplexModel n} (hz : z ∈ O) (hfz : f z ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (v : ComplexModel n) : 0 ≤ leviForm (fun y => normalLog ε (normalRadius f y)) z v := by
  have hR := contDiffAt_normalRadius hO hf hz
  have hr : 0 < normalRadius f z := sq_pos_of_pos (norm_pos_iff.mpr hfz)
  have hlog := SGPT.Trace.OTExt5.leviForm_log_norm_sq_eq_zero
    (by filter_upwards [hO.mem_nhds hz] with y hy
        exact (hf y hy).differentiableAt (hO.mem_nhds hy)) hfz v
  have hcalc := leviForm_log_add
    (hR.of_le (WithTop.coe_le_coe.mpr le_top)) hr hε v
  change leviForm (fun y => Real.log (normalRadius f y)) z v = 0 at hlog
  rw [hlog, mul_zero, zero_add] at hcalc
  rw [leviForm_normalLog (hR.of_le (WithTop.coe_le_coe.mpr le_top)) hε hr.le, hcalc]
  unfold holDerivSq
  positivity

/-- Exact curvature of the ORIGINAL finite part of the actual extended
weight; the logarithmic normal pole is pluriharmonic off its original fibre. -/
theorem actual_native_twistedCurvature {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hL : IsSourceSmoothHermitianMetric L) {φ₀ : X → ℝ} (hφ : ChartSmooth (n := n) φ₀)
    (c : ComplexChart n X) (e : AtlasFrame L) {ρ : ComplexModel n → ℝ}
    {z : ComplexModel n} (hz : z ∈ chartFrameDomain L c e)
    (hρ : ContDiffAt ℝ ∞ ρ z) (hρ0 : 0 < ρ z)
    (hfz : f (c.val.symm z) ≠ 0) {ε σ δ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ) (hR1 : nativeRadius f (c.val.symm z) < 1)
    (v : ComplexModel n) :
    twistedCurvature (fun y => nativeTwist f ε σ δ (c.val.symm y))
      (fun y => nativeCorrection f ε σ δ (c.val.symm y))
      (SGPT.Trace.TwistedL2.localWeight L c e ρ fun x => (optimalNativeWeight f φ₀ ε σ δ x).toReal) z v =
    nativeTwist f ε σ δ (c.val.symm z) *
      leviForm (SGPT.Trace.TwistedL2.localWeight L c e ρ φ₀) z v +
      leviForm (fun y => normalLog ε (nativeRadius f (c.val.symm y))) z v := by
  let R := fun y => nativeRadius f (c.val.symm y)
  let V := fun y => normalLog ε (R y)
  let p₀ := SGPT.Trace.TwistedL2.localWeight L c e ρ φ₀
  let w := annularDensity σ δ
  have hRc := chartSmooth_nativeRadius hf c
  have hR := hRc.contDiffAt (c.val.open_target.mem_nhds hz.1)
  have hr : 0 < R z := sq_pos_of_pos (norm_pos_iff.mpr hfz)
  have hO : IsOpen (c.val.target ∩ R ⁻¹' Ioi 0) :=
    hRc.continuousOn.isOpen_inter_preimage c.val.open_target isOpen_Ioi
  have heq : (SGPT.Trace.TwistedL2.localWeight L c e ρ
      fun x => (optimalNativeWeight f φ₀ ε σ δ x).toReal) =ᶠ[𝓝 z]
      SGPT.Trace.OptimalExtensionCurvature.localWeight w V (fun y => p₀ y + Real.log (R y)) := by
    filter_upwards [hO.mem_nhds ⟨hz.1, hr⟩] with y hy
    have hfy : f (c.val.symm y) ≠ 0 := by
      intro h
      have hh := hy.2
      change 0 < nativeRadius f (c.val.symm y) at hh
      simp only [nativeRadius, h, norm_zero, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hh
    rw [SGPT.Trace.TwistedL2.localWeight, optimalNativeWeight, normalWeight_toReal _ hfy]
    dsimp only [SGPT.Trace.OptimalExtensionCurvature.localWeight, p₀, V, R, normalTime,
      SGPT.Trace.TwistedL2.localWeight, w]
    ring
  have hceq : twistedCurvature (fun y => nativeTwist f ε σ δ (c.val.symm y))
      (fun y => nativeCorrection f ε σ δ (c.val.symm y))
      (SGPT.Trace.TwistedL2.localWeight L c e ρ fun x => (optimalNativeWeight f φ₀ ε σ δ x).toReal) z v =
      twistedCurvature (localTwist w V) (localCorrection w V)
        (SGPT.Trace.OptimalExtensionCurvature.localWeight w V (fun y => p₀ y + Real.log (R y))) z v := by
    simp only [twistedCurvature, leviForm_congr_ev heq v]
    rfl
  have hp := contDiffAt_original_localWeight L hL hφ c e hz hρ hρ0
  have hlog2 : ContDiffAt ℝ 2 (fun y => Real.log (R y)) z :=
    (hR.log hr.ne').of_le (WithTop.coe_le_coe.mpr le_top)
  have hV : ContDiffAt ℝ 2 V z :=
    (contDiffAt_normalLog hR hε hr.le).of_le (WithTop.coe_le_coe.mpr le_top)
  have hT := normalTime_pos hε hr.le hR1
  have hlog := SGPT.Trace.OTExt5.leviForm_log_norm_sq_eq_zero
    (by filter_upwards [c.val.open_target.mem_nhds hz.1] with y hy
        exact ((differentiableOn_native_normal_chart hf c) y hy).differentiableAt
          (c.val.open_target.mem_nhds hy)) hfz v
  have hsum : leviForm (fun y => p₀ y + Real.log (R y)) z v =
      leviForm p₀ z v + leviForm (fun y => Real.log (R y)) z v := by
    convert leviForm_add hp hlog2 v using 1
    rfl
  change leviForm (fun y => Real.log (R y)) z v = 0 at hlog
  rw [hceq, actual_annular_twistedCurvature hσ hδ hV (hp.add hlog2) (neg_pos.mp hT) v,
    hsum, hlog, add_zero]
  rfl

theorem actual_native_twistedCurvature_pos {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hL : IsSourceSmoothHermitianMetric L) {φ₀ : X → ℝ} (hφ : ChartSmooth (n := n) φ₀)
    (c : ComplexChart n X) (e : AtlasFrame L) {ρ : ComplexModel n → ℝ}
    {z : ComplexModel n} (hz : z ∈ chartFrameDomain L c e)
    (hρ : ContDiffAt ℝ ∞ ρ z) (hρ0 : 0 < ρ z)
    (hfz : f (c.val.symm z) ≠ 0) {ε σ δ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ) (hR1 : nativeRadius f (c.val.symm z) < 1)
    (v : ComplexModel n) (hbase : 0 < leviForm (SGPT.Trace.TwistedL2.localWeight L c e ρ φ₀) z v) :
    0 < twistedCurvature (fun y => nativeTwist f ε σ δ (c.val.symm y))
      (fun y => nativeCorrection f ε σ δ (c.val.symm y))
      (SGPT.Trace.TwistedL2.localWeight L c e ρ fun x => (optimalNativeWeight f φ₀ ε σ δ x).toReal) z v := by
  rw [actual_native_twistedCurvature L hf hL hφ c e hz hρ hρ0 hfz hε hσ hδ hR1 v]
  exact add_pos_of_pos_of_nonneg
    (mul_pos (twist_pos (contDiff_annularDensity σ δ).continuous
      (fun t _ => annularDensity_pos σ hδ t) (normalTime_pos hε (sq_nonneg _) hR1)) hbase)
    (leviForm_actual_normalLog_nonneg c.val.open_target
      (differentiableOn_native_normal_chart hf c) hz.1 hfz hε v)

/-- Exact actual physical datum, with the original frame norm cancelled
against the SAME original section coefficient. -/
theorem exact_physical_cutoff_datum {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ)
    (c : ComplexChart n X) (e : AtlasFrame L) {z : ComplexModel n}
    (hz : z ∈ chartFrameDomain L c e) (hfz : f (c.val.symm z) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) (v : ComplexModel n) :
    ‖dbarPairing (chartCoeff L c e (cutoffSection L f ε F)) z v‖ ^ 2 *
        frameNormSq L e (c.val.symm z) =
      curvatureDatum L f ε F (c.val.symm z) *
        leviForm (fun y => normalLog ε (nativeRadius f (c.val.symm y))) z v := by
  have hh := (differentiableOn_original_section_coefficient L hF c e z hz).differentiableAt
    ((isOpen_chartFrameDomain L c e).mem_nhds hz)
  have heq : dbarPairing (chartCoeff L c e (cutoffSection L f ε F)) z v =
      dbarPairing (fun y => chartCoeff L c e F y *
        (normalCutoff ε (nativeRadius f (c.val.symm y)) : ℂ)) z v := by
    rw [dbarPairing_eq_dbarDir, dbarDir_congr_of_eventuallyEq
      (chartCoeff_cutoffSection_eventuallyEq L f ε F c e hz), ← dbarPairing_eq_dbarDir]
  have hscalar := exact_normal_cutoff_datum c.val.open_target
    (differentiableOn_native_normal_chart hf c) hz.1 hfz hh hε v
  simp only [normalRadius] at hscalar
  rw [heq]
  simp only [nativeRadius]
  rw [hscalar, curvatureDatum, norm_sq_eq_frameCoeff e hz.2]
  simp only [nativeRadius, chartCoeff, frameCoeff]
  ring

theorem actual_physical_curvature_datum {f : X → ℂ}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ f)
    (hL : IsSourceSmoothHermitianMetric L) {φ₀ : X → ℝ} (hφ : ChartSmooth (n := n) φ₀)
    {F : (x : X) → L.Fiber x}
    (hF : SGPT.PSH.LineBundleMetric.IsHolomorphicSectionOn (n := n) L.Fiber F univ)
    (c : ComplexChart n X) (e : AtlasFrame L) {ρ : ComplexModel n → ℝ}
    {z : ComplexModel n} (hz : z ∈ chartFrameDomain L c e)
    (hρ : ContDiffAt ℝ ∞ ρ z) (hρ0 : 0 < ρ z)
    (hfz : f (c.val.symm z) ≠ 0) {ε σ δ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ) (hR1 : nativeRadius f (c.val.symm z) < 1)
    (v : ComplexModel n) (hbase : 0 ≤ leviForm (SGPT.Trace.TwistedL2.localWeight L c e ρ φ₀) z v) :
    ‖dbarPairing (chartCoeff L c e (cutoffSection L f ε F)) z v‖ ^ 2 *
        frameNormSq L e (c.val.symm z) ≤
      curvatureDatum L f ε F (c.val.symm z) *
        twistedCurvature (fun y => nativeTwist f ε σ δ (c.val.symm y))
          (fun y => nativeCorrection f ε σ δ (c.val.symm y))
          (SGPT.Trace.TwistedL2.localWeight L c e ρ fun x => (optimalNativeWeight f φ₀ ε σ δ x).toReal) z v := by
  rw [exact_physical_cutoff_datum L hf hF c e hz hfz hε v,
    actual_native_twistedCurvature L hf hL hφ c e hz hρ hρ0 hfz hε hσ hδ hR1 v]
  have hD : 0 ≤ curvatureDatum L f ε F (c.val.symm z) :=
    mul_nonneg (normalDataFactor_nonneg hε.le (sq_nonneg _)) (sq_nonneg _)
  have ha : 0 < nativeTwist f ε σ δ (c.val.symm z) :=
    twist_pos (contDiff_annularDensity σ δ).continuous
      (fun t _ => annularDensity_pos σ hδ t) (normalTime_pos hε (sq_nonneg _) hR1)
  nlinarith [mul_nonneg hD (mul_nonneg ha.le hbase)]

theorem exact_physical_normal_data_energy {f : X → ℂ} {ε σ δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (F : (x : X) → L.Fiber x) {x : X}
    (hfx : f x ≠ 0) (hR1 : nativeRadius f x < 1) :
    curvatureDatum L f ε F x *
        Real.exp (-Real.log (nativeRadius f x) - potential (annularDensity σ δ)
          (normalTime ε (nativeRadius f x))) =
      normalKernel ε (nativeRadius f x) * ‖F x‖ ^ 2 *
        mass (annularDensity σ δ) (normalTime ε (nativeRadius f x)) := by
  have h := exact_normal_data_energy (contDiff_annularDensity σ δ).continuous
    (fun t _ => annularDensity_pos σ hδ t) hε
      (sq_pos_of_pos (norm_pos_iff.mpr hfx)) hR1 (1 : ℂ)
  simp only [norm_one, one_pow, mul_one] at h
  unfold curvatureDatum nativeRadius
  convert congrArg (fun r => r * ‖F x‖ ^ 2) h using 1 <;> ring

theorem sharp_physical_normal_data_energy_bound {f : X → ℂ} {ε σ δ : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hδ : 0 < δ) (F : (x : X) → L.Fiber x) {x : X}
    (hfx : f x ≠ 0) (hR1 : nativeRadius f x < 1) :
    curvatureDatum L f ε F x *
        Real.exp (-Real.log (nativeRadius f x) - potential (annularDensity σ δ)
          (normalTime ε (nativeRadius f x))) ≤
      (windowMass σ + δ) * normalKernel ε (nativeRadius f x) * ‖F x‖ ^ 2 := by
  have h := sharp_normal_data_energy_bound hσ hδ hε
    (sq_pos_of_pos (norm_pos_iff.mpr hfx)) hR1 (1 : ℂ)
  simp only [norm_one, one_pow, mul_one] at h
  unfold curvatureDatum nativeRadius
  convert mul_le_mul_of_nonneg_right h (sq_nonneg ‖F x‖) using 1 <;> first | rfl | ring

end SGPT.Trace.OptimalNativeNormalDatum
