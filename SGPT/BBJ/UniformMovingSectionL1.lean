import SGPT.BBJ.MovingSectionCurrent
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
noncomputable section
namespace SGPT.BBJ
open Set Filter MeasureTheory Metric
open SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal

/-- Genuine compact-ball norm integral of the existing coordinate logarithm. -/
def coordinateLogNormIntegral (T : ℝ) : ℝ :=
  ∫ z in closedBall (0 : ComplexModel 1) T, |Real.log (‖projectiveModelEquiv.symm z‖^2)|

/-- The coordinate logarithm is integrable before its norm integral is used. -/
theorem coordinateLog_integrableOn_closedBall (T : ℝ) :
    IntegrableOn (fun z : ComplexModel 1 => Real.log (‖projectiveModelEquiv.symm z‖^2))
      (closedBall 0 T) volume :=
  locallyIntegrable_projectiveCoordinateLog.integrableOn_compact_subset
    (subset_univ _) (isCompact_closedBall _ _)

theorem coordinateLogNormIntegral_nonneg (T : ℝ) : 0 ≤ coordinateLogNormIntegral T :=
  integral_nonneg fun _ => abs_nonneg _

/-- Literal translation bounds in the original actual chart volume. -/
theorem translatedCoordinateLog_integral_bound (R A : ℝ) (_hA : 0 ≤ A)
    (a : ℂ) (ha : ‖a‖ ≤ A) :
    IntegrableOn (fun z : ComplexModel 1 => Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv a)‖^2))
      (closedBall 0 R) volume ∧
    (∫ z in closedBall (0 : ComplexModel 1) R,
      |Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv a)‖^2)|) ≤
        coordinateLogNormIntegral (R+A) := by
  let f : ComplexModel 1 → ComplexModel 1 := fun z => z + (-projectiveModelEquiv a)
  have hf : MeasurePreserving f volume volume := measurePreserving_add_right volume _
  have he : MeasurableEmbedding f := (Homeomorph.addRight (-projectiveModelEquiv a)).measurableEmbedding
  have hsub : f '' closedBall (0 : ComplexModel 1) R ⊆ closedBall 0 (R+A) := by
    rintro _ ⟨z,hz,rfl⟩
    have hn : ‖projectiveModelEquiv a‖ = ‖a‖ := by
      simpa using (projectiveModelEquiv_symm_norm (projectiveModelEquiv a)).symm
    rw [mem_closedBall_zero_iff] at hz ⊢
    calc ‖f z‖ ≤ ‖z‖+‖projectiveModelEquiv a‖ := by
           simpa only [f,norm_neg] using norm_add_le z (-projectiveModelEquiv a)
         _ ≤ R+A := by rw [hn]; linarith
  have hi := coordinateLog_integrableOn_closedBall (R+A)
  have hit := hi.mono_set hsub
  have hc := (hf.integrableOn_image he).mp hit
  refine ⟨by simpa only [f,sub_eq_add_neg,Function.comp_def] using hc,?_⟩
  have ht := hf.setIntegral_image_emb he
    (fun z : ComplexModel 1 => |Real.log (‖projectiveModelEquiv.symm z‖^2)|) (closedBall 0 R)
  simp only [f,← sub_eq_add_neg] at ht
  rw [← ht]
  exact setIntegral_mono_set hi.norm (Eventually.of_forall fun z => by simp) (Eventually.of_forall hsub)

/-- Every actual kernel density is genuinely integrable on each compact ball. -/
theorem movingSectionDensity_integrableOn_closedBall (c : ℝ) (b : Bool) (R : ℝ) :
    IntegrableOn (movingSectionDensity c b) (closedBall 0 R) volume :=
  (locallyIntegrable_movingSectionDensity c b).integrableOn_compact_subset
    (subset_univ _) (isCompact_closedBall _ _)

/-- Actual smooth FS normalizer on a compact ball. -/
theorem projectiveFSPotential_closedBall_bounds (R : ℝ) (hR : 0 ≤ R)
    (z : ComplexModel 1) (hz : z ∈ closedBall 0 R) :
    0 ≤ projectiveFSPotential z ∧ projectiveFSPotential z ≤ Real.log (1+R^2) := by
  have hn : ‖projectiveModelEquiv.symm z‖ ≤ R := by
    rw [projectiveModelEquiv_symm_norm]; exact mem_closedBall_zero_iff.mp hz
  rw [projectiveFSPotential_eq,← Complex.sq_norm,← projectiveModelEquiv_symm_apply]
  constructor
  · exact Real.log_nonneg (by nlinarith [sq_nonneg ‖projectiveModelEquiv.symm z‖])
  · apply Real.log_le_log (by positivity)
    nlinarith [norm_nonneg (projectiveModelEquiv.symm z)]

private theorem continuous_ereal_sub_real {X : Type*} [TopologicalSpace X]
    (f : X → EReal) (g : X → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => f x-(g x : EReal)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hpair : ContinuousAt (fun y => (f y,(-(g y) : EReal))) x :=
    hf.continuousAt.prodMk ((continuous_coe_real_ereal.comp hg.neg).continuousAt)
  exact (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))).comp hpair

/-- Exact joint continuity includes the moving zero and its bottom value. -/
theorem continuous_movingSectionKernel (b : Bool) :
    Continuous (fun q : ℝ × ComplexModel 1 =>
      movingProjectiveSectionPotential q.1 ((projectiveModelChart b).symm q.2)) := by
  have hc : Continuous (fun q : ℝ × ComplexModel 1 =>
      if b then 1-(q.1 : ℂ)*projectiveModelEquiv.symm q.2
        else projectiveModelEquiv.symm q.2-(q.1 : ℂ)) := by
    cases b <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop
  have hρ : Continuous (fun q : ℝ × ComplexModel 1 => projectiveFSPotential q.2) :=
    contDiff_projectiveFSPotential.continuous.comp continuous_snd
  have hC : Continuous (fun q : ℝ × ComplexModel 1 => Real.log (1+q.1^2)) :=
    (continuous_const.add (continuous_fst.pow 2)).log (fun q => by change 1+q.1^2 ≠ 0; positivity)
  have h := continuous_ereal_sub_real _ _
    (continuous_ereal_sub_real _ _ (continuous_logNormSq.comp hc) hρ) hC
  convert h using 1
  funext q
  simpa only [projectiveModelEquiv_symm_apply,Function.comp_apply] using
    movingProjectiveSectionPotential_chart q.1 b q.2

/-- Realification is measurable, without claiming its continuity at bottom. -/
theorem measurable_movingSectionDensity (b : Bool) :
    Measurable (fun q : ℝ × ComplexModel 1 => movingSectionDensity q.1 b q.2) :=
  (continuous_movingSectionKernel b).measurable.ereal_toReal

theorem measurable_movingSectionDensity_abs (b : Bool) :
    Measurable (fun q : ℝ × ComplexModel 1 => |movingSectionDensity q.1 b q.2|) :=
  by simpa only [Real.norm_eq_abs] using (measurable_movingSectionDensity b).norm

/-- The negative extended deficit retains poles as actual positive infinity. -/
theorem measurable_movingSectionDeficit (b : Bool) :
    Measurable (fun q : ℝ × ComplexModel 1 =>
      (-movingProjectiveSectionPotential q.1 ((projectiveModelChart b).symm q.2)).toENNReal) :=
  (EReal.continuous_toENNReal.comp (continuous_movingSectionKernel b).neg).measurable

/-- Both finite real normalizers have an actual uniform parameter bound. -/
theorem movingSectionConstant_bounds (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1/2) :
    0 ≤ Real.log (1+c^2) ∧ Real.log (1+c^2) ≤ Real.log 2 := by
  constructor
  · exact Real.log_nonneg (by nlinarith [sq_nonneg c])
  · exact Real.log_le_log (by positivity) (by nlinarith)

/-- Integration of a genuine translated-log majorant, with actual finite ball volume. -/
private theorem density_integral_bound (c : ℝ) (b : Bool) (R A D : ℝ)
    (hA : 0 ≤ A) (a : ℂ) (ha : ‖a‖ ≤ A)
    (hbound : ∀ᵐ z ∂volume.restrict (closedBall (0 : ComplexModel 1) R),
      |movingSectionDensity c b z| ≤
        |Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv a)‖^2)|+D) :
    (∫ z in closedBall (0 : ComplexModel 1) R, |movingSectionDensity c b z|) ≤
      coordinateLogNormIntegral (R+A)+D*(volume (closedBall (0 : ComplexModel 1) R)).toReal := by
  obtain ⟨hi,hle⟩ := translatedCoordinateLog_integral_bound R A hA a ha
  have hc : IntegrableOn (fun _ : ComplexModel 1 => D) (closedBall 0 R) volume :=
    integrableOn_const (isCompact_closedBall (0 : ComplexModel 1) R).measure_lt_top.ne
  have hb := integral_mono_ae (movingSectionDensity_integrableOn_closedBall c b R).norm
    (hi.norm.add hc) hbound
  simp only [Pi.add_apply] at hb
  rw [integral_add hi.norm hc] at hb
  simp only [Real.norm_eq_abs,integral_const,Measure.real,Measure.restrict_apply_univ,
    smul_eq_mul] at hb
  change _ ≤ coordinateLogNormIntegral (R+A)+_
  linarith

/-- Explicit finite-chart uniform compact L1 bound, with no parameter moment input. -/
theorem movingSectionDensity_finite_integral_bound (R : ℝ) (hR : 0 ≤ R)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1/2) :
    (∫ z in closedBall (0 : ComplexModel 1) R, |movingSectionDensity c false z|) ≤
      coordinateLogNormIntegral (R+1)+
        (Real.log (1+R^2)+Real.log 2)*(volume (closedBall (0 : ComplexModel 1) R)).toReal := by
  apply density_integral_bound c false R 1 _ zero_le_one (c : ℂ)
    (by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0]; linarith)
  have hae := movingSectionDensity_ae c false
  simp only [TopologicalSpace.Opens.coe_top,Measure.restrict_univ] at hae
  filter_upwards [ae_restrict_of_ae hae,ae_restrict_mem measurableSet_closedBall] with z hz hzB
  have hρ := projectiveFSPotential_closedBall_bounds R hR z hzB
  have hC := movingSectionConstant_bounds c hc0 hc
  rw [hz]
  have he : movingSectionCoefficient c false z =
      projectiveModelEquiv.symm (z-projectiveModelEquiv (c : ℂ)) := by
    simp [movingSectionCoefficient]
  rw [he]
  calc |Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv (c : ℂ))‖^2)-
          projectiveFSPotential z-Real.log (1+c^2)| ≤
        |Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv (c : ℂ))‖^2)|+
          |projectiveFSPotential z|+|Real.log (1+c^2)| :=
      by
        have h1 := abs_sub (Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv (c : ℂ))‖^2)-projectiveFSPotential z) (Real.log (1+c^2))
        have h2 := abs_sub (Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv (c : ℂ))‖^2)) (projectiveFSPotential z)
        linarith
       _ ≤ _ := by rw [abs_of_nonneg hρ.1,abs_of_nonneg hC.1]; linarith

/-- The nonnegative finite small-parameter logarithm bound. -/
def infinitySmallLogBound (R : ℝ) : ℝ := 2*Real.log 2+2*Real.log (1+R/2)

/-- The two genuine finite uniform majorants, including all normalizers. -/
def infinitySmallL1Bound (R : ℝ) : ℝ :=
  (infinitySmallLogBound R+Real.log (1+R^2)+Real.log 2)*
    (volume (closedBall (0 : ComplexModel 1) R)).toReal

def infinityLargeL1Bound (R : ℝ) : ℝ :=
  coordinateLogNormIntegral (R+2*max R 1)+
    (2*Real.log (2*max R 1)+Real.log (1+R^2)+Real.log 2)*
      (volume (closedBall (0 : ComplexModel 1) R)).toReal

private theorem constant_density_integral_bound (c : ℝ) (b : Bool) (R D : ℝ)
    (hb : ∀ᵐ z ∂volume.restrict (closedBall (0 : ComplexModel 1) R),
      |movingSectionDensity c b z| ≤ D) :
    (∫ z in closedBall (0 : ComplexModel 1) R, |movingSectionDensity c b z|) ≤
      D*(volume (closedBall (0 : ComplexModel 1) R)).toReal := by
  have hi : IntegrableOn (fun _ : ComplexModel 1 => D) (closedBall 0 R) volume :=
    integrableOn_const (isCompact_closedBall (0 : ComplexModel 1) R).measure_lt_top.ne
  have h := integral_mono_ae (movingSectionDensity_integrableOn_closedBall c b R).norm hi hb
  simpa only [Real.norm_eq_abs,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using h

/-- Small c is treated without splitting cancelling logarithms. -/
theorem movingSectionDensity_infinity_small_bound (R : ℝ) (hR : 0 ≤ R)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1/2) (hsmall : c ≤ (2*max R 1)⁻¹) :
    (∫ z in closedBall (0 : ComplexModel 1) R, |movingSectionDensity c true z|) ≤
      infinitySmallL1Bound R := by
  apply constant_density_integral_bound
  have hae := movingSectionDensity_ae c true
  simp only [TopologicalSpace.Opens.coe_top,Measure.restrict_univ] at hae
  filter_upwards [ae_restrict_of_ae hae,ae_restrict_mem measurableSet_closedBall] with z hz hzB
  have hS : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hprod : c*(2*max R 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp (by simpa only [one_div] using hsmall)
  have hn : ‖projectiveModelEquiv.symm z‖ ≤ R := by
    rw [projectiveModelEquiv_symm_norm]; exact mem_closedBall_zero_iff.mp hzB
  have hcn : c*‖projectiveModelEquiv.symm z‖ ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_left (le_max_left R 1) hc0
    have hh' := mul_le_mul_of_nonneg_left hn hc0
    nlinarith
  have hnorm : ‖(c : ℂ)*projectiveModelEquiv.symm z‖ = c*‖projectiveModelEquiv.symm z‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0]
  have hglo : (1/2 : ℝ) ≤ ‖1-(c : ℂ)*projectiveModelEquiv.symm z‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) ((c : ℂ)*projectiveModelEquiv.symm z)
    rw [norm_one,hnorm] at ht
    linarith
  have hghi : ‖1-(c : ℂ)*projectiveModelEquiv.symm z‖ ≤ 1+R/2 := by
    have ht := norm_sub_le (1 : ℂ) ((c : ℂ)*projectiveModelEquiv.symm z)
    rw [norm_one,hnorm] at ht
    have hm := mul_le_mul_of_nonneg_right hc (norm_nonneg (projectiveModelEquiv.symm z))
    linarith
  have hloglo : -2*Real.log 2 ≤ Real.log (‖1-(c : ℂ)*projectiveModelEquiv.symm z‖^2) := by
    have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) hglo
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0),Real.log_one] at hl
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat] at *
    linarith
  have hloghi : Real.log (‖1-(c : ℂ)*projectiveModelEquiv.symm z‖^2) ≤ 2*Real.log (1+R/2) := by
    have hl := Real.log_le_log (by linarith : 0 < ‖1-(c : ℂ)*projectiveModelEquiv.symm z‖) hghi
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat] at *
    linarith
  have hln2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlnR : 0 ≤ Real.log (1+R/2) := Real.log_nonneg (by linarith)
  have hlog : |Real.log (‖1-(c : ℂ)*projectiveModelEquiv.symm z‖^2)| ≤ infinitySmallLogBound R := by
    rw [abs_le]
    dsimp [infinitySmallLogBound]
    constructor <;> linarith
  have hρ := projectiveFSPotential_closedBall_bounds R hR z hzB
  have hC := movingSectionConstant_bounds c hc0 hc
  rw [hz]
  change |Real.log (‖1-(c : ℂ)*projectiveModelEquiv.symm z‖^2)-projectiveFSPotential z-Real.log (1+c^2)| ≤ _
  have h1 := abs_sub (Real.log (‖1-(c : ℂ)*projectiveModelEquiv.symm z‖^2)-projectiveFSPotential z) (Real.log (1+c^2))
  have h2 := abs_sub (Real.log (‖1-(c : ℂ)*projectiveModelEquiv.symm z‖^2)) (projectiveFSPotential z)
  rw [abs_of_nonneg hρ.1] at h2
  rw [abs_of_nonneg hC.1] at h1
  linarith

/-- Only the parameter range bounded away from zero uses factorization. -/
theorem movingSectionDensity_infinity_large_bound (R : ℝ) (hR : 0 ≤ R)
    (c : ℝ) (hc : c ≤ 1/2) (hlarge : (2*max R 1)⁻¹ ≤ c) :
    (∫ z in closedBall (0 : ComplexModel 1) R, |movingSectionDensity c true z|) ≤
      infinityLargeL1Bound R := by
  have hS : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hc0 : 0 < c := lt_of_lt_of_le (inv_pos.mpr (by positivity)) hlarge
  have hmul : 1 ≤ c*(2*max R 1) :=
    (div_le_iff₀ (by positivity)).mp (by simpa only [one_div] using hlarge)
  have hr : ‖((c : ℂ)⁻¹)‖ ≤ 2*max R 1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc0,inv_eq_one_div]
    exact (div_le_iff₀ hc0).mpr (by nlinarith)
  have hlogc : |2*Real.log c| ≤ 2*Real.log (2*max R 1) := by
    have hlo := Real.log_le_log (inv_pos.mpr (by positivity)) hlarge
    rw [Real.log_inv] at hlo
    have hhi := Real.log_nonpos hc0.le (by linarith : c ≤ 1)
    rw [abs_le]
    have hn := Real.log_nonneg (by have := le_max_right R 1; linarith : 1 ≤ 2*max R 1)
    constructor <;> linarith
  change _ ≤ coordinateLogNormIntegral (R+2*max R 1)+_
  apply density_integral_bound c true R (2*max R 1) _ (by positivity) ((c : ℂ)⁻¹) hr
  have hae := movingSectionDensity_ae c true
  have hne := Pending.LelongPoincareDivisor.ae_ne_zero isOpen_univ
    (movingSectionCoefficient_differentiable c true).differentiableOn
    (fun z _ => movingSectionCoefficient_frequently_ne_zero c true z)
  simp only [TopologicalSpace.Opens.coe_top,Measure.restrict_univ] at hae
  simp only [Measure.restrict_univ] at hne
  filter_upwards [ae_restrict_of_ae hae,ae_restrict_of_ae hne,
    ae_restrict_mem measurableSet_closedBall] with z hz hz0 hzB
  have hρ := projectiveFSPotential_closedBall_bounds R hR z hzB
  have hC := movingSectionConstant_bounds c hc0.le hc
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc0.ne'
  have he : 1-(c : ℂ)*projectiveModelEquiv.symm z =
      (-(c : ℂ))*(projectiveModelEquiv.symm z-(c : ℂ)⁻¹) := by
    rw [mul_sub,neg_mul,neg_mul,mul_inv_cancel₀ hcC]
    ring
  have hgap : projectiveModelEquiv.symm z-(c : ℂ)⁻¹ ≠ 0 := by
    intro h
    apply hz0
    change 1-(c : ℂ)*projectiveModelEquiv.symm z = 0
    rw [he,h,mul_zero]
  have heLog : Real.log (‖movingSectionCoefficient c true z‖^2) =
      2*Real.log c+Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv ((c : ℂ)⁻¹))‖^2) := by
    change Real.log (‖1-(c : ℂ)*projectiveModelEquiv.symm z‖^2) = _
    rw [he,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc0,mul_pow,
      Real.log_mul (pow_ne_zero 2 hc0.ne') (pow_ne_zero 2 (norm_ne_zero_iff.mpr hgap)),Real.log_pow]
    simp only [Nat.cast_ofNat,map_sub,ContinuousLinearEquiv.symm_apply_apply]
  rw [hz,heLog]
  have h1 := abs_sub (2*Real.log c+Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv ((c : ℂ)⁻¹))‖^2)-projectiveFSPotential z) (Real.log (1+c^2))
  have h2 := abs_sub (2*Real.log c+Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv ((c : ℂ)⁻¹))‖^2)) (projectiveFSPotential z)
  have h3 := norm_add_le (2*Real.log c) (Real.log (‖projectiveModelEquiv.symm (z-projectiveModelEquiv ((c : ℂ)⁻¹))‖^2))
  simp only [Real.norm_eq_abs] at h3
  rw [abs_of_nonneg hρ.1] at h2
  rw [abs_of_nonneg hC.1] at h1
  linarith

/-- Both case constants are actual nonnegative finite reals. -/
theorem infinityL1Bounds_nonneg (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ infinitySmallL1Bound R ∧ 0 ≤ infinityLargeL1Bound R := by
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hRlog : 0 ≤ Real.log (1+R/2) := Real.log_nonneg (by linarith)
  have hQ : 0 ≤ Real.log (1+R^2) := Real.log_nonneg (by nlinarith [sq_nonneg R])
  have hSlog : 0 ≤ Real.log (2*max R 1) := Real.log_nonneg (by have := le_max_right R 1; linarith)
  have hJ := coordinateLogNormIntegral_nonneg (R+2*max R 1)
  dsimp [infinitySmallL1Bound,infinityLargeL1Bound,infinitySmallLogBound]
  constructor <;> positivity

/-- A genuine common infinity-chart bound, including c=0 and both threshold endpoints. -/
theorem movingSectionDensity_infinity_integral_bound (R : ℝ) (hR : 0 ≤ R)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ 1/2) :
    (∫ z in closedBall (0 : ComplexModel 1) R, |movingSectionDensity c true z|) ≤
      infinitySmallL1Bound R+infinityLargeL1Bound R := by
  have hn := infinityL1Bounds_nonneg R hR
  by_cases hs : c ≤ (2*max R 1)⁻¹
  · have h := movingSectionDensity_infinity_small_bound R hR c hc0 hc hs
    linarith
  · have h := movingSectionDensity_infinity_large_bound R hR c hc (le_of_lt (lt_of_not_ge hs))
    linarith

/-- Every actual compact spatial set has an internally produced common finite L1 bound. -/
theorem movingSectionDensity_uniform_compact_L1 (K : Set (ComplexModel 1)) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ c : ℝ, 0 ≤ c → c ≤ 1/2 → ∀ b : Bool,
      IntegrableOn (movingSectionDensity c b) K volume ∧
      (∫ z in K, |movingSectionDensity c b z|) ≤ B := by
  obtain ⟨r,hr⟩ := hK.isBounded.subset_closedBall 0
  let R := max r 0
  have hR : 0 ≤ R := le_max_right _ _
  have hsub : K ⊆ closedBall (0 : ComplexModel 1) R :=
    hr.trans (closedBall_subset_closedBall (le_max_left _ _))
  let F := coordinateLogNormIntegral (R+1)+
    (Real.log (1+R^2)+Real.log 2)*(volume (closedBall (0 : ComplexModel 1) R)).toReal
  let I := infinitySmallL1Bound R+infinityLargeL1Bound R
  have hF : 0 ≤ F := by
    have hJ := coordinateLogNormIntegral_nonneg (R+1)
    have hQ : 0 ≤ Real.log (1+R^2) := Real.log_nonneg (by nlinarith [sq_nonneg R])
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp [F]; positivity
  have hI : 0 ≤ I := add_nonneg (infinityL1Bounds_nonneg R hR).1 (infinityL1Bounds_nonneg R hR).2
  refine ⟨F+I,add_nonneg hF hI,?_⟩
  intro c hc0 hc b
  have hi := movingSectionDensity_integrableOn_closedBall c b R
  refine ⟨hi.mono_set hsub,?_⟩
  have hm : (∫ z in K, |movingSectionDensity c b z|) ≤
      ∫ z in closedBall (0 : ComplexModel 1) R, |movingSectionDensity c b z| :=
    setIntegral_mono_set hi.norm (Eventually.of_forall fun z => abs_nonneg _)
      (Eventually.of_forall hsub)
  cases b
  · have hb := movingSectionDensity_finite_integral_bound R hR c hc0 hc
    change _ ≤ F at hb
    linarith
  · have hb := movingSectionDensity_infinity_integral_bound R hR c hc0 hc
    change _ ≤ I at hb
    linarith

end SGPT.BBJ
