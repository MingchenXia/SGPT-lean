import SGPT.PSH.SourcePlurifineNonBorelKernel

/-! The same actual probability average is finite at its chosen Cantor point,
and has poles at all other actual Cantor points. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceNonBorelDraft
open Set Filter MeasureTheory Metric TopologicalSpace SGPT.BBJ SGPT.Toric
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ENNReal Classical
local notation "Bits" => ℕ → Bool

lemma kernel_at_code (a b : Bits) :
    kernel a b (code a) = (weight a b : EReal) *
      (logNormSq ((cantorCode a-cantorCode b : ℝ) : ℂ)
        -(Real.log (1+cantorCode b^2) : EReal)) := by
  unfold kernel
  rw [movingProjectiveSectionPotential_corrected_chart]
  simp only [Bool.false_eq_true, if_false, code, projectiveModelEquiv_apply_zero,
    ← Complex.ofReal_sub]

lemma kernel_self_deficit_bound (a b : Bits) :
    ((Real.log 2 : EReal)-kernel a b (code a)).toENNReal ≤ ENNReal.ofReal 3 := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  by_cases he : a = b
  · subst b
    simp only [kernel, weight, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      EReal.coe_zero, zero_mul, sub_zero, EReal.real_coe_toENNReal]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hw := weight_bounds a b
  have hwpos := weight_pos he
  have hz : ((cantorCode a-cantorCode b : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (fun h => he (cantorCode_injective h)))
  rw [kernel_at_code, logNormSq_of_ne_zero hz]
  have hnorm : ‖((cantorCode a-cantorCode b : ℝ) : ℂ)‖^2 = weight a b := by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, weight]
  rw [hnorm, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_sub,
    EReal.real_coe_toENNReal]
  apply ENNReal.ofReal_le_ofReal
  have hs := Real.abs_log_mul_self_lt (weight a b) hwpos hw.2
  have hblog : Real.log (1+cantorCode b^2) ≤ 1 := by
    have hb := cantorCode_lt_half b
    have hb0 := cantorCode_nonneg b
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+cantorCode b^2)
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hblog hw.1
  have hlow := (abs_lt.mp hs).1
  nlinarith

lemma separator_ne_bot_at_code (a : Bits) : separator a (code a) ≠ ⊥ := by
  have hI := lintegral_mono (μ := cantorBitProbability) (kernel_self_deficit_bound a)
  rw [lintegral_const, measure_univ, mul_one] at hI
  have hfin : (∫⁻ b, ((Real.log 2 : EReal)-kernel a b (code a)).toENNReal
      ∂cantorBitProbability) ≠ ⊤ := ne_of_lt (hI.trans_lt ENNReal.ofReal_lt_top)
  unfold separator probabilityPshAverage
  rw [← EReal.coe_ennreal_toReal hfin, ← EReal.coe_sub]
  exact EReal.coe_ne_bot _

lemma weight_lower_on_cylinder {a d b : Bits} {n : ℕ}
    (hn : 2*cantorCoefficient n ≤ |cantorCode a-cantorCode d|/2)
    (hb : b ∈ cantorCylinder (Finset.range n) d) :
    weight a d/4 ≤ weight a b := by
  have hclose := (cantorCode_cylinder_abs_lt b d n hb).le.trans hn
  have htri := abs_sub_le (cantorCode a) (cantorCode b) (cantorCode d)
  rw [abs_sub_comm (cantorCode b) (cantorCode d)] at htri
  have habs : |cantorCode a-cantorCode d|/2 ≤ |cantorCode a-cantorCode b| := by
    linarith
  have hs := sq_le_sq₀ (by positivity : 0 ≤ |cantorCode a-cantorCode d|/2)
    (abs_nonneg (cantorCode a-cantorCode b)) |>.mpr habs
  dsimp [weight]
  nlinarith [sq_abs (cantorCode a-cantorCode d), sq_abs (cantorCode a-cantorCode b)]

lemma kernel_other_cylinder_upper {a d b : Bits} {n : ℕ}
    (hn : 2*cantorCoefficient n ≤ |cantorCode a-cantorCode d|/2)
    (hb : b ∈ cantorCylinder (Finset.range n) d) :
    kernel a b (code d) ≤
      ((-(weight a d/8)*((16 : ℝ)^(n+1)*Real.log 2) : ℝ) : EReal) := by
  let A : ℝ := (16 : ℝ)^(n+1)*Real.log 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have htwo : (2 : ℝ) ≤ (16 : ℝ)^(n+1) := by
    exact le_trans (by norm_num : (2 : ℝ) ≤ 16)
      (by exact_mod_cast (Nat.le_pow (Nat.succ_pos n) : 16 ≤ 16^(n+1)))
  have hρ : projectiveFSPotential (code d) ≤ Real.log 2 := by
    rw [projectiveFSPotential_eq, code, projectiveModelEquiv_apply_zero,
      Complex.normSq_ofReal]
    exact Real.log_le_log (by nlinarith [sq_nonneg (cantorCode d)]) (by
      have h0 := cantorCode_nonneg d
      have h1 := cantorCode_lt_half d
      nlinarith)
  have hraw := add_le_add (movingProjectiveSectionPotential_matching_cylinder b d n hb)
    (EReal.coe_le_coe_iff.mpr hρ)
  rw [← code_chart d, ← EReal.coe_add] at hraw
  have hhalf : -(16 : ℝ)^(n+1)*Real.log 2+Real.log 2 ≤ -A/2 := by
    dsimp [A]
    nlinarith [mul_nonneg (sub_nonneg.mpr htwo) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
  have hs := mul_le_mul_of_nonneg_left (hraw.trans (EReal.coe_le_coe_iff.mpr hhalf))
    (EReal.coe_nonneg.mpr (weight_bounds a b).1)
  change kernel a b (code d) ≤ _ at hs
  apply hs.trans
  rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
  have hw := weight_lower_on_cylinder hn hb
  have hp := mul_le_mul_of_nonpos_right hw (by linarith : -A/2 ≤ 0)
  dsimp only [A] at hp ⊢
  nlinarith

end SGPT.PSH.SourceNonBorelDraft
