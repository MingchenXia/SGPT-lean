import SGPT.PSH.GlobalL2Statement
import SGPT.Foundations.Analysis.Pending.HormanderL2Theorem
import SGPT.Foundations.Analysis.Pending.OTWeakDbar
import SGPT.Foundations.Analysis.Pending.WeakDbarWeyl
import SGPT.Foundations.Analysis.Pending.OTChenExtension

/-!
# Local `L²` corrections on balls, smooth weights

Blueprint `claude-global-l2:local-smooth`.  `localBallCorrectionSmooth` proves
`LocalBallCorrectionSmoothStatement n`: on a ball `B(z₀, R) ⊆ ℂⁿ`, for a smooth weight `Φ` with
`Levi Φ ≥ c|ξ|²` and a smooth `a`, there is `G` holomorphic on `B(z₀, r)`, `r < R`, with
`∫_{B(z₀,r)} |a - G|² e^{-Φ} ≤ (2/c) ∫_{B(z₀,R)} |∂̄a|² e^{-Φ}`.

Proof: Hörmander's estimate on the bounded convex domain `B(z₀, R)`
(`SGPT.Foundations.Analysis.Pending.Hormander.hormanderL2Estimate`, with `t = 1` and the compact set
`closedBall z₀ r`) gives a weak solution `u` of `∂̄u = ∂̄a` on a convex `D' ⊇ closedBall z₀ r`;
Weyl's lemma (`exists_differentiableOn_ae_eq_of_weak_dbar`) makes `a - u` holomorphic; the shift
`lam₁ ≥ 0` of the weight vanishes near `closedBall z₀ r`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.PSH.GlobalL2

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.OTChen

variable {n : ℕ}

/-- The squared norm of `∑ ξ_j e_j` in `ℂⁿ`. -/
theorem norm_sum_smul_coordVec_sq (ξ : Fin n → ℂ) :
    ‖(∑ j, ξ j • coordVec j : ComplexModel n)‖ ^ 2 = ∑ j, ‖ξ j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun j _ => by rw [sum_smul_coordVec_apply]

/-- Cauchy--Schwarz: `|∑ conj ξ_j f_j|² ≤ |ξ|² ∑ |f_j|²`. -/
theorem norm_sum_conj_mul_sq_le (ξ f : Fin n → ℂ) :
    ‖∑ j, conj (ξ j) * f j‖ ^ 2 ≤
      ‖(∑ j, ξ j • coordVec j : ComplexModel n)‖ ^ 2 * ∑ j, ‖f j‖ ^ 2 := by
  rw [norm_sum_smul_coordVec_sq]
  have h1 : ‖∑ j, conj (ξ j) * f j‖ ≤ ∑ j, ‖ξ j‖ * ‖f j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [norm_mul, Complex.norm_conj]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖ξ j‖) (fun j => ‖f j‖)
  calc ‖∑ j, conj (ξ j) * f j‖ ^ 2 ≤ (∑ j, ‖ξ j‖ * ‖f j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

theorem dbarNormSq_nonneg (a : ComplexModel n → ℂ) (z : ComplexModel n) :
    0 ≤ dbarNormSq a z :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_dbarDir_sq_le_dbarNormSq (a : ComplexModel n → ℂ) (z : ComplexModel n) (j : Fin n) :
    ‖dbarDir (coordVec j) a z‖ ^ 2 ≤ dbarNormSq a z :=
  Finset.single_le_sum (f := fun j => ‖dbarDir (coordVec j) a z‖ ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ j)

theorem continuousOn_dbarNormSq {D : Set (ComplexModel n)} (hD : IsOpen D)
    {a : ComplexModel n → ℂ} (ha : ContDiffOn ℝ 1 a D) : ContinuousOn (dbarNormSq a) D := by
  unfold dbarNormSq
  exact continuousOn_finsetSum _ fun j _ =>
    ((continuousOn_dbarDir_of_contDiffOn hD ha (coordVec j)).norm).pow 2

/-- **Local `L²` correction on a ball, smooth weights** (`claude-global-l2:local-smooth`). -/
theorem localBallCorrectionSmooth : LocalBallCorrectionSmoothStatement n := by
  intro z₀ r R hr hrR c hc Φ hΦ hΦL a ha
  set D : Set (ComplexModel n) := ball z₀ R with hDdef
  set S : ℝ≥0∞ := ∫⁻ z in D, ENNReal.ofReal (dbarNormSq a z) * ENNReal.ofReal (Real.exp (-Φ z))
    with hSdef
  have h2c : (0 : ℝ) < 2 / c := by positivity
  by_cases hS : S = ⊤
  · refine ⟨fun _ => 0, differentiableOn_const 0, ?_⟩
    rw [hS, ENNReal.mul_top (ENNReal.ofReal_pos.mpr h2c).ne']
    exact le_top
  have hDo : IsOpen D := isOpen_ball
  obtain ⟨D', U, lam₁, lam₂, hD'o, -, hD'cl, -, hKU, hUD', hl₁, hl₂, hl, hl0, hest⟩ :=
    hormanderL2Estimate n D hDo (convex_ball z₀ R) isBounded_ball (closedBall z₀ r)
      (isCompact_closedBall z₀ r) (closedBall_subset_ball hrR) 1 one_pos
  have hD'D : D' ⊆ D := subset_closure.trans hD'cl
  have hD'm : MeasurableSet D' := hD'o.measurableSet
  have hDm : MeasurableSet D := hDo.measurableSet
  have hrD' : ball z₀ r ⊆ D' := ball_subset_closedBall.trans (hKU.trans hUD')
  have hrU : ball z₀ r ⊆ U := ball_subset_closedBall.trans hKU
  have ha1 : ContDiffOn ℝ 1 a D := ha.of_le (WithTop.coe_le_coe.mpr le_top)
  have ha1' : ContDiffOn ℝ 1 a D' := ha1.mono hD'D
  have hΦc : ContinuousOn Φ D := hΦ.continuousOn
  have hΦc' : ContinuousOn Φ D' := hΦc.mono hD'D
  -- the datum and its majorant
  set v : Fin n → ComplexModel n → ℂ := fun j => dbarDir (coordVec j) a with hvdef
  set g : ComplexModel n → ℝ := fun z => dbarNormSq a z / c with hgdef
  have hg0 : ∀ z, 0 ≤ g z := fun z => div_nonneg (dbarNormSq_nonneg a z) hc.le
  have hdNc : ContinuousOn (dbarNormSq a) D := continuousOn_dbarNormSq hDo ha1
  -- the basic integrable majorant `|∂̄a|² e^{-Φ}` on `D`
  have hmaj : IntegrableOn (fun z => dbarNormSq a z * Real.exp (-Φ z)) D := by
    refine ⟨(hdNc.mul hΦc.neg.rexp).aestronglyMeasurable hDm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
      mul_nonneg (dbarNormSq_nonneg a z) (Real.exp_pos _).le)]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_top_iff_ne_top.mpr hS)
    refine setLIntegral_congr_fun hDm fun z _ => ?_
    rw [ENNReal.ofReal_mul (dbarNormSq_nonneg a z)]
  have hmaj' : IntegrableOn (fun z => dbarNormSq a z * Real.exp (-Φ z)) D' := hmaj.mono_set hD'D
  have hweight_le : ∀ z ∈ D', ∀ l : ℝ, 0 ≤ l → Real.exp (-(Φ z + l)) ≤ Real.exp (-Φ z) :=
    fun z _ l hl0 => Real.exp_le_exp.mpr (by linarith)
  have hgle : ∀ z ∈ D', g z * Real.exp (-(Φ z + lam₁ z)) ≤
      c⁻¹ * (dbarNormSq a z * Real.exp (-Φ z)) := by
    intro z hz
    have hgz : g z = c⁻¹ * dbarNormSq a z := by rw [hgdef]; exact div_eq_inv_mul _ _
    rw [hgz, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (hweight_le z hz _ (hl z hz).1) (dbarNormSq_nonneg a z)) (inv_nonneg.mpr hc.le)
  have hvmem : ∀ j, MemLp (v j) 2 (weightedVolume D' fun z => Φ z + lam₂ z) := by
    intro j
    have hvc : ContinuousOn (v j) D' := continuousOn_dbarDir_of_contDiffOn hD'o ha1' (coordVec j)
    rw [memLp_weightedVolume_iff (w := fun z => Φ z + lam₂ z) ((hΦc'.add hl₂).aemeasurable hD'm)
      (hvc.aestronglyMeasurable hD'm)]
    refine hmaj'.mono' ((hvc.norm.pow 2).mul (hΦc'.add hl₂).neg.rexp
      |>.aestronglyMeasurable hD'm) ?_
    refine (ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (norm_dbarDir_sq_le_dbarNormSq a z j)
      (hweight_le z hz _ ((hl z hz).1.trans (hl z hz).2)) (Real.exp_pos _).le
      (dbarNormSq_nonneg a z)
  have hvclosed : WeakDbarClosed D' v := weakDbarClosed_of_contDiffOn hD'o ha1'
  have hglevi : ∀ z ∈ D', ∀ ξ : Fin n → ℂ,
      ‖∑ j, conj (ξ j) * v j z‖ ^ 2 ≤ g z * leviForm Φ z (∑ j, ξ j • coordVec j) := by
    intro z hz ξ
    refine (norm_sum_conj_mul_sq_le ξ (fun j => v j z)).trans ?_
    have hL := hΦL z (hD'D hz) (∑ j, ξ j • coordVec j)
    have hdn : ∑ j, ‖v j z‖ ^ 2 = dbarNormSq a z := rfl
    rw [hdn, hgdef]
    calc ‖(∑ j, ξ j • coordVec j : ComplexModel n)‖ ^ 2 * dbarNormSq a z
        = dbarNormSq a z / c * (c * ‖(∑ j, ξ j • coordVec j : ComplexModel n)‖ ^ 2) := by
          field_simp
      _ ≤ dbarNormSq a z / c * leviForm Φ z (∑ j, ξ j • coordVec j) :=
          mul_le_mul_of_nonneg_left hL (hg0 z)
  have hgint : Integrable (fun z => g z * Real.exp (-(Φ z + lam₁ z))) (volume.restrict D') := by
    refine (hmaj'.const_mul c⁻¹).mono' ((((hdNc.mono hD'D).div_const c).mul
      (hΦc'.add hl₁).neg.rexp).aestronglyMeasurable hD'm) ?_
    refine (ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 z) (Real.exp_pos _).le)]
    exact hgle z hz
  have hΦL0 : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm Φ z ξ := fun z hz ξ =>
    le_trans (by positivity) (hΦL z hz ξ)
  -- Hörmander's estimate
  obtain ⟨⟨u₀, hu₀mem, hu₀eq, hu₀orth⟩, hu₀est⟩ :=
    hest Φ hΦ hΦL0 v hvmem hvclosed g (fun z _ => hg0 z) hglevi hgint
  -- Weyl's lemma: `a - u₀` is holomorphic
  have hwc : ContinuousOn (fun z => Φ z + lam₁ z) D' := hΦc'.add hl₁
  have hu₀loc : LocallyIntegrableOn u₀ D' :=
    locallyIntegrableOn_of_memLp_weightedVolume hD'o hwc hu₀mem
  have haloc : LocallyIntegrableOn a D' := ha1'.continuousOn.locallyIntegrableOn hD'm
  have hFloc : LocallyIntegrableOn (fun z => a z - u₀ z) D' := haloc.sub hu₀loc
  have hcoord : ∀ h, IsTestFunctionOn D' h → ∀ j,
      ∫ z, (a z - u₀ z) * dbarDir (coordVec j) h z = 0 := by
    intro h hh j
    have hdc : Continuous (dbarDir (coordVec j) h) :=
      continuous_dbarDir' (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
    have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
    have hdts := (tsupport_dbarDir_subset (coordVec j) h).trans hh.2.2
    have i1 := integrable_mul_of_locallyIntegrableOn haloc hdc hdcs hdts
    have i2 := integrable_mul_of_locallyIntegrableOn hu₀loc hdc hdcs hdts
    simp only [sub_mul]
    rw [integral_sub i1 i2, hu₀eq h hh j]
    have := weakDbarEq_of_contDiffOn hD'o ha1' h hh j
    rw [this]
    ring
  obtain ⟨G, hG, hGae⟩ := exists_differentiableOn_ae_eq_of_weak_dbar hD'o hFloc
    (integral_mul_dbarDir_eq_zero_of_coord hFloc hcoord)
  have hae : (fun z => a z - G z) =ᵐ[volume.restrict D'] u₀ := by
    filter_upwards [hGae] with z hz
    rw [← hz]; ring
  have hmem : MemLp (fun z => a z - G z) 2 (weightedVolume D' fun z => Φ z + lam₁ z) :=
    hu₀mem.ae_eq ((withDensity_absolutelyContinuous _ _).ae_eq hae.symm)
  have hw₁m : AEMeasurable (fun z => Φ z + lam₁ z) (volume.restrict D') := hwc.aemeasurable hD'm
  have hint : Integrable (fun z => ‖a z - G z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z)))
      (volume.restrict D') := integrable_of_memLp_weightedVolume hw₁m hmem
  have hfinal := hu₀est u₀ hu₀mem hu₀eq hu₀orth
  have heq : ∫ z in D', ‖a z - G z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z)) =
      ∫ z in D', ‖u₀ z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z)) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]
  have hreal : ∫ z in D', ‖a z - G z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z)) ≤
      (2 / c) * ∫ z in D', dbarNormSq a z * Real.exp (-Φ z) := by
    refine (heq.le.trans hfinal).trans ?_
    rw [show (1 : ℝ) + 1 = 2 by norm_num, show (2 / c) = 2 * c⁻¹ by ring, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun z =>
      mul_nonneg (hg0 z) (Real.exp_pos _).le) (hmaj'.const_mul c⁻¹) ?_
    exact (ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun z hz => hgle z hz)
  refine ⟨G, hG.mono hrD', ?_⟩
  -- back to lower integrals
  calc ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ENNReal.ofReal (Real.exp (-Φ z))
      = ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - G z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z))) := by
        refine setLIntegral_congr_fun isOpen_ball.measurableSet fun z hz => ?_
        rw [(hl0 z (hrU hz)).1, add_zero, ENNReal.ofReal_mul (sq_nonneg _)]
    _ ≤ ∫⁻ z in D', ENNReal.ofReal (‖a z - G z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z))) :=
        lintegral_mono_set hrD'
    _ = ENNReal.ofReal (∫ z in D', ‖a z - G z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z))) :=
        (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z =>
          mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)).symm
    _ ≤ ENNReal.ofReal ((2 / c) * ∫ z in D', dbarNormSq a z * Real.exp (-Φ z)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (2 / c) *
          ∫⁻ z in D', ENNReal.ofReal (dbarNormSq a z * Real.exp (-Φ z)) := by
        rw [ENNReal.ofReal_mul h2c.le, ofReal_integral_eq_lintegral_ofReal hmaj'
          (Eventually.of_forall fun z => mul_nonneg (dbarNormSq_nonneg a z) (Real.exp_pos _).le)]
    _ ≤ ENNReal.ofReal (2 / c) *
          ∫⁻ z in D, ENNReal.ofReal (dbarNormSq a z * Real.exp (-Φ z)) :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set hD'D) zero_le
    _ = ENNReal.ofReal (2 / c) * S := by
        congr 1
        refine setLIntegral_congr_fun hDm fun z _ => ?_
        rw [ENNReal.ofReal_mul (dbarNormSq_nonneg a z)]

end SGPT.PSH.GlobalL2
