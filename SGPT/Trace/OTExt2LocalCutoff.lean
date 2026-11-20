import SGPT.Trace.OTExt2LocalModel
import SGPT.Trace.OTMarginFlat
import SGPT.Trace.TwistedL2OTExtCurvature
import SGPT.Okounkov.TranscendentalPoleExtension

/-!
# A complete Kähler metric on `D \ {w = 0}`

Blueprint `claude-ot-ext2.tex`, node `claude-ot-ext2:complete-cutoffs`.  Xia, *Foundations of
pluripotential theory*, proof of `lem:local-critical-gain-extension`, paragraph *Complete cutoffs*.

In `ℂⁿ = ℂ^m × ℂ^{n-m}` (`z = (z', w)`, `|z'|² = tanWeight n m z`, `|w|² = normalWeight n m z`) let
`D = {|z'| < r', |w| < r''}` with `r'' < e^{-2}` and `U = D \ {w = 0}`.  With
`g₁ = r'² - |z'|²`, `g₂ = r''² - |w|²`, `g₃ = -log |w|²` (all positive on `U`, `-ddᶜ gᵢ ≥ 0`) the
function `τ = -log g₁ - log g₂ - log g₃` (`kahlerPot`) satisfies
`Levi(τ)(v) ≥ ∑ |∂ log gᵢ(v)|²`, so `σ = β + ddᶜ τ ≥ β` is Kähler, and the exhaustion
`E = -log g₁ - log g₂ + log g₃` (FPT's `τ₀ - τ₁`) has `|dE(v)|² ≤ 12 Levi(τ)(v)` and compact
sublevel sets in `U`.  The functions `χ_k = λ(E / (2(k + 1)))` are complete cut-offs for `σ`
(`hasCompleteCutoffs_kahlerPot`).

## Main results

* `normalCLM`, `tangCLM`, `normalWeight_eq_norm_sq`, `tanWeight`: the two projections;
* `leviForm_normSq_clm`, `holDerivSq_normSq_clm_le`, `leviForm_log_normSq_clm_nonneg`: the Levi
  calculus of `|L z|²` and `log |L z|²` for `ℂ`-linear `L`;
* `holDerivSq_log_le_leviForm_neg_log`: `|∂ log g|² ≤ Levi(-log g)` when `Levi(g) ≤ 0`;
* `localDom`, `localPunct`, `kahlerPot`, `exhaust`, `localCutoff`;
* `hasCompleteCutoffs_kahlerPot`, `leviForm_kahlerPot_nonneg`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Trace.OTExt2

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.Trace.TwistedL2
open SGPT.Trace.OTMargin (normalWeight normalWeight_nonneg)

variable {n : ℕ}

/-! ### The Levi calculus of `|L z|²` -/

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2

section NormSq

variable (L : ComplexModel n →L[ℂ] ComplexModel n)

theorem contDiff_normSq_clm : ContDiff ℝ ∞ (fun z => ‖L z‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (L.restrictScalars ℝ).contDiff

theorem fderiv_normSq_clm (x v : ComplexModel n) :
    fderiv ℝ (fun z => ‖L z‖ ^ 2) x v = 2 * inner ℝ (L x) (L v) := by
  have h : HasFDerivAt (fun z => ‖L z‖ ^ 2)
      ((2 • innerSL ℝ (L x)).comp (L.restrictScalars ℝ)) x :=
    (hasStrictFDerivAt_norm_sq (L x)).hasFDerivAt.comp x (L.restrictScalars ℝ).hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', _root_.smul_apply, innerSL_apply_apply,
    nsmul_eq_mul, Nat.cast_ofNat]

theorem leviForm_normSq_clm (x v : ComplexModel n) :
    leviForm (fun z => ‖L z‖ ^ 2) x v = ‖L v‖ ^ 2 := by
  have hu : ContDiff ℝ 2 (fun y : ComplexModel n => ‖y‖ ^ 2) :=
    (contDiff_norm_sq ℝ).of_le two_le_infty
  have h := fun a b => realHessian_comp_affine hu (L.restrictScalars ℝ) 0 x a b
  simp only [zero_add, ContinuousLinearMap.coe_restrictScalars'] at h
  rw [leviForm, h, h, realHessian_norm_sq, realHessian_norm_sq, map_smul,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_smul, Complex.norm_I, one_mul]
  ring

theorem holDerivSq_normSq_clm_le (x v : ComplexModel n) :
    holDerivSq (fun z => ‖L z‖ ^ 2) x v ≤ ‖L x‖ ^ 2 * ‖L v‖ ^ 2 := by
  unfold holDerivSq
  rw [fderiv_normSq_clm, fderiv_normSq_clm, map_smul]
  set a := L x
  set b := L v
  have h1 : inner ℝ a b = (inner ℂ a b).re := by
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.inner]
    simp [RCLike.inner_apply]
  have h2 : inner ℝ a (Complex.I • b) = -(inner ℂ a b).im := by
    rw [PiLp.inner_apply, PiLp.inner_apply, Complex.im_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.inner]
    simp [RCLike.inner_apply]
  have h3 : ‖inner ℂ a b‖ ^ 2 = (inner ℂ a b).re ^ 2 + (inner ℂ a b).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h4 : ‖inner ℂ a b‖ ≤ ‖a‖ * ‖b‖ := norm_inner_le_norm a b
  have h5 : ‖inner ℂ a b‖ ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h4 2
  rw [h1, h2]
  nlinarith

theorem leviForm_log_normSq_clm_nonneg {x : ComplexModel n} (hx : 0 < ‖L x‖ ^ 2)
    (v : ComplexModel n) : 0 ≤ leviForm (fun z => Real.log (‖L z‖ ^ 2)) x v := by
  have hS : ContDiffAt ℝ 2 (fun z => ‖L z‖ ^ 2) x :=
    ((contDiff_normSq_clm L).of_le two_le_infty).contDiffAt
  rw [ConcentrationPotentialLevi.leviForm_log_of_pos hS hx v, leviForm_normSq_clm]
  have hle := holDerivSq_normSq_clm_le L x v
  unfold holDerivSq at hle
  rw [sub_nonneg, div_le_div_iff₀ (by positivity) hx]
  nlinarith [sq_nonneg (‖L x‖ ^ 2)]

end NormSq

/-! ### The two projections -/

/-- `z = (z', w) ↦ (0, w)`. -/
def normalCLM (n m : ℕ) : ComplexModel n →L[ℂ] ComplexModel n :=
  ContinuousLinearMap.id ℂ _ - (coordinateInclusion n m).comp (coordinateProjection n m)

/-- `z = (z', w) ↦ (z', 0)`. -/
def tangCLM (n m : ℕ) : ComplexModel n →L[ℂ] ComplexModel n :=
  (coordinateInclusion n m).comp (coordinateProjection n m)

theorem normalCLM_apply (m : ℕ) (z : ComplexModel n) (i : Fin n) :
    normalCLM n m z i = if m ≤ i.1 then z i else 0 := by
  have := SGPT.Okounkov.TranscendentalPole.normalPart_apply m z i
  rw [← this]
  rfl

theorem tangCLM_apply (m : ℕ) (z : ComplexModel n) (i : Fin n) :
    tangCLM n m z i = if i.1 < m then z i else 0 := by
  have h := normalCLM_apply m z i
  have h2 : tangCLM n m z = z - normalCLM n m z := by
    simp [tangCLM, normalCLM]
  rw [h2, PiLp.sub_apply, h]
  by_cases hi : m ≤ i.1
  · rw [if_pos hi, if_neg (by omega), sub_self]
  · rw [if_neg hi, if_pos (by omega), sub_zero]

theorem normalWeight_eq_norm_sq (m : ℕ) (z : ComplexModel n) :
    normalWeight n m z = ‖normalCLM n m z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, normalWeight]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [normalCLM_apply]
  split_ifs <;> simp

/-- `|z'|² = ∑_{i < m} |z_i|²`. -/
def tanWeight (n m : ℕ) (z : ComplexModel n) : ℝ := ‖tangCLM n m z‖ ^ 2

theorem tanWeight_nonneg (m : ℕ) (z : ComplexModel n) : 0 ≤ tanWeight n m z := by
  unfold tanWeight; positivity

theorem tanWeight_eq_sum (m : ℕ) (z : ComplexModel n) :
    tanWeight n m z = ∑ i : Fin n, if i.1 < m then ‖z i‖ ^ 2 else 0 := by
  rw [tanWeight, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tangCLM_apply]
  split_ifs <;> simp

theorem tanWeight_add_normalWeight (m : ℕ) (z : ComplexModel n) :
    tanWeight n m z + normalWeight n m z = ‖z‖ ^ 2 := by
  rw [tanWeight_eq_sum, normalWeight, ← Finset.sum_add_distrib, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.1 < m
  · rw [if_pos hi, if_neg (by omega), add_zero]
  · rw [if_neg hi, if_pos (by omega), zero_add]

theorem tanWeight_eq_norm_proj {m : ℕ} (hmn : m ≤ n) (z : ComplexModel n) :
    tanWeight n m z = ‖coordinateProjection n m z‖ ^ 2 := by
  rw [tanWeight_eq_sum, EuclideanSpace.norm_sq_eq]
  have : ∀ a : Fin m, ‖coordinateProjection n m z a‖ ^ 2 =
      ‖z ⟨a.1, lt_of_lt_of_le a.2 hmn⟩‖ ^ 2 := fun a => by
    rw [coordinateProjection_apply, dif_pos (lt_of_lt_of_le a.2 hmn)]
  simp only [this]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i hi => ⟨i.1, (Finset.mem_filter.mp hi).2⟩) (by simp)
    (fun i hi j hj h => Fin.ext (by simpa using congrArg Fin.val h))
    (fun a _ => ⟨⟨a.1, lt_of_lt_of_le a.2 hmn⟩, by simp, rfl⟩) (fun i _ => rfl)

theorem continuous_normalWeight (m : ℕ) : Continuous (normalWeight n m) := by
  have : normalWeight n m = fun z => ‖normalCLM n m z‖ ^ 2 :=
    funext (normalWeight_eq_norm_sq m)
  rw [this]
  exact (contDiff_normSq_clm _).continuous

theorem continuous_tanWeight (m : ℕ) : Continuous (tanWeight n m) :=
  (contDiff_normSq_clm _).continuous

theorem contDiff_normalWeight (m : ℕ) : ContDiff ℝ ∞ (normalWeight n m) := by
  have : normalWeight n m = fun z => ‖normalCLM n m z‖ ^ 2 :=
    funext (normalWeight_eq_norm_sq m)
  rw [this]
  exact contDiff_normSq_clm _

theorem contDiff_tanWeight (m : ℕ) : ContDiff ℝ ∞ (tanWeight n m) := contDiff_normSq_clm _

theorem leviForm_normalWeight (m : ℕ) (x v : ComplexModel n) :
    leviForm (normalWeight n m) x v = normalWeight n m v := by
  have : normalWeight n m = fun z => ‖normalCLM n m z‖ ^ 2 :=
    funext (normalWeight_eq_norm_sq m)
  rw [this, leviForm_normSq_clm]

theorem leviForm_tanWeight (m : ℕ) (x v : ComplexModel n) :
    leviForm (tanWeight n m) x v = tanWeight n m v :=
  leviForm_normSq_clm _ x v

theorem holDerivSq_normalWeight_le (m : ℕ) (x v : ComplexModel n) :
    holDerivSq (normalWeight n m) x v ≤ normalWeight n m x * normalWeight n m v := by
  have : normalWeight n m = fun z => ‖normalCLM n m z‖ ^ 2 :=
    funext (normalWeight_eq_norm_sq m)
  rw [this]
  exact holDerivSq_normSq_clm_le _ x v

theorem leviForm_log_normalWeight_nonneg (m : ℕ) {x : ComplexModel n}
    (hx : 0 < normalWeight n m x) (v : ComplexModel n) :
    0 ≤ leviForm (fun z => Real.log (normalWeight n m z)) x v := by
  have : (fun z => Real.log (normalWeight n m z)) = fun z => Real.log (‖normalCLM n m z‖ ^ 2) :=
    funext fun z => by rw [normalWeight_eq_norm_sq]
  rw [this]
  rw [normalWeight_eq_norm_sq] at hx
  exact leviForm_log_normSq_clm_nonneg _ hx v

theorem normalWeight_le_norm_sq' (m : ℕ) (v : ComplexModel n) : normalWeight n m v ≤ ‖v‖ ^ 2 := by
  have := tanWeight_add_normalWeight m v
  have := tanWeight_nonneg m v
  linarith

/-! ### Logarithms of functions with nonpositive Levi form -/

theorem fderiv_sq_le_four_holDerivSq (f : ComplexModel n → ℝ) (z v : ComplexModel n) :
    fderiv ℝ f z v ^ 2 ≤ 4 * holDerivSq f z v := by
  unfold holDerivSq
  nlinarith [sq_nonneg (fderiv ℝ f z (Complex.I • v))]

/-- `|∂ log g|² ≤ Levi(-log g)` where `g > 0` and `Levi(g) ≤ 0`. -/
theorem holDerivSq_log_le_leviForm_neg_log {g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hg : ContDiffAt ℝ 2 g z) (hpos : 0 < g z) (v : ComplexModel n)
    (hL : leviForm g z v ≤ 0) :
    holDerivSq (fun y => Real.log (g y)) z v ≤ leviForm (fun y => -Real.log (g y)) z v := by
  have hneg : (fun y => -Real.log (g y)) = -(fun y => Real.log (g y)) := rfl
  rw [hneg, leviForm_neg, ConcentrationPotentialLevi.leviForm_log_of_pos hg hpos v,
    holDerivSq_comp (Real.differentiableAt_log hpos.ne') (hg.differentiableAt (by norm_num)) v,
    Real.deriv_log]
  unfold holDerivSq
  have h1 : 0 ≤ -(leviForm g z v / g z) := by
    rw [neg_nonneg]; exact div_nonpos_of_nonpos_of_nonneg hL hpos.le
  have h2 : (g z)⁻¹ ^ 2 * ((fderiv ℝ g z v ^ 2 + fderiv ℝ g z (Complex.I • v) ^ 2) / 4) =
      (fderiv ℝ g z v ^ 2 + fderiv ℝ g z (Complex.I • v) ^ 2) / (4 * g z ^ 2) := by
    field_simp
  rw [h2]
  linarith

/-! ### The domain and the complete metric -/

/-- The product of balls `D = {|z'| < r', |w| < r''}`. -/
def localDom (n m : ℕ) (r' r'' : ℝ) : Set (ComplexModel n) :=
  {z | tanWeight n m z < r' ^ 2 ∧ normalWeight n m z < r'' ^ 2}

/-- `U = D \ {w = 0}`. -/
def localPunct (n m : ℕ) (r' r'' : ℝ) : Set (ComplexModel n) :=
  {z | tanWeight n m z < r' ^ 2 ∧ normalWeight n m z < r'' ^ 2 ∧ 0 < normalWeight n m z}

theorem isOpen_localDom (m : ℕ) (r' r'' : ℝ) : IsOpen (localDom n m r' r'') :=
  (isOpen_lt (continuous_tanWeight m) continuous_const).inter
    (isOpen_lt (continuous_normalWeight m) continuous_const)

theorem isOpen_localPunct (m : ℕ) (r' r'' : ℝ) : IsOpen (localPunct n m r' r'') :=
  (isOpen_lt (continuous_tanWeight m) continuous_const).inter
    ((isOpen_lt (continuous_normalWeight m) continuous_const).inter
      (isOpen_lt continuous_const (continuous_normalWeight m)))

theorem localPunct_subset (m : ℕ) (r' r'' : ℝ) : localPunct n m r' r'' ⊆ localDom n m r' r'' :=
  fun _ hz => ⟨hz.1, hz.2.1⟩

theorem localPunct_eq (m : ℕ) (r' r'' : ℝ) :
    localPunct n m r' r'' = localDom n m r' r'' \ {z | normalWeight n m z = 0} := by
  ext z
  simp only [localPunct, localDom, Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3.ne'⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, lt_of_le_of_ne (normalWeight_nonneg n m z) (Ne.symm h3)⟩

/-- `g₁ = r'² - |z'|²`. -/
def gTan (n m : ℕ) (r' : ℝ) (z : ComplexModel n) : ℝ := r' ^ 2 - tanWeight n m z

/-- `g₂ = r''² - |w|²`. -/
def gNor (n m : ℕ) (r'' : ℝ) (z : ComplexModel n) : ℝ := r'' ^ 2 - normalWeight n m z

/-- `g₃ = -log |w|²`. -/
def gLog (n m : ℕ) (z : ComplexModel n) : ℝ := -Real.log (normalWeight n m z)

/-- `τ = -log g₁ - log g₂ - log g₃` (FPT `τ₀ + τ₁`). -/
def kahlerPot (n m : ℕ) (r' r'' : ℝ) (z : ComplexModel n) : ℝ :=
  -Real.log (gTan n m r' z) + -Real.log (gNor n m r'' z) + -Real.log (gLog n m z)

/-- The exhaustion `E = -log g₁ - log g₂ + log g₃` (FPT `τ₀ - τ₁`). -/
def exhaust (n m : ℕ) (r' r'' : ℝ) (z : ComplexModel n) : ℝ :=
  -Real.log (gTan n m r' z) + -Real.log (gNor n m r'' z) + Real.log (gLog n m z)

variable {m : ℕ} {r' r'' : ℝ}

theorem gTan_pos {z : ComplexModel n} (hz : z ∈ localPunct n m r' r'') : 0 < gTan n m r' z := by
  unfold gTan; linarith [hz.1]

theorem gNor_pos {z : ComplexModel n} (hz : z ∈ localPunct n m r' r'') :
    0 < gNor n m r'' z := by
  unfold gNor; linarith [hz.2.1]

theorem sq_lt_exp_neg_four {r'' : ℝ} (h0 : 0 < r'') (h : r'' < Real.exp (-2)) :
    r'' ^ 2 < Real.exp (-4) := by
  have h2 : r'' ^ 2 < Real.exp (-2) ^ 2 := pow_lt_pow_left₀ h h0.le two_ne_zero
  rw [← Real.exp_nat_mul] at h2
  norm_num at h2
  exact h2

theorem four_lt_gLog (hr'' : r'' ^ 2 < Real.exp (-4)) {z : ComplexModel n}
    (hz : z ∈ localPunct n m r' r'') : 4 < gLog n m z := by
  unfold gLog
  have h0 : 0 < normalWeight n m z := hz.2.2
  have h1 : normalWeight n m z < Real.exp (-4) := by linarith [hz.2.1]
  have := Real.log_lt_log h0 h1
  rw [Real.log_exp] at this
  linarith

theorem gLog_pos (hr'' : r'' ^ 2 < Real.exp (-4)) {z : ComplexModel n}
    (hz : z ∈ localPunct n m r' r'') : 0 < gLog n m z := by
  linarith [four_lt_gLog hr'' hz]

theorem contDiff_gTan : ContDiff ℝ ∞ (gTan n m r') := contDiff_const.sub (contDiff_tanWeight m)

theorem contDiff_gNor : ContDiff ℝ ∞ (gNor n m r'') := contDiff_const.sub (contDiff_normalWeight m)

theorem contDiffAt_gLog {z : ComplexModel n} (hz : 0 < normalWeight n m z) :
    ContDiffAt ℝ ∞ (gLog n m) z :=
  ((contDiff_normalWeight m).contDiffAt.log hz.ne').neg

theorem contDiffOn_kahlerPot (hr'' : r'' ^ 2 < Real.exp (-4)) :
    ContDiffOn ℝ ∞ (kahlerPot n m r' r'') (localPunct n m r' r'') := by
  intro z hz
  refine ContDiffAt.contDiffWithinAt ?_
  exact ((contDiff_gTan.contDiffAt.log (gTan_pos hz).ne').neg.add
    (contDiff_gNor.contDiffAt.log (gNor_pos hz).ne').neg).add
    ((contDiffAt_gLog hz.2.2).log (gLog_pos hr'' hz).ne').neg

theorem contDiffAt_exhaust (hr'' : r'' ^ 2 < Real.exp (-4)) {z : ComplexModel n}
    (hz : z ∈ localPunct n m r' r'') : ContDiffAt ℝ ∞ (exhaust n m r' r'') z :=
  ((contDiff_gTan.contDiffAt.log (gTan_pos hz).ne').neg.add
    (contDiff_gNor.contDiffAt.log (gNor_pos hz).ne').neg).add
    ((contDiffAt_gLog hz.2.2).log (gLog_pos hr'' hz).ne')

theorem leviForm_gTan_nonpos (z v : ComplexModel n) : leviForm (gTan n m r') z v ≤ 0 := by
  have : gTan n m r' = (fun _ => r' ^ 2) + -tanWeight n m := by
    funext y; simp [gTan, sub_eq_add_neg]
  have hc : ContDiffAt ℝ 2 (-tanWeight n m) z :=
    ((contDiff_tanWeight m).contDiffAt.neg.of_le two_le_infty : _)
  rw [this, leviForm_add (u := fun _ => r' ^ 2) contDiffAt_const hc, leviForm_const, leviForm_neg,
    leviForm_tanWeight]
  linarith [tanWeight_nonneg m v]

theorem leviForm_gNor_nonpos (z v : ComplexModel n) : leviForm (gNor n m r'') z v ≤ 0 := by
  have : gNor n m r'' = (fun _ => r'' ^ 2) + -normalWeight n m := by
    funext y; simp [gNor, sub_eq_add_neg]
  have hc : ContDiffAt ℝ 2 (-normalWeight n m) z :=
    ((contDiff_normalWeight m).contDiffAt.neg.of_le two_le_infty : _)
  rw [this, leviForm_add (u := fun _ => r'' ^ 2) contDiffAt_const hc, leviForm_const,
    leviForm_neg, leviForm_normalWeight]
  linarith [normalWeight_nonneg n m v]

theorem leviForm_gLog_nonpos {z : ComplexModel n} (hz : 0 < normalWeight n m z)
    (v : ComplexModel n) : leviForm (gLog n m) z v ≤ 0 := by
  have : gLog n m = -(fun y => Real.log (normalWeight n m y)) := rfl
  rw [this, leviForm_neg]
  linarith [leviForm_log_normalWeight_nonneg m hz v]

/-- `Levi(τ)(v) ≥ ∑ |∂ log gᵢ(v)|²`. -/
theorem sum_holDerivSq_le_leviForm_kahlerPot (hr'' : r'' ^ 2 < Real.exp (-4)) {z : ComplexModel n}
    (hz : z ∈ localPunct n m r' r'') (v : ComplexModel n) :
    holDerivSq (fun y => Real.log (gTan n m r' y)) z v +
        holDerivSq (fun y => Real.log (gNor n m r'' y)) z v +
          holDerivSq (fun y => Real.log (gLog n m y)) z v ≤
      leviForm (kahlerPot n m r' r'') z v := by
  have h1T : ContDiffAt ℝ 2 (gTan n m r') z :=
    contDiff_gTan.contDiffAt.of_le two_le_infty
  have h1N : ContDiffAt ℝ 2 (gNor n m r'') z :=
    contDiff_gNor.contDiffAt.of_le two_le_infty
  have h1L : ContDiffAt ℝ 2 (gLog n m) z :=
    (contDiffAt_gLog hz.2.2).of_le two_le_infty
  have hT := holDerivSq_log_le_leviForm_neg_log h1T (gTan_pos hz) v (leviForm_gTan_nonpos z v)
  have hN := holDerivSq_log_le_leviForm_neg_log h1N (gNor_pos hz) v (leviForm_gNor_nonpos z v)
  have hL := holDerivSq_log_le_leviForm_neg_log h1L (gLog_pos hr'' hz) v
    (leviForm_gLog_nonpos hz.2.2 v)
  have e1 : ContDiffAt ℝ 2 (fun y => -Real.log (gTan n m r' y)) z := (h1T.log (gTan_pos hz).ne').neg
  have e2 : ContDiffAt ℝ 2 (fun y => -Real.log (gNor n m r'' y)) z :=
    (h1N.log (gNor_pos hz).ne').neg
  have e3 : ContDiffAt ℝ 2 (fun y => -Real.log (gLog n m y)) z :=
    (h1L.log (gLog_pos hr'' hz).ne').neg
  have hsplit : kahlerPot n m r' r'' = ((fun y => -Real.log (gTan n m r' y)) +
      fun y => -Real.log (gNor n m r'' y)) + fun y => -Real.log (gLog n m y) := rfl
  rw [hsplit, leviForm_add (u := (fun y => -Real.log (gTan n m r' y)) +
      fun y => -Real.log (gNor n m r'' y)) (e1.add e2) e3, leviForm_add e1 e2]
  linarith

theorem leviForm_kahlerPot_nonneg (hr'' : r'' ^ 2 < Real.exp (-4)) {z : ComplexModel n}
    (hz : z ∈ localPunct n m r' r'') (v : ComplexModel n) :
    0 ≤ leviForm (kahlerPot n m r' r'') z v := by
  refine le_trans ?_ (sum_holDerivSq_le_leviForm_kahlerPot hr'' hz v)
  have := holDerivSq_nonneg (fun y => Real.log (gTan n m r' y)) z v
  have := holDerivSq_nonneg (fun y => Real.log (gNor n m r'' y)) z v
  have := holDerivSq_nonneg (fun y => Real.log (gLog n m y)) z v
  linarith

/-- `|dE(v)|² ≤ 12 Levi(τ)(v)`. -/
theorem fderiv_exhaust_sq_le (hr'' : r'' ^ 2 < Real.exp (-4)) {z : ComplexModel n}
    (hz : z ∈ localPunct n m r' r'') (v : ComplexModel n) :
    fderiv ℝ (exhaust n m r' r'') z v ^ 2 ≤ 12 * leviForm (kahlerPot n m r' r'') z v := by
  have d1 : DifferentiableAt ℝ (fun y => Real.log (gTan n m r' y)) z :=
    (contDiff_gTan.contDiffAt.log (gTan_pos hz).ne').differentiableAt (by simp)
  have d2 : DifferentiableAt ℝ (fun y => Real.log (gNor n m r'' y)) z :=
    (contDiff_gNor.contDiffAt.log (gNor_pos hz).ne').differentiableAt (by simp)
  have d3 : DifferentiableAt ℝ (fun y => Real.log (gLog n m y)) z :=
    ((contDiffAt_gLog hz.2.2).log (gLog_pos hr'' hz).ne').differentiableAt (by simp)
  have hsplit : exhaust n m r' r'' = ((-fun y => Real.log (gTan n m r' y)) +
      -fun y => Real.log (gNor n m r'' y)) + fun y => Real.log (gLog n m y) := rfl
  rw [hsplit, fderiv_add (d1.neg.add d2.neg) d3, fderiv_add d1.neg d2.neg, fderiv_neg, fderiv_neg]
  simp only [_root_.add_apply, _root_.neg_apply]
  have h1 := fderiv_sq_le_four_holDerivSq (fun y => Real.log (gTan n m r' y)) z v
  have h2 := fderiv_sq_le_four_holDerivSq (fun y => Real.log (gNor n m r'' y)) z v
  have h3 := fderiv_sq_le_four_holDerivSq (fun y => Real.log (gLog n m y)) z v
  have hs := sum_holDerivSq_le_leviForm_kahlerPot hr'' hz v
  set a := fderiv ℝ (fun y => Real.log (gTan n m r' y)) z v
  set b := fderiv ℝ (fun y => Real.log (gNor n m r'' y)) z v
  set c := fderiv ℝ (fun y => Real.log (gLog n m y)) z v
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + c), sq_nonneg (b + c)]

/-! ### Compact sublevel sets -/

/-- The sublevel sets `{E ≤ t}` of the exhaustion are compact subsets of `U`. -/
theorem isCompact_exhaust_sublevel (hr' : 0 < r') (hr'' : 0 < r'') (hr''e : r'' ^ 2 < Real.exp (-4))
    (t : ℝ) :
    ∃ K : Set (ComplexModel n), IsCompact K ∧ K ⊆ localPunct n m r' r'' ∧
      ∀ z ∈ localPunct n m r' r'', exhaust n m r' r'' z ≤ t → z ∈ K := by
  set a₁ : ℝ := -Real.log (r' ^ 2)
  set a₂ : ℝ := -Real.log (r'' ^ 2)
  set K : Set (ComplexModel n) := {z | tanWeight n m z ≤ r' ^ 2 - Real.exp (-(t - a₂)) ∧
    normalWeight n m z ≤ r'' ^ 2 - Real.exp (-(t - a₁)) ∧
    Real.exp (-Real.exp (t - a₁ - a₂)) ≤ normalWeight n m z}
  have hKc : IsClosed K :=
    (isClosed_le (continuous_tanWeight m) continuous_const).inter
      ((isClosed_le (continuous_normalWeight m) continuous_const).inter
        (isClosed_le continuous_const (continuous_normalWeight m)))
  have hKb : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : ComplexModel n)) (r := r' + r'')).subset ?_
    intro z hz
    rw [mem_closedBall_zero_iff]
    have h1 := tanWeight_add_normalWeight m z
    have h2 : ‖z‖ ^ 2 ≤ (r' + r'') ^ 2 := by
      obtain ⟨h3, h4, -⟩ := hz
      have := Real.exp_pos (-(t - a₂)); have := Real.exp_pos (-(t - a₁))
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg z) (by positivity) two_ne_zero).mp h2
  refine ⟨K, Metric.isCompact_of_isClosed_isBounded hKc hKb, fun z hz => ?_, fun z hz hE => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hz
    have e1 := Real.exp_pos (-(t - a₂))
    have e2 := Real.exp_pos (-(t - a₁))
    exact ⟨by linarith, by linarith, lt_of_lt_of_le (Real.exp_pos _) h3⟩
  · have hT := gTan_pos hz
    have hN := gNor_pos hz
    have hL4 := four_lt_gLog hr''e hz
    have hT' : gTan n m r' z ≤ r' ^ 2 := by unfold gTan; linarith [tanWeight_nonneg m z]
    have hN' : gNor n m r'' z ≤ r'' ^ 2 := by unfold gNor; linarith [normalWeight_nonneg n m z]
    have l1 : a₁ ≤ -Real.log (gTan n m r' z) := by
      simp only [a₁, neg_le_neg_iff]; exact Real.log_le_log hT hT'
    have l2 : a₂ ≤ -Real.log (gNor n m r'' z) := by
      simp only [a₂, neg_le_neg_iff]; exact Real.log_le_log hN hN'
    have l3 : 0 ≤ Real.log (gLog n m z) := Real.log_nonneg (by linarith)
    unfold exhaust at hE
    show _ ∧ _ ∧ _
    refine ⟨?_, ?_, ?_⟩
    · have : -Real.log (gTan n m r' z) ≤ t - a₂ := by linarith
      have h2 : Real.exp (-(t - a₂)) ≤ gTan n m r' z := by
        rw [← Real.exp_log hT]; exact Real.exp_le_exp.mpr (by linarith)
      unfold gTan at h2; linarith
    · have : -Real.log (gNor n m r'' z) ≤ t - a₁ := by linarith
      have h2 : Real.exp (-(t - a₁)) ≤ gNor n m r'' z := by
        rw [← Real.exp_log hN]; exact Real.exp_le_exp.mpr (by linarith)
      unfold gNor at h2; linarith
    · have : Real.log (gLog n m z) ≤ t - a₁ - a₂ := by linarith
      have h2 : gLog n m z ≤ Real.exp (t - a₁ - a₂) := by
        rw [← Real.exp_log (gLog_pos hr''e hz)]; exact Real.exp_le_exp.mpr this
      unfold gLog at h2
      have h3 : -Real.exp (t - a₁ - a₂) ≤ Real.log (normalWeight n m z) := by linarith
      rw [← Real.exp_log hz.2.2]
      exact Real.exp_le_exp.mpr h3

/-! ### The cut-offs -/

/-- `χ_k = λ(E / (2(k + 1)))` on `U`, `0` off `U` (`λ = chenCutoff`). -/
def localCutoff (n m : ℕ) (r' r'' : ℝ) (k : ℕ) (z : ComplexModel n) : ℝ :=
  open Classical in
  if z ∈ localPunct n m r' r'' then chenCutoff (exhaust n m r' r'' z / (2 * ((k : ℝ) + 1)))
  else 0

theorem localCutoff_eq_zero_of_lt {k : ℕ} {z : ComplexModel n}
    (hz : 2 * ((k : ℝ) + 1) ≤ exhaust n m r' r'' z) : localCutoff n m r' r'' k z = 0 := by
  unfold localCutoff
  split_ifs
  · exact chenCutoff_of_ge (by rw [le_div_iff₀ (by positivity)]; linarith)
  · rfl

/-- **Complete cut-offs** for `σ = β + ddᶜ τ` on `U = D \ {w = 0}` (FPT, proof of
`lem:local-critical-gain-extension`, *Complete cutoffs*). -/
theorem hasCompleteCutoffs_kahlerPot (hr' : 0 < r') (hr'' : 0 < r'')
    (hr''e : r'' ^ 2 < Real.exp (-4)) :
    HasCompleteCutoffs (flatModelKahler n) (kahlerPot n m r' r'') (localPunct n m r' r'') := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_deriv_chenCutoff_le
  set U := localPunct n m r' r''
  have hUo : IsOpen U := isOpen_localPunct m r' r''
  -- support control
  have hsupp : ∀ k : ℕ, ∃ K : Set (ComplexModel n), IsCompact K ∧ K ⊆ U ∧
      ∀ z, z ∉ K → localCutoff n m r' r'' k z = 0 := by
    intro k
    obtain ⟨K, hKc, hKU, hK⟩ := isCompact_exhaust_sublevel (m := m) hr' hr'' hr''e
      (2 * ((k : ℝ) + 1))
    refine ⟨K, hKc, hKU, fun z hz => ?_⟩
    by_cases hzU : z ∈ U
    · refine localCutoff_eq_zero_of_lt ?_
      by_contra h
      exact hz (hK z hzU (not_le.mp h).le)
    · unfold localCutoff; rw [if_neg hzU]
  have hloc : ∀ (k : ℕ) (z : ComplexModel n), z ∈ U → localCutoff n m r' r'' k =ᶠ[𝓝 z]
      fun y => chenCutoff (exhaust n m r' r'' y / (2 * ((k : ℝ) + 1))) := by
    intro k z hz
    filter_upwards [hUo.mem_nhds hz] with y hy
    unfold localCutoff; rw [if_pos hy]
  have hsmooth : ∀ k : ℕ, ContDiff ℝ ∞ (localCutoff n m r' r'' k) := by
    intro k
    obtain ⟨K, hKc, hKU, hK⟩ := hsupp k
    refine contDiff_iff_contDiffAt.mpr fun z => ?_
    by_cases hzU : z ∈ U
    · refine ContDiffAt.congr_of_eventuallyEq ?_ (hloc k z hzU)
      exact contDiff_chenCutoff.contDiffAt.comp z
        ((contDiffAt_exhaust hr''e hzU).div_const _)
    · have hzK : z ∉ K := fun h => hzU (hKU h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hzK] with y hy
      exact hK y hy
  refine ⟨localCutoff n m r' r'', M * Real.sqrt (12 * Real.pi), fun k => chartSmooth_model
    (hsmooth k), fun k => ?_, fun k => ?_, fun k z => ?_, fun z hz => ?_, ?_⟩
  · obtain ⟨K, hKc, -, hK⟩ := hsupp k
    exact HasCompactSupport.intro hKc fun z hz => hK z hz
  · obtain ⟨K, hKc, hKU, hK⟩ := hsupp k
    refine (closure_minimal (fun z hz => ?_) hKc.isClosed).trans hKU
    by_contra h
    exact hz (hK z h)
  · unfold localCutoff
    split_ifs
    · exact ⟨chenCutoff_nonneg _, chenCutoff_le_one _⟩
    · exact ⟨le_rfl, zero_le_one⟩
  · have hev : ∀ᶠ k : ℕ in atTop, localCutoff n m r' r'' k z = 1 := by
      have ht : Tendsto (fun k : ℕ => exhaust n m r' r'' z / (2 * ((k : ℝ) + 1))) atTop
          (𝓝 0) := by
        refine Tendsto.div_atTop tendsto_const_nhds ?_
        exact Tendsto.const_mul_atTop (by norm_num)
          (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      filter_upwards [ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk
      unfold localCutoff
      rw [if_pos hz]
      exact chenCutoff_of_le hk.le
    exact tendsto_nhds_of_eventually_eq hev
  · intro k c z _ hzU v
    obtain rfl := chart_eq c
    rw [modifiedKahlerQuad_flatModelKahler]
    change fderiv ℝ (localCutoff n m r' r'' k) z v ^ 2 ≤ _
    rw [(hloc k z hzU).fderiv_eq]
    have hEd : DifferentiableAt ℝ (exhaust n m r' r'') z :=
      (contDiffAt_exhaust hr''e hzU).differentiableAt (by simp)
    set c : ℝ := 2 * ((k : ℝ) + 1) with hc
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hc0 : 0 < c := by positivity
    set θ : ℝ → ℝ := fun t => chenCutoff (t / c) with hθ
    set d := deriv chenCutoff (exhaust n m r' r'' z / c)
    have hθd : HasDerivAt θ (d * (1 / c)) (exhaust n m r' r'' z) := by
      have h1 : HasDerivAt (fun t : ℝ => t / c) (1 / c) (exhaust n m r' r'' z) :=
        (hasDerivAt_id _).div_const c
      exact ((contDiff_chenCutoff (k := ⊤)).differentiable (by simp) _).hasDerivAt.comp _ h1
    have hfd : fderiv ℝ (fun y => θ (exhaust n m r' r'' y)) z v =
        d * (1 / c) * fderiv ℝ (exhaust n m r' r'') z v := by
      rw [fderiv_comp_real hθd.differentiableAt hEd, hθd.deriv]
      rfl
    change fderiv ℝ (fun y => θ (exhaust n m r' r'' y)) z v ^ 2 ≤ _
    rw [hfd]
    have hd : d ^ 2 ≤ M ^ 2 := by
      have := hM (exhaust n m r' r'' z / c)
      exact sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
    have hE := fderiv_exhaust_sq_le hr''e hzU v
    have hL := leviForm_kahlerPot_nonneg hr''e hzU v
    have hpi : 0 < Real.pi := Real.pi_pos
    have hsq : Real.sqrt (12 * Real.pi) ^ 2 = 12 * Real.pi := Real.sq_sqrt (by positivity)
    set E := fderiv ℝ (exhaust n m r' r'') z v
    set L := leviForm (kahlerPot n m r' r'') z v
    have hv : 0 ≤ ‖v‖ ^ 2 := by positivity
    have h2 : d ^ 2 * E ^ 2 ≤ M ^ 2 * (12 * L) :=
      mul_le_mul hd hE (sq_nonneg _) (sq_nonneg _)
    have hR : (M * Real.sqrt (12 * Real.pi) / ((k : ℝ) + 1)) ^ 2 * (‖v‖ ^ 2 + L / Real.pi) =
        12 * M ^ 2 * (Real.pi * ‖v‖ ^ 2 + L) / ((k : ℝ) + 1) ^ 2 := by
      rw [div_pow, mul_pow, hsq]
      field_simp
    rw [hR, hc]
    rw [le_div_iff₀ (by positivity)]
    have hl : (d * (1 / (2 * ((k : ℝ) + 1))) * E) ^ 2 * ((k : ℝ) + 1) ^ 2 =
        d ^ 2 * E ^ 2 / 4 := by
      field_simp
      ring
    rw [hl]
    have hpv : 0 ≤ Real.pi * ‖v‖ ^ 2 := by positivity
    nlinarith [sq_nonneg M]

end SGPT.Trace.OTExt2
