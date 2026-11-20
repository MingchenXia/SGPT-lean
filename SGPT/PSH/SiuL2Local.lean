import SGPT.PSH.GlobalL2Gluing
import SGPT.Foundations.Analysis.Pending.ProductComplexManifold
import SGPT.Foundations.Analysis.Pending.WeightedL2ExtensionLimit

/-!
# Local `L²` corrections on convex domains and on products `B × Δ`

Blueprint `claude-siu-l2.tex`, nodes `claude-siu-l2:convex-smooth`, `claude-siu-l2:convex-singular`,
`claude-siu-l2:product-local`.

The global `L²` theory of `SGPT/PSH/GlobalL2*.lean` solves `∂̄` on a *compact* manifold by a
Neumann series of local Hörmander corrections on chart balls.  On the non-compact `X × Δ`
(`lma:Siu_global_uniform_generatedness`) we use instead the product domains
`B(z₀, R) × Δ ⊆ ℂⁿ × ℂ`: the cover is finite in the `X`-direction and the whole disc `Δ` is
treated by the local solver.  This file proves the local solver.

* `convexCorrectionSmooth`: Hörmander's estimate (TN `hormanderL2Estimate`) on a bounded convex
  domain `D` for a smooth weight `Φ` with `Levi Φ ≥ c|ξ|²`, giving a holomorphic `G` on an open `S`
  with compact closure in `D` and `∫_S |a - G|² e^{-Φ} ≤ (2/c) ∫_D |∂̄a|² e^{-Φ}` (the proof of
  `localBallCorrectionSmooth`, for general `D, S`).
* `convexCorrection`: the same for the singular weight `Ψ + c|z - z₀|²`, `Ψ` an arbitrary psh
  function on `D` (the proof of `localBallCorrection`: truncation, mollification on a convex
  `A ⋐ D`, normal families).
* `productCorrection`: for `D_R = B(z₀, R) × Δ` and `D_r = B(z₀, r) × Δ` (`r < R`), the estimate on
  all of `D_r`, which is *not* relatively compact in `D_R`: exhaustion of `D_r` by
  `B(z₀, r) × Δ_{1 - 1/(ν+2)}` and a normal-family limit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.PSH.SiuL2

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.PSH.GlobalL2

variable {n : ℕ}

/-! ### Bounded sets -/

/-- A set with compact closure has finite volume. -/
theorem volume_lt_top_of_isCompact_closure {S : Set (ComplexModel n)}
    (hS : IsCompact (closure S)) : volume S < ⊤ :=
  (measure_mono subset_closure).trans_lt hS.measure_lt_top

/-- A function bounded by a constant on a measurable set with compact closure has finite set
integral. -/
theorem setLIntegral_lt_top_of_bound {S : Set (ComplexModel n)} (hSm : MeasurableSet S)
    (hS : IsCompact (closure S)) {f : ComplexModel n → ℝ≥0∞} {M : ℝ}
    (hf : ∀ z ∈ S, f z ≤ ENNReal.ofReal M) : ∫⁻ z in S, f z < ⊤ := by
  calc ∫⁻ z in S, f z ≤ ∫⁻ _ in S, ENNReal.ofReal M := setLIntegral_mono' hSm hf
    _ = ENNReal.ofReal M * volume S := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (volume_lt_top_of_isCompact_closure hS)

/-- **A convex open set between a compact set and a bounded convex open set.**  For `K ⊆ D`
compact, `D` open, convex and bounded, the set `A = {z | ∃ δ' > δ, B(z, δ') ⊆ D}` (for a small
`δ > 0`) is open, convex, contains `K`, and has compact closure inside `D`. -/
theorem exists_convex_between {D K : Set (ComplexModel n)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ A : Set (ComplexModel n), IsOpen A ∧ Convex ℝ A ∧ K ⊆ A ∧ IsCompact (closure A) ∧
      closure A ⊆ D := by
  obtain ⟨δ₀, hδ₀, hth⟩ := hK.exists_cthickening_subset_open hDo hKD
  set δ : ℝ := δ₀ / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set A : Set (ComplexModel n) := {z | ∃ δ' > δ, ball z δ' ⊆ D} with hAdef
  refine ⟨A, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Metric.isOpen_iff]
    rintro z ⟨δ', hδ', hz⟩
    refine ⟨(δ' - δ) / 2, by linarith, fun y hy => ⟨(δ' + δ) / 2, by linarith, ?_⟩⟩
    intro w hw
    refine hz ?_
    rw [mem_ball] at hw hy ⊢
    calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      _ < (δ' + δ) / 2 + (δ' - δ) / 2 := add_lt_add hw hy
      _ = δ' := by ring
  · intro x hx y hy a b ha hb hab
    obtain ⟨δ₁, hδ₁, hx'⟩ := hx
    obtain ⟨δ₂, hδ₂, hy'⟩ := hy
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun w hw => ?_⟩
    set p := a • x + b • y with hp
    have hwx : x + (w - p) ∈ D := hx' (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (mem_ball_iff_norm.mp hw).trans_le (min_le_left _ _))
    have hwy : y + (w - p) ∈ D := hy' (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact (mem_ball_iff_norm.mp hw).trans_le (min_le_right _ _))
    have hcomb := hDc hwx hwy ha hb hab
    have : a • (x + (w - p)) + b • (y + (w - p)) = w := by
      rw [smul_add, smul_add, add_add_add_comm, ← hp, ← add_smul, hab, one_smul]
      abel
    rwa [this] at hcomb
  · intro z hz
    refine ⟨δ₀, by linarith, fun w hw => hth ?_⟩
    exact mem_cthickening_of_dist_le w z δ₀ K hz (mem_ball.mp hw).le
  · refine hDb.isCompact_closure.of_isClosed_subset isClosed_closure (closure_mono ?_)
    rintro z ⟨δ', hδ', hz⟩
    exact hz (mem_ball_self (by linarith))
  · intro z hz
    obtain ⟨y, hyA, hyz⟩ := Metric.mem_closure_iff.mp hz δ hδ
    obtain ⟨δ', hδ', hy⟩ := hyA
    refine hy ?_
    rw [mem_ball]
    exact hyz.trans hδ'

/-! ### Smooth weights on convex domains -/

/-- **Local `L²` correction on a bounded convex domain, smooth weights**
(`claude-siu-l2:convex-smooth`).  The proof of `localBallCorrectionSmooth` with the ball
`B(z₀, R)` replaced by a bounded convex `D` and the small ball by an open `S` with compact closure
in `D`. -/
theorem convexCorrectionSmooth {D S : Set (ComplexModel n)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D) (hSo : IsOpen S) (hSc : IsCompact (closure S))
    (hSD : closure S ⊆ D)
    {c : ℝ} (hc : 0 < c) {Φ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ D)
    (hΦL : ∀ z ∈ D, ∀ ξ : ComplexModel n, c * ‖ξ‖ ^ 2 ≤ leviForm Φ z ξ)
    {a : ComplexModel n → ℂ} (ha : ContDiffOn ℝ ∞ a D) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G S ∧
      ∫⁻ z in S, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ENNReal.ofReal (Real.exp (-Φ z)) ≤
        ENNReal.ofReal (2 / c) *
          ∫⁻ z in D, ENNReal.ofReal (dbarNormSq a z) * ENNReal.ofReal (Real.exp (-Φ z)) := by
  set S' : ℝ≥0∞ := ∫⁻ z in D, ENNReal.ofReal (dbarNormSq a z) * ENNReal.ofReal (Real.exp (-Φ z))
    with hSdef
  have h2c : (0 : ℝ) < 2 / c := by positivity
  by_cases hS : S' = ⊤
  · refine ⟨fun _ => 0, differentiableOn_const 0, ?_⟩
    rw [hS, ENNReal.mul_top (ENNReal.ofReal_pos.mpr h2c).ne']
    exact le_top
  obtain ⟨D', U, lam₁, lam₂, hD'o, -, hD'cl, -, hKU, hUD', hl₁, hl₂, hl, hl0, hest⟩ :=
    hormanderL2Estimate n D hDo hDc hDb (closure S) hSc hSD 1 one_pos
  have hD'D : D' ⊆ D := subset_closure.trans hD'cl
  have hD'm : MeasurableSet D' := hD'o.measurableSet
  have hDm : MeasurableSet D := hDo.measurableSet
  have hrD' : S ⊆ D' := subset_closure.trans (hKU.trans hUD')
  have hrU : S ⊆ U := subset_closure.trans hKU
  have ha1 : ContDiffOn ℝ 1 a D := ha.of_le (WithTop.coe_le_coe.mpr le_top)
  have ha1' : ContDiffOn ℝ 1 a D' := ha1.mono hD'D
  have hΦc : ContinuousOn Φ D := hΦ.continuousOn
  have hΦc' : ContinuousOn Φ D' := hΦc.mono hD'D
  set v : Fin n → ComplexModel n → ℂ := fun j => dbarDir (coordVec j) a with hvdef
  set g : ComplexModel n → ℝ := fun z => dbarNormSq a z / c with hgdef
  have hg0 : ∀ z, 0 ≤ g z := fun z => div_nonneg (dbarNormSq_nonneg a z) hc.le
  have hdNc : ContinuousOn (dbarNormSq a) D := continuousOn_dbarNormSq hDo ha1
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
  obtain ⟨⟨u₀, hu₀mem, hu₀eq, hu₀orth⟩, hu₀est⟩ :=
    hest Φ hΦ hΦL0 v hvmem hvclosed g (fun z _ => hg0 z) hglevi hgint
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
  calc ∫⁻ z in S, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ENNReal.ofReal (Real.exp (-Φ z))
      = ∫⁻ z in S, ENNReal.ofReal (‖a z - G z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z))) := by
        refine setLIntegral_congr_fun hSo.measurableSet fun z hz => ?_
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
    _ = ENNReal.ofReal (2 / c) * S' := by
        congr 1
        refine setLIntegral_congr_fun hDm fun z _ => ?_
        rw [ENNReal.ofReal_mul (dbarNormSq_nonneg a z)]

/-! ### Singular weights on convex domains -/

/-- A continuous function is bounded on a set with compact closure inside its domain. -/
theorem exists_bound_norm_sq_of_isCompact_closure {D S : Set (ComplexModel n)}
    (hSc : IsCompact (closure S)) (hSD : closure S ⊆ D) {a : ComplexModel n → ℂ}
    (ha : ContinuousOn a D) : ∃ M : ℝ, ∀ z ∈ S, ‖a z‖ ^ 2 ≤ M := by
  obtain ⟨M, hM⟩ := hSc.exists_bound_of_continuousOn (ha.mono hSD)
  refine ⟨M ^ 2, fun z hz => ?_⟩
  exact pow_le_pow_left₀ (norm_nonneg _) (hM z (subset_closure hz)) 2

/-- **Local `L²` correction on a bounded convex domain, singular weights**
(`claude-siu-l2:convex-singular`).  For every plurisubharmonic `Ψ` on a bounded convex open `D`,
`c > 0`, `z₀`, and smooth `a` on `D`, there is `G` holomorphic on an open `S` with compact closure
in `D` with `∫_S |a - G|² e^{-Ψ - c|z - z₀|²} ≤ (2/c) ∫_D |∂̄a|² e^{-Ψ - c|z - z₀|²}` (the proof of
`localBallCorrection`, with the regularization performed on a convex `A`,
`closure S ⊆ A ⋐ D`). -/
theorem convexCorrection {D S : Set (ComplexModel n)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D) (hSo : IsOpen S) (hSc : IsCompact (closure S))
    (hSD : closure S ⊆ D) (z₀ : ComplexModel n) {c : ℝ} (hc : 0 < c)
    {Ψ : ComplexModel n → EReal} (hΨ : PlurisubharmonicOn Ψ D)
    {a : ComplexModel n → ℂ} (ha : ContDiffOn ℝ ∞ a D) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G S ∧
      ∫⁻ z in S, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ballWeight Ψ c z₀ z ≤
        ENNReal.ofReal (2 / c) *
          ∫⁻ z in D, ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c z₀ z := by
  set S' : ℝ≥0∞ := ∫⁻ z in D, ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c z₀ z
    with hSdef
  have h2c : (0 : ℝ) < 2 / c := by positivity
  by_cases hS : S' = ⊤
  · refine ⟨fun _ => 0, differentiableOn_const 0, ?_⟩
    rw [hS, ENNReal.mul_top (ENNReal.ofReal_pos.mpr h2c).ne']
    exact le_top
  have hAtop : ENNReal.ofReal (2 / c) * S' ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS
  obtain ⟨A, hAo, hAc, hSA, hAcl, hAD⟩ := exists_convex_between hDo hDc hDb hSc hSD
  have hAb : Bornology.IsBounded A := hAcl.isBounded.subset subset_closure
  have hAD' : A ⊆ D := subset_closure.trans hAD
  have hSA' : S ⊆ A := subset_closure.trans hSA
  have hSD' : S ⊆ D := hSA'.trans hAD'
  have hSm : MeasurableSet S := hSo.measurableSet
  obtain ⟨CD, hCD⟩ := hDb.subset_closedBall z₀
  have hCD' : ∀ y ∈ D, ‖y - z₀‖ ^ 2 ≤ CD ^ 2 := fun y hy =>
    pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_iff_norm.mp (hCD hy)) 2
  let Ω : TopologicalSpace.Opens (ComplexModel n) := ⟨D, hDo⟩
  let A' : TopologicalSpace.Opens (ComplexModel n) := ⟨A, hAo⟩
  have hA : RelativelyCompactIn A' Ω := ⟨hAcl, hAD⟩
  have hΨΩ : PlurisubharmonicOn Ψ Ω := hΨ
  have haR : ContinuousOn a D := ha.continuousOn
  obtain ⟨Ma, hMa⟩ := exists_bound_norm_sq_of_isCompact_closure hSc hSD haR
  have hnsq : ∀ z : ComplexModel n, 0 ≤ c * ‖z - z₀‖ ^ 2 := fun z => by positivity
  have hnsqc : Continuous fun z : ComplexModel n => c * ‖z - z₀‖ ^ 2 := by fun_prop
  have hnsqs : ContDiff ℝ ∞ fun z : ComplexModel n => c * ‖z - z₀‖ ^ 2 :=
    contDiff_const.mul ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hLeviNsq : ∀ z ξ : ComplexModel n,
      leviForm (fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2) z ξ = c * ‖ξ‖ ^ 2 := by
    intro z ξ
    have e : (fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2) =
        fun y => (c • fun w : ComplexModel n => ‖w‖ ^ 2) (y - z₀) := by
      funext y; simp [smul_eq_mul]
    rw [e, LocalBedfordTaylorCollar.leviForm_comp_sub_const,
      leviForm_smul (contDiff_norm_sq ℝ).contDiffAt, leviForm_norm_sq]
  -- Stage 1: for fixed `N`, the smooth regularizations of `max (Ψ, -N)` on `A`
  have stage1 : ∀ N : ℕ, ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G S ∧
      ∫⁻ z in S, ENNReal.ofReal (‖a z - G z‖ ^ 2) *
          ballWeight (fun z => (truncationReal Ψ N z : EReal)) c z₀ z ≤
        ENNReal.ofReal (2 / c) * S' := by
    intro N
    obtain ⟨fs, hfs⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation
      (truncationReal_isLocallyBoundedPshOn hΨΩ N) hA
    set Φ : ℕ → ComplexModel n → ℝ := fun j z => fs j z + c * ‖z - z₀‖ ^ 2 with hΦdef
    have hΦs : ∀ j, ContDiffOn ℝ ∞ (Φ j) A := fun j => (hfs.1 j).1.add hnsqs.contDiffOn
    have hΦL : ∀ j, ∀ z ∈ A, ∀ ξ : ComplexModel n, c * ‖ξ‖ ^ 2 ≤ leviForm (Φ j) z ξ := by
      intro j z hz ξ
      have h1 : ContDiffAt ℝ 2 (fs j) z :=
        (((hfs.1 j).1.contDiffAt (hAo.mem_nhds hz))).of_le (WithTop.coe_le_coe.mpr le_top)
      have h2 : ContDiffAt ℝ 2 (fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2) z :=
        (hnsqs.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      have hsplit : Φ j = fs j + fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2 := rfl
      rw [hsplit, leviForm_add h1 h2, hLeviNsq]
      have h0 := leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := A') (hfs.1 j).1
        (hfs.1 j).2.1 hz ξ
      linarith
    have hge : ∀ j, ∀ z ∈ A, truncationReal Ψ N z ≤ fs j z := fun j z hz =>
      (hfs.2.1 z hz).le_of_tendsto (hfs.2.2 z hz) j
    have hΨle : ∀ z ∈ D, Ψ z ≤ (truncationReal Ψ N z : EReal) := fun z hz => by
      rw [coe_truncationReal hΨΩ N hz]
      exact le_max_left _ _
    have hloc := fun j => convexCorrectionSmooth hAo hAc hAb hSo hSc hSA hc (hΦs j) (hΦL j)
      (ha.mono hAD')
    choose F hF hFb using hloc
    have hwle : ∀ j, ∀ z ∈ A, ENNReal.ofReal (Real.exp (-Φ j z)) ≤ ballWeight Ψ c z₀ z := by
      intro j z hz
      have : ENNReal.ofReal (Real.exp (-Φ j z)) = multiplierWeight 1 ((Φ j z : ℝ) : EReal) := by
        rw [multiplierWeight_coe, one_mul]
      rw [this, ballWeight]
      refine multiplierWeight_antitone zero_le_one ?_
      rw [hΦdef]
      dsimp only
      rw [EReal.coe_add]
      gcongr
      exact (hΨle z (hAD' hz)).trans (EReal.coe_le_coe_iff.mpr (hge j z hz))
    have hbound : ∀ j, ∫⁻ z in S, ENNReal.ofReal (‖a z - F j z‖ ^ 2) *
        ENNReal.ofReal (Real.exp (-Φ j z)) ≤ ENNReal.ofReal (2 / c) * S' := by
      intro j
      refine (hFb j).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      calc ∫⁻ z in A, ENNReal.ofReal (dbarNormSq a z) * ENNReal.ofReal (Real.exp (-Φ j z))
          ≤ ∫⁻ z in A, ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c z₀ z :=
            setLIntegral_mono' hAo.measurableSet fun z hz =>
              mul_le_mul_of_nonneg_left (hwle j z hz) zero_le
        _ ≤ S' := lintegral_mono_set hAD'
    have hΦc : ∀ j, ContinuousOn (Φ j) A := fun j => (hΦs j).continuousOn
    obtain ⟨G, hG, hGint⟩ := exists_correction_limit hSo (haR.mono hSD')
      (w := fun j z => ENNReal.ofReal (Real.exp (-Φ j z)))
      (fun z hz i j hij => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
        have := (hfs.2.1 z (hSA' hz)) hij
        simp only [hΦdef]; linarith)))
      (fun j => (ENNReal.measurable_ofReal.comp Real.measurable_exp).comp_aemeasurable
        (((hΦc j).mono hSA').neg.aemeasurable hSm))
      (fun x hx => by
        have hcont : ContinuousAt (Φ 0) x := (hΦc 0).continuousAt (hAo.mem_nhds (hSA' hx))
        obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
        refine ⟨ρ, hρ, Real.exp (-(Φ 0 x + 1)), Real.exp_pos _, fun y hy => ?_⟩
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have h1 := hball (mem_ball.mp hy)
        rw [Real.dist_eq] at h1
        linarith [le_abs_self (Φ 0 y - Φ 0 x)])
      hF hAtop hbound
      (by
        obtain ⟨MΦ, hMΦ⟩ := hSc.exists_bound_of_continuousOn ((hΦc 0).mono hSA)
        refine (setLIntegral_lt_top_of_bound hSm hSc (M := Ma * Real.exp MΦ) fun z hz => ?_).ne
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul (hMa z hz) (Real.exp_le_exp.mpr ?_)
          (Real.exp_pos _).le (le_trans (sq_nonneg _) (hMa z hz)))
        have := hMΦ z (subset_closure hz)
        rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (Φ 0 z)])
    refine ⟨G, hG, le_trans ?_ hGint⟩
    refine setLIntegral_mono' hSm fun z hz => ?_
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [ballWeight_coe]
    have ht : Tendsto (fun j => ENNReal.ofReal (Real.exp (-Φ j z))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-(truncationReal Ψ N z + c * ‖z - z₀‖ ^ 2))))) := by
      refine ENNReal.tendsto_ofReal (Real.continuous_exp.tendsto _ |>.comp ?_)
      exact ((hfs.2.2 z (hSA' hz)).add tendsto_const_nhds).neg
    exact le_of_tendsto' ht fun j => le_iSup (fun j => ENNReal.ofReal (Real.exp (-Φ j z))) j
  -- Stage 2: `N → ∞`
  choose G hG hGb using stage1
  have hwmeas2 : ∀ N, AEMeasurable (fun z => ballWeight (fun z => (truncationReal Ψ N z : EReal))
      c z₀ z) (volume.restrict S) := by
    intro N
    have hq : QuasiPlurisubharmonicOn (fun z => (truncationReal Ψ N z : EReal)) D :=
      fun x hx => (truncationReal_plurisubharmonicOn hΨΩ N x hx).quasiPlurisubharmonicAt
    have h := aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
      (μ := volume) hDo hq one_ne_zero (f := fun _ => (1 : ℂ)) continuousOn_const
    have h' : AEMeasurable (fun z => multiplierWeight 1 (truncationReal Ψ N z : EReal))
        (volume.restrict D) := h.congr (Eventually.of_forall fun z => by
          simp [multiplierDensity])
    have h'' := h'.mono_measure (Measure.restrict_mono hSD' le_rfl)
    refine (h''.mul ((ENNReal.measurable_ofReal.comp Real.measurable_exp).comp_aemeasurable
      (hnsqc.neg.aemeasurable))).congr (Eventually.of_forall fun z => ?_)
    exact (ballWeight_eq_mul (Ψ := fun z => ((truncationReal Ψ N z : ℝ) : EReal))
      (EReal.coe_ne_top _) c z₀).symm
  obtain ⟨G', hG', hG'int⟩ := exists_correction_limit hSo (haR.mono hSD')
    (w := fun N z => ballWeight (fun z => (truncationReal Ψ N z : EReal)) c z₀ z)
    (fun z hz i j hij => by
      simp only [ballWeight_coe]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have := truncationReal_antitone hΨΩ (hSD' hz) hij
      linarith)
    hwmeas2
    (fun x hx => by
      obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hDo x (hSD' hx)
      obtain ⟨B, hB0, hB⟩ := hΨ.exists_nonnegative_compact_upper_bound
        (isCompact_closedBall x (ρ₀ / 2)) ((closedBall_subset_ball (by linarith)).trans hball)
      refine ⟨ρ₀ / 2, by positivity, Real.exp (-(B + c * CD ^ 2)), Real.exp_pos _, fun y hy => ?_⟩
      have hyR : y ∈ D := hball (ball_subset_ball (by linarith) hy)
      rw [ballWeight_coe]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have htr : truncationReal Ψ 0 y ≤ B := by
        apply EReal.coe_le_coe_iff.mp
        rw [coe_truncationReal hΨΩ 0 hyR]
        refine max_le (hB y (ball_subset_closedBall hy)) ?_
        exact EReal.coe_le_coe_iff.mpr (by simpa using hB0)
      have hyz := hCD' y hyR
      nlinarith)
    hG hAtop hGb
    (by
      refine (setLIntegral_lt_top_of_bound hSm hSc (M := Ma) fun z hz => ?_).ne
      have hw1 : ballWeight (fun z => (truncationReal Ψ 0 z : EReal)) c z₀ z ≤ 1 := by
        rw [ballWeight_coe, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.exp_le_one_iff, neg_nonpos]
        have h0 : 0 ≤ truncationReal Ψ 0 z := by
          apply EReal.coe_le_coe_iff.mp
          rw [coe_truncationReal hΨΩ 0 (hSD' hz)]
          exact le_max_right _ _ |>.trans' (by simp)
        linarith [hnsq z]
      calc ENNReal.ofReal (‖a z‖ ^ 2) * ballWeight (fun z => (truncationReal Ψ 0 z : EReal)) c z₀ z
          ≤ ENNReal.ofReal (‖a z‖ ^ 2) * 1 := mul_le_mul_of_nonneg_left hw1 zero_le
        _ ≤ ENNReal.ofReal Ma := by rw [mul_one]; exact ENNReal.ofReal_le_ofReal (hMa z hz))
  refine ⟨G', hG', le_trans ?_ hG'int⟩
  refine setLIntegral_mono' hSm fun z hz => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have hzR := hSD' hz
  rw [ballWeight_eq_mul ((hΨ z hzR).ne_top) c z₀]
  have hfac : ∀ N : ℕ, ballWeight (fun z => (truncationReal Ψ N z : EReal)) c z₀ z =
      multiplierWeight 1 (truncationReal Ψ N z : EReal) *
        ENNReal.ofReal (Real.exp (-(c * ‖z - z₀‖ ^ 2))) := fun N =>
    ballWeight_eq_mul (Ψ := fun z => ((truncationReal Ψ N z : ℝ) : EReal)) (EReal.coe_ne_top _) c z₀
  rw [iSup_congr hfac, ← ENNReal.iSup_mul]
  exact mul_le_mul_of_nonneg_right
    (multiplierWeight_le_iSup_truncationReal (Ω := Ω) hΨΩ one_pos hzR) zero_le

/-! ### Product domains `B(z₀, R) × Δ_ρ` -/

open SGPT.Foundations.Analysis.Pending.ProductComplexManifold in
/-- The product domain `B(z₀, R) × Δ_ρ ⊆ ℂⁿ × ℂ ≃ ℂⁿ⁺¹` (through `prodModelEquiv n 1`). -/
def prodDom (z₀ : ComplexModel n) (R ρ : ℝ) : Set (ComplexModel (n + 1)) :=
  (prodModelEquiv n 1).symm ⁻¹' (ball z₀ R ×ˢ ball (0 : ComplexModel 1) ρ)

open SGPT.Foundations.Analysis.Pending.ProductComplexManifold

theorem mem_prodDom {z₀ : ComplexModel n} {R ρ : ℝ} {w : ComplexModel (n + 1)} :
    w ∈ prodDom z₀ R ρ ↔ ((prodModelEquiv n 1).symm w).1 ∈ ball z₀ R ∧
      ‖((prodModelEquiv n 1).symm w).2‖ < ρ := by
  simp [prodDom]

theorem isOpen_prodDom (z₀ : ComplexModel n) (R ρ : ℝ) : IsOpen (prodDom z₀ R ρ) :=
  (isOpen_ball.prod isOpen_ball).preimage (prodModelEquiv n 1).symm.continuous

theorem convex_prodDom (z₀ : ComplexModel n) (R ρ : ℝ) : Convex ℝ (prodDom z₀ R ρ) :=
  ((convex_ball z₀ R).prod (convex_ball (0 : ComplexModel 1) ρ)).linear_preimage
    (((prodModelEquiv n 1).symm.toLinearEquiv.toLinearMap).restrictScalars ℝ)

theorem prodDom_eq_image (z₀ : ComplexModel n) (R ρ : ℝ) :
    prodDom z₀ R ρ = (prodModelEquiv n 1) '' (ball z₀ R ×ˢ ball (0 : ComplexModel 1) ρ) :=
  ((prodModelEquiv n 1).toHomeomorph.image_eq_preimage_symm _).symm

theorem isBounded_prodDom (z₀ : ComplexModel n) (R ρ : ℝ) :
    Bornology.IsBounded (prodDom z₀ R ρ) := by
  rw [prodDom_eq_image]
  exact (prodModelEquiv n 1).lipschitz.isBounded_image (isBounded_ball.prod isBounded_ball)

theorem prodDom_mono {z₀ : ComplexModel n} {r R ρ' ρ : ℝ} (hrR : r ≤ R) (hρ : ρ' ≤ ρ) :
    prodDom z₀ r ρ' ⊆ prodDom z₀ R ρ :=
  preimage_mono (prod_mono (ball_subset_ball hrR) (ball_subset_ball hρ))

theorem closure_prodDom_subset {z₀ : ComplexModel n} {r R ρ' ρ : ℝ} (hrR : r < R)
    (hρ : ρ' < ρ) : closure (prodDom z₀ r ρ') ⊆ prodDom z₀ R ρ := by
  rw [prodDom, ← (prodModelEquiv n 1).symm.preimage_closure, closure_prod_eq]
  exact preimage_mono (prod_mono (closure_ball_subset_closedBall.trans (closedBall_subset_ball hrR))
    (closure_ball_subset_closedBall.trans (closedBall_subset_ball hρ)))

theorem isCompact_closure_prodDom (z₀ : ComplexModel n) (r ρ : ℝ) :
    IsCompact (closure (prodDom z₀ r ρ)) :=
  (isBounded_prodDom z₀ r ρ).isCompact_closure

/-- Weights of the form `e^{-Ψ - c|z - w₀|²}`, `Ψ` psh on an open `D`, are measurable on `D`. -/
theorem aemeasurable_ballWeight {N : ℕ} {D : Set (ComplexModel N)} (hDo : IsOpen D)
    {Ψ : ComplexModel N → EReal} (hΨ : PlurisubharmonicOn Ψ D) (c : ℝ) (w₀ : ComplexModel N) :
    AEMeasurable (ballWeight Ψ c w₀) (volume.restrict D) := by
  have hq : QuasiPlurisubharmonicOn Ψ D := fun x hx => (hΨ x hx).quasiPlurisubharmonicAt
  have h := aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
    (μ := volume) hDo hq one_ne_zero (f := fun _ => (1 : ℂ)) continuousOn_const
  have h' : AEMeasurable (fun z => multiplierWeight 1 (Ψ z)) (volume.restrict D) :=
    h.congr (Eventually.of_forall fun z => by simp [multiplierDensity])
  have hc : Continuous fun z : ComplexModel N => c * ‖z - w₀‖ ^ 2 := by fun_prop
  refine (h'.mul ((ENNReal.measurable_ofReal.comp Real.measurable_exp).comp_aemeasurable
    hc.neg.aemeasurable)).congr ?_
  refine (ae_restrict_iff' hDo.measurableSet).mpr (Eventually.of_forall fun z hz => ?_)
  exact (ballWeight_eq_mul ((hΨ z hz).ne_top) c w₀).symm

/-- Weights `e^{-Ψ - c|z - w₀|²}` are locally bounded below by positive constants on a bounded
open set where `Ψ` is psh. -/
theorem ballWeight_locally_ge {N : ℕ} {D : Set (ComplexModel N)} (hDo : IsOpen D)
    (hDb : Bornology.IsBounded D) {Ψ : ComplexModel N → EReal} (hΨ : PlurisubharmonicOn Ψ D)
    {c : ℝ} (hc : 0 < c) (w₀ : ComplexModel N) {x : ComplexModel N} (hx : x ∈ D) :
    ∃ ρ > 0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ y ∈ ball x ρ, ENNReal.ofReal δ ≤ ballWeight Ψ c w₀ y := by
  obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hDo x hx
  obtain ⟨B, hB0, hB⟩ := hΨ.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall x (ρ₀ / 2)) ((closedBall_subset_ball (by linarith)).trans hball)
  obtain ⟨CD, hCD⟩ := hDb.subset_closedBall w₀
  refine ⟨ρ₀ / 2, by positivity, Real.exp (-(B + c * CD ^ 2)), Real.exp_pos _, ?_,
    fun y hy => ?_⟩
  · rw [Real.exp_le_one_iff, neg_nonpos]; positivity
  have hyR : y ∈ D := hball (ball_subset_ball (by linarith) hy)
  have hyz : ‖y - w₀‖ ^ 2 ≤ CD ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (mem_closedBall_iff_norm.mp (hCD hyR)) 2
  have hle : Ψ y + ((c * ‖y - w₀‖ ^ 2 : ℝ) : EReal) ≤ ((B + c * CD ^ 2 : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact add_le_add (hB y (ball_subset_closedBall hy))
      (EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left hyz hc.le))
  calc ENNReal.ofReal (Real.exp (-(B + c * CD ^ 2)))
      = multiplierWeight 1 ((B + c * CD ^ 2 : ℝ) : EReal) := by
        rw [multiplierWeight_coe, one_mul]
    _ ≤ ballWeight Ψ c w₀ y := multiplierWeight_antitone zero_le_one hle

/-- **Exhaustion limit.**  Let `S_ν` be increasing open sets with union `S` of compact closure,
`a` continuous on an open `D ⊇ S`, `W` a measurable weight on `S` locally bounded below by
positive constants, and `G_ν` holomorphic on `S_ν` with `∫_{S_ν} |a - G_ν|² W ≤ B < ∞`.  Then a
holomorphic `G` on `S` has `∫_S |a - G|² W ≤ B`. -/
theorem exists_exhaustion_limit {N : ℕ} {D : Set (ComplexModel N)}
    {Sν : ℕ → Set (ComplexModel N)} (hSo : ∀ ν, IsOpen (Sν ν)) (hSm : Monotone Sν)
    (hSc : IsCompact (closure (⋃ ν, Sν ν))) (hSD : (⋃ ν, Sν ν) ⊆ D)
    {a : ComplexModel N → ℂ} (ha : ContinuousOn a D) {W : ComplexModel N → ℝ≥0∞}
    (hWm : AEMeasurable W (volume.restrict (⋃ ν, Sν ν)))
    (hWlow : ∀ x ∈ ⋃ ν, Sν ν, ∃ ρ > 0, ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ ball x ρ, ENNReal.ofReal δ ≤ W y)
    {G : ℕ → ComplexModel N → ℂ} (hG : ∀ ν, DifferentiableOn ℂ (G ν) (Sν ν)) {B : ℝ≥0∞}
    (hB : B ≠ ⊤) (hbound : ∀ ν, ∫⁻ z in Sν ν, ENNReal.ofReal (‖a z - G ν z‖ ^ 2) * W z ≤ B) :
    ∃ G' : ComplexModel N → ℂ, DifferentiableOn ℂ G' (⋃ ν, Sν ν) ∧
      ∫⁻ z in ⋃ ν, Sν ν, ENNReal.ofReal (‖a z - G' z‖ ^ 2) * W z ≤ B := by
  set S := ⋃ ν, Sν ν with hSdef
  have hSo' : IsOpen S := isOpen_iUnion hSo
  have hSm' : MeasurableSet S := hSo'.measurableSet
  have hSν : ∀ ν, Sν ν ⊆ S := fun ν => subset_iUnion Sν ν
  set w' : ComplexModel N → ℝ≥0∞ := fun z => min (W z) (ENNReal.ofReal (1 / (1 + ‖a z‖ ^ 2)))
    with hw'
  have haS : ContinuousOn a S := ha.mono hSD
  have hw'm : AEMeasurable w' (volume.restrict S) :=
    hWm.min (ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuousOn_const.div (continuousOn_const.add (haS.norm.pow 2)) fun z _ =>
        (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne').aemeasurable hSm')))
  have hpt1 : ∀ z, ENNReal.ofReal (‖a z‖ ^ 2) * w' z ≤ 1 := by
    intro z
    calc ENNReal.ofReal (‖a z‖ ^ 2) * w' z
        ≤ ENNReal.ofReal (‖a z‖ ^ 2) * ENNReal.ofReal (1 / (1 + ‖a z‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) zero_le
      _ = ENNReal.ofReal (‖a z‖ ^ 2 * (1 / (1 + ‖a z‖ ^ 2))) :=
          (ENNReal.ofReal_mul (sq_nonneg _)).symm
      _ ≤ ENNReal.ofReal 1 := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_one_div, div_le_one (by positivity)]
          linarith
      _ = 1 := ENNReal.ofReal_one
  set A' : ℝ≥0∞ := 2 * B + 2 * volume S with hA'
  have hA'top : A' ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hB,
    ENNReal.mul_ne_top (by norm_num) (volume_lt_top_of_isCompact_closure hSc).ne⟩
  have hbound' : ∀ ν, ∫⁻ z in Sν ν, ENNReal.ofReal (‖G ν z‖ ^ 2) * w' z ≤ A' := by
    intro ν
    calc ∫⁻ z in Sν ν, ENNReal.ofReal (‖G ν z‖ ^ 2) * w' z
        ≤ ∫⁻ z in Sν ν, (2 * (ENNReal.ofReal (‖a z - G ν z‖ ^ 2) * W z) + 2 * 1) := by
          refine lintegral_mono fun z => ?_
          have h1 : ENNReal.ofReal (‖G ν z‖ ^ 2) ≤
              2 * ENNReal.ofReal (‖a z - G ν z‖ ^ 2) + 2 * ENNReal.ofReal (‖a z‖ ^ 2) := by
            rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
            exact ENNReal.ofReal_le_ofReal (norm_sq_le_two_mul (a z) (G ν z))
          calc ENNReal.ofReal (‖G ν z‖ ^ 2) * w' z
              ≤ (2 * ENNReal.ofReal (‖a z - G ν z‖ ^ 2) + 2 * ENNReal.ofReal (‖a z‖ ^ 2)) *
                  w' z := mul_le_mul_of_nonneg_right h1 zero_le
            _ = 2 * (ENNReal.ofReal (‖a z - G ν z‖ ^ 2) * w' z) +
                  2 * (ENNReal.ofReal (‖a z‖ ^ 2) * w' z) := by ring
            _ ≤ _ := by
                gcongr
                · exact min_le_left _ _
                · exact hpt1 z
      _ = 2 * (∫⁻ z in Sν ν, ENNReal.ofReal (‖a z - G ν z‖ ^ 2) * W z) + 2 * volume (Sν ν) := by
          rw [lintegral_add_right' _ aemeasurable_const, lintegral_const_mul' _ _ (by norm_num),
            setLIntegral_const, mul_one, mul_comm (2 : ℝ≥0∞) (volume (Sν ν))]
      _ ≤ A' := by
          rw [hA']
          gcongr
          · exact hbound ν
          · exact hSν ν
  obtain ⟨ψ, G', hψ, hG', hconv, -, -⟩ :=
    exists_subseq_differentiableOn_extension_of_weighted_bounds (N := N) (α := Empty)
      (ι := Empty.elim) (g := Empty.elim) (U := Sν) hSo hSm
      (w := fun _ => w') (fun _ _ => monotone_const)
      (fun _ => hw'm)
      (fun x hx => by
        obtain ⟨ρ, hρ, δ, hδ, hle⟩ := hWlow x hx
        have hca : ContinuousAt a x := haS.continuousAt (hSo'.mem_nhds hx)
        obtain ⟨ρ', hρ', hball'⟩ := Metric.continuousAt_iff.mp hca 1 one_pos
        refine ⟨min ρ ρ', lt_min hρ hρ', min δ (1 / (1 + (‖a x‖ + 1) ^ 2)),
          lt_min hδ (by positivity), fun y hy => le_min ?_ ?_⟩
        · exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans
            (hle y (ball_subset_ball (min_le_left _ _) hy))
        · refine (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
            (ENNReal.ofReal_le_ofReal ?_)
          have hy' : dist y x < ρ' := (mem_ball.mp hy).trans_le (min_le_right _ _)
          have hdist := hball' hy'
          have hn : ‖a y‖ ≤ ‖a x‖ + 1 := by
            have := norm_sub_norm_le (a y) (a x)
            rw [dist_eq_norm] at hdist
            linarith
          have hn2 : ‖a y‖ ^ 2 ≤ (‖a x‖ + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
          exact one_div_le_one_div_of_le (by positivity) (by linarith))
      hG (fun _ e => e.elim) hA'top (fun ν => by simpa using hbound' ν)
  refine ⟨G', hG', ?_⟩
  have hfixed : ∀ ν₀, ∫⁻ z in Sν ν₀, ENNReal.ofReal (‖a z - G' z‖ ^ 2) * W z ≤ B := by
    intro ν₀
    have hle_idx : ∀ k, ν₀ ≤ ψ (k + ν₀) := fun k => (Nat.le_add_left ν₀ k).trans (hψ.id_le _)
    refine GluingSystem.lintegral_le_of_tendsto (hSo ν₀).measurableSet
      (hWm.mono_measure (Measure.restrict_mono (hSν ν₀) le_rfl)) (F := fun k => G (ψ (k + ν₀)))
      (fun k => ((haS.mono (hSν ν₀)).sub ((hG (ψ (k + ν₀))).continuousOn.mono
        (hSm (hle_idx k)))).aestronglyMeasurable (hSo ν₀).measurableSet)
      (fun z hz => (hconv.tendsto_at (hSν ν₀ hz)).comp (tendsto_add_atTop_nat ν₀))
      (Eventually.of_forall fun k => (lintegral_mono_set (hSm (hle_idx k))).trans
        (hbound (ψ (k + ν₀))))
  rw [setLIntegral_iUnion_of_directed _ hSm.directed_le]
  exact iSup_le hfixed

theorem iUnion_prodDom (z₀ : ComplexModel n) (r : ℝ) :
    (⋃ ν : ℕ, prodDom z₀ r (1 - 1 / ((ν : ℝ) + 2))) = prodDom z₀ r 1 := by
  ext w
  simp only [mem_iUnion, mem_prodDom]
  constructor
  · rintro ⟨ν, h1, h2⟩
    have h3 : (0 : ℝ) ≤ 1 / ((ν : ℝ) + 2) := by positivity
    exact ⟨h1, h2.trans_le (by linarith)⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨ν, hν⟩ := exists_nat_gt (1 / (1 - ‖((prodModelEquiv n 1).symm w).2‖))
    refine ⟨ν, h1, ?_⟩
    have hpos : 0 < 1 - ‖((prodModelEquiv n 1).symm w).2‖ := by linarith
    have h3 : 1 / ((ν : ℝ) + 2) < 1 - ‖((prodModelEquiv n 1).symm w).2‖ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hν
      nlinarith
    linarith

theorem monotone_prodDom (z₀ : ComplexModel n) (r : ℝ) :
    Monotone fun ν : ℕ => prodDom z₀ r (1 - 1 / ((ν : ℝ) + 2)) := by
  intro i j hij
  refine prodDom_mono le_rfl ?_
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  have : 1 / ((j : ℝ) + 2) ≤ 1 / ((i : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- **Local `L²` correction on a product `B(z₀, R) × Δ`** (`claude-siu-l2:product-local`).  For
`r < R`, a plurisubharmonic `Ψ` on `D_R = B(z₀, R) × Δ`, `c > 0`, any `w₀` and a smooth `a` on
`D_R`, there is `G` holomorphic on *all of* `D_r = B(z₀, r) × Δ` with
`∫_{D_r} |a - G|² e^{-Ψ - c|w - w₀|²} ≤ (2/c) ∫_{D_R} |∂̄a|² e^{-Ψ - c|w - w₀|²}`. -/
theorem productCorrection (z₀ : ComplexModel n) {r R : ℝ} (hrR : r < R)
    (w₀ : ComplexModel (n + 1)) {c : ℝ} (hc : 0 < c) {Ψ : ComplexModel (n + 1) → EReal}
    (hΨ : PlurisubharmonicOn Ψ (prodDom z₀ R 1)) {a : ComplexModel (n + 1) → ℂ}
    (ha : ContDiffOn ℝ ∞ a (prodDom z₀ R 1)) :
    ∃ G : ComplexModel (n + 1) → ℂ, DifferentiableOn ℂ G (prodDom z₀ r 1) ∧
      ∫⁻ z in prodDom z₀ r 1, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ballWeight Ψ c w₀ z ≤
        ENNReal.ofReal (2 / c) *
          ∫⁻ z in prodDom z₀ R 1, ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c w₀ z := by
  set E : ℝ≥0∞ := ∫⁻ z in prodDom z₀ R 1, ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c w₀ z
    with hEdef
  have h2c : (0 : ℝ) < 2 / c := by positivity
  by_cases hE : E = ⊤
  · refine ⟨fun _ => 0, differentiableOn_const 0, ?_⟩
    rw [hE, ENNReal.mul_top (ENNReal.ofReal_pos.mpr h2c).ne']
    exact le_top
  set Sν : ℕ → Set (ComplexModel (n + 1)) := fun ν => prodDom z₀ r (1 - 1 / ((ν : ℝ) + 2))
    with hSνdef
  have hDo := isOpen_prodDom z₀ R 1
  have hSU : (⋃ ν, Sν ν) = prodDom z₀ r 1 := iUnion_prodDom z₀ r
  have hlt : ∀ ν : ℕ, 1 - 1 / ((ν : ℝ) + 2) < 1 := fun ν => by
    have : (0 : ℝ) < 1 / ((ν : ℝ) + 2) := by positivity
    linarith
  have hloc : ∀ ν, ∃ G : ComplexModel (n + 1) → ℂ, DifferentiableOn ℂ G (Sν ν) ∧
      ∫⁻ z in Sν ν, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ballWeight Ψ c w₀ z ≤
        ENNReal.ofReal (2 / c) * E := fun ν =>
    convexCorrection hDo (convex_prodDom z₀ R 1) (isBounded_prodDom z₀ R 1)
      (isOpen_prodDom _ _ _) (isCompact_closure_prodDom _ _ _)
      (closure_prodDom_subset hrR (hlt ν)) w₀ hc hΨ ha
  choose G hG hGb using hloc
  have hrD : prodDom z₀ r 1 ⊆ prodDom z₀ R 1 := prodDom_mono hrR.le le_rfl
  obtain ⟨G', hG', hG'b⟩ := exists_exhaustion_limit (fun ν => isOpen_prodDom _ _ _)
    (monotone_prodDom z₀ r) (by rw [hSU]; exact isCompact_closure_prodDom _ _ _)
    (by rw [hSU]; exact hrD) ha.continuousOn
    (by
      rw [hSU]
      exact (aemeasurable_ballWeight hDo hΨ c w₀).mono_measure (Measure.restrict_mono hrD le_rfl))
    (fun x hx => by
      rw [hSU] at hx
      obtain ⟨ρ, hρ, δ, hδ, -, hle⟩ := ballWeight_locally_ge hDo (isBounded_prodDom z₀ R 1) hΨ
        hc w₀ (hrD hx)
      exact ⟨ρ, hρ, δ, hδ, hle⟩)
    hG (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE) hGb
  rw [hSU] at hG' hG'b
  exact ⟨G', hG', hG'b⟩

end SGPT.PSH.SiuL2
