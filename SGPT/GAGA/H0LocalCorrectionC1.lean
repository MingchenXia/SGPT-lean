import SGPT.PSH.GlobalL2LocalSingular

/-!
# Local `L²` corrections on balls for `C¹` data


`SGPT.PSH.GlobalL2.localBallCorrectionSmooth` and `SGPT.PSH.GlobalL2.localBallCorrection`
(Hörmander's estimate on a ball, smooth resp. singular plurisubharmonic weights) are stated for
`C^∞` data `a`, but their proofs only use that `a` is `C¹` (the weak `∂̄`-closedness of `∂̄a`, the
continuity of `|∂̄a|²` and Weyl's lemma).  This file restates them for `C¹` data, with the same
proofs.  The `C¹` version is needed for the cone extension of `SGPT/GAGA/H0ConeExtension.lean`:
there the datum is a homogeneous function of degree `k ≥ 2` on `ℂ^{N+1}`, which is `C¹` but in
general not `C^∞` at the vertex.

* `SGPT.GAGA.H0.localBallCorrectionSmoothC1`: smooth weights `Φ` with `Levi Φ ≥ c`.
* `SGPT.GAGA.H0.localBallCorrectionC1`: weights `Ψ + c|z - z₀|²`, `Ψ` plurisubharmonic.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.GAGA.H0

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal ContDiff ComplexConjugate
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.Hormander
  SGPT.Foundations.Analysis.Pending.CauchyGreen SGPT.Foundations.Analysis.Pending.OTChen
open SGPT.PSH.GlobalL2

variable {n : ℕ}

/-- **Local `L²` correction on a ball, smooth weights, `C¹` data** (the proof of
`SGPT.PSH.GlobalL2.localBallCorrectionSmooth`, which only uses that `a` is `C¹`). -/
theorem localBallCorrectionSmoothC1 (z₀ : ComplexModel n) (r R : ℝ) (_hr : 0 < r) (hrR : r < R)
    (c : ℝ) (hc : 0 < c) (Φ : ComplexModel n → ℝ) (hΦ : ContDiffOn ℝ ∞ Φ (ball z₀ R))
    (hΦL : ∀ z ∈ ball z₀ R, ∀ ξ : ComplexModel n, c * ‖ξ‖ ^ 2 ≤ leviForm Φ z ξ)
    (a : ComplexModel n → ℂ) (ha : ContDiffOn ℝ 1 a (ball z₀ R)) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G (ball z₀ r) ∧
      ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ENNReal.ofReal (Real.exp (-Φ z)) ≤
        ENNReal.ofReal (2 / c) *
          ∫⁻ z in ball z₀ R, ENNReal.ofReal (dbarNormSq a z) * ENNReal.ofReal (Real.exp (-Φ z)) := by
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
  have ha1 : ContDiffOn ℝ 1 a D := ha
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

/-- **Local `L²` correction on a ball, singular weights, `C¹` data** (the proof of
`SGPT.PSH.GlobalL2.localBallCorrection`, which only uses that `a` is `C¹`): for `Ψ`
plurisubharmonic on `B(z₀, R)`, `c > 0` and `a` of class `C¹` on `B(z₀, R)` there is `G`
holomorphic on `B(z₀, r)` with
`∫_{B(z₀,r)} |a - G|² e^{-Ψ - c|z-z₀|²} ≤ (2/c) ∫_{B(z₀,R)} |∂̄a|² e^{-Ψ - c|z-z₀|²}`. -/
theorem localBallCorrectionC1 (z₀ : ComplexModel n) (r R : ℝ) (hr : 0 < r) (hrR : r < R)
    (c : ℝ) (hc : 0 < c) (Ψ : ComplexModel n → EReal) (hΨ : PlurisubharmonicOn Ψ (ball z₀ R))
    (a : ComplexModel n → ℂ) (ha : ContDiffOn ℝ 1 a (ball z₀ R)) :
    ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G (ball z₀ r) ∧
      ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - G z‖ ^ 2) * ballWeight Ψ c z₀ z ≤
        ENNReal.ofReal (2 / c) *
          ∫⁻ z in ball z₀ R, ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c z₀ z := by
  set S : ℝ≥0∞ := ∫⁻ z in ball z₀ R, ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c z₀ z
    with hSdef
  have h2c : (0 : ℝ) < 2 / c := by positivity
  by_cases hS : S = ⊤
  · refine ⟨fun _ => 0, differentiableOn_const 0, ?_⟩
    rw [hS, ENNReal.mul_top (ENNReal.ofReal_pos.mpr h2c).ne']
    exact le_top
  have hAtop : ENNReal.ofReal (2 / c) * S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS
  set R' : ℝ := (r + R) / 2 with hR'def
  have hrR' : r < R' := by rw [hR'def]; linarith
  have hR'R : R' < R := by rw [hR'def]; linarith
  have hr0 : (0 : ℝ) ≤ r := hr.le
  let Ω : TopologicalSpace.Opens (ComplexModel n) := ⟨ball z₀ R, isOpen_ball⟩
  let A : TopologicalSpace.Opens (ComplexModel n) := ⟨ball z₀ R', isOpen_ball⟩
  have hA : RelativelyCompactIn A Ω := by
    refine ⟨(isCompact_closedBall z₀ R').of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
      closure_ball_subset_closedBall.trans (closedBall_subset_ball hR'R)⟩
  have hΨΩ : PlurisubharmonicOn Ψ Ω := hΨ
  have hrA : ball z₀ r ⊆ ball z₀ R' := ball_subset_ball hrR'.le
  have hrR'' : ball z₀ r ⊆ ball z₀ R := ball_subset_ball hrR.le
  have haR : ContinuousOn a (ball z₀ R) := ha.continuousOn
  obtain ⟨Ma, hMa⟩ := exists_bound_norm_sq_on_ball hrR haR
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
    rw [e, LocalBedfordTaylorCollar.leviForm_comp_sub_const, leviForm_smul (contDiff_norm_sq ℝ).contDiffAt,
      leviForm_norm_sq]
  -- Stage 1: for fixed `N`, the smooth regularizations of `max (Ψ, -N)`
  have stage1 : ∀ N : ℕ, ∃ G : ComplexModel n → ℂ, DifferentiableOn ℂ G (ball z₀ r) ∧
      ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - G z‖ ^ 2) *
          ballWeight (fun z => (truncationReal Ψ N z : EReal)) c z₀ z ≤
        ENNReal.ofReal (2 / c) * S := by
    intro N
    obtain ⟨fs, hfs⟩ := HolomorphicPullback.exists_decreasingMollifierApproximation
      (truncationReal_isLocallyBoundedPshOn hΨΩ N) hA
    set Φ : ℕ → ComplexModel n → ℝ := fun j z => fs j z + c * ‖z - z₀‖ ^ 2 with hΦdef
    have hΦs : ∀ j, ContDiffOn ℝ ∞ (Φ j) (ball z₀ R') := fun j =>
      (hfs.1 j).1.add hnsqs.contDiffOn
    have hΦL : ∀ j, ∀ z ∈ ball z₀ R', ∀ ξ : ComplexModel n, c * ‖ξ‖ ^ 2 ≤ leviForm (Φ j) z ξ := by
      intro j z hz ξ
      have h1 : ContDiffAt ℝ 2 (fs j) z :=
        (((hfs.1 j).1.contDiffAt (isOpen_ball.mem_nhds hz))).of_le
          (WithTop.coe_le_coe.mpr le_top)
      have h2 : ContDiffAt ℝ 2 (fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2) z :=
        (hnsqs.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
      have hsplit : Φ j = fs j + fun y : ComplexModel n => c * ‖y - z₀‖ ^ 2 := rfl
      rw [hsplit, leviForm_add h1 h2, hLeviNsq]
      have h0 := leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := A) (hfs.1 j).1
        (hfs.1 j).2.1 hz ξ
      linarith
    have hge : ∀ j, ∀ z ∈ ball z₀ R', truncationReal Ψ N z ≤ fs j z := fun j z hz =>
      (hfs.2.1 z hz).le_of_tendsto (hfs.2.2 z hz) j
    have hΨle : ∀ z ∈ ball z₀ R, Ψ z ≤ (truncationReal Ψ N z : EReal) := fun z hz => by
      rw [coe_truncationReal hΨΩ N hz]
      exact le_max_left _ _
    have hloc := fun j => localBallCorrectionSmoothC1 z₀ r R' hr hrR' c hc (Φ j) (hΦs j) (hΦL j) a
      (ha.mono (ball_subset_ball hR'R.le))
    choose F hF hFb using hloc
    have hwle : ∀ j, ∀ z ∈ ball z₀ R', ENNReal.ofReal (Real.exp (-Φ j z)) ≤ ballWeight Ψ c z₀ z := by
      intro j z hz
      have : ENNReal.ofReal (Real.exp (-Φ j z)) = multiplierWeight 1 ((Φ j z : ℝ) : EReal) := by
        rw [multiplierWeight_coe, one_mul]
      rw [this, ballWeight]
      refine multiplierWeight_antitone zero_le_one ?_
      rw [hΦdef]
      dsimp only
      rw [EReal.coe_add]
      gcongr
      exact (hΨle z (ball_subset_ball hR'R.le hz)).trans (EReal.coe_le_coe_iff.mpr (hge j z hz))
    have hbound : ∀ j, ∫⁻ z in ball z₀ r, ENNReal.ofReal (‖a z - F j z‖ ^ 2) *
        ENNReal.ofReal (Real.exp (-Φ j z)) ≤ ENNReal.ofReal (2 / c) * S := by
      intro j
      refine (hFb j).trans (mul_le_mul_of_nonneg_left ?_ zero_le)
      calc ∫⁻ z in ball z₀ R', ENNReal.ofReal (dbarNormSq a z) * ENNReal.ofReal (Real.exp (-Φ j z))
          ≤ ∫⁻ z in ball z₀ R', ENNReal.ofReal (dbarNormSq a z) * ballWeight Ψ c z₀ z :=
            setLIntegral_mono' isOpen_ball.measurableSet fun z hz =>
              mul_le_mul_of_nonneg_left (hwle j z hz) zero_le
        _ ≤ S := lintegral_mono_set (ball_subset_ball hR'R.le)
    have hΦc : ∀ j, ContinuousOn (Φ j) (ball z₀ R') := fun j => (hΦs j).continuousOn
    obtain ⟨G, hG, hGint⟩ := exists_correction_limit isOpen_ball (haR.mono hrR'')
      (w := fun j z => ENNReal.ofReal (Real.exp (-Φ j z)))
      (fun z hz i j hij => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by
        have := (hfs.2.1 z (hrA hz)) hij
        simp only [hΦdef]; linarith)))
      (fun j => (ENNReal.measurable_ofReal.comp Real.measurable_exp).comp_aemeasurable
        (((hΦc j).mono hrA).neg.aemeasurable isOpen_ball.measurableSet))
      (fun x hx => by
        have hcont : ContinuousAt (Φ 0) x := (hΦc 0).continuousAt (isOpen_ball.mem_nhds (hrA hx))
        obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
        refine ⟨ρ, hρ, Real.exp (-(Φ 0 x + 1)), Real.exp_pos _, fun y hy => ?_⟩
        refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
        have h1 := hball (mem_ball.mp hy)
        rw [Real.dist_eq] at h1
        linarith [le_abs_self (Φ 0 y - Φ 0 x)])
      hF hAtop hbound
      (by
        obtain ⟨MΦ, hMΦ⟩ := (isCompact_closedBall z₀ r).exists_bound_of_continuousOn
          ((hΦc 0).mono (closedBall_subset_ball hrR'))
        refine (setLIntegral_ball_lt_top_of_bound (M := Ma * Real.exp MΦ) fun z hz => ?_).ne
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (mul_le_mul (hMa z hz) (Real.exp_le_exp.mpr ?_)
          (Real.exp_pos _).le (le_trans (sq_nonneg _) (hMa z hz)))
        have := hMΦ z (ball_subset_closedBall hz)
        rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (Φ 0 z)])
    refine ⟨G, hG, le_trans ?_ hGint⟩
    refine setLIntegral_mono' isOpen_ball.measurableSet fun z hz => ?_
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    rw [ballWeight_coe]
    have ht : Tendsto (fun j => ENNReal.ofReal (Real.exp (-Φ j z))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-(truncationReal Ψ N z + c * ‖z - z₀‖ ^ 2))))) := by
      refine ENNReal.tendsto_ofReal (Real.continuous_exp.tendsto _ |>.comp ?_)
      exact ((hfs.2.2 z (hrA hz)).add tendsto_const_nhds).neg
    exact le_of_tendsto' ht fun j => le_iSup (fun j => ENNReal.ofReal (Real.exp (-Φ j z))) j
  -- Stage 2: `N → ∞`
  choose G hG hGb using stage1
  have hwmeas2 : ∀ N, AEMeasurable (fun z => ballWeight (fun z => (truncationReal Ψ N z : EReal))
      c z₀ z) (volume.restrict (ball z₀ r)) := by
    intro N
    have hq : QuasiPlurisubharmonicOn (fun z => (truncationReal Ψ N z : EReal)) (ball z₀ R) :=
      fun x hx => (truncationReal_plurisubharmonicOn hΨΩ N x hx).quasiPlurisubharmonicAt
    have h := aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
      (μ := volume) isOpen_ball hq one_ne_zero (f := fun _ => (1 : ℂ)) continuousOn_const
    have h' : AEMeasurable (fun z => multiplierWeight 1 (truncationReal Ψ N z : EReal))
        (volume.restrict (ball z₀ R)) := h.congr (Eventually.of_forall fun z => by
          simp [multiplierDensity])
    have h'' := h'.mono_measure (Measure.restrict_mono hrR'' le_rfl)
    refine (h''.mul ((ENNReal.measurable_ofReal.comp Real.measurable_exp).comp_aemeasurable
      (hnsqc.neg.aemeasurable))).congr (Eventually.of_forall fun z => ?_)
    exact (ballWeight_eq_mul (Ψ := fun z => ((truncationReal Ψ N z : ℝ) : EReal))
      (EReal.coe_ne_top _) c z₀).symm
  obtain ⟨G', hG', hG'int⟩ := exists_correction_limit isOpen_ball (haR.mono hrR'')
    (w := fun N z => ballWeight (fun z => (truncationReal Ψ N z : EReal)) c z₀ z)
    (fun z hz i j hij => by
      simp only [ballWeight_coe]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have := truncationReal_antitone hΨΩ (hrR'' hz) hij
      linarith)
    hwmeas2
    (fun x hx => by
      obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp isOpen_ball x (hrR'' hx)
      obtain ⟨B, hB0, hB⟩ := hΨ.exists_nonnegative_compact_upper_bound
        (isCompact_closedBall x (ρ₀ / 2)) ((closedBall_subset_ball (by linarith)).trans hball)
      refine ⟨ρ₀ / 2, by positivity, Real.exp (-(B + c * R ^ 2)), Real.exp_pos _, fun y hy => ?_⟩
      have hyR : y ∈ ball z₀ R := hball (ball_subset_ball (by linarith) hy)
      rw [ballWeight_coe]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have htr : truncationReal Ψ 0 y ≤ B := by
        apply EReal.coe_le_coe_iff.mp
        rw [coe_truncationReal hΨΩ 0 hyR]
        refine max_le (hB y (ball_subset_closedBall hy)) ?_
        exact EReal.coe_le_coe_iff.mpr (by simpa using hB0)
      have hyz : ‖y - z₀‖ ^ 2 ≤ R ^ 2 := by
        have := mem_ball_iff_norm.mp hyR
        exact pow_le_pow_left₀ (norm_nonneg _) this.le 2
      nlinarith)
    hG hAtop hGb
    (by
      refine (setLIntegral_ball_lt_top_of_bound (M := Ma) fun z hz => ?_).ne
      have hw1 : ballWeight (fun z => (truncationReal Ψ 0 z : EReal)) c z₀ z ≤ 1 := by
        rw [ballWeight_coe, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.exp_le_one_iff, neg_nonpos]
        have h0 : 0 ≤ truncationReal Ψ 0 z := by
          apply EReal.coe_le_coe_iff.mp
          rw [coe_truncationReal hΨΩ 0 (hrR'' hz)]
          exact le_max_right _ _ |>.trans' (by simp)
        linarith [hnsq z]
      calc ENNReal.ofReal (‖a z‖ ^ 2) * ballWeight (fun z => (truncationReal Ψ 0 z : EReal)) c z₀ z
          ≤ ENNReal.ofReal (‖a z‖ ^ 2) * 1 := mul_le_mul_of_nonneg_left hw1 zero_le
        _ ≤ ENNReal.ofReal Ma := by rw [mul_one]; exact ENNReal.ofReal_le_ofReal (hMa z hz))
  refine ⟨G', hG', le_trans ?_ hG'int⟩
  refine setLIntegral_mono' isOpen_ball.measurableSet fun z hz => ?_
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  have hzR := hrR'' hz
  rw [ballWeight_eq_mul ((hΨ z hzR).ne_top) c z₀]
  have hfac : ∀ N : ℕ, ballWeight (fun z => (truncationReal Ψ N z : EReal)) c z₀ z =
      multiplierWeight 1 (truncationReal Ψ N z : EReal) *
        ENNReal.ofReal (Real.exp (-(c * ‖z - z₀‖ ^ 2))) := fun N =>
    ballWeight_eq_mul (Ψ := fun z => ((truncationReal Ψ N z : ℝ) : EReal)) (EReal.coe_ne_top _) c z₀
  rw [iSup_congr hfac, ← ENNReal.iSup_mul]
  exact mul_le_mul_of_nonneg_right (multiplierWeight_le_iSup_truncationReal hΨΩ one_pos hzR)
    zero_le

end SGPT.GAGA.H0
