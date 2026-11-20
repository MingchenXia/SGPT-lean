import SGPT.Trace.OTExt5Data

/-!
# Vanishing on `Y` from the critical weight `R^{-q}`

Blueprint `claude-ot-ext5.tex`, node `claude-ot-ext5:vanish`.  Xia, *Foundations of
pluripotential theory*, q07, proof of `thm:compact-submanifold-extension`, Step 3: "since
`R ≤ C|w|²` near `y` and `∫_{|w| < r} |w|^{-2q} dV(w) = ∞`, the continuous function `u_ε` vanishes
at `y`".

* `eq_zero_of_lintegral_logPole`: a continuous `g ≥ 0` with `∫_X g R^{-q} dμ < ∞` vanishes on `W`
  (`q = n - m` the codimension, `R` a normal pole of `W`).  The proof applies the critical
  non-integrability of the pole region (`exists_poleRegion`, clause 4) to the constant function `1`
  on the open set `{g > g(y)/2}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace SGPT.Trace.OTExt5

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.SubmanifoldChartedSpace
  SGPT.Foundations.Analysis.FirstPass.RegularLocusDense SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Trace.TwistedL2 SGPT.Trace.OTMargin
open SGPT.Trace.OTExt2 (IsGlobalNormalPole logPole)

variable {n m : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [MeasurableSpace X] [BorelSpace X] {W : Set X}

/-- **Vanishing from the critical weight**: a continuous `g ≥ 0` with `∫ g R^{-q} dμ < ∞`
(`q = n - m`) vanishes on `W`. -/
theorem eq_zero_of_lintegral_logPole {μ : Measure X} (hμ : IsSmoothPositiveVolume (n := n) μ)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x m) (hmn : m < n) {ωb : KahlerBackground n X}
    {R : X → ℝ} (hR : IsGlobalNormalPole ωb W R) {g : X → ℝ} (hg : Continuous g)
    (hint : ∫⁻ x, ENNReal.ofReal (g x) * multiplierWeight ((n - m : ℕ) : ℝ) (logPole R x) ∂μ ≠ ⊤)
    {y : X} (hy : y ∈ W) : g y ≤ 0 := by
  by_contra hgy
  rw [not_le] at hgy
  set Fd := FlatData.ofRegularAtDim (hW y hy)
  have hpF := FlatData.mem_ambSource_ofRegularAtDim (hW y hy)
  have hp0 : fcoord Fd y = 0 := (hW y hy).2.2.choose_spec.2.1
  obtain ⟨U, hU, C, hC⟩ := localForm_normalized hW hR.pole 0 ⟨y, hy⟩
  have hloc : ∃ U ∈ 𝓝 y, ∃ C : ℝ, ∀ x ∈ U, x ∉ W →
      |(logPole R x).toReal - Real.log (normalWeight n m (fcoord Fd x))| ≤ C := by
    refine ⟨U, hU, C, fun x hx hxW => ?_⟩
    have := hC x hx hxW
    rwa [neg_zero, EReal.coe_zero, add_zero] at this
  obtain ⟨ε₀, hε₀, hreg⟩ := exists_poleRegion hμ Fd hmn hpF hp0 hR.pole.continuous.measurable
    hR.pole.ne_top (fun x hx => (hR.pole.eq_bot_iff x).mp hx) hloc
  obtain ⟨-, -, -, h4, -⟩ := hreg ε₀ hε₀ le_rfl
  set O : Set X := {x | g y / 2 < g x} with hO
  have hOo : IsOpen O := isOpen_lt continuous_const hg
  have hyO : y ∈ O := by show g y / 2 < g y; linarith
  have hyB : y ∈ finv Fd '' ball 0 ε₀ := ⟨0, mem_ball_self hε₀, by rw [← hp0, finv_fcoord Fd hpF]⟩
  have hfin : ∫⁻ x in O ∩ finv Fd '' closedBall 0 ε₀,
      ENNReal.ofReal (‖(fun _ : X => (1 : ℂ)) x‖ ^ 2) *
        multiplierWeight ((n - m : ℕ) : ℝ) (logPole R x) ∂μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2 / g y)) hint) ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_mono_ae' ((hOo.measurableSet).inter ?_) ?_).trans
      (setLIntegral_le_lintegral _ _)
    · exact ((isCompact_closedBall _ _).image_of_continuousOn
        ((continuousOn_finv Fd).mono (hreg ε₀ hε₀ le_rfl).1)).isClosed.measurableSet
    · refine Eventually.of_forall fun x hx => ?_
      have hxO : g y / 2 < g x := hx.1
      simp only [norm_one, one_pow, ENNReal.ofReal_one, one_mul]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine le_mul_of_one_le_left zero_le (ENNReal.one_le_ofReal.mpr ?_)
      rw [div_mul_eq_mul_div, le_div_iff₀ hgy]
      linarith
  have := h4 (fun _ => (1 : ℂ)) O hOo (fun _ _ => mdifferentiableAt_const) y hyO hy hyB hfin
  exact one_ne_zero this

end SGPT.Trace.OTExt5
