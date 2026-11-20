import SGPT.Envelopes.LapClassRooftop
import SGPT.Envelopes.DNTRegKahlerClass

/-!
# The trace estimate for a background different from the metric

Lane LAP-CLASS (`claude-lap-class`, nodes `lap-class:trace-form`,
`lap-class:trace-estimate-gen`).  Source: FPT `lem:penalized-equation-trace` as stated there, with
a Kähler background `κ` for the envelope and a Kähler form `ω` measuring the Laplacian.

* `chartTrace`, `traceForm`: `tr_ω α = Re tr(H_ω⁻¹ H_α)`, chart independent
  (`chartTrace_eq_of_mem`) and continuous (`continuous_traceForm`).
* `levTr_le_of_isLocalMax_gen`: the flat maximum principle step with `Hess σ(0) ≥ γ`.
* `betaSolution_traceForm_le`: for β-solutions of `(κ + ddᶜu)^N = e^{β(u - F)} κ^N` and
  `Δ_ω F ≤ S`, `tr_ω(κ + ddᶜu) ≤ 2(T + S) e^{a(u - m)}`, `a, T, β₀` depending on `(Y, ω, κ)`.

The consequences (`prop:DR16_C11bar` for any reference metric, `thm:DNT23_C11bar` for Kähler
classes) are in `SGPT.Envelopes.LapClassKahlerClass`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Matrix Metric MeasureTheory
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.Envelopes.LapClass

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
open KahlerLaplacianChart KahlerLaplacianStokes IntegrationCurrent HolomorphicMixedDensity
open SGPT.Analysis.KahlerNormal SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.DNTReg
open AubinYauEstimate AubinYauUniformConstants

/-! ### The flat step with a general background -/

section Flat

variable {n : ℕ}

/-- **The maximum principle step, general background.**  As `levTr_le_of_isLocalMax`, with
`Hess_ℂ σ(0) ≥ γ` instead of `= 1`: if `a γ ≥ 2K + C₁`, `β > 2an` and
`∑ₚ (log det Hess_ℂ ψ)_{pp̄}(0) ≥ β(tr Hess ψ(0) - tr Hess σ(0) - ∑ₚ F_{pp̄}(0)) - C₁` with
`tr Hess σ(0) ≤ T`, `∑ₚ F_{pp̄}(0) ≤ S`, then `tr Hess ψ(0) ≤ 2(T + S)`. -/
theorem levTr_le_of_isLocalMax_gen (hn : 0 < n) {ψ σ F : ComplexModel n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hσ : ContDiff ℝ ∞ σ) (hpos : (complexHessian ψ 0).PosDef)
    {γ T β K a C₁ S : ℝ} (hγ : 0 < γ) (hσlow : ∀ v, γ * ‖v‖ ^ 2 ≤ leviForm σ 0 v)
    (hσT : levTr σ 0 ≤ T) (hK : 0 ≤ K) (hC₁ : 0 ≤ C₁) (ha : 2 * K + C₁ ≤ a * γ)
    (hβ : 2 * a * n < β)
    (hdetlow : β * (levTr ψ 0 - levTr σ 0 - levTr F 0) - C₁ ≤
      levTr (fun w => Real.log (complexHessian ψ w).det.re) 0)
    (hFS : levTr F 0 ≤ S)
    (hmax : IsLocalMax (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0) :
    levTr ψ 0 ≤ 2 * (T + S) := by
  classical
  set P := (complexHessian ψ 0)⁻¹ with hPdef
  have hP : P.PosSemidef := hpos.inv.posSemidef
  obtain ⟨m, w, hw, htrP⟩ := exists_trace_eq_sum_leviForm hP
  set trP := P.trace.re with htrPdef
  have htrP0 : 0 ≤ trP := by rw [htrP]; positivity
  have hψ2 := AubinYauLocalStep.contDiffAt_two hψ (0 : ComplexModel n)
  have hσ2 := AubinYauLocalStep.contDiffAt_two hσ (0 : ComplexModel n)
  have hℓpos : ∀ p : Fin n, 0 < leviForm ψ 0 (coordinateVector p) := by
    intro p
    have hne : (Pi.single p (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
      intro h
      have := congrFun h p
      simp at this
    have h1 := hpos.re_dotProduct_pos hne
    have h2 := dotProduct_mulVec_complexHessian_eq_leviForm hψ2 (Pi.single p (1 : ℂ))
    rw [coordCombination_single] at h2
    rw [h2] at h1
    simpa using h1
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have hℓ₀ : 0 < levTr ψ 0 := Finset.sum_pos (fun p _ => hℓpos p) hne
  have hnℓ : (n : ℝ) ≤ levTr ψ 0 * trP := by
    have h1 : ∀ p : Fin n, 1 ≤ leviForm ψ 0 (coordinateVector p) * trP := by
      intro p
      have hnorm : ‖(coordinateVector p : ComplexModel n)‖ = 1 := by
        simp [coordinateVector]
      exact AubinYauLocalStep.one_le_leviForm_mul_re_trace_inv hψ2 hpos hnorm
    have h2 := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => h1 p
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      ← Finset.sum_mul] at h2
    exact h2
  have hL : ContDiff ℝ ∞ (levTr ψ) := by
    have : levTr ψ = fun y => ∑ p, leviForm ψ y (coordinateVector p) := rfl
    rw [this]
    exact ContDiff.sum fun p _ => BlockiLocalEstimate.contDiff_leviForm hψ _
  have hlogL : ContDiffAt ℝ 2 (fun w => Real.log (levTr ψ w)) 0 :=
    (AubinYauLocalStep.contDiffAt_two hL 0).log hℓ₀.ne'
  have hsq : ContDiffAt ℝ 2 (fun w : ComplexModel n => ‖w‖ ^ 2) 0 :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hΘ2 : ContDiffAt ℝ 2
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0 :=
    (hlogL.sub (contDiffAt_const.mul hsq)).sub (contDiffAt_const.mul (hψ2.sub hσ2))
  have hT0 : (P * complexHessian
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0).trace.re ≤ 0 := by
    rw [hw _ 0 hΘ2]
    exact Finset.sum_nonpos fun i _ =>
      SGPT.Okounkov.TranscendentalWNReg.leviForm_nonpos_of_isLocalMax hΘ2 hmax (w i)
  have hlevΘ : ∀ v, leviForm (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 -
      a * (ψ w - σ w)) 0 v = leviForm (fun w => Real.log (levTr ψ w)) 0 v -
        2 * K * ‖v‖ ^ 2 - a * (leviForm ψ 0 v - leviForm σ 0 v) := by
    intro v
    rw [SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' (hlogL.sub (contDiffAt_const.mul hsq))
      (contDiffAt_const.mul (hψ2.sub hσ2)),
      SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hlogL (contDiffAt_const.mul hsq),
      leviForm_const_mul hsq, leviForm_const_mul (hψ2.sub hσ2),
      SGPT.Okounkov.TranscendentalWNReg.leviForm_sub' hψ2 hσ2, leviForm_norm_sq]
  have hTΘ : (P * complexHessian
      (fun w => Real.log (levTr ψ w) - 2 * K * ‖w‖ ^ 2 - a * (ψ w - σ w)) 0).trace.re =
      (P * complexHessian (fun w => Real.log (levTr ψ w)) 0).trace.re - 2 * K * trP -
        a * ((P * complexHessian ψ 0).trace.re - (P * complexHessian σ 0).trace.re) := by
    rw [hw _ 0 hΘ2, hw _ 0 hlogL, hw _ 0 hψ2, hw _ 0 hσ2, htrP]
    simp only [hlevΘ, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hTψ : (P * complexHessian ψ 0).trace.re = n := by
    rw [hPdef, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hpos.det_pos.ne'),
      Matrix.trace_one]
    simp
  have hTσ : γ * trP ≤ (P * complexHessian σ 0).trace.re := by
    rw [hw _ 0 hσ2, htrP, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hσlow (w i)
  have hflat := levTr_logDet_div_le hn hψ hpos
  have hflat' := (div_le_div_of_nonneg_right hdetlow hℓ₀.le).trans hflat
  have hmain : (β * (levTr ψ 0 - levTr σ 0 - levTr F 0) - C₁) / levTr ψ 0 -
      2 * K * trP - a * (n - γ * trP) ≤ 0 := by
    have := hT0
    rw [hTΘ, hTψ] at this
    have ha0 : 0 ≤ a := by
      have : 0 ≤ a * γ := le_trans (by positivity) ha
      exact nonneg_of_mul_nonneg_left this hγ
    nlinarith [mul_le_mul_of_nonneg_left hTσ ha0]
  rw [div_sub' hℓ₀.ne', div_sub' hℓ₀.ne', div_le_iff₀ hℓ₀, zero_mul] at hmain
  by_contra hcon
  push Not at hcon
  have ha0 : 0 ≤ a := by
    have : 0 ≤ a * γ := le_trans (by positivity) ha
    exact nonneg_of_mul_nonneg_left this hγ
  have hβ0 : 0 < β := by
    have : 0 ≤ 2 * a * n := by positivity
    linarith
  have hC1 : C₁ ≤ C₁ * (levTr ψ 0 * trP) := by
    have : (1 : ℝ) ≤ levTr ψ 0 * trP := le_trans (by exact_mod_cast hn) hnℓ
    nlinarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : β * (levTr ψ 0 - T - S) ≤ a * n * levTr ψ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (mul_nonneg hℓ₀.le htrP0)]
  have h2 : β * levTr ψ 0 / 2 < β * (levTr ψ 0 - T - S) := by nlinarith
  have h3 : a * n * levTr ψ 0 < β * levTr ψ 0 / 2 := by nlinarith
  linarith

end Flat

/-! ### The trace of a form relative to the metric -/

section TraceForm

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- `tr_g α = Re tr(H_g⁻¹ H_α)` in a chart. -/
def chartTrace (g α : SmoothRealForm N Y 2) (e : ComplexChart N Y) (z : ComplexModel N) : ℝ :=
  ((normalizedHermitianMatrix (g.coeff e z))⁻¹ * normalizedHermitianMatrix (α.coeff e z)).trace.re

/-- **The trace `tr_g α`** on `Y`, read in the preferred chart. -/
def traceForm (g α : SmoothRealForm N Y 2) (y : Y) : ℝ :=
  chartTrace g α (complexChartAt (n := N) y) ((complexChartAt (n := N) y).val y)

/-- **Chart independence of the trace.** -/
theorem chartTrace_eq_of_mem {g α : SmoothRealForm N Y 2} (hg : g.IsHermitian)
    (hα : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → IsOneOne (α.coeff e z))
    {e f : ComplexChart N Y} {y : Y} (hye : y ∈ e.val.source) (hyf : y ∈ f.val.source) :
    chartTrace g α e (e.val y) = chartTrace g α f (f.val y) := by
  have hz : e.val y ∈ (chartTransition e f).source :=
    RelativeEigenvalueMax.mem_chartTransition_source hye hyf
  have hτz : chartTransition e f (e.val y) = f.val y :=
    RelativeEigenvalueMax.chartTransition_apply_chart hye
  have hft : f.val y ∈ f.val.target := f.val.map_source hyf
  have hg11 : IsOneOne (g.coeff f (chartTransition e f (e.val y))) := by
    rw [hτz]; exact (hg f _ hft).1
  have hα11 : IsOneOne (α.coeff f (chartTransition e f (e.val y))) := by
    rw [hτz]; exact hα f _ hft
  unfold chartTrace
  rw [coeff_eq_compLinearMap g e f hz, coeff_eq_compLinearMap α e f hz,
    normalizedHermitianMatrix_compLinearMap hg11, normalizedHermitianMatrix_compLinearMap hα11,
    standardMatrix_transitionLinear, trace_inv_mul_congr (isUnit_det_jacobianMatrix e f hye hyf),
    hτz]

theorem traceForm_eq {g α : SmoothRealForm N Y 2} (hg : g.IsHermitian)
    (hα : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → IsOneOne (α.coeff e z))
    {e : ComplexChart N Y} {y : Y} (hy : y ∈ e.val.source) :
    traceForm g α y = chartTrace g α e (e.val y) :=
  chartTrace_eq_of_mem hg hα (mem_complexChartAt_source y) hy

/-- **The trace of a closed real `(1,1)`-form is continuous.** -/
theorem continuous_traceForm {g : SmoothRealForm N Y 2} (hg : g.IsHermitian)
    (θ : ClosedRealOneOneForm N Y) : Continuous (traceForm g θ.val) := by
  have hα : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target → IsOneOne (θ.val.coeff e z) :=
    fun e z hz => θ.property.2 e z hz
  refine continuous_iff_continuousAt.2 fun y => ?_
  set e := complexChartAt (n := N) y
  have hy : y ∈ e.val.source := mem_complexChartAt_source y
  have hz : e.val y ∈ e.val.target := e.val.map_source hy
  obtain ⟨W, ρ, hzW, hpot⟩ := LocalPotentials.closedRealOneOne_hasLocalPotentials θ e (e.val y) hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hpot.1 (e.val y) hzW
  obtain ⟨ρ', hρ', hρ'eq⟩ := exists_contDiff_eqOn_ball hpot.1 hpot.2.2.1
    (by positivity : 0 < r / 4) (by linarith : r / 4 < r / 2)
    ((closedBall_subset_ball (by linarith)).trans hball)
  -- near `e y`, the chart trace is the chart Laplacian of `ρ'`
  have hloc : chartTrace g θ.val e =ᶠ[𝓝 (e.val y)] chartLaplacian g e ρ' := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by positivity : 0 < r / 4))] with z hz'
    have hzW' : z ∈ W := hball (ball_subset_ball (by linarith) hz')
    have hρ2 : ContDiffAt ℝ 2 ρ z := contDiffAt_two_of_contDiffOn hpot.1 hpot.2.2.1 hzW'
    have hgerm : ρ' =ᶠ[𝓝 z] ρ := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz') hρ'eq
    unfold chartTrace chartLaplacian
    rw [complexHessian_congr hgerm, ← normalizedHermitianMatrix_smoothDDC hρ2,
      hpot.2.2.2 hzW']
  have hcont : ContinuousAt (chartTrace g θ.val e) (e.val y) := by
    refine ContinuousAt.congr ?_ hloc.symm
    exact (continuousOn_chartLaplacian hg e
      (hρ'.contDiffOn.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))).continuousAt
      (e.val.open_target.mem_nhds hz)
  have hcomp : ContinuousAt (fun x => chartTrace g θ.val e (e.val x)) y :=
    hcont.comp (e.val.continuousAt hy)
  refine hcomp.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hy] with x hx
  exact (traceForm_eq hg hα hx).symm

/-- `tr_ω(κ + ddᶜu) = tr_ω κ + Δ_ω u`. -/
theorem traceForm_add_ddc (w A : KahlerBackground N Y) {u : Y → ℝ}
    (hu : ChartSmooth (n := N) u) (y : Y) :
    traceForm w.form.val (A.form + ddcClosedForm u hu).val y =
      traceForm w.form.val A.form.val y + laplacian w.form.val u y := by
  set e := complexChartAt (n := N) y
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  unfold traceForm chartTrace
  rw [laplacian_eq_trace, normalizedHermitianMatrix_add_ddc A hu hz, Matrix.mul_add,
    Matrix.trace_add, Complex.add_re]

/-- `tr_ω κ > 0` for Kähler forms. -/
theorem traceForm_pos (hN : 0 < N) {g α : SmoothRealForm N Y 2} (hg : g.IsHermitian)
    (hα : α.IsKahler) (y : Y) : 0 < traceForm g α y := by
  set e := complexChartAt (n := N) y
  have hz : e.val y ∈ e.val.target := e.val.map_source (mem_complexChartAt_source y)
  exact re_trace_mul_pos hN (posDef_coeff hg hz).inv (posDef_coeff hα.1 hz)

end TraceForm

/-! ### The trace estimate for a general Kähler background -/

section Estimate

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

theorem leviForm_eq_norm_sq_of_complexHessian_eq_one {f : ComplexModel N → ℝ}
    {z : ComplexModel N} (hf : ContDiffAt ℝ 2 f z) (h1 : complexHessian f z = 1)
    (v : ComplexModel N) : leviForm f z v = ‖v‖ ^ 2 := by
  have h := dotProduct_mulVec_complexHessian_eq_leviForm hf (fun d => star (v d))
  rw [coordCombination_star, h1, Matrix.one_mulVec] at h
  have h2 := congrArg Complex.re h
  rw [Complex.ofReal_re, BlockiLocalEstimate.re_star_dotProduct_self] at h2
  rw [← h2, EuclideanSpace.norm_sq_eq]
  simp

/-- **The trace bound at the maximum point, general background** (FPT
`lem:penalized-equation-trace`, Steps 2–3, background `κ = A`, metric `ω = w`). -/
theorem traceForm_le_of_isMax (hN : 0 < N) (w A : KahlerBackground N Y) {β : ℝ} {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F) (U : BetaSolution A β F) {E : ComplexChart N Y}
    {Wω Wκ : Set (ComplexModel N)} {ρω ρκ : ComplexModel N → ℝ}
    (hpotω : IsSmoothLocalPotential w.form.val E Wω ρω)
    (hpotκ : IsSmoothLocalPotential A.form.val E Wκ ρκ) {ρω' ρκ' u' : ComplexModel N → ℝ}
    (hρω' : ContDiff ℝ ∞ ρω') (hρκ' : ContDiff ℝ ∞ ρκ') (hu' : ContDiff ℝ ∞ u')
    {V : Set (ComplexModel N)} (hVo : IsOpen V) (hVWω : V ⊆ Wω) (hVWκ : V ⊆ Wκ)
    (hρω'eq : EqOn ρω' ρω V) (hρκ'eq : EqOn ρκ' ρκ V)
    (hu'eq : EqOn u' (fun w => ρκ w + U.u (E.val.symm w)) V) {z₀ : ComplexModel N}
    (hz₀ : z₀ ∈ V) {K₁ CA Kb a S cκ Cκ Cω : ℝ} (hK₁ : 0 ≤ K₁) (hKb : 0 ≤ Kb) (hcκ : 0 < cκ)
    (hCκ : 0 ≤ Cκ) (hCω : 0 < Cω)
    (hlog : ∀ ζ : ComplexModel N, ‖ζ‖ ≤ 1 →
      -K₁ ≤ leviForm (fun y => Real.log (complexHessian ρκ' y).det.re) z₀ ζ)
    (hκlow : ∀ v, cκ * ‖v‖ ^ 2 ≤ leviForm ρκ' z₀ v) (hκup : ∀ v, leviForm ρκ' z₀ v ≤ Cκ * ‖v‖ ^ 2)
    (hωup : ∀ v, leviForm ρω' z₀ v ≤ Cω * ‖v‖ ^ 2)
    (L : ComplexModel N →L[ℂ] ComplexModel N)
    {c : ComplexModel N →L[ℂ] ComplexModel N →L[ℂ] ComplexModel N}
    (hsymm : ∀ p u, c p u = c u p) (hLbd : ∀ x, ‖L x‖ ≤ CA * ‖x‖)
    (hJ0 : IsUnit (jacobianMatrix (normalCoord z₀ L c) 0).det)
    (h0 : normalizedHermitianMatrix (pullbackField (normalCoord z₀ L c) (w.form.val.coeff E) 0) = 1)
    (hbar : ∀ᶠ x in 𝓝 (0 : ComplexModel N), ∀ v : Fin N → ℂ,
      (star v ⬝ᵥ (normalizedHermitianMatrix
        (pullbackField (normalCoord z₀ L c) (w.form.val.coeff E) x) *ᵥ v)).re ≤
          (1 + Kb * ‖x‖ ^ 2) * (star v ⬝ᵥ v).re)
    (hFS : ∀ y, laplacian w.form.val F y ≤ S)
    (ha : 2 * Kb + K₁ * N * CA ^ 2 ≤ a * (cκ / Cω)) (hβ : 2 * a * N < β)
    (hmax : ∀ y, Real.log (traceForm w.form.val (A.form + ddcClosedForm U.u U.smooth).val y) -
        a * U.u y ≤
      Real.log (traceForm w.form.val (A.form + ddcClosedForm U.u U.smooth).val (E.val.symm z₀)) -
        a * U.u (E.val.symm z₀)) :
    traceForm w.form.val (A.form + ddcClosedForm U.u U.smooth).val (E.val.symm z₀) ≤
      2 * (Cκ * N * CA ^ 2 + S) := by
  classical
  have hg : w.form.val.IsHermitian := w.isKahler.1
  have hVt : V ⊆ E.val.target := hVWω.trans hpotω.2.1
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  set Tr := traceForm w.form.val (A.form + ddcClosedForm U.u U.smooth).val with hTrdef
  have hα : ∀ (e : ComplexChart N Y) z, z ∈ e.val.target →
      IsOneOne ((A.form + ddcClosedForm U.u U.smooth).val.coeff e z) :=
    fun e z hz => (U.isKahler.1 e z hz).1
  -- Hessians of the local potentials
  have hHω : ∀ z ∈ V, complexHessian ρω' z = normalizedHermitianMatrix (w.form.val.coeff E z) := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hρω'eq),
      ← normalizedHermitianMatrix_smoothDDC
        (contDiffAt_two_of_contDiffOn hpotω.1 hpotω.2.2.1 (hVWω hz)), hpotω.2.2.2 (hVWω hz)]
  have hκ2 : ∀ z ∈ V, ContDiffAt ℝ 2 ρκ z := fun z hz =>
    contDiffAt_two_of_contDiffOn hpotκ.1 hpotκ.2.2.1 (hVWκ hz)
  have hHκ0 : ∀ z ∈ V, complexHessian ρκ z = normalizedHermitianMatrix (A.form.val.coeff E z) := by
    intro z hz
    rw [← normalizedHermitianMatrix_smoothDDC (hκ2 z hz), hpotκ.2.2.2 (hVWκ hz)]
  have hHκ : ∀ z ∈ V, complexHessian ρκ' z = normalizedHermitianMatrix (A.form.val.coeff E z) := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hρκ'eq), hHκ0 z hz]
  have hHu : ∀ z ∈ V, complexHessian u' z =
      normalizedHermitianMatrix ((A.form + ddcClosedForm U.u U.smooth).val.coeff E z) := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hu'eq),
      normalizedHermitianMatrix_add_ddc A U.smooth (hVt hz), ← hHκ0 z hz]
    exact AubinYauLocalStep.complexHessian_fun_add (hκ2 z hz)
      (contDiffAt_two_of_contDiffOn E.val.open_target (U.smooth E) (hVt hz))
  have hρω'V : ContDiffOn ℝ 2 ρω' V := hρω'.contDiffOn.of_le h2
  have hu'V : ContDiffOn ℝ 2 u' V := hu'.contDiffOn.of_le h2
  -- the normal coordinate map
  have hΦ0 : normalCoord z₀ L c 0 = z₀ := normalCoord_zero z₀ L c
  have hΦc : ContDiff ℂ ∞ (normalCoord z₀ L c) := contDiff_normalCoord z₀ L c
  have hΦcR : ContDiff ℝ ∞ (normalCoord z₀ L c) := hΦc.restrict_scalars ℝ
  have hU₀ : IsOpen (normalCoord z₀ L c ⁻¹' V) := hVo.preimage hΦcR.continuous
  have h0U₀ : (0 : ComplexModel N) ∈ normalCoord z₀ L c ⁻¹' V := by
    show normalCoord z₀ L c 0 ∈ V
    rw [hΦ0]; exact hz₀
  have hdetJc : ContDiff ℂ ∞ (fun w => (jacobianMatrix (normalCoord z₀ L c) w).det) :=
    contDiff_det_jacobianMatrix z₀ L hsymm
  have hevJ : ∀ᶠ w in 𝓝 (0 : ComplexModel N),
      IsUnit (jacobianMatrix (normalCoord z₀ L c) w).det := by
    filter_upwards [hdetJc.continuous.continuousAt.eventually_ne hJ0.ne_zero] with w hw
    exact isUnit_iff_ne_zero.mpr hw
  -- the functions in the coordinates `w`
  obtain ⟨σt, hσt⟩ : ∃ f : ComplexModel N → ℝ, f = fun x => ρω' (normalCoord z₀ L c x) :=
    ⟨_, rfl⟩
  obtain ⟨κt, hκt⟩ : ∃ f : ComplexModel N → ℝ, f = fun x => ρκ' (normalCoord z₀ L c x) :=
    ⟨_, rfl⟩
  obtain ⟨ψt, hψt⟩ : ∃ f : ComplexModel N → ℝ, f = fun x => u' (normalCoord z₀ L c x) :=
    ⟨_, rfl⟩
  obtain ⟨ut, hut⟩ : ∃ f : ComplexModel N → ℝ,
      f = fun x => U.u (E.val.symm (normalCoord z₀ L c x)) := ⟨_, rfl⟩
  obtain ⟨Ft, hFt⟩ : ∃ f : ComplexModel N → ℝ,
      f = fun x => F (E.val.symm (normalCoord z₀ L c x)) := ⟨_, rfl⟩
  have hσs : ContDiff ℝ ∞ σt := by rw [hσt]; exact hρω'.comp hΦcR
  have hκs : ContDiff ℝ ∞ κt := by rw [hκt]; exact hρκ'.comp hΦcR
  have hψs : ContDiff ℝ ∞ ψt := by rw [hψt]; exact hu'.comp hΦcR
  have hcomp2 : ∀ {v : Y → ℝ}, ChartSmooth (n := N) v → ∀ w,
      normalCoord z₀ L c w ∈ V →
      ContDiffAt ℝ 2 (fun x => v (E.val.symm (normalCoord z₀ L c x))) w := by
    intro v hv w hw
    exact ContDiffAt.comp (g := fun z => v (E.val.symm z)) w
      (contDiffAt_two_of_contDiffOn E.val.open_target (hv E) (hVt hw))
      (hΦcR.contDiffAt.of_le h2)
  have hut2 : ContDiffAt ℝ 2 ut 0 := by rw [hut]; exact hcomp2 U.smooth 0 h0U₀
  have hFt2 : ContDiffAt ℝ 2 Ft 0 := by rw [hFt]; exact hcomp2 hF 0 h0U₀
  -- Hessians in the coordinates `w`
  have hHσJ : ∀ x, normalCoord z₀ L c x ∈ V → complexHessian σt x =
      (jacobianMatrix (normalCoord z₀ L c) x)ᵀ *
        normalizedHermitianMatrix (w.form.val.coeff E (normalCoord z₀ L c x)) *
          (jacobianMatrix (normalCoord z₀ L c) x).map (starRingEnd ℂ) := by
    intro x hx
    rw [hσt, complexHessian_comp_normalCoord z₀ L hVo hρω'V hx, hHω _ hx]
  have hHσpb : ∀ x, normalCoord z₀ L c x ∈ V → complexHessian σt x =
      normalizedHermitianMatrix (pullbackField (normalCoord z₀ L c) (w.form.val.coeff E) x) := by
    intro x hx
    rw [hσt]
    exact complexHessian_comp_potential z₀ L w.isKahler hVo hVt hρω'V hHω hsymm hx
  have hσ0 : complexHessian σt 0 = 1 := by rw [hHσpb 0 h0U₀, h0]
  have hHψJ : ∀ x, normalCoord z₀ L c x ∈ V → complexHessian ψt x =
      (jacobianMatrix (normalCoord z₀ L c) x)ᵀ * complexHessian u' (normalCoord z₀ L c x) *
        (jacobianMatrix (normalCoord z₀ L c) x).map (starRingEnd ℂ) := by
    intro x hx
    rw [hψt]
    exact complexHessian_comp_normalCoord z₀ L hVo hu'V hx
  have hHσpd : ∀ x, normalCoord z₀ L c x ∈ V →
      IsUnit (jacobianMatrix (normalCoord z₀ L c) x).det → (complexHessian σt x).PosDef := by
    intro x hx hJ
    rw [hHσJ x hx]
    exact posDef_transpose_mul_mul_conj (posDef_coeff hg (hVt hx)) hJ
  have hHψpd : ∀ x, normalCoord z₀ L c x ∈ V →
      IsUnit (jacobianMatrix (normalCoord z₀ L c) x).det → (complexHessian ψt x).PosDef := by
    intro x hx hJ
    rw [hHψJ x hx, hHu _ hx]
    exact posDef_transpose_mul_mul_conj (posDef_coeff U.isKahler.1 (hVt hx)) hJ
  have hψeq : ∀ x, normalCoord z₀ L c x ∈ V → ψt x = κt x + ut x := fun x hx => by
    rw [hψt, hκt, hut]
    simp only
    rw [hu'eq hx, hρκ'eq hx]
  -- the trace in the coordinates `w`
  have hNtr : ∀ x, normalCoord z₀ L c x ∈ V →
      IsUnit (jacobianMatrix (normalCoord z₀ L c) x).det →
      Tr (E.val.symm (normalCoord z₀ L c x)) =
        ((complexHessian σt x)⁻¹ * complexHessian ψt x).trace.re := by
    intro x hx hJ
    have hzt := hVt hx
    rw [hTrdef, traceForm_eq hg hα (E.val.map_target hzt), E.val.right_inv hzt, chartTrace,
      hHσJ x hx, hHψJ x hx, hHu _ hx, trace_inv_mul_congr hJ]
  have hlapσ : ∀ (v : Y → ℝ) (hv : ChartSmooth (n := N) v) (x : ComplexModel N),
      normalCoord z₀ L c x ∈ V → IsUnit (jacobianMatrix (normalCoord z₀ L c) x).det →
      laplacian w.form.val v (E.val.symm (normalCoord z₀ L c x)) =
        ((complexHessian σt x)⁻¹ *
          complexHessian (fun y => v (E.val.symm (normalCoord z₀ L c y))) x).trace.re := by
    intro v hv x hx hJ
    rw [hσt]
    exact laplacian_normalCoord z₀ L hg hVo hVt hρω'V hHω hv hx hJ
  have hy0 : E.val.symm (normalCoord z₀ L c 0) = E.val.symm z₀ := by rw [hΦ0]
  have hℓ0 : levTr ψt 0 = Tr (E.val.symm z₀) := by
    rw [← hy0, hNtr 0 h0U₀ hJ0, hσ0, inv_one, Matrix.one_mul,
      re_trace_complexHessian (AubinYauLocalStep.contDiffAt_two hψs 0)]
  have hℓpos0 : 0 < levTr ψt 0 := hℓ0 ▸ traceForm_pos hN hg U.isKahler _
  -- the local maximum
  have hLs : ContDiff ℝ ∞ (levTr ψt) := by
    have : levTr ψt = fun y => ∑ q, leviForm ψt y (coordinateVector q) := rfl
    rw [this]
    exact ContDiff.sum fun q _ => BlockiLocalEstimate.contDiff_leviForm hψs _
  have hmaxw : IsLocalMax
      (fun x => Real.log (levTr ψt x) - 2 * Kb * ‖x‖ ^ 2 - a * (ψt x - κt x)) 0 := by
    have hevℓ : ∀ᶠ x in 𝓝 (0 : ComplexModel N), 0 < levTr ψt x :=
      continuousAt_const.eventually_lt hLs.continuous.continuousAt hℓpos0
    have hsmall : ∀ᶠ x in 𝓝 (0 : ComplexModel N), Kb * ‖x‖ ^ 2 < 1 / 2 := by
      have hc : Continuous fun x : ComplexModel N => Kb * ‖x‖ ^ 2 := by fun_prop
      exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
    filter_upwards [hbar, hevJ, hU₀.mem_nhds h0U₀, hevℓ, hsmall] with x hb hJ hxU hℓx hsm
    have hb' : ∀ v : Fin N → ℂ, (star v ⬝ᵥ (complexHessian σt x *ᵥ v)).re ≤
        (1 + Kb * ‖x‖ ^ 2) * (star v ⬝ᵥ v).re := by
      rw [hHσpb x hxU]; exact hb
    have hb1 := one_sub_mul_re_trace_le (hHσpd x hxU hJ) (hHψpd x hxU hJ).posSemidef hb'
    rw [re_trace_complexHessian (AubinYauLocalStep.contDiffAt_two hψs x),
      ← hNtr x hxU hJ] at hb1
    have hδ0 : 0 ≤ Kb * ‖x‖ ^ 2 := by positivity
    have hlog1 : Real.log (levTr ψt x) - 2 * (Kb * ‖x‖ ^ 2) ≤
        Real.log ((1 - Kb * ‖x‖ ^ 2) * levTr ψt x) := by
      rw [Real.log_mul (by linarith) hℓx.ne']
      linarith [log_one_sub_ge hδ0 hsm.le]
    have hlog2 : Real.log ((1 - Kb * ‖x‖ ^ 2) * levTr ψt x) ≤
        Real.log (Tr (E.val.symm (normalCoord z₀ L c x))) :=
      Real.log_le_log (mul_pos (by linarith) hℓx) hb1
    have hu_x : U.u (E.val.symm (normalCoord z₀ L c x)) = ψt x - κt x := by
      rw [hψeq x hxU, hut]; ring
    have hu_0 : U.u (E.val.symm z₀) = ψt 0 - κt 0 := by
      rw [hψeq 0 h0U₀, hut]; simp only [hΦ0]; ring
    have hQx := hmax (E.val.symm (normalCoord z₀ L c x))
    show Real.log (levTr ψt x) - 2 * Kb * ‖x‖ ^ 2 - a * (ψt x - κt x) ≤
      Real.log (levTr ψt 0) - 2 * Kb * ‖(0 : ComplexModel N)‖ ^ 2 - a * (ψt 0 - κt 0)
    rw [hℓ0, norm_zero, ← hu_0, ← hu_x]
    nlinarith
  -- the determinant term
  have hdetu' : ∀ z ∈ V, (complexHessian u' z).det.re =
      Real.exp (β * (U.u (E.val.symm z) - F (E.val.symm z))) *
        (complexHessian ρκ' z).det.re := by
    intro z hz
    rw [complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hu'eq),
      complexHessian_congr (Filter.eventuallyEq_of_mem (hVo.mem_nhds hz) hρκ'eq)]
    exact re_det_complexHessian_eq_exp (G := fun y => β * (U.u y - F y)) A U.smooth
      U.density hpotκ (hVWκ hz)
  have hdetρpos : ∀ z ∈ V, 0 < (complexHessian ρκ' z).det.re := fun z hz => by
    rw [hHκ z hz]
    exact (Complex.pos_iff.mp (posDef_coeff A.isKahler.1 (hVt hz)).det_pos).1
  have hdetdecomp : (fun x => Real.log (complexHessian ψt x).det.re) =ᶠ[𝓝 0]
      fun x => Real.log (‖(jacobianMatrix (normalCoord z₀ L c) x).det‖ ^ 2) +
        (β * (ut x - Ft x) +
          Real.log (complexHessian ρκ' (normalCoord z₀ L c x)).det.re) := by
    filter_upwards [hevJ, hU₀.mem_nhds h0U₀] with x hJ hxU
    have hherm : (complexHessian u' (normalCoord z₀ L c x)).IsHermitian :=
      complexHessian_isHermitian (AubinYauLocalStep.contDiffAt_two hu' _)
    have hJn : ‖(jacobianMatrix (normalCoord z₀ L c) x).det‖ ^ 2 ≠ 0 :=
      pow_ne_zero 2 (norm_ne_zero_iff.mpr hJ.ne_zero)
    rw [hHψJ x hxU, re_det_transpose_mul_mul_conj hherm, hdetu' _ hxU,
      Real.log_mul hJn (mul_pos (Real.exp_pos _) (hdetρpos _ hxU)).ne',
      Real.log_mul (Real.exp_pos _).ne' (hdetρpos _ hxU).ne', Real.log_exp, hut, hFt]
  have hdetρc : ContDiff ℝ ∞ (fun z => (complexHessian ρκ' z).det.re) :=
    Complex.reCLM.contDiff.comp (WirtingerLogDet.contDiff_det_complexHessian hρκ')
  have hLρV : ContDiffOn ℝ ∞ (fun z => Real.log (complexHessian ρκ' z).det.re) V :=
    hdetρc.contDiffOn.log fun z hz => (hdetρpos z hz).ne'
  have hLρΦ2 : ContDiffAt ℝ 2
      (fun x => Real.log (complexHessian ρκ' (normalCoord z₀ L c x)).det.re) 0 := by
    have h1 : ContDiffAt ℝ ∞ (fun z => Real.log (complexHessian ρκ' z).det.re)
        (normalCoord z₀ L c 0) := hLρV.contDiffAt (hVo.mem_nhds h0U₀)
    exact (h1.comp (0 : ComplexModel N) hΦcR.contDiffAt).of_le h2
  have hlnJ2 : ContDiffAt ℝ 2
      (fun x => Real.log (‖(jacobianMatrix (normalCoord z₀ L c) x).det‖ ^ 2)) 0 := by
    have h1 : ContDiff ℝ ∞ (fun x => ‖(jacobianMatrix (normalCoord z₀ L c) x).det‖ ^ 2) :=
      (hdetJc.restrict_scalars ℝ).norm_sq ℝ
    exact (h1.contDiffAt.of_le h2).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hJ0.ne_zero))
  have hlnJ0 := levTr_log_normSq_nonneg hdetJc hJ0.ne_zero
  have hLq : ∀ q : Fin N, ‖L (coordinateVector q)‖ ≤ CA := by
    intro q
    have := hLbd (coordinateVector q)
    rwa [show ‖(coordinateVector q : ComplexModel N)‖ = 1 by simp [coordinateVector],
      mul_one] at this
  have hcomp0 : ∀ (f : ComplexModel N → ℝ), ContDiffOn ℝ ∞ f V → ∀ v,
      leviForm (fun x => f (normalCoord z₀ L c x)) 0 v = leviForm f z₀ (L v) := by
    intro f hf v
    rw [LeviFormHolomorphicComp.leviForm_comp hU₀ hVo hΦc.contDiffOn hf (fun _ hx => hx) h0U₀,
      fderiv_normalCoord_apply z₀ L hsymm, normalLinear_apply, map_zero, _root_.zero_apply,
      sub_zero, hΦ0]
  have hLρbound : -(K₁ * N * CA ^ 2) ≤
      levTr (fun x => Real.log (complexHessian ρκ' (normalCoord z₀ L c x)).det.re) 0 := by
    have hterm : ∀ q : Fin N, -(K₁ * CA ^ 2) ≤ leviForm
        (fun x => Real.log (complexHessian ρκ' (normalCoord z₀ L c x)).det.re) 0
        (coordinateVector q) := by
      intro q
      rw [hcomp0 _ hLρV]
      exact neg_le_leviForm_of_norm_le hK₁ hlog (hLq q)
    have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => hterm q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    unfold levTr
    linarith
  have hutr : levTr ut 0 = levTr ψt 0 - levTr κt 0 := by
    have h1 : levTr ψt 0 = levTr κt 0 + levTr ut 0 := by
      rw [levTr_congr (Filter.eventuallyEq_of_mem (hU₀.mem_nhds h0U₀) hψeq),
        levTr_add (AubinYauLocalStep.contDiffAt_two hκs 0) hut2]
    linarith
  have hdetlow : β * (levTr ψt 0 - levTr κt 0 - levTr Ft 0) - K₁ * N * CA ^ 2 ≤
      levTr (fun x => Real.log (complexHessian ψt x).det.re) 0 := by
    rw [levTr_congr hdetdecomp,
      levTr_add hlnJ2 ((contDiffAt_const.mul (hut2.sub hFt2)).add hLρΦ2),
      levTr_add (contDiffAt_const.mul (hut2.sub hFt2)) hLρΦ2,
      levTr_const_mul (hut2.sub hFt2), levTr_sub hut2 hFt2, hutr]
    linarith
  have hFS0 : levTr Ft 0 ≤ S := by
    rw [← re_trace_complexHessian hFt2]
    have h := hlapσ F hF 0 h0U₀ hJ0
    rw [hσ0, inv_one, Matrix.one_mul, hy0, ← hFt] at h
    rw [← h]
    exact hFS _
  -- the background in the coordinates `w`
  have hκlow' : ∀ v, cκ / Cω * ‖v‖ ^ 2 ≤ leviForm κt 0 v := by
    intro v
    have e1 : leviForm κt 0 v = leviForm ρκ' z₀ (L v) := by
      rw [hκt]; exact hcomp0 ρκ' hρκ'.contDiffOn v
    have e2 : ‖v‖ ^ 2 = leviForm ρω' z₀ (L v) := by
      rw [← leviForm_eq_norm_sq_of_complexHessian_eq_one
        (AubinYauLocalStep.contDiffAt_two hσs 0) hσ0 v, hσt]
      exact hcomp0 ρω' hρω'.contDiffOn v
    have h1 := hκlow (L v)
    have h2 := hωup (L v)
    rw [e1, div_mul_eq_mul_div, div_le_iff₀ hCω]
    rw [← e2] at h2
    nlinarith [sq_nonneg ‖L v‖]
  have hκT : levTr κt 0 ≤ Cκ * N * CA ^ 2 := by
    have hterm : ∀ q : Fin N, leviForm κt 0 (coordinateVector q) ≤ Cκ * CA ^ 2 := by
      intro q
      rw [hκt, hcomp0 ρκ' hρκ'.contDiffOn]
      refine (hκup _).trans (mul_le_mul_of_nonneg_left ?_ hCκ)
      exact pow_le_pow_left₀ (norm_nonneg _) (hLq q) 2
    have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => hterm q
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    unfold levTr
    linarith
  have hfinal := levTr_le_of_isLocalMax_gen hN hψs hκs (hHψpd 0 h0U₀ hJ0) (div_pos hcκ hCω)
    hκlow' hκT hKb (by positivity) ha hβ hdetlow hFS0 hmaxw
  rw [← hℓ0]
  exact hfinal

end Estimate

/-! ### The global estimate, envelopes and Kähler classes -/

section Global

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **The trace form of Berman's estimate, general Kähler background** (FPT
`lem:penalized-equation-trace`, uniform bound).  For Kähler forms `ω = w` (metric) and `κ = A`
(background) on a compact connected `Y` there are `a ≥ 0`, `T ≥ 0`, `β₀ > 0` such that for
`β ≥ β₀`, smooth `F` with `Δ_ω F ≤ S`, every β-solution `u` of
`(κ + ddᶜu)^N = e^{β(u - F)} κ^N` and every `m ≤ u`:
`tr_ω(κ + ddᶜu) ≤ 2(T + S) e^{a(u - m)}`. -/
theorem betaSolution_traceForm_le [CompactSpace Y] [ConnectedSpace Y]
    (w A : KahlerBackground N Y) :
    ∃ a T β₀ : ℝ, 0 ≤ a ∧ 0 ≤ T ∧ 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∀ (F : Y → ℝ),
      ChartSmooth (n := N) F → ∀ (S : ℝ), (∀ y, laplacian w.form.val F y ≤ S) →
      ∀ (U : BetaSolution A β F) (m : ℝ), (∀ y, m ≤ U.u y) →
      ∀ y, traceForm w.form.val (A.form + ddcClosedForm U.u U.smooth).val y ≤
        2 * (T + S) * Real.exp (a * (U.u y - m)) := by
  classical
  have hg : w.form.val.IsHermitian := w.isKahler.1
  rcases isEmpty_or_nonempty Y with hY | hY
  · exact ⟨0, 0, 1, le_rfl, le_rfl, one_pos, fun β _ F _ S _ U m _ y => (hY.false y).elim⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine ⟨0, 0, 1, le_rfl, le_rfl, one_pos, fun β _ F hF S hFS U m _ y => ?_⟩
    subst hN
    have h0 : ∀ (v : Y → ℝ) x, laplacian w.form.val v x = 0 := fun v x => by
      simp [laplacian, chartLaplacian, Matrix.trace]
    have ht0 : ∀ (α : SmoothRealForm 0 Y 2) x, traceForm w.form.val α x = 0 := fun α x => by
      simp [traceForm, chartTrace, Matrix.trace]
    have hS : 0 ≤ S := by have := hFS y; rwa [h0] at this
    rw [ht0]
    positivity
  -- the pieces
  choose Wκ ρκ ρκ' Rκ hRκ hpotκ hWκ hρκ' hρκ'eq cκ Cκ Mκ K₁ hcκ hCκ hMκ hK₁ hbdκ using
    exists_piece hN A
  choose Wω ρω ρω' Rω hRω hpotω hWω hρω' hρω'eq cω Cω Mω K₁ω hcω hCω hMω hK₁ω hbdω using
    exists_piece hN w
  set R : Y → ℝ := fun p => min (Rκ p) (Rω p) with hRdef
  have hR : ∀ p, 0 < R p := fun p => lt_min (hRκ p) (hRω p)
  have hRκle : ∀ p, R p ≤ Rκ p := fun p => min_le_left _ _
  have hRωle : ∀ p, R p ≤ Rω p := fun p => min_le_right _ _
  have hKt : ∀ p, closedBall ((complexChartAt (n := N) p).val p) (R p) ⊆
      (complexChartAt (n := N) p).val.target := fun p =>
    ((closedBall_subset_closedBall (by linarith [hRωle p, hRω p])).trans (hWω p)).trans
      (hpotω p).2.1
  choose CA Kb hCA hKb hnb using fun p =>
    exists_normal_barrier w.isKahler (complexChartAt (n := N) p)
      (isCompact_closedBall ((complexChartAt (n := N) p).val p) (R p)) (hKt p)
  obtain ⟨O, hOdef⟩ : ∃ O : Y → Set Y, O = fun p => (complexChartAt (n := N) p).val.source ∩
      (complexChartAt (n := N) p).val ⁻¹' ball ((complexChartAt (n := N) p).val p) (R p) :=
    ⟨_, rfl⟩
  have hO : ∀ p, IsOpen (O p) := fun p => by
    rw [hOdef]; exact (complexChartAt (n := N) p).val.isOpen_inter_preimage isOpen_ball
  have hpO : ∀ p, p ∈ O p := fun p => by
    rw [hOdef]; exact ⟨mem_complexChartAt_source p, mem_ball_self (hR p)⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => mem_iUnion.mpr ⟨p, hpO p⟩)
  have hCω' : ∀ p, 0 < Cω p + 1 := fun p => by linarith [hCω p]
  obtain ⟨a, hadef⟩ : ∃ a : ℝ,
      a = ∑ p ∈ t, (2 * Kb p + K₁ p * N * CA p ^ 2) / (cκ p / (Cω p + 1)) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = ∑ p ∈ t, Cκ p * N * CA p ^ 2 := ⟨_, rfl⟩
  have hterm0 : ∀ p, 0 ≤ (2 * Kb p + K₁ p * N * CA p ^ 2) / (cκ p / (Cω p + 1)) := fun p => by
    have := hKb p; have := hK₁ p; have := hcκ p; have := hCω' p; positivity
  have ha0 : 0 ≤ a := by rw [hadef]; exact Finset.sum_nonneg fun p _ => hterm0 p
  have hT0 : 0 ≤ T := by
    rw [hTdef]; exact Finset.sum_nonneg fun p _ => by have := hCκ p; positivity
  have hale : ∀ p ∈ t, 2 * Kb p + K₁ p * N * CA p ^ 2 ≤ a * (cκ p / (Cω p + 1)) := by
    intro p hp
    have h := Finset.single_le_sum (f := fun p =>
      (2 * Kb p + K₁ p * N * CA p ^ 2) / (cκ p / (Cω p + 1))) (fun q _ => hterm0 q) hp
    rw [← hadef] at h
    have hq : 0 < cκ p / (Cω p + 1) := div_pos (hcκ p) (hCω' p)
    rwa [div_le_iff₀ hq] at h
  have hTle : ∀ p ∈ t, Cκ p * N * CA p ^ 2 ≤ T := fun p hp => by
    rw [hTdef]; exact Finset.single_le_sum (f := fun p => Cκ p * N * CA p ^ 2)
      (fun q _ => by have := hCκ q; positivity) hp
  refine ⟨a, T, 2 * a * N + 1, ha0, hT0, by positivity, ?_⟩
  intro β hβ F hF S hFS U m hm
  have hβ' : 2 * a * N < β := by linarith
  set Tr := traceForm w.form.val (A.form + ddcClosedForm U.u U.smooth).val with hTrdef
  have htrpos : ∀ y, 0 < Tr y := traceForm_pos hN hg U.isKahler
  have hQc : Continuous fun y => Real.log (Tr y) - a * U.u y :=
    ((continuous_traceForm hg (A.form + ddcClosedForm U.u U.smooth)).log
      fun y => (htrpos y).ne').sub
      (continuous_const.mul (YauUniformEstimate.continuous_of_chartSmooth U.smooth))
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hQc.continuousOn
  have hQmax : ∀ y, Real.log (Tr y) - a * U.u y ≤ Real.log (Tr y₀) - a * U.u y₀ :=
    fun y => hy₀ (mem_univ y)
  have hkey : Tr y₀ ≤ 2 * (T + S) := by
    obtain ⟨p, hpt, hyp⟩ : ∃ p ∈ t, y₀ ∈ O p := by
      have := ht (mem_univ y₀)
      rw [mem_iUnion₂] at this
      obtain ⟨p, hp, h⟩ := this
      exact ⟨p, hp, h⟩
    rw [hOdef] at hyp
    have hz₀B : (complexChartAt (n := N) p).val y₀ ∈
        ball ((complexChartAt (n := N) p).val p) (R p) := hyp.2
    have hz₀Kκ : (complexChartAt (n := N) p).val y₀ ∈
        closedBall ((complexChartAt (n := N) p).val p) (Rκ p) :=
      closedBall_subset_closedBall (hRκle p) (ball_subset_closedBall hz₀B)
    have hz₀Kω : (complexChartAt (n := N) p).val y₀ ∈
        closedBall ((complexChartAt (n := N) p).val p) (Rω p) :=
      closedBall_subset_closedBall (hRωle p) (ball_subset_closedBall hz₀B)
    have hz₀V : (complexChartAt (n := N) p).val y₀ ∈
        ball ((complexChartAt (n := N) p).val p) (2 * R p) :=
      ball_subset_ball (by linarith [hR p]) hz₀B
    have hVWκ : ball ((complexChartAt (n := N) p).val p) (2 * R p) ⊆ Wκ p :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall
        (by linarith [hRκle p, hRκ p]))).trans (hWκ p)
    have hVWω : ball ((complexChartAt (n := N) p).val p) (2 * R p) ⊆ Wω p :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall
        (by linarith [hRωle p, hRω p]))).trans (hWω p)
    have hu_on : ContDiffOn ℝ ∞
        (fun x => ρκ p x + U.u ((complexChartAt (n := N) p).val.symm x)) (Wκ p) :=
      (hpotκ p).2.2.1.add ((U.smooth _).mono (hpotκ p).2.1)
    obtain ⟨u', hu', hu'eq⟩ := exists_contDiff_eqOn_ball (hpotκ p).1 hu_on
      (by linarith [hR p] : 0 < 2 * R p) (by linarith [hR p] : 2 * R p < 4 * R p)
      ((closedBall_subset_closedBall (by linarith [hRκle p])).trans (hWκ p))
    obtain ⟨Le, cc, hsymm, hLbd, h0, hbar⟩ := hnb p _ (ball_subset_closedBall hz₀B)
    have hy₀eq : (complexChartAt (n := N) p).val.symm ((complexChartAt (n := N) p).val y₀) = y₀ :=
      (complexChartAt (n := N) p).val.left_inv hyp.1
    have hEqκ : EqOn (ρκ' p) (ρκ p) (ball ((complexChartAt (n := N) p).val p) (2 * R p)) :=
      fun x hx => hρκ'eq p (ball_subset_ball (by linarith [hRκle p]) hx)
    have hEqω : EqOn (ρω' p) (ρω p) (ball ((complexChartAt (n := N) p).val p) (2 * R p)) :=
      fun x hx => hρω'eq p (ball_subset_ball (by linarith [hRωle p]) hx)
    have hωup : ∀ v, leviForm (ρω' p) ((complexChartAt (n := N) p).val y₀) v ≤
        (Cω p + 1) * ‖v‖ ^ 2 := fun v =>
      ((hbdω p _ hz₀Kω).2.1 v).trans (by nlinarith [sq_nonneg ‖v‖])
    have h := traceForm_le_of_isMax hN w A hF U (hpotω p) (hpotκ p) (hρω' p) (hρκ' p) hu'
      isOpen_ball hVWω hVWκ hEqω hEqκ hu'eq hz₀V (hK₁ p) (hKb p) (hcκ p) (hCκ p) (hCω' p)
      ((hbdκ p _ hz₀Kκ).2.2.2) ((hbdκ p _ hz₀Kκ).1) ((hbdκ p _ hz₀Kκ).2.1) hωup
      (Le : ComplexModel N →L[ℂ] ComplexModel N) hsymm hLbd
      (isUnit_det_jacobianMatrix_zero _ _ hsymm Le rfl) h0 hbar hFS (hale p hpt) hβ'
      (by rw [hy₀eq]; exact hQmax)
    rw [hy₀eq] at h
    exact h.trans (by linarith [hTle p hpt])
  intro y
  have h1 := hQmax y
  have hpos0 := htrpos y₀
  have hS2 : 0 < 2 * (T + S) := hpos0.trans_le hkey
  have h3 : Real.log (Tr y₀) ≤ Real.log (2 * (T + S)) := Real.log_le_log hpos0 hkey
  have h4 : a * m ≤ a * U.u y₀ := mul_le_mul_of_nonneg_left (hm y₀) ha0
  have h2 : Real.log (Tr y) ≤ Real.log (2 * (T + S)) + a * (U.u y - m) := by nlinarith
  have := Real.exp_le_exp.mpr h2
  rw [Real.exp_log (htrpos y), Real.exp_add, Real.exp_log hS2] at this
  exact this

end Global

end SGPT.Envelopes.LapClass
