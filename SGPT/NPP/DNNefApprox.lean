import SGPT.NPP.DNNefTraceGlobal
import SGPT.Envelopes.LapClassKahlerClass
import SGPT.Foundations.Analysis.Pending.XiaoYauTestVolume

/-!
# β-solutions with the metric as reference volume

Lane DN (`thm:DNT23_C11bar`, nef and big classes).  Source: Berman 2019
(`references/berman19-zero-temperature`), §2.1.2 and Proposition 2.4, with the reference volume
`ω^N` of a fixed Kähler form `ω` instead of `A^N`: the Tsuji-weighted trace estimate
(`tsuji_traceForm_le`) needs the Levi form of `log(ω^N)` (bounded independently of the class),
not that of `log(A^N)`.

* `logVolRatio A w = log(A^N/ω^N)`: chart-smooth, `A^N = e^{logVolRatio} ω^N` in chart densities.
* `exists_refBetaSolution_close`: for every `δ > 0` and every `β₀` there are `β ≥ β₀` and a smooth
  `u` with `A + ddᶜu` Kähler, `(A + ddᶜu)^N = e^{β(u - F)} ω^N` and `|u - P_A(F)| ≤ δ`.  The
  solution is Berman's β-solution for the datum `F + logVolRatio/β`, which differs from the one
  for `F` by at most `sup|logVolRatio|/β` (`betaSolution_le_of_le`), and the latter converges to
  `P_A(F)` (`envelope_bounds`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Matrix Metric MeasureTheory
open scoped Topology ContDiff ComplexConjugate ComplexOrder

namespace SGPT.NPP.DNNef

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ManifoldTubePositivity
open IntegrationCurrent TopDegreeDensity ProductTestForms
open SGPT.Okounkov.TranscendentalWNReg SGPT.Envelopes.DNTReg SGPT.Envelopes.LapClass

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y]

/-- **`log(A^N/ω^N)`**, the logarithm of the ratio of the volume forms of two Kähler forms. -/
def logVolRatio (A w : KahlerBackground N Y) (y : Y) : ℝ :=
  Real.log (topRatio w.form.val (formPow A.form.val N) y)

theorem topRatio_formPow_eq (A w : KahlerBackground N Y) {e : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ e.val.target) :
    topRatio w.form.val (formPow A.form.val N) (e.val.symm z) =
      actualTopPowerDensity (A.form.val.coeff e z) /
        actualTopPowerDensity (w.form.val.coeff e z) := by
  rw [topRatio_eq_chartRatio w.isKahler.1 _ (e.val.map_target hz), e.val.right_inv hz, chartRatio,
    formPow_coeff, formPow_coeff, topDensity_formPower, topDensity_formPower]

theorem topRatio_formPow_pos (A w : KahlerBackground N Y) (y : Y) :
    0 < topRatio w.form.val (formPow A.form.val N) y := by
  set e := complexChartAt (n := N) y
  have hy : y ∈ e.val.source := mem_complexChartAt_source y
  have hz : e.val y ∈ e.val.target := e.val.map_source hy
  have h := topRatio_formPow_eq A w hz
  rw [e.val.left_inv hy] at h
  rw [h]
  exact div_pos (density_pos A hz) (density_pos w hz)

theorem chartSmooth_logVolRatio (A w : KahlerBackground N Y) :
    ChartSmooth (n := N) (logVolRatio A w) := fun e =>
  (TopBidimensionCurrents.chartSmooth_topRatio w.isKahler.1 (formPow A.form.val N) e).log
    fun _ _ => (topRatio_formPow_pos A w _).ne'

/-- `A^N = e^{log(A^N/ω^N)} ω^N` in chart densities. -/
theorem exp_logVolRatio_mul (A w : KahlerBackground N Y) {e : ComplexChart N Y}
    {z : ComplexModel N} (hz : z ∈ e.val.target) :
    Real.exp (logVolRatio A w (e.val.symm z)) * actualTopPowerDensity (w.form.val.coeff e z) =
      actualTopPowerDensity (A.form.val.coeff e z) := by
  rw [logVolRatio, Real.exp_log (topRatio_formPow_pos A w _), topRatio_formPow_eq A w hz]
  field_simp [(density_pos w hz).ne']

variable [CompactSpace Y] [ConnectedSpace Y]

/-- **β-solutions with reference volume `ω^N`, close to the envelope.**  For Kähler forms `A`,
`ω = w`, a smooth `F`, `δ > 0` and `β₀`, there are `β ≥ β₀` and a smooth `u` with `A + ddᶜu`
Kähler, `(A + ddᶜu)^N = e^{β(u - F)} ω^N` and `|u - P_A(F)| ≤ δ` on `Y`; `P_A(F)` is real-valued. -/
theorem exists_refBetaSolution_close (A w : KahlerBackground N Y) {F : Y → ℝ}
    (hF : ChartSmooth (n := N) F) {δ : ℝ} (hδ : 0 < δ) (β₀ : ℝ) :
    ∃ β : ℝ, β₀ ≤ β ∧ ∃ (u : Y → ℝ) (hu : ChartSmooth (n := N) u),
      (A.form + ddcClosedForm u hu).val.IsKahler ∧
      (∀ (e : ComplexChart N Y) z, z ∈ e.val.target →
        actualTopPowerDensity ((A.form + ddcClosedForm u hu).val.coeff e z) =
          Real.exp (β * (u (e.val.symm z) - F (e.val.symm z))) *
            actualTopPowerDensity (w.form.val.coeff e z)) ∧
      (∀ x, rooftopEnvelope A.form.val (fun y => (F y : EReal)) x =
        ((envelopeReal A.form F x : ℝ) : EReal)) ∧
      ∀ x, |u x - envelopeReal A.form F x| ≤ δ := by
  classical
  set h := logVolRatio A w with hhdef
  have hhs : ChartSmooth (n := N) h := chartSmooth_logVolRatio A w
  have hhc : Continuous h := YauUniformEstimate.continuous_of_chartSmooth hhs
  obtain ⟨Bh₀, hBh₀⟩ := isCompact_univ.exists_bound_of_continuousOn hhc.continuousOn
  set Bh := |Bh₀| with hBhdef
  have hBh : ∀ y, |h y| ≤ Bh := fun y => by
    have := hBh₀ y (mem_univ y); rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  have hFc : Continuous F := YauUniformEstimate.continuous_of_chartSmooth hF
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.exists_bound_of_continuousOn hFc.continuousOn
  set B := |B₀| with hBdef
  have hB : ∀ y, |F y| ≤ B := fun y => by
    have := hB₀ y (mem_univ y); rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  obtain ⟨S', hS'0, hFS'⟩ := exists_ddc_line_le_of_chartSmooth A hF
  set c₀ : ℝ := max β₀ 1 with hc₀def
  set β : ℕ → ℝ := fun j => (j : ℝ) + c₀ with hβdef
  have hβ1 : ∀ j, 1 ≤ β j := fun j => by
    have := le_max_right β₀ 1
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [hβdef]; linarith
  have hββ₀ : ∀ j, β₀ ≤ β j := fun j => by
    have := le_max_left β₀ 1
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [hβdef]; linarith
  have hβpos : ∀ j, 0 < β j := fun j => by linarith [hβ1 j]
  -- the error
  set ε : ℕ → ℝ := fun j => (Bh + N * Real.log (1 + S') + 2 * B) / β j +
    N * (Real.log (β j) / β j) with hεdef
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 := tendsto_const_div_natCast_add (Bh + N * Real.log (1 + S') + 2 * B) c₀
    have h2 := (tendsto_log_div_natCast_add c₀).const_mul (N : ℝ)
    simpa [hεdef, hβdef] using h1.add h2
  obtain ⟨j, hj⟩ := (hεlim.eventually (gt_mem_nhds hδ)).exists
  have hβj := hβpos j
  -- the two β-solutions
  have hG : ChartSmooth (n := N) (fun y => F y + h y / β j) := fun e =>
    (hF e).add ((hhs e).div_const _)
  obtain ⟨U⟩ := exists_betaSolution A hβj hG
  obtain ⟨U'⟩ := exists_betaSolution A hβj hF
  have hfin : ∀ x, rooftopEnvelope A.form.val (fun y => (F y : EReal)) x =
      ((envelopeReal A.form F x : ℝ) : EReal) := by
    intro x
    obtain ⟨h1, h2⟩ := envelope_bounds A (hβ1 j) hF hS'0 hFS' hB U' x
    exact (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) h2)
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h1)).symm
  refine ⟨β j, hββ₀ j, U.u, U.smooth, U.isKahler, fun e z hz => ?_, hfin, fun x => ?_⟩
  · rw [U.density e z hz, ← exp_logVolRatio_mul A w hz, ← mul_assoc, ← Real.exp_add]
    congr 2
    rw [← hhdef]
    field_simp
    ring
  · -- `|U - U'| ≤ Bh/β`
    have hc1 : U.u x ≤ U'.u x + Bh / β j :=
      betaSolution_le_of_le hβj (fun y => by
        have := (abs_le.mp (hBh y)).2
        have : h y / β j ≤ Bh / β j := div_le_div_of_nonneg_right this hβj.le
        linarith) U U' x
    have hc2 : U'.u x ≤ U.u x + Bh / β j :=
      betaSolution_le_of_le hβj (fun y => by
        have := (abs_le.mp (hBh y)).1
        have : -Bh / β j ≤ h y / β j := div_le_div_of_nonneg_right this hβj.le
        have : -(Bh / β j) ≤ h y / β j := by rw [← neg_div]; exact this
        linarith) U' U x
    -- `U'` is close to the envelope
    obtain ⟨h1, h2⟩ := envelope_bounds A (hβ1 j) hF hS'0 hFS' hB U' x
    rw [hfin x] at h1 h2
    have h1' := EReal.coe_le_coe_iff.mp h1
    have h2' := EReal.coe_le_coe_iff.mp h2
    have hS1 : 0 ≤ Real.log (1 + S') := Real.log_nonneg (by linarith)
    have hlogβ : 0 ≤ Real.log (β j) := Real.log_nonneg (hβ1 j)
    have hBh0 : 0 ≤ Bh := abs_nonneg _
    have hB0 : 0 ≤ B := abs_nonneg _
    have hεj : ε j = Bh / β j + N * Real.log (1 + S') / β j +
        (2 * B + N * Real.log (β j)) / β j := by
      simp only [hεdef]; field_simp; ring
    have p1 : 0 ≤ N * Real.log (1 + S') / β j := by positivity
    have p2 : 0 ≤ (2 * B + N * Real.log (β j)) / β j := by positivity
    have p3 : 0 ≤ Bh / β j := by positivity
    have hjlt : ε j < δ := hj
    rw [abs_le]
    constructor <;> linarith

end SGPT.NPP.DNNef
