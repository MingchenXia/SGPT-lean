import SGPT.Foundations.Analysis.Pending.XiaoSmoothFormTopology
import SGPT.Foundations.Analysis.Pending.XiaoFiniteTensorNorm
import SGPT.Foundations.Analysis.Pending.XiaoPositiveCompactChartCover

set_option autoImplicit false

/-! # Actual finite zero-order coefficient probes control the global intrinsic seminorm -/

open Set Filter
open scoped Topology BoundedContinuousFunction

namespace SGPT.Foundations.Analysis.Pending.XiaoFiniteProbeDomination

open FirstPass FirstPass.PositiveClasses XiaoFormC0Topology XiaoSmoothFormTopology
  XiaoFiniteTensorNorm XiaoPositiveCompactChartCover

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {I : Type*} [Fintype I]

/-- The actual zero-order scalar coefficient probe on an actual compact positivity patch. -/
def coefficientProbe {w : KahlerBackground n M} (p : PositiveChartPatch w)
    (b : Module.Basis I ℝ (ComplexModel n)) (s : Fin 2 → I) : JetProbe n M where
  chart := p.chart
  compactSet := p.compactSet
  isCompact := p.isCompact_compactSet
  subset_target := p.target_closedBall
  order := 0
  vectors := fun i => b (s i)
  directions := fun i => Fin.elim0 i

omit [Fintype I] in
/-- Genuine zero-order iterated derivatives recover the actual scalar tensor coefficient. -/
theorem coefficientProbe_apply {w : KahlerBackground n M} (p : PositiveChartPatch w)
    (b : Module.Basis I ℝ (ComplexModel n)) (s : Fin 2 → I)
    (θ : ClosedRealOneOneForm n M) (z : p.compactSet) :
    jetLinearMap (coefficientProbe p b s) θ z = θ.val.coeff p.chart z (fun i => b (s i)) := by
  change iteratedFDeriv ℝ 0 (fun y => θ.val.coeff p.chart y (fun i => b (s i))) z
    (fun i : Fin 0 => Fin.elim0 i) = _
  exact iteratedFDeriv_zero_apply _

/-- The actual finite sum of actual scalar coefficient supremum norms on the actual compact patch. -/
def patchProbeSum {w : KahlerBackground n M} (p : PositiveChartPatch w)
    (b : Module.Basis I ℝ (ComplexModel n)) (θ : ClosedRealOneOneForm n M) : ℝ :=
  ∑ s : Fin 2 → I, ‖jetLinearMap (coefficientProbe p b s) θ‖

/-- All actual coefficient-probe weights are nonnegative. -/
theorem patchProbeSum_nonneg {w : KahlerBackground n M} (p : PositiveChartPatch w)
    (b : Module.Basis I ℝ (ComplexModel n)) (θ : ClosedRealOneOneForm n M) :
    0 ≤ patchProbeSum p b θ :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- An actual finite tensor coordinate bound gives the actual pointwise tensor bound from actual compact probes. -/
theorem norm_coeff_le_patchProbeSum {w : KahlerBackground n M} (p : PositiveChartPatch w)
    (b : Module.Basis I ℝ (ComplexModel n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ,
      ‖A‖ ≤ C * ∑ s : Fin 2 → I, |A (fun i => b (s i))|)
    (θ : ClosedRealOneOneForm n M) {z : ComplexModel n} (hz : z ∈ p.compactSet) :
    ‖θ.val.coeff p.chart z‖ ≤ C * patchProbeSum p b θ := by
  apply (hbound (θ.val.coeff p.chart z)).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Finset.sum_le_sum
  intro s _
  have hnorm := BoundedContinuousFunction.norm_coe_le_norm
    (jetLinearMap (coefficientProbe p b s) θ) (⟨z, hz⟩ : p.compactSet)
  rw [coefficientProbe_apply, Real.norm_eq_abs] at hnorm
  exact hnorm

/-- Actual complex-linear chart transport and actual background positivity control every actual tangent ratio. -/
theorem abs_normalizedProbe_le_patchBound (w : KahlerBackground n M) (p : PositiveChartPatch w)
    (b : Module.Basis I ℝ (ComplexModel n)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ,
      ‖A‖ ≤ C * ∑ s : Fin 2 → I, |A (fun i => b (s i))|)
    (θ : ClosedRealOneOneForm n M) (q : LineProbe n M)
    (hpatch : q.chart.val.symm q.point ∈ p.sourceNeighborhood) :
    |normalizedProbe w θ q| ≤ (C / p.lowerConstant) * patchProbeSum p b θ := by
  let z : ComplexModel n := p.chart.val (q.chart.val.symm q.point)
  have hz : z ∈ p.compactSet := Metric.mem_closedBall.mpr (Metric.mem_ball.mp hpatch.2).le
  have htrans : q.point ∈ (chartTransition q.chart p.chart).source := by
    rw [chartTransition]
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    exact ⟨q.mem_target, hpatch.1⟩
  let v : ComplexModel n := chartTransitionDerivative q.chart p.chart q.point q.vector
  have hθ := KahlerDomination.lineValue_compatible θ.val q.chart p.chart htrans q.vector
  have hω := KahlerDomination.lineValue_compatible w.form.val q.chart p.chart htrans q.vector
  change θ.val.coeff q.chart q.point ![q.vector, Complex.I • q.vector] =
    θ.val.coeff p.chart z ![v, Complex.I • v] at hθ
  change w.form.val.coeff q.chart q.point ![q.vector, Complex.I • q.vector] =
    w.form.val.coeff p.chart z ![v, Complex.I • v] at hω
  have hd : 0 < w.form.val.coeff p.chart z ![v, Complex.I • v] := by
    rw [← hω]
    exact probe_denominator_pos w q
  have hn := norm_coeff_le_patchProbeSum p b hC hbound θ hz
  have ha := KahlerDomination.abs_lineValue_le (θ.val.coeff p.chart z) v
  have habs : |θ.val.coeff p.chart z ![v, Complex.I • v]| ≤
      (C * patchProbeSum p b θ) * ‖v‖ ^ 2 :=
    ha.trans (mul_le_mul_of_nonneg_right hn (sq_nonneg ‖v‖))
  have hlow := p.lowerBound z hz v
  have hsum : 0 ≤ C * patchProbeSum p b θ :=
    mul_nonneg hC (patchProbeSum_nonneg p b θ)
  have hscaled : p.lowerConstant * |θ.val.coeff p.chart z ![v, Complex.I • v]| ≤
      (C * patchProbeSum p b θ) * w.form.val.coeff p.chart z ![v, Complex.I • v] := by
    calc
      _ ≤ p.lowerConstant * ((C * patchProbeSum p b θ) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left habs p.lowerConstant_pos.le
      _ = (C * patchProbeSum p b θ) * (p.lowerConstant * ‖v‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow hsum
  unfold normalizedProbe
  rw [hθ, hω, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ ((C * patchProbeSum p b θ) *
        w.form.val.coeff p.chart z ![v, Complex.I • v]) / p.lowerConstant :=
      (le_div_iff₀ p.lowerConstant_pos).mpr (by nlinarith only [hscaled])
    _ = _ := by ring

variable [CompactSpace M]

/-- An actual finite positivity cover and actual finite tensor bound control the actual global supremum seminorm. -/
theorem formC0Seminorm_le_patch_cover (w : KahlerBackground n M)
    (b : Module.Basis I ℝ (ComplexModel n)) (t : Finset (PositiveChartPatch w))
    (hcover : ∀ x : M, ∃ p ∈ t, x ∈ p.sourceNeighborhood) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ A : (ComplexModel n) [⋀^Fin 2]→L[ℝ] ℝ,
      ‖A‖ ≤ C * ∑ s : Fin 2 → I, |A (fun i => b (s i))|)
    (θ : ClosedRealOneOneForm n M) :
    formC0Seminorm w θ ≤ ∑ p ∈ t, (C / p.lowerConstant) * patchProbeSum p b θ := by
  have hnonneg : ∀ p : PositiveChartPatch w,
      0 ≤ (C / p.lowerConstant) * patchProbeSum p b θ :=
    fun p => mul_nonneg (div_nonneg hC p.lowerConstant_pos.le) (patchProbeSum_nonneg p b θ)
  rw [formC0Seminorm_eq, BoundedContinuousFunction.norm_le
    (Finset.sum_nonneg fun p _ => hnonneg p)]
  intro q
  change |normalizedProbe w θ q| ≤ _
  obtain ⟨p, hp, hpatch⟩ := hcover (q.chart.val.symm q.point)
  apply (abs_normalizedProbe_le_patchBound w p b hC hbound θ q hpatch).trans
  exact Finset.single_le_sum (f := fun p : PositiveChartPatch w =>
    (C / p.lowerConstant) * patchProbeSum p b θ) (fun p _ => hnonneg p) hp

/-- All finite probes and all fixed weights are produced from the actual background and actual finite basis. -/
theorem exists_formC0Seminorm_le_finite_probes (w : KahlerBackground n M)
    (b : Module.Basis I ℝ (ComplexModel n)) :
    ∃ t : Finset (PositiveChartPatch w), ∃ C : ℝ, 0 < C ∧
      ∀ θ : ClosedRealOneOneForm n M,
        formC0Seminorm w θ ≤ ∑ p ∈ t, (C / p.lowerConstant) * patchProbeSum p b θ := by
  obtain ⟨t, hcover⟩ := exists_finite_cover w
  obtain ⟨C, hC, hbound⟩ := exists_tensor_norm_le_sum b
  exact ⟨t, C, hC, fun θ => formC0Seminorm_le_patch_cover w b t hcover hC.le hbound θ⟩

end

end SGPT.Foundations.Analysis.Pending.XiaoFiniteProbeDomination
