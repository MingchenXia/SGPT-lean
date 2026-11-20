import SGPT.Foundations.Analysis.Pending.DivisorialUniformFamilySliceBound
import SGPT.Foundations.Analysis.Pending.LelongNumberChartTransport
import Mathlib.Topology.Order.MonotoneConvergence

set_option autoImplicit false

/-! # Scalar generic Lelong numbers for a genuine regularized family supremum -/

open Set Filter Metric
open scoped Topology ENNReal NNReal Manifold

namespace SGPT.Foundations.Analysis.Pending.DivisorialFamilySupremumLelong

open FirstPass FirstPass.NonKahlerLocus DemaillyApproximantDivisorialLelong
  DivisorialUniformFamilySliceBound LelongNumberChartTransport

noncomputable section

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- A genuine flattening transports the family slice barrier to an actual
admissible exponent for the regularized supremum on the original manifold. -/
theorem iInf_divisorialLelongNumber_le_supremum_point {I : Type*} [Nonempty I]
    {θ : SmoothRealForm (m + 1) Y 2} {u : I → Y → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic θ (u i)) {B : ℝ}
    (hB : ∀ i y, u i y ≤ (B : EReal))
    {E : Set Y} {x : Y} (Φ : DivisorFlattening (m := m) E x) :
    (⨅ i, divisorialLelongNumber m (u i) E) ≤
      lelongNumber (n := m + 1) (uscRegularization (fun y => ⨆ i, u i y)) x := by
  apply ENNReal.le_of_forall_pos_nnreal_lt
  intro γ hγ hγinf
  have hν (i : I) : (γ : ℝ≥0∞) < divisorialLelongNumber m (u i) E :=
    hγinf.trans_le (iInf_le _ i)
  obtain ⟨r, hr, A, hrt, hall⟩ := exists_uniform_regularized_sup_slice_bound hu hB Φ
  let e := complexChartAt (n := m + 1) x
  let h : OpenPartialHomeomorph Y (ComplexModel (m + 1)) :=
    e.val.trans Φ.Φ.toOpenPartialHomeomorph
  have hcov (z : ComplexModel (m + 1)) (hz : z ∈ Φ.Φ.target) :
      uscRegularization (fun w => ⨆ i, u i (Φ.point w)) z =
        uscRegularization (fun y => ⨆ i, u i y) (Φ.point z) := by
    have hzh : z ∈ h.symm.source := by
      change z ∈ Φ.Φ.target ∧ Φ.Φ.invFun z ∈ e.val.target
      exact ⟨hz, Φ.invFun_mem_target hz⟩
    exact uscRegularization_comp_openPartialHomeomorph_apply
      (fun y => ⨆ i, u i y) h.symm hzh
  have hfd : DifferentiableAt ℂ Φ.Φ.toFun (e.val x) :=
    Φ.Φ.toFun_holomorphic.differentiableAt
      (Φ.Φ.isOpen_source.mem_nhds Φ.chart_mem_source)
  obtain ⟨L, hL, hLbound⟩ := hfd.hasFDerivAt.isBigO_sub.exists_pos
  have hlip : ∀ᶠ y in 𝓝 x, ‖Φ.coord y‖ ≤ L * ‖e.val y - e.val x‖ := by
    have hh := (e.val.continuousAt (mem_complexChartAt_source x)).eventually hLbound.bound
    simpa only [e, DivisorFlattening.coord, Φ.map_center, sub_zero] using hh
  have hcoord : ContinuousAt Φ.coord x := Φ.mdifferentiableAt_coord.continuousAt
  have hball : ∀ᶠ y in 𝓝 x, Φ.coord y ∈ ball (0 : ComplexModel (m + 1)) r := by
    have hxball : Φ.coord x ∈ ball (0 : ComplexModel (m + 1)) r := by
      rw [Φ.coord_x]; exact mem_ball_self hr
    exact hcoord.eventually (isOpen_ball.mem_nhds hxball)
  have hγreal : 0 < (γ : ℝ) := by exact_mod_cast hγ
  have hadm : ∀ᶠ y in 𝓝[≠] x,
      uscRegularization (fun y => ⨆ i, u i y) y ≤
        (((γ : ℝ) * Real.log ‖e.val y - e.val x‖ +
          (A - (γ : ℝ) * Real.log r + (γ : ℝ) * Real.log L) : ℝ) : EReal) := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hlip, hball, Φ.eventually_point_coord,
      e.val.open_source.mem_nhds (mem_complexChartAt_source x)] with y hyL hyball hypoint hysrc hyx
    have hflat := hall γ hγ hν (Φ.coord y) hyball
    rw [hcov _ (hrt hyball), hypoint] at hflat
    by_cases hz0 : Φ.coord y (Fin.last m) = 0
    · rw [hz0, logNormSq_zero, EReal.coe_mul_bot_of_pos (by positivity), EReal.bot_add] at hflat
      exact hflat.trans bot_le
    have hny : 0 < ‖e.val y - e.val x‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact fun hy => hyx (e.val.injOn hysrc (mem_complexChartAt_source x) hy)
    have hlastpos : 0 < ‖Φ.coord y (Fin.last m)‖ := norm_pos_iff.mpr hz0
    have hlast : ‖Φ.coord y (Fin.last m)‖ ≤ L * ‖e.val y - e.val x‖ :=
      (PiLp.norm_apply_le (Φ.coord y) (Fin.last m)).trans hyL
    have hlog : Real.log ‖Φ.coord y (Fin.last m)‖ ≤
        Real.log L + Real.log ‖e.val y - e.val x‖ := by
      rw [← Real.log_mul hL.ne' hny.ne']
      exact Real.log_le_log hlastpos hlast
    have hlogSq : logNormSq (Φ.coord y (Fin.last m)) =
        ((2 * Real.log ‖Φ.coord y (Fin.last m)‖ : ℝ) : EReal) := by
      rw [logNormSq_of_ne_zero hz0, Real.log_pow]; norm_num
    rw [hlogSq, ← EReal.coe_mul, ← EReal.coe_add] at hflat
    apply hflat.trans
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [hlog, hγreal]
  have hle := ofReal_le_lelongNumber hγreal.le hadm
  simpa only [ENNReal.ofReal_coe_nnreal] using hle

/-- Actual flattenings throughout the hypersurface turn the regular-point
bound into a literal equality of extended generic Lelong numbers. -/
theorem divisorialLelongNumber_regularized_iSup_eq_iInf {I : Type*} [Nonempty I]
    {θ : SmoothRealForm (m + 1) Y 2} {u : I → Y → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic θ (u i)) {B : ℝ}
    (hB : ∀ i y, u i y ≤ (B : EReal)) {E : Set Y}
    (hflat : ∀ x ∈ E, Nonempty (DivisorFlattening (m := m) E x)) :
    divisorialLelongNumber m (uscRegularization (fun y => ⨆ i, u i y)) E =
      ⨅ i, divisorialLelongNumber m (u i) E := by
  classical
  apply le_antisymm
  · refine le_iInf fun i => ?_
    change divisorialLelongNumber m (uscRegularization (fun y => ⨆ i, u i y)) E ≤
      ⨅ x ∈ E, lelongNumber (n := m + 1) (u i) x
    refine le_iInf fun x => le_iInf fun hx => ?_
    exact (divisorialLelongNumber_le hx).trans
      (KahlerCurrentMax.lelongNumber_le_of_eventually_le (Eventually.of_forall fun y =>
        (le_iSup (fun i => u i y) i).trans (le_uscRegularization (fun y => ⨆ i, u i y) y)))
  · change (⨅ i, divisorialLelongNumber m (u i) E) ≤
      ⨅ x ∈ E, lelongNumber (n := m + 1) (uscRegularization (fun y => ⨆ i, u i y)) x
    refine le_iInf fun x => le_iInf fun hx => ?_
    exact iInf_divisorialLelongNumber_le_supremum_point hu hB (Classical.choice (hflat x hx))

/-- The complete order-topological limit for a genuinely increasing family;
no countable cofinal subset, finite Lelong value or positive mass is assumed. -/
theorem tendsto_divisorialLelongNumber_of_monotone {I : Type*} [Nonempty I] [Preorder I]
    {θ : SmoothRealForm (m + 1) Y 2} {u : I → Y → EReal}
    (hu : ∀ i, ThetaPlurisubharmonic θ (u i)) {B : ℝ}
    (hB : ∀ i y, u i y ≤ (B : EReal)) (hmono : Monotone u) {E : Set Y}
    (hflat : ∀ x ∈ E, Nonempty (DivisorFlattening (m := m) E x)) :
    Tendsto (fun i => divisorialLelongNumber m (u i) E) atTop
      (𝓝 (divisorialLelongNumber m (uscRegularization (fun y => ⨆ i, u i y)) E)) := by
  have hanti : Antitone (fun i => divisorialLelongNumber m (u i) E) := by
    intro i j hij
    change divisorialLelongNumber m (u j) E ≤ ⨅ x ∈ E, lelongNumber (n := m + 1) (u i) x
    refine le_iInf fun x => le_iInf fun hx => ?_
    exact (divisorialLelongNumber_le hx).trans
      (KahlerCurrentMax.lelongNumber_le_of_eventually_le (Eventually.of_forall (hmono hij)))
  rw [divisorialLelongNumber_regularized_iSup_eq_iInf hu hB hflat]
  exact tendsto_atTop_iInf hanti

end
end SGPT.Foundations.Analysis.Pending.DivisorialFamilySupremumLelong
