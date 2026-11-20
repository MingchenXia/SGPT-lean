import SGPT.Foundations.Analysis.Pending.XiaoChartLocalization
import SGPT.Foundations.Analysis.Pending.SmoothCurrentClosedness
import SGPT.Foundations.Analysis.Pending.ChartPartition

set_option autoImplicit false

/-!
# Global Stokes for actual arbitrary smooth forms

The actual chart-supported coefficients extend smoothly by zero. Genuine
signed change of variables cancels the Kähler chart density, and local Stokes
proves each chart-supported integral vanishes. The actual finite smooth
partition of unity gives global exterior Stokes. The real determinant of the
complex structure is one, giving the normalized complex Stokes identity.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoGlobalStokes

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms IntegrationCurrent TopDegreeDensity XiaoChartLocalization XiaoLocalStokes
  XiaoComplexDifferential XiaoLocalComplexStokes SmoothMixedMeasureDensity GlobalNonPluripolar
  ChartPartition

noncomputable section

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem extDeriv_eq_zero_of_notMem_tsupport {n k : ℕ}
    {a : ComplexModel n → RealForm n k} {z : ComplexModel n} (hz : z ∉ tsupport a) :
    extDeriv a z = 0 := by
  rw [(notMem_tsupport_iff_eventuallyEq.mp hz).extDeriv_eq]
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
    (fderiv ℝ (fun _ : ComplexModel n => (0 : RealForm n k)) z) = 0
  rw [fderiv_const_apply, map_zero]

private theorem topRatio_exteriorDerivative_smulFun_eq_zero
    (w : KahlerBackground (m + 1) M) (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (a : SmoothRealForm (m + 1) M (2 * m + 1)) {x : M} (hx : x ∉ tsupport f) :
    topRatio w.form.val (smulFun f hf a).exteriorDerivative x = 0 := by
  let e := complexChartAt (n := m + 1) x
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hscalar := SmoothCurrentClosedness.chart_eventuallyEq_zero (e := e) hx hxs
  have hcoeff : (smulFun f hf a).coeff e =ᶠ[𝓝 (e.val x)] 0 := by
    filter_upwards [hscalar] with z hz
    simp only [smulFun_coeff, hz, Pi.zero_apply, zero_smul]
  have hd : (smulFun f hf a).exteriorDerivative.coeff e (e.val x) = 0 := by
    rw [SmoothRealForm.exteriorDerivative_coeff, hcoeff.extDeriv_eq]
    change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel (m + 1)) ℝ)
      (fderiv ℝ (fun _ : ComplexModel (m + 1) => (0 : RealForm (m + 1) (2 * m + 1)))
        (e.val x)) = 0
    rw [fderiv_const_apply, map_zero]
  change topDensity ((smulFun f hf a).exteriorDerivative.coeff e (e.val x)) / _ = 0
  rw [hd, topDensity_zero, zero_div]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Genuine signed chart change of variables and local Stokes give the chart-supported case. -/
theorem integral_exteriorDerivative_smulFun_eq_zero_of_chart_support
    (w : KahlerBackground (m + 1) M) (e : ComplexChart (m + 1) M)
    (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (a : SmoothRealForm (m + 1) M (2 * m + 1))
    (hc : IsCompact (tsupport f)) (hs : tsupport f ⊆ e.val.source) :
    (∫ x, topRatio w.form.val (smulFun f hf a).exteriorDerivative x ∂(kahlerVolume w)) = 0 := by
  let b := (smulFun f hf a).exteriorDerivative
  let r := localizedCoeff e f a
  obtain ⟨hr, hrc, hrs⟩ := localizedCoeff_smooth_compact e f hf a hc hs
  have houtside : ∀ x ∉ e.val.source, topRatio w.form.val b x = 0 := by
    intro x hx
    exact topRatio_exteriorDerivative_smulFun_eq_zero w f hf a (fun h => hx (hs h))
  have hzero : ∀ z ∉ e.val.target, topDensity (extDeriv r z) = 0 := by
    intro z hz
    have hn : z ∉ tsupport r := by
      intro h
      obtain ⟨x, hx, hxe⟩ := hrs h
      exact hz (hxe ▸ e.val.map_source (hs hx))
    rw [extDeriv_eq_zero_of_notMem_tsupport hn, topDensity_zero]
  have hlocal : (∫ z, topDensity (extDeriv r z)) = 0 := by
    obtain ⟨_, hz⟩ := integrable_and_integral_topDensity_extDeriv_eq_zero
      (hr.of_le (by simp)) hrc (rfl : (2 * m + 1) + 1 = 2 * (m + 1))
    simpa only [ConstantFormProducts.castForm_self] using hz
  have hω : ∀ _ : Fin (m + 1), ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      globalMixedMeasure (fun _ : Fin (m + 1) => w.form) (fun _ _ => 0) hω := rfl
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero houtside,
    ← e.val.symm_image_target_eq_source, hvol,
    SmoothCurrentClosedness.setIntegral_image_eq hω e e.val.open_target.measurableSet
      (subset_refl _) (continuous_topRatio w.isKahler.1 b)]
  have hpoint : ∀ z ∈ e.val.target,
      (chartDensity (fun _ : Fin (m + 1) => w.form) e z).toReal *
        topRatio w.form.val b (e.val.symm z) = topDensity (extDeriv r z) := by
    intro z hz
    have hratio : topRatio w.form.val b (e.val.symm z) = chartRatio w.form.val b e z := by
      rw [topRatio_eq_chartRatio w.isKahler.1 b (e.val.map_target hz), e.val.right_inv hz]
    have hden : topDensity ((formPow w.form.val (m + 1)).coeff e z) =
        actualMixedTopDensity fun _ => w.form.val.coeff e z := by
      rw [formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]
    have hpos := topDensity_formPow_pos w.isKahler.1 hz
    rw [hratio, chartRatio, chartDensity, ← hden, ENNReal.toReal_ofReal hpos.le,
      mul_div_cancel₀ _ hpos.ne']
    exact congrArg topDensity (extDeriv_localizedCoeff_eq e f hf a hz).symm
  rw [setIntegral_congr_fun e.val.open_target.measurableSet hpoint,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  exact hlocal

/-- Global exterior Stokes for every actual smooth real form one degree below the top. -/
theorem integral_exteriorDerivative_eq_zero (w : KahlerBackground (m + 1) M)
    (a : SmoothRealForm (m + 1) M (2 * m + 1)) :
    (∫ x, topRatio w.form.val a.exteriorDerivative x ∂(kahlerVolume w)) = 0 := by
  classical
  let S : ComplexChart (m + 1) M → Opens M := fun e => ⟨e.val.source, e.val.open_source⟩
  obtain ⟨s, χ, idx, hχ, _, hχS, hχC, hsum⟩ := exists_chartSmooth_partitionOfUnity (n := m + 1) S
    (fun x => ⟨complexChartAt (n := m + 1) x, mem_complexChartAt_source x⟩)
  have hpieces (i : Fin s) :
      (∫ x, topRatio w.form.val (smulFun (χ i) (hχ i) a).exteriorDerivative x
        ∂(kahlerVolume w)) = 0 :=
    integral_exteriorDerivative_smulFun_eq_zero_of_chart_support w (idx i)
      (χ i) (hχ i) a (hχC i) (hχS i)
  have hsplit : ∀ (e : ComplexChart (m + 1) M) z, z ∈ e.val.target →
      a.exteriorDerivative.coeff e z =
        ∑ i : Fin s, (smulFun (χ i) (hχ i) a).exteriorDerivative.coeff e z := by
    intro e z hz
    have hfun : a.coeff e = fun y => ∑ i : Fin s, (smulFun (χ i) (hχ i) a).coeff e y := by
      funext y
      simp only [smulFun_coeff, ← Finset.sum_smul, hsum, one_smul]
    change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (a.coeff e) z) =
      ∑ i : Fin s, ContinuousAlternatingMap.alternatizeUncurryFin
        (fderiv ℝ ((smulFun (χ i) (hχ i) a).coeff e) z)
    rw [hfun, fderiv_fun_sum fun i _ =>
      (((smulFun (χ i) (hχ i) a).smooth e).contDiffAt
        (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)]
    exact map_sum (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ
      (ComplexModel (m + 1)) ℝ) _ _
  have hratio : topRatio w.form.val a.exteriorDerivative =
      fun x => ∑ i : Fin s, topRatio w.form.val (smulFun (χ i) (hχ i) a).exteriorDerivative x := by
    funext x
    let e := complexChartAt (n := m + 1) x
    have hz := e.val.map_source (mem_complexChartAt_source x)
    change topDensity (a.exteriorDerivative.coeff e (e.val x)) / _ =
      ∑ i : Fin s, topDensity ((smulFun (χ i) (hχ i) a).exteriorDerivative.coeff e (e.val x)) / _
    rw [hsplit e (e.val x) hz, ← Finset.sum_div]
    congr 1
    exact map_sum (topDensityLM (m + 1)) _ _
  rw [hratio, integral_finsetSum _ fun i _ => integrable_topRatio w _]
  exact Finset.sum_eq_zero fun i _ => hpieces i

/-- The actual normalized complex differential also satisfies global Stokes. -/
theorem integral_dc_eq_zero (w : KahlerBackground (m + 1) M)
    (a : SmoothRealForm (m + 1) M (2 * m + 1)) :
    (∫ x, topRatio w.form.val (dc a) x ∂(kahlerVolume w)) = 0 := by
  have heq : topRatio w.form.val (dc a) =
      fun x => ((-1 : ℝ) ^ ((2 * m + 1) + 1) / (4 * Real.pi)) *
        topRatio w.form.val (complexTwist a).exteriorDerivative x := by
    funext x
    simp only [topRatio, chartRatio, dc, coeff_smul, complexTwist_coeff,
      topDensity_smul, topDensity_comp_modelComplexStructure, mul_div_assoc]
    rfl
  rw [heq, integral_const_mul, integral_exteriorDerivative_eq_zero, mul_zero]

end

end SGPT.Foundations.Analysis.Pending.XiaoGlobalStokes
