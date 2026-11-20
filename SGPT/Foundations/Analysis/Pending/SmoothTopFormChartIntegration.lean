import SGPT.Foundations.Analysis.Pending.ClosedTopCurrents
import SGPT.Foundations.Analysis.Pending.XiaoPositiveGauduchonExtension
import SGPT.Foundations.Analysis.Pending.XiaoChartLocalization

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SmoothTopFormChartIntegration

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms ProductTestForms
  TopDegreeDensity IntegrationCurrent ClosedTopCurrents XiaoChartLocalization
  XiaoPositiveGauduchonExtension

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Actual full smooth top-form integration in a chart with a signed cutoff. -/
theorem integral_topRatio_smulFun_eq_chart_integral
    (w : KahlerBackground (m + 1) M) (e : ComplexChart (m + 1) M)
    (χ : M → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hs : tsupport χ ⊆ e.val.source)
    (Φ : SmoothRealForm (m + 1) M (2 * (m + 1))) :
    (∫ x, topRatio w.form.val (smulFun χ hχ Φ) x ∂(kahlerVolume w)) =
      ∫ z, topDensity (localizedCoeff e χ Φ z) := by
  have himage : e.val.symm '' e.val.target = e.val.source := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact e.val.symm.map_source hz
    · intro hx
      exact ⟨e.val x, e.val.map_source hx, e.val.left_inv hx⟩
  have hzero : ∀ x ∉ e.val.source,
      topRatio w.form.val (smulFun χ hχ Φ) x = 0 := by
    intro x hx
    have hxχ : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hs h)
    let f := complexChartAt (n := m + 1) x
    rw [topRatio_eq_chartRatio w.isKahler.1 _ (mem_complexChartAt_source x)]
    change topDensity (χ (f.val.symm (f.val x)) • Φ.coeff f (f.val x)) / _ = 0
    rw [f.val.left_inv (mem_complexChartAt_source x), hxχ, zero_smul,
      topDensity_zero, zero_div]
  have hzoutside : ∀ z ∉ e.val.target, topDensity (localizedCoeff e χ Φ z) = 0 := by
    intro z hz
    rw [localizedCoeff, indicator_of_notMem hz, topDensity_zero]
  calc
    _ = ∫ x in e.val.source, topRatio w.form.val (smulFun χ hχ Φ) x
        ∂(kahlerVolume w) := (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ z in e.val.target, volDensity w e z *
        topRatio w.form.val (smulFun χ hχ Φ) (e.val.symm z) := by
      rw [← himage]
      exact setIntegral_kahlerVolume_image w e e.val.open_target.measurableSet
        (Subset.rfl) (continuous_topRatio w.isKahler.1 _)
    _ = ∫ z in e.val.target, topDensity (localizedCoeff e χ Φ z) := by
      refine setIntegral_congr_fun e.val.open_target.measurableSet fun z hz => ?_
      rw [topRatio_eq_chartRatio w.isKahler.1 _ (e.val.symm.map_source hz),
        e.val.right_inv hz]
      change volDensity w e z *
        (topDensity (χ (e.val.symm z) • Φ.coeff e z) / volDensity w e z) = _
      rw [localizedCoeff, indicator_of_mem hz]
      field_simp [(volDensity_pos w e hz).ne']
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero hzoutside

/-- The full smooth pairing equals its actual localized coordinate wedge integral. -/
theorem smoothPairing_smulFun_eq_localized_wedge_integral
    (w : KahlerBackground (m + 1) M) (e : ComplexChart (m + 1) M)
    (χ : M → ℝ) (hχ : ChartSmooth (n := m + 1) χ)
    (hs : tsupport χ ⊆ e.val.source)
    (θ : SmoothRealForm (m + 1) M 2) (G : SmoothRealForm (m + 1) M (2 * m)) :
    smoothPairing w θ (smulFun χ hχ G) =
      ∫ z, topDensity (coordinateWedge (localizedCoeff e χ G z) (θ.coeff e z)) := by
  have hwedge : wedgeTwo (smulFun χ hχ G) θ = smulFun χ hχ (wedgeTwo G θ) :=
    smoothRealForm_ext fun f z => by
      rw [wedgeTwo_coeff, smulFun_coeff, smulFun_coeff, wedgeTwo_coeff,
        coordinateWedge_smul_left]
  rw [smoothPairing_apply, hwedge,
    integral_topRatio_smulFun_eq_chart_integral w e χ hχ hs]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ e.val.target
  · simp only [localizedCoeff, indicator_of_mem hz, wedgeTwo_coeff,
      coordinateWedge_smul_left]
  · have hwzero : coordinateWedge (0 : RealForm (m + 1) (2 * m)) (θ.coeff e z) = 0 := by
      simpa only [zero_smul] using coordinateWedge_smul_left (0 : ℝ)
        (0 : RealForm (m + 1) (2 * m)) (θ.coeff e z)
    simp only [localizedCoeff, indicator_of_notMem hz, hwzero, topDensity_zero]

end SGPT.Foundations.Analysis.Pending.SmoothTopFormChartIntegration
