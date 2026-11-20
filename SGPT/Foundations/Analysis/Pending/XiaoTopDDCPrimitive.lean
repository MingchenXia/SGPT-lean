import SGPT.Foundations.Analysis.Pending.XiaoKahlerScalarDDC
import SGPT.Foundations.Analysis.Pending.XiaoPoissonProducer
import SGPT.Foundations.Analysis.Pending.XiaoMixedDensityTrace
import SGPT.Foundations.Analysis.Pending.NormalDirectionVanishing
import SGPT.Foundations.Analysis.Pending.TopBidimensionCurrents

set_option autoImplicit false

/-!
# Actual smooth top-degree `ddᶜ` primitives

The actual one-slot cofactor formula identifies the genuine top-degree tensor
density with the actual Kähler Laplacian. The proved actual Poisson producer
then constructs smooth mean-zero primitives, without assuming a right inverse.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoTopDDCPrimitive

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ConstantFormProducts ClosedProductCurrents CoordinateWedgeAssoc ProductTestForms
  LocalProductCurrents TopDegreeDensity IntegrationCurrent TopBidimensionCurrents
  XiaoComplexDifferential XiaoGauduchonIntegration XiaoKahlerPowerClosed
  XiaoKahlerScalarDDC XiaoPoissonProducer XiaoMixedDensityTrace KahlerLaplacianChart

noncomputable section

variable {m : ℕ}

/-- A genuine one-slot tensor power has the existing actual mixed density. -/
theorem topDensity_wedgeTo_formPower {A : RealForm (m + 1) 2}
    (hA : IsSemipositiveOneOne A) (B : RealForm (m + 1) 2) :
    topDensity (wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1)) B (formPower A m)) =
      actualMixedTopDensity (Fin.cons B (fun _ : Fin m => A)) := by
  rw [← wedgeTo_comm_of_mem_formSpan
    (mem_formSpan_of_mem_spCone (formPower_mem_spCone hA m)) B rfl (by omega)]
  change topDensity (coordinateWedge (formPower A m) B) = _
  rw [formPower_eq_wedgeProd, ← wedgeProd_snoc,
    NormalDirectionVanishing.wedgeProd_snoc_eq_cons, topDensity_wedgeProd]

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual scalar `ddᶜ` power product has exactly the actual Laplacian density. -/
theorem topRatio_ddc_scalar_power_eq_laplacian (w : KahlerBackground (m + 1) M)
    (u : M → ℝ) (hu : ChartSmooth (n := m + 1) u) (x : M) :
    topRatio w.form.val
      (exteriorProductTo (by omega : 2 + 2 * m = 2 * (m + 1))
        (SmoothDDCForm.ddcForm u hu) (formPow w.form.val m)) x =
      laplacian w.form.val u x / (m + 1 : ℝ) := by
  let e := complexChartAt (n := m + 1) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have hC : ContDiffAt ℝ 2 (fun z => u (e.val.symm z)) (e.val x) :=
    ((hu e).contDiffAt (e.val.open_target.mem_nhds hz)).of_le
      (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hA := w.isKahler.1 e (e.val x) hz
  have hid := actualTopPowerDensity_mul_trace hA.1 (smoothDDC_isOneOne hC) hA.2
  have hpower := topDensity_wedgeTo_formPower
    ⟨hA.1, w.isSemipositive e (e.val x) hz⟩
    (smoothDDC (fun z => u (e.val.symm z)) (e.val x))
  rw [normalizedHermitianMatrix_smoothDDC hC, ← hpower] at hid
  rw [topRatio_eq_chartRatio w.isKahler.1 _ hx, chartRatio, exteriorProductTo_coeff,
    SmoothDDCForm.ddcForm_coeff, formPow_coeff, formPow_coeff, topDensity_formPower]
  rw [laplacian_eq w.isKahler.1 (fun f => (hu f).of_le
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hx]
  change _ = ((normalizedHermitianMatrix (w.form.val.coeff e (e.val x)))⁻¹ *
    complexHessian (fun z => u (e.val.symm z)) (e.val x)).trace.re / (m + 1 : ℝ)
  have hpos : 0 < actualTopPowerDensity (w.form.val.coeff e (e.val x)) :=
    actualTopPowerDensity_pos hA.1 hA.2
  have hn : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hpos.ne', hn]
  nlinarith [hid]

/-- The actual higher-degree `ddᶜ` has the same genuine Laplacian density. -/
theorem topRatio_ddc_smulFun_formPow_eq_laplacian (w : KahlerBackground (m + 1) M)
    (u : M → ℝ) (hu : ChartSmooth (n := m + 1) u) (x : M) :
    topRatio w.form.val (ddc (smulFun u hu (formPow w.form.val m))) x =
      laplacian w.form.val u x / (m + 1 : ℝ) := by
  let e := complexChartAt (n := m + 1) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have hform := ddc_smulFun_formPow_geometricallyEq w m u hu e hz
  have heq : topRatio w.form.val (ddc (smulFun u hu (formPow w.form.val m))) x =
      topRatio w.form.val
        (exteriorProductTo (by omega : 2 + 2 * m = 2 * (m + 1))
          (SmoothDDCForm.ddcForm u hu) (formPow w.form.val m)) x := by
    change topDensity _ / topDensity _ = topDensity _ / topDensity _
    rw [hform]
  rw [heq]
  exact topRatio_ddc_scalar_power_eq_laplacian w u hu x

variable [CompactSpace M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Actual Poisson solvability constructs a genuine smooth tensor primitive for a mean-zero top form. -/
theorem exists_smooth_mean_zero_ddc_primitive (w : KahlerBackground (m + 1) M)
    (Φ : SmoothRealForm (m + 1) M (2 * (m + 1)))
    (hΦ : (∫ x, topRatio w.form.val Φ x ∂(kahlerVolume w)) = 0) :
    ∃ (u : M → ℝ) (hu : ChartSmooth (n := m + 1) u),
      (∫ x, u x ∂(kahlerVolume w)) = 0 ∧
      (ddc (smulFun u hu (formPow w.form.val m))).GeometricallyEq Φ := by
  let h : M → ℝ := fun x => (m + 1 : ℝ) * topRatio w.form.val Φ x
  have hh : ChartSmooth (n := m + 1) h := fun e =>
    contDiffOn_const.mul ((chartSmooth_topRatio w.isKahler.1 Φ) e)
  have hm : (∫ x, h x ∂(kahlerVolume w)) = 0 := by
    dsimp only [h]
    rw [integral_const_mul, hΦ, mul_zero]
  obtain ⟨u, hu, hum, hLap, _⟩ := exists_unique_smooth_mean_zero_poisson w h hh hm
  refine ⟨u, hu, hum, ?_⟩
  intro e z hz
  calc
    (ddc (smulFun u hu (formPow w.form.val m))).coeff e z =
        topRatio w.form.val (ddc (smulFun u hu (formPow w.form.val m))) (e.val.symm z) •
          (formPow w.form.val (m + 1)).coeff e z :=
      coeff_eq_topRatio_smul w.isKahler.1 _ e hz
    _ = topRatio w.form.val Φ (e.val.symm z) • (formPow w.form.val (m + 1)).coeff e z := by
      rw [topRatio_ddc_smulFun_formPow_eq_laplacian w u hu, hLap]
      dsimp only [h]
      rw [mul_div_cancel_left₀ _ (by positivity : (m + 1 : ℝ) ≠ 0)]
    _ = Φ.coeff e z := (coeff_eq_topRatio_smul w.isKahler.1 Φ e hz).symm

/-- Actual Stokes supplies the mean-zero condition for every image of the actual test-form `ddᶜ`. -/
theorem exists_smooth_ddc_image_primitive (w : KahlerBackground (m + 1) M)
    (G : SmoothRealForm (m + 1) M (2 * m)) :
    ∃ (u : M → ℝ) (hu : ChartSmooth (n := m + 1) u),
      (∫ x, u x ∂(kahlerVolume w)) = 0 ∧
      (ddc (smulFun u hu (formPow w.form.val m))).GeometricallyEq (ddc G) :=
  exists_smooth_mean_zero_ddc_primitive w (ddc G)
    (XiaoGlobalStokes.integral_exteriorDerivative_eq_zero w (dc G))

end

end SGPT.Foundations.Analysis.Pending.XiaoTopDDCPrimitive
