import SGPT.Foundations.Analysis.Pending.XiaoKahlerPowerClosed
import SGPT.Foundations.Analysis.Pending.XiaoKahlerScalarDDC
import SGPT.Foundations.Analysis.Pending.PositivityLeviLink
import SGPT.Foundations.Analysis.Pending.NormalDirectionVanishing

set_option autoImplicit false

/-! # Actual closed powers and actual tensor densities of directional Levi tests -/

open Set Filter
open scoped Topology ContDiff Distributions

namespace SGPT.Foundations.Analysis.Pending.XiaoLeviTestDDCDensity

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses ProductTestForms
  LocalProductCurrents StronglyPositiveForms ConstantFormProducts XiaoComplexDifferential
  XiaoComplexProducts XiaoKahlerPowerClosed XiaoKahlerScalarDDC XiaoGauduchonIntegration
  SmoothDDCForm PositivityLeviLink DirectionalLeviDensity ChartPartition SlotTestForms
  TopDegreeDensity IntegrationCurrent

noncomputable section

section ClosedPowers

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual powers of any real `(1,1)`-form have their actual tensors in the existing form span. -/
theorem formPow_coeff_mem_formSpan (β : ClosedRealOneOneForm n M) (q : ℕ)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (formPow β.val q).coeff e z ∈ formSpan n q := by
  induction q with
  | zero => exact mem_formSpan_of_mem_spCone unit_mem_spCone
  | succ q ih =>
      change coordinateWedge ((formPow β.val q).coeff e z) (β.val.coeff e z) ∈ _
      exact wedge_mem_formSpan ih (β.2.2 e z hz)

/-- Every actual power of an arbitrary actual closed real `(1,1)`-form has genuine derivative zero. -/
theorem formPow_closedReal_isClosed (β : ClosedRealOneOneForm n M) :
    ∀ q, (formPow β.val q).IsClosed := by
  intro q
  induction q with
  | zero =>
      intro e z _
      change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
        (fderiv ℝ (fun _ : ComplexModel n => (coordinateWedgeUnit : RealForm n 0)) z) = 0
      rw [fderiv_const_apply, map_zero]
  | succ q ih =>
      intro e z hz
      obtain ⟨W, ρ, hzW, hW, hWe, hρ, heq⟩ :=
        LocalPotentials.closedRealOneOne_hasLocalPotentials β e z hz
      have hA : ContDiffOn ℝ ∞ ((formPow β.val q).coeff e) W :=
        ((formPow β.val q).smooth e).mono hWe
      have hlocal := extDeriv_wedgeTo_smoothDDC_eq_zero hW hρ hA
        (fun y hy => ih e y (hWe hy)) hzW
      have hgerm : (formPow β.val (q + 1)).coeff e =ᶠ[𝓝 z]
          fun y => wedgeTo (by omega : 2 + 2 * q = 2 * q + 1 + 1)
            (smoothDDC ρ y) ((formPow β.val q).coeff e y) := by
        filter_upwards [hW.mem_nhds hzW] with y hy
        change coordinateWedge ((formPow β.val q).coeff e y) (β.val.coeff e y) = _
        rw [heq hy]
        exact wedgeTo_comm_of_mem_formSpan (formPow_coeff_mem_formSpan β q e (hWe hy))
          (β.val.coeff e y) rfl (by omega)
      rw [hgerm.extDeriv_eq]
      exact hlocal

/-- Every actual closed real `(1,1)`-form power is geometrically complex invariant. -/
theorem complexTwist_formPow_closedReal_geometricallyEq (β : ClosedRealOneOneForm n M)
    (q : ℕ) : (complexTwist (formPow β.val q)).GeometricallyEq (formPow β.val q) :=
  complexTwist_geometricallyEq_of_formSpan _ fun e _ hz => formPow_coeff_mem_formSpan β q e hz

/-- The actual scalar `ddᶜ` product with any actual closed real `(1,1)`-form power. -/
theorem ddc_smulFun_formPow_closedReal_geometricallyEq (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (β : ClosedRealOneOneForm n M) (q : ℕ) :
    (ddc (smulFun f hf (formPow β.val q))).GeometricallyEq
      (exteriorProductTo (by omega : 2 + 2 * q = 2 * q + 1 + 1)
        (ddcForm f hf) (formPow β.val q)) :=
  ddc_smulFun_geometricallyEq_of_closed_invariant f hf _ (formPow_closedReal_isClosed β q)
    (complexTwist_formPow_closedReal_geometricallyEq β q)

end ClosedPowers

section LeviTest

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- The actual higher-degree differential of the existing product-generated Levi test. -/
theorem ddc_leviTest_coeff_eq (e : ComplexChart (m + 1) M) (ψ φ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (m + 1)) (f : ComplexChart (m + 1) M)
    {z : ComplexModel (m + 1)} (hz : z ∈ f.val.target) :
    (ddc (leviTest e ψ a φ : SmoothRealForm (m + 1) M (2 * m))).coeff f z =
      wedgeTo (by omega : 2 + 2 * m = 2 * (m + 1))
        ((ddcForm (chartExtend e φ) (chartSmooth_testFunction e φ)).coeff f z)
        ((formPow (leviSlot e ψ a).val m).coeff f z) := by
  have h := ddc_smulFun_formPow_closedReal_geometricallyEq (chartExtend e φ)
    (chartSmooth_testFunction e φ) (leviSlot e ψ a) m f hz
  rw [exteriorProductTo_coeff] at h
  exact h

/-- The actual Levi-test differential has precisely the genuine ordinary directional Levi density. -/
theorem topDensity_ddc_leviTest (e : ComplexChart (m + 1) M) (ψ φ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (m + 1)) (ha : ‖a‖ = 1)
    (hψ : ∀ z ∈ tsupport φ, (ψ : ComplexModel (m + 1) → ℝ) =ᶠ[𝓝 z] 1)
    {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target) :
    topDensity ((ddc (leviTest e ψ a φ : SmoothRealForm (m + 1) M (2 * m))).coeff e z) =
      ((m.factorial : ℝ) / Real.pi ^ (m + 1)) * leviForm φ z a := by
  rw [ddc_leviTest_coeff_eq e ψ φ a e hz, ddcForm_coeff,
    smoothDDC_congr (chartExtend_eventuallyEq hz)]
  by_cases hzφ : z ∈ tsupport φ
  · rw [← wedgeTo_comm_of_mem_formSpan
      (formPow_coeff_mem_formSpan (leviSlot e ψ a) m e hz) (smoothDDC φ z) rfl (by omega)]
    change topDensity (coordinateWedge ((formPow (leviSlot e ψ a).val m).coeff e z)
      (smoothDDC φ z)) = _
    rw [formPow_coeff, leviSlot_coeff_eq hz (hψ z hzφ), formPower_eq_wedgeProd,
      ← wedgeProd_snoc, NormalDirectionVanishing.wedgeProd_snoc_eq_cons]
    exact topDensity_smoothDDC_perpQuadratic
      (φ.contDiff.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) a ha
  · have h0 : smoothDDC φ z = 0 :=
      (smoothDDC_congr (notMem_tsupport_iff_eventuallyEq.1 hzφ)).trans (smoothDDC_zero z)
    rw [h0, wedgeTo_zero_left, topDensity_zero,
      leviForm_eq_zero_of_notMem_tsupport hzφ a, mul_zero]

/-- The actual Levi-test `ddᶜ` tensor vanishes off its genuinely transported compact support. -/
theorem ddc_leviTest_coeff_eq_zero_of_notMem_image (e : ComplexChart (m + 1) M)
    (ψ φ : 𝓓(chartTarget e, ℝ)) (a : ComplexModel (m + 1))
    (f : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)} (hz : z ∈ f.val.target)
    (hx : f.val.symm z ∉ e.val.symm '' tsupport φ) :
    (ddc (leviTest e ψ a φ : SmoothRealForm (m + 1) M (2 * m))).coeff f z = 0 := by
  rw [ddc_leviTest_coeff_eq e ψ φ a f hz]
  have hsup : tsupport (chartExtend e φ) ⊆ e.val.symm '' tsupport φ :=
    tsupport_chartExtend_subset φ.hasCompactSupport φ.tsupport_subset Subset.rfl
  rw [ddcForm_coeff_eq_zero (chartSmooth_testFunction e φ) hz (fun h => hx (hsup h)),
    wedgeTo_zero_left]

/-- The actual intrinsic `ddᶜ` ratio vanishes outside the actual Levi test's transported support. -/
theorem topRatio_ddc_leviTest_eq_zero_of_notMem_image (w : KahlerBackground (m + 1) M)
    (e : ComplexChart (m + 1) M) (ψ φ : 𝓓(chartTarget e, ℝ))
    (a : ComplexModel (m + 1)) {x : M} (hx : x ∉ e.val.symm '' tsupport φ) :
    topRatio w.form.val (ddc (leviTest e ψ a φ : SmoothRealForm (m + 1) M (2 * m))) x = 0 := by
  have hxs := mem_complexChartAt_source (n := m + 1) x
  have hxt := (complexChartAt (n := m + 1) x).val.map_source hxs
  have hx' : (complexChartAt (n := m + 1) x).val.symm
      ((complexChartAt (n := m + 1) x).val x) ∉ e.val.symm '' tsupport φ := by
    rw [(complexChartAt (n := m + 1) x).val.left_inv hxs]
    exact hx
  rw [topRatio, chartRatio, ddc_leviTest_coeff_eq_zero_of_notMem_image e ψ φ a _ hxt hx',
    topDensity_zero, zero_div]

end LeviTest

end

end SGPT.Foundations.Analysis.Pending.XiaoLeviTestDDCDensity
