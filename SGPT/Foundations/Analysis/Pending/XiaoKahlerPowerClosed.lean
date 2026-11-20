import SGPT.Foundations.Analysis.Pending.XiaoGauduchonCrossDensity
import SGPT.Foundations.Analysis.Pending.LocalPotentials
import SGPT.Foundations.Analysis.FirstPass.PositiveClasses

set_option autoImplicit false

/-!
# Actual exterior closedness of Kähler powers

Local actual `ddᶜ` potentials, the genuine covector product rule and `d² = 0`
produce closedness of the actual tensor fields. No closed-current product is
used in place of the actual differential.
-/

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoKahlerPowerClosed

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ConstantFormProducts ClosedProductCurrents CoordinateWedgeAssoc ProductTestForms
  LocalProductCurrents XiaoComplexDifferential XiaoComplexProducts XiaoCovectorProducts
  XiaoGauduchonCrossDensity

noncomputable section

variable {n k q : ℕ}

/-- The actual local product has a smooth primitive, hence actual derivative zero. -/
theorem extDeriv_wedgeTo_smoothDDC_eq_zero {U : Set (ComplexModel n)} (hU : IsOpen U)
    {ρ : ComplexModel n → ℝ} (hρ : ContDiffOn ℝ ∞ ρ U)
    {A : ComplexModel n → RealForm n k} (hA : ContDiffOn ℝ ∞ A U)
    (hclosed : ∀ y ∈ U, extDeriv A y = 0) {z : ComplexModel n} (hz : z ∈ U) :
    extDeriv (fun y => wedgeTo (by omega : 2 + k = k + 1 + 1)
      (smoothDDC ρ y) (A y)) z = 0 := by
  let L : ComplexModel n → (ComplexModel n →L[ℝ] ℝ) := fun y =>
    (-1 / (4 * Real.pi) : ℝ) • (fderiv ℝ ρ y).comp (modelComplexStructure n)
  have hL : ContDiffOn ℝ ∞ L U :=
    ((hρ.fderiv_of_isOpen hU (by simp)).clm_comp contDiffOn_const).const_smul _
  have hprod : ContDiffOn ℝ ∞ (fun y => oneWedge (L y) (A y)) U := by
    simpa only [Function.comp_apply, covectorWedgeCLM_apply] using
      ((covectorWedgeCLM n k).contDiff.comp_contDiffOn hL).clm_apply hA
  have heq : (fun y => wedgeTo (by omega : 2 + k = k + 1 + 1)
      (smoothDDC ρ y) (A y)) =ᶠ[𝓝 z]
      extDeriv (fun y => oneWedge (L y) (A y)) := by
    filter_upwards [hU.mem_nhds hz] with y hy
    have hd := extDeriv_oneWedge_eq
      ((hL.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((hA.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
    rw [hclosed y hy] at hd
    have hzero : oneWedge (L y) (0 : RealForm n (k + 1)) = 0 := by
      simpa only [covectorWedgeCLM_apply] using (covectorWedgeCLM n (k + 1) (L y)).map_zero
    rw [hzero, sub_zero] at hd
    exact hd.symm
  rw [heq.extDeriv_eq]
  exact extDeriv_extDeriv_apply (hprod.contDiffAt (hU.mem_nhds hz))
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The existing actual powers have genuinely strongly positive chart tensors. -/
theorem formPow_coeff_mem_spCone (w : KahlerBackground n M) (q : ℕ)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (formPow w.form.val q).coeff e z ∈ spCone q := by
  rw [formPow_coeff]
  exact formPower_mem_spCone ⟨(w.isKahler.1 e z hz).1, w.isSemipositive e z hz⟩ q

/-- Genuine differential closedness of every actual Kähler tensor power. -/
theorem formPow_isClosed (w : KahlerBackground n M) :
    ∀ q, (formPow w.form.val q).IsClosed := by
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
        LocalPotentials.closedRealOneOne_hasLocalPotentials w.form e z hz
      have hA : ContDiffOn ℝ ∞ ((formPow w.form.val q).coeff e) W :=
        ((formPow w.form.val q).smooth e).mono hWe
      have hlocal := extDeriv_wedgeTo_smoothDDC_eq_zero hW hρ hA
        (fun y hy => ih e y (hWe hy)) hzW
      have hgerm : (formPow w.form.val (q + 1)).coeff e =ᶠ[𝓝 z]
          fun y => wedgeTo (by omega : 2 + 2 * q = 2 * q + 1 + 1)
            (smoothDDC ρ y) ((formPow w.form.val q).coeff e y) := by
        filter_upwards [hW.mem_nhds hzW] with y hy
        change coordinateWedge ((formPow w.form.val q).coeff e y) (w.form.val.coeff e y) = _
        rw [heq hy]
        exact wedgeTo_comm_of_mem_formSpan
          (mem_formSpan_of_mem_spCone (formPow_coeff_mem_spCone w q e (hWe hy)))
          (w.form.val.coeff e y) rfl (by omega)
      rw [hgerm.extDeriv_eq]
      exact hlocal

/-- Every actual Kähler tensor power is geometrically complex invariant. -/
theorem complexTwist_formPow_geometricallyEq (w : KahlerBackground n M) (q : ℕ) :
    (complexTwist (formPow w.form.val q)).GeometricallyEq (formPow w.form.val q) :=
  complexTwist_geometricallyEq_of_stronglyPositive _ fun e _ hz =>
    formPow_coeff_mem_spCone w q e hz

/-- The actual normalized complex differential of every Kähler power vanishes. -/
theorem dc_formPow_geometricallyEq_zero (w : KahlerBackground n M) (q : ℕ) :
    (dc (formPow w.form.val q)).GeometricallyEq SmoothRealForm.zero := by
  intro e z hz
  rw [dc_coeff_of_complex_invariant _ (complexTwist_formPow_geometricallyEq w q) e hz]
  change (-1 / (4 * Real.pi) : ℝ) •
    (extDeriv ((formPow w.form.val q).coeff e) z).compContinuousLinearMap
      (modelComplexStructure n) = 0
  rw [formPow_isClosed w q e z hz]
  ext v
  simp

end

end SGPT.Foundations.Analysis.Pending.XiaoKahlerPowerClosed
