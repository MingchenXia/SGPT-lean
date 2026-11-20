import SGPT.Foundations.Analysis.Pending.XiaoKahlerPowerClosed
import SGPT.Foundations.Analysis.Pending.XiaoGauduchonIntegration

set_option autoImplicit false

/-!
# The actual scalar `ddᶜ` producer against closed invariant fields

Genuine scalar and covector product rules yield geometric tensor identities.
In particular the actual Kähler powers consume the actual Poisson solution.
-/

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoKahlerScalarDDC

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ConstantFormProducts ClosedProductCurrents CoordinateWedgeAssoc ProductTestForms
  XiaoComplexDifferential XiaoComplexLeibniz XiaoCovectorProducts XiaoGauduchonCrossDensity
  XiaoGauduchonIntegration XiaoKahlerPowerClosed

noncomputable section

variable {n k q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Actual vanishing of `dᶜG` removes the complex scalar product cross term. -/
theorem dc_smulFun_geometricallyEq_dcProduct (f : M → ℝ) (hf : ChartSmooth (n := n) f)
    (G : SmoothRealForm n M k) (hG : (dc G).GeometricallyEq SmoothRealForm.zero) :
    (dc (smulFun f hf G)).GeometricallyEq
      (exteriorProductTo (Nat.add_comm 1 k) (SmoothDDCForm.dcForm f hf) G) := by
  intro e z hz
  rw [dc_smulFun_coeff f hf G e hz, hG e hz]
  change oneWedge _ (G.coeff e z) + f (e.val.symm z) • (0 : RealForm n (k + 1)) = _
  rw [smul_zero, add_zero, exteriorProductTo_coeff]
  exact (wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 k) _ (G.coeff e z)).symm

/-- Actual `ddᶜ(fG)` is the genuine scalar `ddᶜ` product when `G` is closed and invariant. -/
theorem ddc_smulFun_geometricallyEq_of_closed_invariant (f : M → ℝ)
    (hf : ChartSmooth (n := n) f) (G : SmoothRealForm n M (2 * q))
    (hclosed : G.IsClosed) (hinv : (complexTwist G).GeometricallyEq G) :
    (ddc (smulFun f hf G)).GeometricallyEq
      (exteriorProductTo (by omega : 2 + 2 * q = 2 * q + 1 + 1)
        (SmoothDDCForm.ddcForm f hf) G) := by
  have hdc0 : (dc G).GeometricallyEq SmoothRealForm.zero := by
    intro e z hz
    rw [dc_coeff_of_complex_invariant G hinv e hz]
    change (-1 / (4 * Real.pi) : ℝ) •
      (extDeriv (G.coeff e) z).compContinuousLinearMap (modelComplexStructure n) = 0
    rw [hclosed e z hz]
    ext v
    simp
  have hd := (dc_smulFun_geometricallyEq_dcProduct f hf G hdc0).exteriorDerivative
  intro e z hz
  change (dc (smulFun f hf G)).exteriorDerivative.coeff e z = _
  rw [hd e hz, exteriorDerivative_dcProduct_coeff f hf G e hz,
    exteriorProductTo_coeff]
  change _ - wedgeTo _ _ (extDeriv (G.coeff e) z) = _
  rw [hclosed e z hz, wedgeTo_zero_right, sub_zero]

/-- Genuine scalar `ddᶜ` against each actual Kähler tensor power. -/
theorem ddc_smulFun_formPow_geometricallyEq (w : KahlerBackground n M) (q : ℕ)
    (f : M → ℝ) (hf : ChartSmooth (n := n) f) :
    (ddc (smulFun f hf (formPow w.form.val q))).GeometricallyEq
      (exteriorProductTo (by omega : 2 + 2 * q = 2 * q + 1 + 1)
        (SmoothDDCForm.ddcForm f hf) (formPow w.form.val q)) :=
  ddc_smulFun_geometricallyEq_of_closed_invariant f hf (formPow w.form.val q)
    (formPow_isClosed w q) (complexTwist_formPow_geometricallyEq w q)

end

end SGPT.Foundations.Analysis.Pending.XiaoKahlerScalarDDC
