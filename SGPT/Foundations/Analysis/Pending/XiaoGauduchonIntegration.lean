import SGPT.Foundations.Analysis.Pending.XiaoGauduchonCrossDensity
import SGPT.Foundations.Analysis.Pending.XiaoComplexLeibniz
import SGPT.Foundations.Analysis.Pending.XiaoGlobalStokes

set_option autoImplicit false

/-!
# Genuine Gauduchon integration by parts

All differentials and products are the existing actual smooth forms. Two actual
global Stokes identities and the determinant-one complex cross-density identity
give integration by parts and then cancellation from actual geometric `ddᶜG = 0`.
-/

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoGauduchonIntegration

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ConstantFormProducts ClosedProductCurrents CoordinateWedgeAssoc ProductTestForms
  LocalProductCurrents TopDegreeDensity IntegrationCurrent GlobalNonPluripolar XiaoComplexDifferential
  XiaoComplexProducts XiaoCovectorProducts XiaoGauduchonCrossDensity XiaoComplexLeibniz
  XiaoGlobalStokes

noncomputable section

variable {n p q r k m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The existing actual global exterior product read in its prescribed equal degree. -/
def exteriorProductTo (h : p + q = r) (A : SmoothRealForm n M p) (B : SmoothRealForm n M q) :
    SmoothRealForm n M r := h ▸ exteriorProduct A B

@[simp] theorem exteriorProductTo_coeff (h : p + q = r)
    (A : SmoothRealForm n M p) (B : SmoothRealForm n M q)
    (e : ComplexChart n M) (z : ComplexModel n) :
    (exteriorProductTo h A B).coeff e z = wedgeTo h (A.coeff e z) (B.coeff e z) := by
  subst h
  rfl

/-- The genuine scalar complex covector product rule for the actual global forms. -/
theorem exteriorDerivative_dcProduct_coeff (f : M → ℝ) (hf : ChartSmooth (n := n) f)
    (G : SmoothRealForm n M k) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    (exteriorProductTo (Nat.add_comm 1 k) (SmoothDDCForm.dcForm f hf) G).exteriorDerivative.coeff e z =
      wedgeTo (by omega : 2 + k = k + 1 + 1) ((SmoothDDCForm.ddcForm f hf).coeff e z)
        (G.coeff e z) -
      wedgeTo (Nat.add_comm 1 (k + 1)) ((SmoothDDCForm.dcForm f hf).coeff e z)
        (G.exteriorDerivative.coeff e z) := by
  let L : ComplexModel n → (ComplexModel n →L[ℝ] ℝ) := fun y =>
    (-1 / (4 * Real.pi) : ℝ) •
      (fderiv ℝ (fun t => f (e.val.symm t)) y).comp (modelComplexStructure n)
  have hL : ContDiffOn ℝ ∞ L e.val.target :=
    (((hf e).fderiv_of_isOpen e.val.open_target (by simp)).clm_comp
      contDiffOn_const).const_smul (-1 / (4 * Real.pi) : ℝ)
  have hLD := (hL.contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hGD := ((G.smooth e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hb : (SmoothDDCForm.dcForm f hf).coeff e = fun y => oneForm n (L y) := rfl
  have hp : (exteriorProductTo (Nat.add_comm 1 k) (SmoothDDCForm.dcForm f hf) G).coeff e =
      fun y => oneWedge (L y) (G.coeff e y) := by
    funext y
    rw [exteriorProductTo_coeff, hb]
    exact wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 k) (L y) (G.coeff e y)
  change extDeriv _ z = _
  rw [hp, extDeriv_oneWedge_eq hLD hGD]
  rw [← hb]
  change _ - oneWedge (L z) (G.exteriorDerivative.coeff e z) = _
  rw [hb, wedgeTo_oneForm_eq_oneWedge]
  rfl

section TopDegree

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem topRatio_gauduchon_difference (w : KahlerBackground (m + 1) M)
    (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (G : SmoothRealForm (m + 1) M (2 * m))
    (hG : (complexTwist G).GeometricallyEq G) (x : M) :
    topRatio w.form.val (exteriorProductTo (by omega : 2 + 2 * m = 2 * (m + 1))
      (SmoothDDCForm.ddcForm f hf) G) x -
      topRatio w.form.val (smulFun f hf (ddc G)) x =
    topRatio w.form.val (exteriorProductTo (Nat.add_comm 1 (2 * m))
      (SmoothDDCForm.dcForm f hf) G).exteriorDerivative x -
      topRatio w.form.val (smulFun f hf (dc G)).exteriorDerivative x := by
  let e := complexChartAt (n := m + 1) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have hB := exteriorDerivative_dcProduct_coeff f hf G e hz
  have hH := exteriorDerivative_smulFun_coeff f hf (dc G) e hz
  have hcross := topDensity_scalar_complex_cross f hf G hG e hz
  change topDensity (exteriorProductTo _ (SmoothDDCForm.ddcForm f hf) G |>.coeff e (e.val x)) /
      topDensity ((formPow w.form.val (m + 1)).coeff e (e.val x)) -
      topDensity ((smulFun f hf (ddc G)).coeff e (e.val x)) /
      topDensity ((formPow w.form.val (m + 1)).coeff e (e.val x)) = _
  change _ = topDensity ((exteriorProductTo _ (SmoothDDCForm.dcForm f hf) G).exteriorDerivative.coeff e (e.val x)) /
      topDensity ((formPow w.form.val (m + 1)).coeff e (e.val x)) -
      topDensity ((smulFun f hf (dc G)).exteriorDerivative.coeff e (e.val x)) /
      topDensity ((formPow w.form.val (m + 1)).coeff e (e.val x))
  rw [exteriorProductTo_coeff, smulFun_coeff, hB, hH, topDensity_sub, topDensity_add,
    topDensity_smul, topDensity_smul, hcross]
  dsimp only [XiaoComplexDifferential.ddc]
  ring

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Actual global Stokes proves genuine integration by parts against a complex-invariant test form. -/
theorem integral_ddcProduct_eq_integral_smul_ddc (w : KahlerBackground (m + 1) M)
    (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (G : SmoothRealForm (m + 1) M (2 * m))
    (hG : (complexTwist G).GeometricallyEq G) :
    (∫ x, topRatio w.form.val (exteriorProductTo (by omega : 2 + 2 * m = 2 * (m + 1))
      (SmoothDDCForm.ddcForm f hf) G) x ∂(kahlerVolume w)) =
    ∫ x, topRatio w.form.val (smulFun f hf (ddc G)) x ∂(kahlerVolume w) := by
  have heq := funext (topRatio_gauduchon_difference w f hf G hG)
  have hi := congrArg (fun h : M → ℝ => ∫ x, h x ∂(kahlerVolume w)) heq
  rw [integral_sub (integrable_topRatio w _) (integrable_topRatio w _),
    integral_sub (integrable_topRatio w _) (integrable_topRatio w _),
    integral_exteriorDerivative_eq_zero, integral_exteriorDerivative_eq_zero, sub_self] at hi
  exact sub_eq_zero.mp hi

/-- The genuine geometric Gauduchon condition removes every actual smooth potential term. -/
theorem integral_ddcProduct_eq_zero_of_gauduchon (w : KahlerBackground (m + 1) M)
    (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (G : SmoothRealForm (m + 1) M (2 * m))
    (hG : (complexTwist G).GeometricallyEq G)
    (hddc : (ddc G).GeometricallyEq (0 : SmoothRealForm (m + 1) M (2 * (m + 1)))) :
    (∫ x, topRatio w.form.val (exteriorProductTo (by omega : 2 + 2 * m = 2 * (m + 1))
      (SmoothDDCForm.ddcForm f hf) G) x ∂(kahlerVolume w)) = 0 := by
  rw [integral_ddcProduct_eq_integral_smul_ddc w f hf G hG]
  have heq : topRatio w.form.val (smulFun f hf (ddc G)) = fun _ => 0 := by
    funext x
    let e := complexChartAt (n := m + 1) x
    have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
    change topDensity ((smulFun f hf (ddc G)).coeff e (e.val x)) /
      topDensity ((formPow w.form.val (m + 1)).coeff e (e.val x)) = 0
    rw [smulFun_coeff, hddc e hz, coeff_zero, smul_zero, topDensity_zero, zero_div]
  rw [heq, integral_zero]

/-- Actual `(m,m)` test tensors commute with the two-form, so Gauduchon cancellation holds in test order. -/
theorem integral_wedgeTwo_ddcForm_eq_zero_of_gauduchon (w : KahlerBackground (m + 1) M)
    (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (G : SmoothRealForm (m + 1) M (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ formSpan (m + 1) m)
    (hddc : (ddc G).GeometricallyEq (0 : SmoothRealForm (m + 1) M (2 * (m + 1)))) :
    (∫ x, topRatio w.form.val (wedgeTwo G (SmoothDDCForm.ddcForm f hf)) x ∂(kahlerVolume w)) = 0 := by
  have hzero := integral_ddcProduct_eq_zero_of_gauduchon w f hf G
    (complexTwist_geometricallyEq_of_formSpan G hG) hddc
  have heq : topRatio w.form.val (wedgeTwo G (SmoothDDCForm.ddcForm f hf)) =
      topRatio w.form.val (exteriorProductTo (by omega : 2 + 2 * m = 2 * (m + 1))
        (SmoothDDCForm.ddcForm f hf) G) := by
    funext x
    let e := complexChartAt (n := m + 1) x
    have hz : e.val x ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
    simp only [topRatio, chartRatio, wedgeTwo_coeff, exteriorProductTo_coeff]
    congr 1
    exact congrArg topDensity (wedgeTo_comm_of_mem_formSpan (hG e (e.val x) hz)
      ((SmoothDDCForm.ddcForm f hf).coeff e (e.val x)) rfl (by omega))
  rw [heq]
  exact hzero

/-- The actual Gauduchon test integral depends only on the smooth potential class of a two-form. -/
theorem integral_wedgeTwo_add_ddcForm_eq (w : KahlerBackground (m + 1) M)
    (A : SmoothRealForm (m + 1) M 2) (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (G : SmoothRealForm (m + 1) M (2 * m))
    (hG : ∀ e z, z ∈ e.val.target → G.coeff e z ∈ formSpan (m + 1) m)
    (hddc : (ddc G).GeometricallyEq (0 : SmoothRealForm (m + 1) M (2 * (m + 1)))) :
    (∫ x, topRatio w.form.val (wedgeTwo G (A + SmoothDDCForm.ddcForm f hf)) x ∂(kahlerVolume w)) =
    ∫ x, topRatio w.form.val (wedgeTwo G A) x ∂(kahlerVolume w) := by
  have hforms : wedgeTwo G (A + SmoothDDCForm.ddcForm f hf) =
      wedgeTwo G A + wedgeTwo G (SmoothDDCForm.ddcForm f hf) := by
    apply smoothRealForm_ext
    intro e z
    exact coordinateWedge_add_right _ _ _
  have heq : topRatio w.form.val (wedgeTwo G (A + SmoothDDCForm.ddcForm f hf)) =
      fun x => topRatio w.form.val (wedgeTwo G A) x +
        topRatio w.form.val (wedgeTwo G (SmoothDDCForm.ddcForm f hf)) x := by
    funext x
    rw [hforms]
    exact topRatio_add w.form.val _ _ x
  rw [heq]
  rw [integral_add (integrable_topRatio w _) (integrable_topRatio w _),
    integral_wedgeTwo_ddcForm_eq_zero_of_gauduchon w f hf G hG hddc, add_zero]

end TopDegree

end

end SGPT.Foundations.Analysis.Pending.XiaoGauduchonIntegration
