import SGPT.Foundations.Analysis.Pending.XiaoCovectorProducts
import SGPT.Foundations.Analysis.Pending.XiaoLocalComplexStokes

set_option autoImplicit false

/-!
# Genuine complex cross terms for Gauduchon test forms

The existing actual normalized complex differential reduces to an outer complex
twist for complex-invariant even forms. The actual determinant-one top-density
law and `J² = -id` give the cross-term sign, with no integral assumption.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoGauduchonCrossDensity

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms ConstantFormProducts
  ClosedProductCurrents CoordinateWedgeAssoc ProductTestForms TopDegreeDensity
  XiaoComplexDifferential XiaoComplexProducts XiaoCovectorProducts XiaoLocalComplexStokes

noncomputable section

variable {n k m q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem oneWedge_neg_left (L : ComplexModel n →L[ℝ] ℝ) (A : RealForm n k) :
    oneWedge (-L) A = -oneWedge L A := by
  rw [← covectorWedgeCLM_apply, map_neg, neg_apply, covectorWedgeCLM_apply]

private theorem oneWedge_smul_left (c : ℝ) (L : ComplexModel n →L[ℝ] ℝ)
    (A : RealForm n k) : oneWedge (c • L) A = c • oneWedge L A := by
  rw [← covectorWedgeCLM_apply, map_smul, smul_apply, covectorWedgeCLM_apply]

private theorem oneWedge_smul_right (c : ℝ) (L : ComplexModel n →L[ℝ] ℝ)
    (A : RealForm n k) : oneWedge L (c • A) = c • oneWedge L A := by
  rw [← covectorWedgeCLM_apply, map_smul, covectorWedgeCLM_apply]

/-- Actual complex invariance gives the genuine even-degree complex differential. -/
theorem dc_coeff_of_complex_invariant (G : SmoothRealForm n M (2 * q))
    (hG : (complexTwist G).GeometricallyEq G)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target) :
    (dc G).coeff e z = (-1 / (4 * Real.pi) : ℝ) •
      (G.exteriorDerivative.coeff e z).compContinuousLinearMap (modelComplexStructure n) := by
  have hd := hG.exteriorDerivative
  change ((-1 : ℝ) ^ (2 * q + 1) / (4 * Real.pi)) •
    ((complexTwist G).exteriorDerivative.coeff e z).compContinuousLinearMap
      (modelComplexStructure n) = _
  rw [hd e hz]
  simp [pow_add, pow_mul]

/-- The actual top-density cross sign follows from `J² = -id` and real determinant one. -/
theorem topDensity_oneWedge_complex_swap (L : ComplexModel (m + 1) →L[ℝ] ℝ)
    (H : RealForm (m + 1) (2 * m + 1)) :
    topDensity (oneWedge (L.comp (modelComplexStructure (m + 1))) H) =
      -topDensity (oneWedge L (H.compContinuousLinearMap (modelComplexStructure (m + 1)))) := by
  have hLL : (L.comp (modelComplexStructure (m + 1))).comp (modelComplexStructure (m + 1)) =
      -L := by
    ext v
    simp [ContinuousLinearMap.comp_apply, modelComplexStructure_apply, smul_smul, Complex.I_mul_I]
  have h := topDensity_comp_modelComplexStructure
    (oneWedge (L.comp (modelComplexStructure (m + 1))) H)
  rw [oneWedge_compContinuousLinearMap, hLL, oneWedge_neg_left] at h
  have hneg : topDensity (-oneWedge L
      (H.compContinuousLinearMap (modelComplexStructure (m + 1)))) =
      -topDensity (oneWedge L (H.compContinuousLinearMap (modelComplexStructure (m + 1)))) :=
    (topDensityLM (m + 1)).map_neg _
  rw [hneg] at h
  exact h.symm

/-- Actual scalar `dᶜ` and actual `dᶜG` have opposite top-density cross terms. -/
theorem topDensity_scalar_complex_cross {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
    (f : M → ℝ) (hf : ChartSmooth (n := m + 1) f)
    (G : SmoothRealForm (m + 1) M (2 * m))
    (hG : (complexTwist G).GeometricallyEq G)
    (e : ComplexChart (m + 1) M) {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target) :
    topDensity (wedgeTo (Nat.add_comm 1 (2 * m + 1))
      ((SmoothDDCForm.dcForm f hf).coeff e z)
      (G.exteriorDerivative.coeff e z)) =
    -topDensity (oneWedge (fderiv ℝ (fun y => f (e.val.symm y)) z) ((dc G).coeff e z)) := by
  change topDensity (wedgeTo (Nat.add_comm 1 (2 * m + 1))
    (oneForm (m + 1) ((-1 / (4 * Real.pi) : ℝ) •
      (fderiv ℝ (fun y => f (e.val.symm y)) z).comp (modelComplexStructure (m + 1))))
      (G.exteriorDerivative.coeff e z)) = _
  rw [wedgeTo_oneForm_eq_oneWedge, dc_coeff_of_complex_invariant G hG e hz, oneWedge_smul_left,
    oneWedge_smul_right, topDensity_smul, topDensity_smul,
    topDensity_oneWedge_complex_swap, mul_neg]

end

end SGPT.Foundations.Analysis.Pending.XiaoGauduchonCrossDensity
