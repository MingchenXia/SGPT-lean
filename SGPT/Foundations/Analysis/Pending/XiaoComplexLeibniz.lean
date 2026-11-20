import SGPT.Foundations.Analysis.Pending.XiaoComplexProducts

set_option autoImplicit false

/-!
# Actual scalar Leibniz rules for the higher-degree complex differential

Both identities concern actual chart coefficient functions on their chart
targets. The exterior rule is the existing Fréchet scalar product rule, and
the complex rule uses the actual complex action and its proved square.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoComplexLeibniz

open FirstPass FirstPass.MongeAmpere ProductTestForms ConstantFormProducts
  StronglyPositiveForms ClosedProductCurrents XiaoComplexDifferential XiaoComplexProducts

noncomputable section

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem oneWedge_smul_left (c : ℝ) (L : ComplexModel n →L[ℝ] ℝ)
    (a : RealForm n k) : oneWedge (c • L) a = c • oneWedge L a := by
  have h : (c • L).smulRight a = c • L.smulRight a := by
    ext v
    simp [ContinuousLinearMap.smulRight_apply, smul_smul]
  unfold oneWedge
  rw [h, ContinuousAlternatingMap.alternatizeUncurryFin_smul]

private theorem oneWedge_smul_right (c : ℝ) (L : ComplexModel n →L[ℝ] ℝ)
    (a : RealForm n k) : oneWedge L (c • a) = c • oneWedge L a := by
  rw [← wedgeTo_oneForm_eq_oneWedge (Nat.add_comm 1 k), wedgeTo_smul_right,
    wedgeTo_oneForm_eq_oneWedge]

/-- The actual exterior differential obeys the scalar rule in every degree. -/
theorem exteriorDerivative_smulFun_coeff (f : M → ℝ) (hf : ChartSmooth (n := n) f)
    (a : SmoothRealForm n M k) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    (smulFun f hf a).exteriorDerivative.coeff e z =
      oneWedge (fderiv ℝ (fun y => f (e.val.symm y)) z) (a.coeff e z) +
        f (e.val.symm z) • a.exteriorDerivative.coeff e z :=
  extDeriv_smul_eq
    (((hf e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp))
    (((a.smooth e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp))

/-- The genuine normalized complex differential obeys the actual scalar rule. -/
theorem dc_smulFun_coeff (f : M → ℝ) (hf : ChartSmooth (n := n) f)
    (a : SmoothRealForm n M k) (e : ComplexChart n M) {z : ComplexModel n}
    (hz : z ∈ e.val.target) :
    (dc (smulFun f hf a)).coeff e z =
      oneWedge ((-1 / (4 * Real.pi) : ℝ) •
        (fderiv ℝ (fun y => f (e.val.symm y)) z).comp (modelComplexStructure n))
        (a.coeff e z) + f (e.val.symm z) • (dc a).coeff e z := by
  let t : ℝ := (-1 : ℝ) ^ (k + 1) / (4 * Real.pi)
  have hcoeff : (complexTwist (smulFun f hf a)).coeff e =
      fun y => f (e.val.symm y) • (complexTwist a).coeff e y := by
    funext y
    ext v
    rfl
  have hF := ((hf e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt
    (by simp)
  have hA := (((complexTwist a).smooth e).contDiffAt
    (e.val.open_target.mem_nhds hz)).differentiableAt (by simp)
  have hsq := congrArg (fun b : SmoothRealForm n M k => b.coeff e z) (complexTwist_sq a)
  have hmul : t * (-1 : ℝ) ^ k = -1 / (4 * Real.pi) := by
    dsimp [t]
    rw [pow_succ]
    have hpow : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    field_simp
    nlinarith [hpow]
  change t • (extDeriv ((complexTwist (smulFun f hf a)).coeff e) z).compContinuousLinearMap
      (modelComplexStructure n) = _
  rw [hcoeff, extDeriv_smul_eq hF hA]
  have hlinear (u v : RealForm n (k + 1)) (s : ℝ) :
      (u + s • v).compContinuousLinearMap (modelComplexStructure n) =
        u.compContinuousLinearMap (modelComplexStructure n) +
          s • v.compContinuousLinearMap (modelComplexStructure n) := by
    ext w
    rfl
  rw [hlinear, oneWedge_compContinuousLinearMap]
  change t • (oneWedge
      ((fderiv ℝ (fun y => f (e.val.symm y)) z).comp (modelComplexStructure n))
      ((complexTwist (complexTwist a)).coeff e z) +
      f (e.val.symm z) • (extDeriv ((complexTwist a).coeff e) z).compContinuousLinearMap
        (modelComplexStructure n)) = _
  rw [hsq, coeff_smul, oneWedge_smul_right, smul_add, smul_smul, hmul,
    ← oneWedge_smul_left]
  congr 1
  change t • (f (e.val.symm z) • _) = f (e.val.symm z) • (t • _)
  exact smul_comm _ _ _

end

end SGPT.Foundations.Analysis.Pending.XiaoComplexLeibniz
