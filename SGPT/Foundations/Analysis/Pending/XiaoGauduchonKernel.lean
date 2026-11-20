import SGPT.Foundations.Analysis.Pending.XiaoKahlerPowerClosed
import SGPT.Foundations.Analysis.Pending.PositiveProductCurrents

set_option autoImplicit false

/-!
# The actual Gauduchon kernel and its positive order unit

The actual differential is linear on geometric forms. Its genuine vanishing
locus in the existing test space is a real submodule containing the actual
Kähler order unit; the actual strongly positive tests form a pointed cone.
-/

open Set Filter
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.XiaoGauduchonKernel

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents XiaoComplexDifferential XiaoKahlerPowerClosed

noncomputable section

variable {n k q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual exterior derivative preserves sums on all chart targets. -/
theorem exteriorDerivative_add_geometricallyEq (A B : SmoothRealForm n M k) :
    (A + B).exteriorDerivative.GeometricallyEq
      (A.exteriorDerivative + B.exteriorDerivative) := by
  intro e z hz
  exact extDeriv_add
    (((A.smooth e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp))
    (((B.smooth e).contDiffAt (e.val.open_target.mem_nhds hz)).differentiableAt (by simp))

/-- The actual exterior derivative preserves real scalar multiples on chart targets. -/
theorem exteriorDerivative_smul_geometricallyEq (c : ℝ) (A : SmoothRealForm n M k) :
    (c • A).exteriorDerivative.GeometricallyEq (c • A.exteriorDerivative) := by
  intro e z _
  exact extDeriv_smul c (A.coeff e)

/-- The actual normalized complex differential preserves sums geometrically. -/
theorem dc_add_geometricallyEq (A B : SmoothRealForm n M k) :
    (dc (A + B)).GeometricallyEq (dc A + dc B) := by
  have htw : complexTwist (A + B) = complexTwist A + complexTwist B :=
    (complexTwistLM (n := n) (M := M) (k := k)).map_add A B
  have hd := exteriorDerivative_add_geometricallyEq (complexTwist A) (complexTwist B)
  intro e z hz
  change _ • ((complexTwist (A + B)).exteriorDerivative.coeff e z).compContinuousLinearMap
      (modelComplexStructure n) = _
  rw [htw, hd e hz]
  ext v
  simp [dc, complexTwist_coeff, coeff_add, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply, mul_add]

/-- The actual normalized complex differential preserves real scalar multiples geometrically. -/
theorem dc_smul_geometricallyEq (c : ℝ) (A : SmoothRealForm n M k) :
    (dc (c • A)).GeometricallyEq (c • dc A) := by
  have htw : complexTwist (c • A) = c • complexTwist A :=
    (complexTwistLM (n := n) (M := M) (k := k)).map_smul c A
  have hd := exteriorDerivative_smul_geometricallyEq c (complexTwist A)
  intro e z hz
  change _ • ((complexTwist (c • A)).exteriorDerivative.coeff e z).compContinuousLinearMap
      (modelComplexStructure n) = _
  rw [htw, hd e hz]
  ext v
  simp [dc, complexTwist_coeff, coeff_smul, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply]
  ring

/-- The actual higher-degree `ddᶜ` preserves sums on geometric forms. -/
theorem ddc_add_geometricallyEq (A B : SmoothRealForm n M k) :
    (ddc (A + B)).GeometricallyEq (ddc A + ddc B) :=
  (dc_add_geometricallyEq A B).exteriorDerivative.trans
    (exteriorDerivative_add_geometricallyEq (dc A) (dc B))

/-- The actual higher-degree `ddᶜ` preserves real scalar multiples geometrically. -/
theorem ddc_smul_geometricallyEq (c : ℝ) (A : SmoothRealForm n M k) :
    (ddc (c • A)).GeometricallyEq (c • ddc A) :=
  (dc_smul_geometricallyEq c A).exteriorDerivative.trans
    (exteriorDerivative_smul_geometricallyEq c (dc A))

/-- The actual second complex differential of the zero tensor vanishes geometrically. -/
theorem ddc_zero_geometricallyEq :
    (ddc (0 : SmoothRealForm n M k)).GeometricallyEq 0 := by
  simpa only [zero_smul] using ddc_smul_geometricallyEq (0 : ℝ) (0 : SmoothRealForm n M k)

/-- The actual Gauduchon condition, as a genuine submodule of the existing test space. -/
def gauduchonKernel (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (q : ℕ) :
    Submodule ℝ (testSpace n M q) where
  carrier := {G | (ddc (G : SmoothRealForm n M (2 * q))).GeometricallyEq 0}
  zero_mem' := ddc_zero_geometricallyEq
  add_mem' := by
    intro A B hA hB e z hz
    change (ddc ((A : SmoothRealForm n M (2 * q)) +
      (B : SmoothRealForm n M (2 * q)))).coeff e z = 0
    rw [ddc_add_geometricallyEq (A : SmoothRealForm n M (2 * q)) B e hz, coeff_add,
      hA e hz, hB e hz]
    change (0 : RealForm n (2 * q + 1 + 1)) + 0 = 0
    exact zero_add 0
  smul_mem' := by
    intro c A hA e z hz
    change (ddc (c • (A : SmoothRealForm n M (2 * q)))).coeff e z = 0
    rw [ddc_smul_geometricallyEq c (A : SmoothRealForm n M (2 * q)) e hz, coeff_smul,
      hA e hz]
    exact smul_zero c

@[simp] theorem mem_gauduchonKernel (G : testSpace n M q) :
    G ∈ gauduchonKernel n M q ↔
      (ddc (G : SmoothRealForm n M (2 * q))).GeometricallyEq 0 := Iff.rfl

/-- The existing pointwise strongly positive tests form an actual pointed convex cone. -/
def stronglyPositiveTestCone (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] (q : ℕ) :
    PointedCone ℝ (testSpace n M q) where
  carrier := positiveCone n M q
  zero_mem' := fun _ _ _ => (spCone q).zero_mem
  add_mem' := by
    intro A B hA hB e z hz
    exact (spCone q).add_mem (hA e z hz) (hB e z hz)
  smul_mem' := by
    intro c A hA e z hz
    exact (spCone q).smul_mem c.property (hA e z hz)

@[simp] theorem mem_stronglyPositiveTestCone (G : testSpace n M q) :
    G ∈ stronglyPositiveTestCone n M q ↔ G ∈ positiveCone n M q := Iff.rfl

/-- The actual Kähler power is annihilated by the actual higher-degree `ddᶜ`. -/
theorem ddc_formPow_geometricallyEq_zero (w : KahlerBackground n M) (q : ℕ) :
    (ddc (formPow w.form.val q)).GeometricallyEq 0 := by
  have hd := (dc_formPow_geometricallyEq_zero w q).exteriorDerivative
  intro e z hz
  change (dc (formPow w.form.val q)).exteriorDerivative.coeff e z = 0
  have heq := hd e hz
  rw [heq]
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (ComplexModel n) ℝ)
    (fderiv ℝ (fun _ : ComplexModel n => (0 : RealForm n (2 * q + 1))) z) = 0
  rw [fderiv_const_apply, map_zero]

/-- The actual positive Kähler order unit belongs to the actual Gauduchon kernel. -/
theorem kahlerTest_mem_gauduchonKernel (w : KahlerBackground n M) (q : ℕ) :
    kahlerTest w q ∈ gauduchonKernel n M q := ddc_formPow_geometricallyEq_zero w q

end

end SGPT.Foundations.Analysis.Pending.XiaoGauduchonKernel
