import SGPT.Convex.Subgradient
import SGPT.Convex.FamilyOperations
import Mathlib.Analysis.Normed.Operator.Prod

/-! The genuine spatial-plus-time pairing, with its actual perfect-duality
producer. The product spaces retain their original product topologies. -/

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The original product cost B(x,m)+t*s. -/
def timeProductPairing (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) :
    (E × ℝ) →ₗ[ℝ] (F × ℝ) →ₗ[ℝ] ℝ :=
  B.compl₁₂ (LinearMap.fst ℝ E ℝ) (LinearMap.fst ℝ F ℝ) +
    (LinearMap.mul ℝ ℝ).compl₁₂ (LinearMap.snd ℝ E ℝ) (LinearMap.snd ℝ F ℝ)

@[simp]
theorem timeProductPairing_apply (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (x : E × ℝ) (y : F × ℝ) :
    timeProductPairing B x y = B x.1 y.1 + x.2 * y.2 := rfl

private def realStrongDualEquiv : ℝ ≃ₗ[ℝ] StrongDual ℝ ℝ where
  toFun r := r • ContinuousLinearMap.id ℝ ℝ
  invFun l := l 1
  left_inv r := by simp
  right_inv l := by
    apply ContinuousLinearMap.ext
    intro s
    change l 1 * s = l s
    simpa only [smul_eq_mul, mul_one, mul_comm] using (l.map_smul s 1).symm
  map_add' r s := by simp [add_smul]
  map_smul' r s := by simp [smul_smul]

/-- Perfection is produced by the actual decomposition of every continuous
linear functional on a product into its two coordinate functionals. -/
instance timeProductPairing_isContPerfPair
    (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) [B.IsContPerfPair] :
    (timeProductPairing B).IsContPerfPair where
  continuous_uncurry := by
    change Continuous (fun p : (E × ℝ) × (F × ℝ) => B p.1.1 p.2.1 + p.1.2 * p.2.2)
    exact (B.continuous_uncurry_of_isContPerfPair.comp
      (continuous_fst.fst.prodMk continuous_snd.fst)).add
      (continuous_fst.snd.mul continuous_snd.snd)
  bijective_left := by
    let e : (E × ℝ) ≃ₗ[ℝ] StrongDual ℝ (F × ℝ) :=
      (B.toContPerfPair.prodCongr realStrongDualEquiv).trans ContinuousLinearMap.coprodEquiv
    convert e.bijective using 1
    funext x
    apply ContinuousLinearMap.ext
    intro y
    rfl
  bijective_right := by
    let e : (F × ℝ) ≃ₗ[ℝ] StrongDual ℝ (E × ℝ) :=
      (B.flip.toContPerfPair.prodCongr realStrongDualEquiv).trans ContinuousLinearMap.coprodEquiv
    convert e.bijective using 1
    funext x
    apply ContinuousLinearMap.ext
    intro y
    change B y.1 x.1 + y.2 * x.2 = B y.1 x.1 + x.2 * y.2
    rw [mul_comm y.2 x.2]

end SGPT.Convex
