import SGPT.Convex.Subgradient
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.ConstMulAction

set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set
open scoped Topology Pointwise RealInnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Literal finite-profile supporting inequalities produce the genuine
positive-scaled subgradient image. No prescribed convex body is an input. -/
theorem rawSubgradientImage_coe_pos_mul (f : E → ℝ) {c : ℝ} (hc : 0 < c) :
    rawSubgradientImage (innerₗ E) (fun x => ((c * f x : ℝ) : EReal)) =
      c • rawSubgradientImage (innerₗ E) (fun x => (f x : EReal)) := by
  ext m
  constructor
  · intro hm
    obtain ⟨x,hx⟩ := mem_iUnion.mp hm
    refine ⟨c⁻¹ • m, mem_iUnion.mpr ⟨x, ?_⟩, smul_inv_smul₀ hc.ne' m⟩
    intro y
    have hineq : c * f x + ⟪y-x,m⟫ ≤ c * f y := by
      have hi := hx y
      change ((c * f x : ℝ) : EReal) + (⟪y-x,m⟫ : EReal) ≤ ((c * f y : ℝ) : EReal) at hi
      rwa [←EReal.coe_add, EReal.coe_le_coe_iff] at hi
    change (f x : EReal) + (⟪y-x,c⁻¹ • m⟫ : EReal) ≤ (f y : EReal)
    rw [real_inner_smul_right, ←EReal.coe_add, EReal.coe_le_coe_iff]
    apply (mul_le_mul_iff_right₀ hc).mp
    simpa only [mul_add, ←mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hineq
  · rintro ⟨m,hm,rfl⟩
    obtain ⟨x,hx⟩ := mem_iUnion.mp hm
    apply mem_iUnion.mpr
    refine ⟨x, ?_⟩
    intro y
    have hineq : f x + ⟪y-x,m⟫ ≤ f y := by
      have hi := hx y
      change (f x : EReal) + (⟪y-x,m⟫ : EReal) ≤ (f y : EReal) at hi
      rwa [←EReal.coe_add, EReal.coe_le_coe_iff] at hi
    change ((c * f x : ℝ) : EReal) + (⟪y-x,c • m⟫ : EReal) ≤ ((c * f y : ℝ) : EReal)
    rw [real_inner_smul_right, ←EReal.coe_add, EReal.coe_le_coe_iff]
    simpa only [mul_add] using (mul_le_mul_of_nonneg_left hineq hc.le)

/-- Actual closed subgradient bodies retain exact positive scaling,
including lower-dimensional bodies and dimension zero. -/
theorem closure_rawSubgradientImage_coe_pos_mul (f : E → ℝ) {c : ℝ} (hc : 0 < c) :
    closure (rawSubgradientImage (innerₗ E) (fun x => ((c * f x : ℝ) : EReal))) =
      c • closure (rawSubgradientImage (innerₗ E) (fun x => (f x : EReal))) := by
  rw [rawSubgradientImage_coe_pos_mul f hc, closure_smul₀]

end SGPT.Convex
