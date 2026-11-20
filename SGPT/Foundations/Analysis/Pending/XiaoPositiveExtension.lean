import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false

/-!
# The positive extension step of Lamari's separation argument

A concrete norm ball about an order unit gives both the cofinality required by
Riesz extension and a uniform norm bound on the produced functional. This is
the functional-analytic producer in Xiao's appendix, `lamari4`, independent of
any manifold differential operator or bigness assumption.
-/

open Set

namespace SGPT.Foundations.Analysis.Pending.XiaoPositiveExtension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Positivity on a cone containing a ball about an order unit bounds the functional. -/
theorem abs_le_of_positive_on_order_unit_ball (C : PointedCone ℝ V)
    (L : V →ₗ[ℝ] ℝ) (hL : ∀ x ∈ C, 0 ≤ L x) {e : V} {r : ℝ}
    (hr : 0 < r) (hball : ∀ x, ‖x‖ ≤ r → e + x ∈ C) (x : V) :
    |L x| ≤ (L e / r) * ‖x‖ := by
  have he : e ∈ C := by simpa using hball 0 (by simpa using hr.le)
  have he0 : 0 ≤ L e := hL e he
  by_cases hx : x = 0
  · subst x
    simp
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let t : ℝ := r / ‖x‖
  have ht : 0 < t := div_pos hr hnx
  have hn : ‖t • x‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    exact div_mul_cancel₀ r hnx.ne'
  have hp := hL (e + t • x) (hball (t • x) hn.le)
  have hm := hL (e + -(t • x)) (hball (-(t • x)) (by simpa only [norm_neg] using hn.le))
  simp only [map_add, map_neg, map_smul, smul_eq_mul] at hp hm
  have hscaled : t * |L x| ≤ L e := by
    rw [← abs_of_pos ht, ← abs_mul]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hfinal : r * |L x| ≤ L e * ‖x‖ := by
    change r / ‖x‖ * |L x| ≤ L e at hscaled
    rw [div_mul_eq_mul_div, div_le_iff₀ hnx] at hscaled
    exact hscaled
  rw [div_mul_eq_mul_div, le_div_iff₀ hr]
  nlinarith

/-- Riesz extension with the order-unit ball supplies an actual continuous positive functional. -/
theorem exists_continuous_positive_extension (C : PointedCone ℝ V)
    (S : Submodule ℝ V) (ell : S →ₗ[ℝ] ℝ) (e : S) {r : ℝ}
    (hr : 0 < r) (hball : ∀ x : V, ‖x‖ ≤ r → (e : V) + x ∈ C)
    (hell : ∀ x : S, (x : V) ∈ C → 0 ≤ ell x) :
    ∃ L : V →L[ℝ] ℝ, (∀ x : S, L x = ell x) ∧
      (∀ x ∈ C, 0 ≤ L x) ∧ ∀ x : V, ‖L x‖ ≤ (ell e / r) * ‖x‖ := by
  have hdense : ∀ y : V, ∃ x : S, (x : V) + y ∈ C := by
    intro y
    let t : ℝ := ‖y‖ / r + 1
    have ht : 0 < t := by dsimp [t]; positivity
    have hn : ‖t⁻¹ • y‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht), inv_mul_eq_div,
        div_le_iff₀ ht]
      dsimp [t]
      nlinarith [div_mul_cancel₀ ‖y‖ hr.ne']
    refine ⟨t • e, ?_⟩
    have hscaled := C.smul_mem ht.le (hball (t⁻¹ • y) hn)
    simpa only [smul_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul,
      Submodule.coe_smul] using hscaled
  obtain ⟨L, hext, hpos⟩ := riesz_extension C (⟨S, ell⟩ : V →ₗ.[ℝ] ℝ) hell hdense
  have hext' : ∀ x : S, L x = ell x := hext
  have hbound : ∀ x : V, ‖L x‖ ≤ (ell e / r) * ‖x‖ := by
    intro x
    rw [Real.norm_eq_abs, ← hext' e]
    exact abs_le_of_positive_on_order_unit_ball C L hpos hr hball x
  exact ⟨L.mkContinuous (ell e / r) hbound, hext', hpos, hbound⟩

end SGPT.Foundations.Analysis.Pending.XiaoPositiveExtension
