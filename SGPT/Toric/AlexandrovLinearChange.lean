import SGPT.Convex.SubgradientMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The real Monge–Ampère measure under a unimodular affine change of variables

For a finite convex `h` on `E = ℝ^n` (Euclidean model, standard pairing), a linear
automorphism `B` with inverse `C`, and a vector `w`, the function
`F x = h (B x) + ⟪w, x⟫` has Legendre transform `F^*(p) = h^*(A (p - w))`, where `A`
is the transpose of `C`, and gradient `∇F^*(p) = C (∇h^*(A (p - w)))`.  If
`|det A| = 1` then the real Monge–Ampère (Alexandrov) measures satisfy
`MA_ℝ(F) = C_* MA_ℝ(h)`.

This is used to transport the tropical Monge–Ampère identity from the vertex chart
coordinates of a toric manifold to the standard coordinates of `N_ℝ`
(source `prop:toricMAandrealMA`).
-/

set_option autoImplicit false
noncomputable section
namespace SGPT.Toric
open Set Filter MeasureTheory SGPT.Convex
open scoped Topology RealInnerProductSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Data of a unimodular linear change of variables and its transpose. -/
structure UnimodularChange (n : ℕ) where
  /-- The forward map. -/
  B : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)
  /-- Its inverse. -/
  C : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)
  /-- The transpose of `C`. -/
  A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)
  C_B : ∀ x, C (B x) = x
  B_C : ∀ y, B (C y) = y
  inner_C : ∀ y q, ⟪C y, q⟫ = ⟪y, A q⟫
  abs_det_A : |LinearMap.det (A : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))| = 1

namespace UnimodularChange

variable (T : UnimodularChange n)

/-- The affine change `p ↦ A (p - w)`. -/
def affine (w : E) : E ≃ₜ E :=
  (Homeomorph.subRight w).trans T.A.toHomeomorph

theorem affine_apply (w p : E) : T.affine w p = T.A (p - w) := rfl

theorem measurePreserving_affine (w : E) :
    Measure.map (T.affine w) (volume : Measure E) = volume := by
  have hA : Measure.map (T.A : E → E) (volume : Measure E) = volume := by
    have hdet : LinearMap.det (T.A : E →ₗ[ℝ] E) ≠ 0 := by
      intro h
      have := T.abs_det_A
      rw [h, abs_zero] at this
      exact zero_ne_one this
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E) hdet
    rw [abs_inv, T.abs_det_A, inv_one, ENNReal.ofReal_one, one_smul] at h
    exact h
  have hsub : Measure.map (fun p : E => p - w) (volume : Measure E) = volume := by
    simpa only [sub_eq_add_neg] using map_add_right_eq_self (volume : Measure E) (-w)
  calc Measure.map (T.affine w) (volume : Measure E)
      = Measure.map (T.A : E → E) (Measure.map (fun p : E => p - w) volume) :=
        (Measure.map_map (f := fun p : E => p - w) T.A.continuous.measurable
          (measurable_id.sub_const w)).symm
    _ = volume := by rw [hsub, hA]

/-- `F^*(p) = h^*(A (p - w))`. -/
theorem conjugate_comp (h : E → ℝ) (w : E) :
    conjugate (innerₗ E) (fun x => ((h (T.B x) + ⟪w, x⟫ : ℝ) : EReal)) =
      fun p => conjugate (innerₗ E) (fun y => (h y : EReal)) (T.affine w p) := by
  funext p
  have hterm (x : E) : ((innerₗ E x p : ℝ) : EReal) - ((h (T.B x) + ⟪w, x⟫ : ℝ) : EReal) =
      ((innerₗ E (T.B x) (T.affine w p) : ℝ) : EReal) - (h (T.B x) : EReal) := by
    rw [← EReal.coe_sub, ← EReal.coe_sub, affine_apply, innerₗ_apply_apply, innerₗ_apply_apply,
      ← T.inner_C, T.C_B, inner_sub_right, real_inner_comm w x]
    congr 1
    ring
  apply le_antisymm
  · refine iSup_le fun x => ?_
    beta_reduce
    rw [hterm x]
    exact le_iSup (fun y => ((innerₗ E y (T.affine w p) : ℝ) : EReal) - (h y : EReal)) (T.B x)
  · refine iSup_le fun y => ?_
    beta_reduce
    have h' := hterm (T.C y)
    have hle := le_iSup (fun x => ((innerₗ E x p : ℝ) : EReal) -
      ((h (T.B x) + ⟪w, x⟫ : ℝ) : EReal)) (T.C y)
    rw [T.B_C] at h' hle
    rw [← h']
    exact hle

/-- `∇F^*(p) = C (∇h^*(A (p - w)))`. -/
theorem conjugateGradient_comp (h : E → ℝ) (w : E) (p : E) :
    conjugateGradient (innerₗ E) (fun x => ((h (T.B x) + ⟪w, x⟫ : ℝ) : EReal)) p =
      T.C (conjugateGradient (innerₗ E) (fun y => (h y : EReal)) (T.affine w p)) := by
  let g : E → ℝ := fun r => (conjugate (innerₗ E) (fun y => (h y : EReal)) r).toReal
  have hfun : (fun q => (conjugate (innerₗ E)
      (fun x => ((h (T.B x) + ⟪w, x⟫ : ℝ) : EReal)) q).toReal) =
      fun q => (g ∘ T.A) (q - w) := by
    rw [T.conjugate_comp h w]
    rfl
  have hder : fderiv ℝ (fun q => (conjugate (innerₗ E)
      (fun x => ((h (T.B x) + ⟪w, x⟫ : ℝ) : EReal)) q).toReal) p =
      (fderiv ℝ g (T.affine w p)).comp (T.A : E →L[ℝ] E) := by
    rw [hfun, fderiv_comp_sub (f := g ∘ T.A) w, T.A.comp_right_fderiv]
    rfl
  let P := (innerₗ E).toContPerfPair.toContinuousLinearEquiv
  change P.symm (fderiv ℝ _ p) = T.C (P.symm (fderiv ℝ g (T.affine w p)))
  rw [hder]
  apply P.injective
  rw [P.apply_symm_apply]
  ext z
  have key : ∀ x y : E, P x y = ⟪x, y⟫ := fun x y => rfl
  rw [ContinuousLinearMap.comp_apply, key, T.inner_C, ← key, P.apply_symm_apply]
  rfl

/-- The real Monge–Ampère measure is transported by `C`: `MA_ℝ(F) = C_* MA_ℝ(h)`. -/
theorem alexandrovMeasure_comp (h : E → ℝ) (w : E) :
    alexandrovMeasure (innerₗ E) (volume : Measure E)
        (fun x => ((h (T.B x) + ⟪w, x⟫ : ℝ) : EReal)) =
      Measure.map T.C (alexandrovMeasure (innerₗ E) (volume : Measure E)
        (fun y => (h y : EReal))) := by
  have hC : Measurable (T.C : E → E) := T.C.continuous_of_finiteDimensional.measurable
  have hdom : interior (effectiveDomain (conjugate (innerₗ E)
      (fun x => ((h (T.B x) + ⟪w, x⟫ : ℝ) : EReal)))) =
      T.affine w ⁻¹' interior (effectiveDomain (conjugate (innerₗ E)
        (fun y => (h y : EReal)))) := by
    rw [T.conjugate_comp h w]
    change interior ((T.affine w) ⁻¹' effectiveDomain (conjugate (innerₗ E)
      (fun y => (h y : EReal)))) = _
    rw [(T.affine w).preimage_interior]
  have hgrad : conjugateGradient (innerₗ E) (fun x => ((h (T.B x) + ⟪w, x⟫ : ℝ) : EReal)) =
      (T.C : E → E) ∘ conjugateGradient (innerₗ E) (fun y => (h y : EReal)) ∘ T.affine w :=
    funext (T.conjugateGradient_comp h w)
  have hrestrict : Measure.map (T.affine w) ((volume : Measure E).restrict
      (T.affine w ⁻¹' interior (effectiveDomain (conjugate (innerₗ E)
        (fun y => (h y : EReal)))))) =
      (volume : Measure E).restrict (interior (effectiveDomain (conjugate (innerₗ E)
        (fun y => (h y : EReal))))) := by
    rw [← Measure.restrict_map (T.affine w).continuous.measurable isOpen_interior.measurableSet,
      T.measurePreserving_affine w]
  rw [alexandrovMeasure, alexandrovMeasure, hdom, hgrad, Measure.map_smul,
    ← Measure.map_map hC ((measurable_conjugateGradient _ _).comp
      (T.affine w).continuous.measurable),
    ← Measure.map_map (measurable_conjugateGradient _ _) (T.affine w).continuous.measurable,
    hrestrict]

end UnimodularChange

end SGPT.Toric
