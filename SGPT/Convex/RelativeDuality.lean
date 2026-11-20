import SGPT.Convex.Legendre
import SGPT.Convex.IntrinsicSegment

/-!
# Legendre conjugation on the actual intrinsic-interior domain

This completes the second equality in Appendix A `def:Legendregeneral`.
Actual epigraph density handles every convex obstacle, including improper
functions and empty effective domains; no continuity of the obstacle is assumed.
-/

namespace SGPT.Convex

open Set

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The actual Legendre supremum restricted to a specified subset. -/
noncomputable def conjugateOn (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal)
    (D : Set V) (y : W) : EReal := ⨆ (x : V) (_ : x ∈ D), (B x y : EReal) - f x

/-- Restricting the supremum cannot raise the conjugate. -/
theorem conjugateOn_le (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal) (D : Set V) :
    conjugateOn B f D ≤ conjugate B f := by
  intro y
  exact iSup_le fun x ↦ iSup_le fun _ ↦ le_iSup (fun z ↦ (B z y : EReal) - f z) x

/-- Finite bounds on the restricted supremum are actual affine minorant
inequalities at every point of the specified subset. -/
theorem conjugateOn_le_coe_iff (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal)
    (D : Set V) (y : W) (c : ℝ) :
    conjugateOn B f D y ≤ (c : EReal) ↔ ∀ x ∈ D, ((B x y - c : ℝ) : EReal) ≤ f x := by
  simp only [conjugateOn, iSup_le_iff]
  apply forall_congr'
  intro x
  apply forall_congr'
  intro _
  simpa only [EReal.coe_sub] using real_sub_le_iff_comm (B x y) (f x) (c : EReal)

section FiniteDimension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The full Legendre supremum equals its restriction to the actual intrinsic
interior of the effective domain, for every convex extended-real obstacle. -/
theorem conjugate_intrinsicInterior (B : E →ₗ[ℝ] W →ₗ[ℝ] ℝ)
    {f : E → EReal} (hf : IsConvex f) :
    conjugateOn B f (intrinsicInterior ℝ (effectiveDomain f)) = conjugate B f := by
  funext y
  have hbound (c : ℝ)
      (hc : conjugateOn B f (intrinsicInterior ℝ (effectiveDomain f)) y ≤ (c : EReal)) :
      conjugate B f y ≤ (c : EReal) := by
    have hminor := (conjugateOn_le_coe_iff B f _ y c).mp hc
    have hclosed : IsClosed (epigraph (fun x ↦ ((B x y - c : ℝ) : EReal))) := by
      simpa only [LinearMap.flip_apply, EReal.coe_sub] using
        isClosed_epigraph_linear_sub (B.flip y) (c : EReal)
    have hrestricted : restrictedEpigraph f ⊆ epigraph (fun x ↦ ((B x y - c : ℝ) : EReal)) := by
      intro p hp
      exact (hminor p.1 hp.2).trans hp.1
    have hfull : epigraph f ⊆ epigraph (fun x ↦ ((B x y - c : ℝ) : EReal)) :=
      (epigraph_subset_closure_restrictedEpigraph hf).trans (closure_minimal hrestricted hclosed)
    exact (conjugate_le_coe_iff B f y c).mpr (le_iff_epigraph_subset.mpr hfull)
  apply le_antisymm (conjugateOn_le B f _ y)
  cases hs : conjugateOn B f (intrinsicInterior ℝ (effectiveDomain f)) y using EReal.rec with
  | bot =>
    apply le_bot_iff.mpr
    apply (EReal.eq_bot_iff_forall_lt _).mpr
    intro c
    exact (hbound (c - 1) (by rw [hs]; exact bot_le)).trans_lt
      (EReal.coe_lt_coe (by linarith : c - 1 < c))
  | coe c => exact hbound c (le_of_eq hs)
  | top => exact le_top

end FiniteDimension

end SGPT.Convex
