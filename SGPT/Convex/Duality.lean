import SGPT.Convex.Epigraph
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Support functions and the Legendre transform

The full-domain formula in SGPT Appendix A, `def:Legendregeneral`, is used.
A bilinear pairing includes the source's pairing with the real dual vector space.
Convexity and indicator conjugation are proved independently of finite dimension.
Closedness is proved for finite-dimensional topological real vector spaces.
Properness preservation and biconjugation in `thm:Legendredual` remain separate obligations.
-/

namespace SGPT.Convex

open Set

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The support function of a set, with the empty support equal to `-∞`. -/
noncomputable def support (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (P : Set V) : W → EReal :=
  fun y ↦ ⨆ x : P, (B x y : EReal)

/-- The full-domain Legendre transform with respect to a bilinear pairing. -/
noncomputable def conjugate (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal) : W → EReal :=
  fun y ↦ ⨆ x, (B x y : EReal) - f x

/-- Affine summands remain convex even when the subtracted constant is infinite. -/
theorem isConvex_linear_sub (l : W →ₗ[ℝ] ℝ) (c : EReal) :
    IsConvex (fun y ↦ (l y : EReal) - c) := by
  induction c using EReal.rec with
  | bot => simp
  | coe c => simpa [← EReal.coe_sub, sub_eq_add_neg] using isConvex_affine l (-c)
  | top => simp

/-- Convexity of a support function does not require the defining set to be convex. -/
theorem isConvex_support (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (P : Set V) :
    IsConvex (support B P) :=
  isConvex_iSup fun x ↦ isConvex_linear (B x)

/-- Convexity clause of Appendix A's Legendre theorem, for arbitrary functions. -/
theorem isConvex_conjugate (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal) :
    IsConvex (conjugate B f) :=
  isConvex_iSup fun x ↦ isConvex_linear_sub (B x) (f x)

/-- The conjugate reverses pointwise order, including at infinite values. -/
theorem conjugate_antitone (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) {f g : V → EReal}
    (hfg : f ≤ g) : conjugate B g ≤ conjugate B f := by
  intro y
  exact iSup_le fun x ↦ (EReal.sub_le_sub le_rfl (hfg x)).trans
    (le_iSup (fun z ↦ (B z y : EReal) - f z) x)

/-- Exact indicator-to-support equality in `ex:suppfundual`; no separation theorem is needed. -/
theorem conjugate_indicator (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (P : Set V) :
    conjugate B (indicator P) = support B P := by
  classical
  funext y
  apply le_antisymm
  · refine iSup_le fun x ↦ ?_
    by_cases hx : x ∈ P
    · simpa [support, indicator, hx] using
        (le_iSup (fun z : P ↦ (B z y : EReal)) ⟨x, hx⟩)
    · simp [indicator, hx]
  · refine iSup_le fun x ↦ ?_
    simpa [conjugate, indicator, x.property] using
      (le_iSup (fun z ↦ (B z y : EReal) - indicator P z) x.val)

section Closedness

variable [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul ℝ W]
  [T2Space W] [FiniteDimensional ℝ W]

/-- Each affine summand has a closed epigraph, including infinite constants. -/
theorem isClosed_epigraph_linear_sub (l : W →ₗ[ℝ] ℝ) (c : EReal) :
    IsClosed (epigraph (fun y ↦ (l y : EReal) - c)) := by
  induction c using EReal.rec with
  | bot => simp [epigraph]
  | coe c =>
    simp only [epigraph, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    exact isClosed_le
      ((l.continuous_of_finiteDimensional.comp continuous_fst).sub continuous_const)
      continuous_snd
  | top => simp [epigraph]

/-- Closedness clause of the source's Legendre theorem; the obstacle need not be convex. -/
theorem isClosed_epigraph_conjugate (B : V →ₗ[ℝ] W →ₗ[ℝ] ℝ) (f : V → EReal) :
    IsClosed (epigraph (conjugate B f)) := by
  have hepi : epigraph (conjugate B f) =
      ⋂ x, epigraph (fun y ↦ (B x y : EReal) - f x) := by
    ext p
    simp [epigraph, conjugate]
  rw [hepi]
  exact isClosed_iInter fun x ↦ isClosed_epigraph_linear_sub (B x) (f x)

end Closedness

section CanonicalDual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty set has support value zero at the zero functional. -/
theorem support_dual_zero {P : Set E} (hP : P.Nonempty) :
    support (Module.Dual.eval ℝ E) P (0 : Module.Dual ℝ E) = 0 := by
  obtain ⟨z, hz⟩ := hP
  apply le_antisymm
  · exact iSup_le fun _ ↦ by simp
  · simpa [support] using
      (le_iSup (fun p : P ↦ (((0 : Module.Dual ℝ E) p : ℝ) : EReal)) ⟨z, hz⟩)

/-- Source `ex:suppfundual`: the support-to-indicator direction uses the full real dual.
Geometric Hahn–Banach supplies an actual separating functional outside the closed convex set.
Unlike the arbitrary-pairing direction, no nondegeneracy assumption is hidden. -/
theorem conjugate_support_dual {P : Set E} (hconv : Convex ℝ P) (hclosed : IsClosed P) :
    conjugate (Module.Dual.eval ℝ E).flip (support (Module.Dual.eval ℝ E) P) =
      indicator P := by
  classical
  by_cases hP : P = ∅
  · subst P
    funext x
    simp [conjugate, support, indicator]
  have hne : P.Nonempty := Set.nonempty_iff_ne_empty.mpr hP
  funext x
  by_cases hx : x ∈ P
  · simp only [indicator, if_pos hx]
    apply le_antisymm
    · refine iSup_le fun l ↦ ?_
      have hbound : (l x : EReal) ≤ support (Module.Dual.eval ℝ E) P l := by
        exact le_iSup (fun p : P ↦ (l p : EReal)) ⟨x, hx⟩
      have h := EReal.sub_le_sub (le_refl (l x : EReal)) hbound
      simpa only [LinearMap.flip_apply, Module.Dual.eval_apply, ← EReal.coe_sub,
        sub_self, EReal.coe_zero] using h
    · have hz := le_iSup
        (fun l : Module.Dual ℝ E ↦ (l x : EReal) - support (Module.Dual.eval ℝ E) P l) 0
      simpa [support_dual_zero hne, conjugate] using hz
  · simp only [indicator, if_neg hx]
    apply (EReal.eq_top_iff_forall_lt _).mpr
    intro R
    obtain ⟨l, c, hlP, hcx⟩ := geometric_hahn_banach_closed_point hconv hclosed hx
    let δ : ℝ := l x - c
    have hδ : 0 < δ := sub_pos.mpr hcx
    let t : ℝ := (|R| + 1) / δ
    have ht : 0 < t := div_pos (by positivity) hδ
    let lt : Module.Dual ℝ E := t • l.toLinearMap
    have hsupport : support (Module.Dual.eval ℝ E) P lt ≤ ((t * c : ℝ) : EReal) := by
      refine iSup_le fun p ↦ ?_
      exact EReal.coe_le_coe_iff.mpr
        (show lt p ≤ t * c from mul_le_mul_of_nonneg_left (hlP p p.property).le ht.le)
    have hgap : ((t * δ : ℝ) : EReal) ≤
        conjugate (Module.Dual.eval ℝ E).flip (support (Module.Dual.eval ℝ E) P) x := by
      have h := EReal.sub_le_sub (le_refl (lt x : EReal)) hsupport
      have hval : (lt x : EReal) - ((t * c : ℝ) : EReal) = ((t * δ : ℝ) : EReal) := by
        rw [← EReal.coe_sub]
        congr 1
        change t * l x - t * c = t * (l x - c)
        ring
      rw [hval] at h
      exact h.trans (le_iSup
        (fun a : Module.Dual ℝ E ↦ (a x : EReal) - support (Module.Dual.eval ℝ E) P a) lt)
    have hR : R < t * δ := by
      have htδ : t * δ = |R| + 1 := div_mul_cancel₀ _ (ne_of_gt hδ)
      rw [htδ]
      linarith [le_abs_self R]
    exact (EReal.coe_lt_coe_iff.mpr hR).trans_le hgap

end CanonicalDual

end SGPT.Convex
