import SGPT.Foundations.Schemes.AffineRegularRestriction

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual unit ideal is the genuine empty effective Cartier divisor. -/
theorem IsEffectiveCartierIdeal.one (X : Scheme.{u}) :
    IsEffectiveCartierIdeal (1 : X.IdealSheafData) := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  refine ⟨⟨U, hU⟩, hxU, 1, (nonZeroDivisors Γ(X, U)).one_mem, ?_⟩
  simp

/-- Common ACTUAL affine refinement and genuine restriction of regularity
produce effective Cartier multiplication without a domain/CM/reduced premise. -/
theorem IsEffectiveCartierIdeal.mul {X : Scheme.{u}} {I J : X.IdealSheafData}
    (hI : IsEffectiveCartierIdeal I) (hJ : IsEffectiveCartierIdeal J) :
    IsEffectiveCartierIdeal (I * J) := by
  intro x
  obtain ⟨U, hxU, r, hr, hIr⟩ := hI x
  obtain ⟨V, hxV, s, hs, hJs⟩ := hJ x
  obtain ⟨W, hW, hxW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U.val ⊓ V.val from ⟨hxU, hxV⟩)
  let Z : X.affineOpens := ⟨W, hW⟩
  have hZU : Z ≤ U := fun y hy ↦ (hWUV hy).1
  have hZV : Z ≤ V := fun y hy ↦ (hWUV hy).2
  let rZ : Γ(X, Z) := X.presheaf.map (homOfLE hZU).op r
  let sZ : Γ(X, Z) := X.presheaf.map (homOfLE hZV).op s
  have hrZ : rZ ∈ nonZeroDivisors Γ(X, Z) :=
    affineOpen_nonZeroDivisors_restrict U.property hZU r hr
  have hsZ : sZ ∈ nonZeroDivisors Γ(X, Z) :=
    affineOpen_nonZeroDivisors_restrict V.property hZV s hs
  have hIZ : I.ideal Z = Ideal.span {rZ} := by
    rw [← I.map_ideal hZU, hIr, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl
  have hJZ : J.ideal Z = Ideal.span {sZ} := by
    rw [← J.map_ideal hZV, hJs, Ideal.map_span]
    simp only [Set.image_singleton]
    rfl
  refine ⟨Z, hxW, rZ * sZ, (nonZeroDivisors Γ(X, Z)).mul_mem hrZ hsZ, ?_⟩
  change I.ideal Z * J.ideal Z = _
  rw [hIZ, hJZ, Ideal.span_singleton_mul_span_singleton]

/-- Genuine actual ideal powers retain Cartier multiplicities, including the
unit in degree zero; no radical or reduced-support replacement is used. -/
theorem IsEffectiveCartierIdeal.pow {X : Scheme.{u}} {I : X.IdealSheafData}
    (hI : IsEffectiveCartierIdeal I) (m : ℕ) : IsEffectiveCartierIdeal (I ^ m) := by
  induction m with
  | zero => simpa only [pow_zero] using IsEffectiveCartierIdeal.one X
  | succ m ih => simpa only [pow_succ] using ih.mul hI

end
end SGPT.Foundations.Schemes
