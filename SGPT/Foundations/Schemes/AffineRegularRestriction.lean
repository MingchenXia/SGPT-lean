import SGPT.Foundations.Schemes.RegularCartierZeroIdeal

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual affine basic-open localization and structure-sheaf separation
preserve SAME-ring regularity on EVERY smaller actual open, not only affines. -/
theorem affineOpen_nonZeroDivisors_restrict {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (hVU : V ≤ U) (r : Γ(X, U))
    (hr : r ∈ nonZeroDivisors Γ(X, U)) :
    X.presheaf.map (homOfLE hVU).op r ∈ nonZeroDivisors Γ(X, V) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro t ht
  apply TopCat.Presheaf.IsSheaf.section_ext X.sheaf.property
  intro x hx
  obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le (⟨x, hx⟩ : V) (hVU hx)
  let W := X.basicOpen f
  let : Algebra Γ(X, U) Γ(X, W) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  let : IsLocalization.Away f Γ(X, W) := hU.isLocalization_basicOpen f
  have hrW : X.presheaf.map (homOfLE (X.basicOpen_le f)).op r ∈
      nonZeroDivisors Γ(X, W) :=
    IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers f) Γ(X, W) hr
  refine ⟨W, hf, hxf, ?_⟩
  rw [map_zero]
  apply (mem_nonZeroDivisors_iff_left.mp hrW)
  have hh := congrArg (X.presheaf.map (homOfLE hf).op) ht
  rw [map_mul, map_zero] at hh
  have hres : X.presheaf.map (homOfLE hf).op (X.presheaf.map (homOfLE hVU).op r) =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op r := by
    simp only [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, ← op_comp]
    rfl
  rw [hres] at hh
  exact hh

end
end SGPT.Foundations.Schemes
