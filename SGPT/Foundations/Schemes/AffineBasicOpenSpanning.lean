import SGPT.Foundations.Schemes.AffineOpenSectionDenominators

universe u
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal restrictions of an actual affine spanning family span every
genuine basic open over its original ring of regular functions. -/
theorem affineBasicOpen_restricted_sections_span {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    {I : Type*} (v : I → Γ(M, U))
    (hv : Submodule.span Γ(X, U) (Set.range v) = ⊤) (f : Γ(X, U)) :
    Submodule.span Γ(X, X.basicOpen f)
      (Set.range (fun i ↦ M.val.map (homOfLE (X.basicOpen_le f)).op (v i))) = ⊤ := by
  let D := X.basicOpen f
  let hDU : D ≤ U := X.basicOpen_le f
  let S : Submodule Γ(X, D) Γ(M, D) :=
    Submodule.span Γ(X, D) (Set.range (fun i ↦ M.val.map (homOfLE hDU).op (v i)))
  have hres (a : Γ(M, U)) : M.val.map (homOfLE hDU).op a ∈ S := by
    have ha : a ∈ Submodule.span Γ(X, U) (Set.range v) := by rw [hv]; trivial
    refine Submodule.span_induction (p := fun x _ ↦ M.val.map (homOfLE hDU).op x ∈ S)
      ?_ ?_ ?_ ?_ ha
    · rintro x ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i, rfl⟩
    · simpa only [map_zero] using S.zero_mem
    · intro x y hx hy ihx ihy
      simpa only [map_add] using S.add_mem ihx ihy
    · intro r x hx ih
      rw [(M.val.map (homOfLE hDU).op).hom.map_smul]
      exact S.smul_mem _ ih
  apply top_unique
  intro z _
  obtain ⟨n, a, ha⟩ := affineOpenSection_clearDenominator M hU f z
  change M.val.map (homOfLE hDU).op a = (X.presheaf.map (homOfLE hDU).op f) ^ n • z at ha
  have hu : IsUnit (X.presheaf.map (homOfLE hDU).op f) :=
    X.toRingedSpace.isUnit_res_basicOpen f
  obtain ⟨w, hw⟩ := hu
  have hz := S.smul_mem ((↑(w⁻¹) : Γ(X, D)) ^ n) (hres a)
  rw [ha, ← hw, smul_smul] at hz
  have hc : (↑(w⁻¹) : Γ(X, D)) ^ n * (↑w : Γ(X, D)) ^ n = 1 := by
    rw [← mul_pow]
    simp
  simpa only [hc, one_smul] using hz

end
end SGPT.Foundations.Schemes
