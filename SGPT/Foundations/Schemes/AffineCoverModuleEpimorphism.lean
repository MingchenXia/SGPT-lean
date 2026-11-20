import SGPT.Foundations.Schemes.AffineOpenSectionDenominators
import Mathlib.Topology.Sheaves.LocallySurjective

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Surjectivity on a genuine affine cover gives EXACT local lifts of all
target sections. Arbitrary all-open section surjectivity is not assumed. -/
theorem moduleHom_local_lifts_of_affine_cover {X : Scheme.{u}}
    {M N : X.Modules} [N.IsQuasicoherent] (α : M ⟶ N)
    {I : Type u} (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hsurj : ∀ i, Function.Surjective (α.val.app (.op (U i)))) :
    ∀ (V : X.Opens) (t : Γ(N, V)) (x : X), x ∈ V →
      ∃ (W : X.Opens) (hWV : W ≤ V), x ∈ W ∧
        ∃ s : Γ(M, W), α.val.app (.op W) s = N.val.map (homOfLE hWV).op t := by
  intro V t x hx
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨f, hfV, hxf⟩ := (hU i).exists_basicOpen_le (show V from ⟨x, hx⟩) hxi
  let D := X.basicOpen f
  let hDU : D ≤ U i := X.basicOpen_le f
  let tD : Γ(N, D) := N.val.map (homOfLE hfV).op t
  obtain ⟨n, a, ha⟩ := affineOpenSection_clearDenominator N (hU i) f tD
  obtain ⟨b, hb⟩ := hsurj i a
  have hn := PresheafOfModules.naturality_apply α.val (homOfLE hDU).op b
  change α.val.app (.op D) (M.val.map (homOfLE hDU).op b) =
    N.val.map (homOfLE hDU).op (α.val.app (.op (U i)) b) at hn
  rw [hb] at hn
  change N.val.map (homOfLE hDU).op a =
    (X.presheaf.map (homOfLE hDU).op f) ^ n • tD at ha
  have hu : IsUnit (X.presheaf.map (homOfLE hDU).op f) :=
    X.toRingedSpace.isUnit_res_basicOpen f
  obtain ⟨v, hv⟩ := hu
  refine ⟨D, hfV, hxf, (↑(v⁻¹) : Γ(X, D)) ^ n • M.val.map (homOfLE hDU).op b, ?_⟩
  change α.val.app (.op D) ((↑(v⁻¹) : Γ(X, D)) ^ n • M.val.map (homOfLE hDU).op b) = tD
  rw [map_smul, hn, ha, ← hv, smul_smul]
  have hc : (↑(v⁻¹) : Γ(X, D)) ^ n * (↑v : Γ(X, D)) ^ n = 1 := by
    rw [← mul_pow]
    simp
  rw [hc, one_smul]

/-- Genuine affine-cover component surjectivity PRODUCES an epimorphism
of the ORIGINAL module sheaves through actual local lifts. -/
theorem moduleHom_epi_of_affine_cover {X : Scheme.{u}}
    {M N : X.Modules} [N.IsQuasicoherent] (α : M ⟶ N)
    {I : Type u} (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hsurj : ∀ i, Function.Surjective (α.val.app (.op (U i)))) : Epi α := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hl : TopCat.Presheaf.IsLocallySurjective (F.map α).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro V t x hx
    obtain ⟨W, hWV, hxW, s, hs⟩ :=
      moduleHom_local_lifts_of_affine_cover α U hU hcover hsurj V t x hx
    exact ⟨W, hWV, ⟨s, hs⟩, hxW⟩
  let : CategoryTheory.Sheaf.IsLocallySurjective (F.map α) := hl
  have he : Epi (F.map α) := inferInstance
  exact F.epi_of_epi_map he

end
end SGPT.Foundations.Schemes
