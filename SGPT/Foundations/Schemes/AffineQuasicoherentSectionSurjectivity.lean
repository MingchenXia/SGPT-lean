import SGPT.Foundations.Schemes.AffineOpenSectionDenominators
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! Genuine quasicoherent epimorphisms give surjective ORIGINAL section maps
on actual affine opens, without choosing line frames or changing scalars. -/

universe u
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual spectrum section component of a quasicoherent epimorphism is
surjective. The native tilde counit identifies the ORIGINAL map. -/
theorem moduleSpecSections_surjective_of_epi {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (α : M ⟶ N) [Epi α] :
    Function.Surjective (α.val.app (.op ⊤)) := by
  let G := moduleSpecΓFunctor (R := R)
  let T := tilde.functor R
  have hn : T.map (G.map α) ≫ N.fromTildeΓ = M.fromTildeΓ ≫ α :=
    Scheme.Modules.fromTildeΓNatTrans.naturality α
  have he : T.map (G.map α) =
      M.fromTildeΓ ≫ α ≫ inv N.fromTildeΓ := by
    apply (cancel_mono N.fromTildeΓ).1
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hn
  have ht : Epi (T.map (G.map α)) := by
    rw [he]
    infer_instance
  have hg : Epi (G.map α) := T.epi_of_epi_map ht
  exact (ModuleCat.epi_iff_surjective (G.map α)).mp hg

/-- Original section maps of genuine quasicoherent epimorphisms are
surjective on every actual affine open, with no frame chosen there. -/
theorem affineOpenSections_surjective_of_epi {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (α : M ⟶ N) [Epi α] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (α.val.app (.op U)) := by
  let c := hU.fromSpec
  let hi : c ''ᵁ ⊤ = U :=
    c.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  let α' := (Scheme.Modules.restrictFunctor c).map α
  let eM : Γ(M.restrict c, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso c ⊤ ≪≫ M.presheaf.mapIso (eqToIso hi.symm).op
  let eN : Γ(N.restrict c, ⊤) ≅ Γ(N, U) :=
    N.restrictAppIso c ⊤ ≪≫ N.presheaf.mapIso (eqToIso hi.symm).op
  have hn (x : Γ(M.restrict c, ⊤)) :
      α.val.app (.op U) (eM.hom x) = eN.hom (α'.val.app (.op ⊤) x) := by
    exact PresheafOfModules.naturality_apply α.val (eqToHom hi.symm).op x
  intro y
  obtain ⟨x, hx⟩ := moduleSpecSections_surjective_of_epi α' (eN.inv y)
  refine ⟨eM.hom x, ?_⟩
  rw [hn, hx, Iso.inv_hom_id_apply]

end
end SGPT.Foundations.Schemes
