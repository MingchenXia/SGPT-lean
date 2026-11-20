import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback

/-! Actual full global ring pullback functoriality and true open-immersion nonzero-germ transport.
Blueprint: prime-nov16-analytic-normalization-original-global-section-functor.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionFunctor
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback

theorem pullTop_comp {A B C : LocallyRingedSpace} (F : A ⟶ B) (G : B ⟶ C)
    (s : (C.presheaf.obj (op ⊤)).carrier) :
    pullTopRingHom (F ≫ G) s=pullTopRingHom F (pullTopRingHom G s) := by
  apply TopCat.Presheaf.section_ext A.toSheafedSpace.sheaf ⊤
  intro x _hx
  change A.presheaf.germ ⊤ x (by trivial) (pullTopRingHom (F ≫ G) s)=
    A.presheaf.germ ⊤ x (by trivial) (pullTopRingHom F (pullTopRingHom G s))
  calc
    _=(F ≫ G).stalkMap x (C.presheaf.germ ⊤ ((F ≫ G).base x) (by trivial) s) := pullTop_germ _ _ _
    _=F.stalkMap x (G.stalkMap (F.base x) (C.presheaf.germ ⊤ (G.base (F.base x)) (by trivial) s)) := by
      rw [LocallyRingedSpace.stalkMap_comp]
      rfl
    _=F.stalkMap x (B.presheaf.germ ⊤ (F.base x) (by trivial) (pullTopRingHom G s)) :=
      congrArg (F.stalkMap x) (pullTop_germ G s (F.base x)).symm
    _= _ := (pullTop_germ F (pullTopRingHom G s) x).symm

theorem pullTop_id (A : LocallyRingedSpace) (s : (A.presheaf.obj (op ⊤)).carrier) :
    pullTopRingHom (𝟙 A) s=s := by
  apply TopCat.Presheaf.section_ext A.toSheafedSpace.sheaf ⊤
  intro x _hx
  change A.presheaf.germ ⊤ x (by trivial) (pullTopRingHom (𝟙 A) s)=A.presheaf.germ ⊤ x (by trivial) s
  exact (pullTop_germ (𝟙 A) s x).trans (by simp)

theorem pullTop_nonzero_of_openImmersion {A B : LocallyRingedSpace} (F : A ⟶ B)
    [LocallyRingedSpace.IsOpenImmersion F] (s : (B.presheaf.obj (op ⊤)).carrier)
    (hs : ∀ b : B,B.presheaf.germ ⊤ b (by trivial) s ≠ 0) (a : A) :
    A.presheaf.germ ⊤ a (by trivial) (pullTopRingHom F s) ≠ 0 := by
  rw [pullTop_germ]
  let E := (asIso (F.stalkMap a)).commRingCatIsoToRingEquiv
  intro hz
  apply hs (F.base a)
  apply E.injective
  rw [map_zero]
  exact hz

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionFunctor
