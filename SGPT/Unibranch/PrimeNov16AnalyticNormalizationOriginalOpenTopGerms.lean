import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback

/-! Full actual original open-top section and entire stalk compatibility.
Blueprint: prime-nov16-analytic-normalization-original-open-top-germs.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenTopGerms
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback

private theorem image_top (A : LocallyRingedSpace) (U : Opens A.toTopCat) :
    U.isOpenEmbedding.functor.obj ⊤=U := by
  ext p
  constructor
  · rintro ⟨u,_hu,rfl⟩
    exact u.property
  · intro hp
    exact ⟨⟨p,hp⟩,trivial,rfl⟩

private theorem transported_germ (A : LocallyRingedSpace) (U V : Opens A.toTopCat)
    (h : U=V) (p : A) (hp : p ∈ U) (s : (A.presheaf.obj (op U)).carrier) :
    A.presheaf.germ V p (h ▸ hp) ((A.presheaf.mapIso (eqToIso (congrArg op h))).hom s)=
      A.presheaf.germ U p hp s := by
  subst V
  simp

theorem openTopEquiv_germ (A : LocallyRingedSpace) (U : Opens A.toTopCat)
    (s : ((A.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)).carrier) (p : U) :
    A.presheaf.germ U p.val p.property (openTopEquiv A U s)=
      (A.restrictStalkIso U.isOpenEmbedding p).hom
        ((A.restrict U.isOpenEmbedding).presheaf.germ ⊤ p (by trivial) s) := by
  rw [A.restrictStalkIso_hom_eq_germ_apply U.isOpenEmbedding ⊤ p (by trivial) s]
  exact transported_germ A (U.isOpenEmbedding.functor.obj ⊤) U (image_top A U)
    p.val ⟨p,trivial,rfl⟩ s

theorem openTopEquiv_germ_ne_zero_iff (A : LocallyRingedSpace) (U : Opens A.toTopCat)
    (s : ((A.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)).carrier) (p : U) :
    A.presheaf.germ U p.val p.property (openTopEquiv A U s) ≠ 0 ↔
      (A.restrict U.isOpenEmbedding).presheaf.germ ⊤ p (by trivial) s ≠ 0 := by
  rw [openTopEquiv_germ]
  let E := (A.restrictStalkIso U.isOpenEmbedding p).commRingCatIsoToRingEquiv
  exact not_congr (map_eq_zero_iff E E.injective)

theorem normal_original_stalk_of_normal_restriction (A : LocallyRingedSpace) (U : Opens A.toTopCat)
    (hn : ∀ p : U,IsDomain ((A.restrict U.isOpenEmbedding).presheaf.stalk p).carrier ∧
      IsIntegrallyClosed ((A.restrict U.isOpenEmbedding).presheaf.stalk p).carrier)
    (p : U) : IsDomain (A.presheaf.stalk p.val).carrier ∧ IsIntegrallyClosed (A.presheaf.stalk p.val).carrier := by
  obtain ⟨hd,hc⟩ := hn p
  let := hd
  let := hc
  let E := (A.restrictStalkIso U.isOpenEmbedding p).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain E.symm E.symm.injective,IsIntegrallyClosed.of_equiv E⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenTopGerms
