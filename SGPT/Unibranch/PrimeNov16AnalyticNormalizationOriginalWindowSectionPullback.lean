import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionFunctor
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenTopGerms

/-! Genuine full original window section pullback, whole germ square, and functor laws.
Blueprint: prime-nov16-analytic-normalization-original-window-section-pullback.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalWindowSectionPullback
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionFunctor
open PrimeNov16AnalyticNormalizationOriginalOpenTopGerms

def pullWindowRingHom {A B : LocallyRingedSpace} {W : Opens A.toTopCat} {U : Opens B.toTopCat}
    (f : A.restrict W.isOpenEmbedding ⟶ B.restrict U.isOpenEmbedding) :
    (B.presheaf.obj (op U)).carrier →+* (A.presheaf.obj (op W)).carrier :=
  (openTopEquiv A W).toRingHom.comp
    ((pullTopRingHom f).comp (openTopEquiv B U).symm.toRingHom)

theorem pullWindow_germ {A B : LocallyRingedSpace} {W : Opens A.toTopCat} {U : Opens B.toTopCat}
    (f : A.restrict W.isOpenEmbedding ⟶ B.restrict U.isOpenEmbedding)
    (s : (B.presheaf.obj (op U)).carrier) (p : W) :
    A.presheaf.germ W p.val p.property (pullWindowRingHom f s)=
      (A.restrictStalkIso W.isOpenEmbedding p).hom
        (f.stalkMap p ((B.restrictStalkIso U.isOpenEmbedding (f.base p)).inv
          (B.presheaf.germ U (f.base p).val (f.base p).property s))) := by
  apply (openTopEquiv_germ A W _ p).trans
  apply congrArg (A.restrictStalkIso W.isOpenEmbedding p).hom
  apply (pullTop_germ f ((openTopEquiv B U).symm s) p).trans
  apply congrArg (f.stalkMap p)
  let E := (B.restrictStalkIso U.isOpenEmbedding (f.base p)).commRingCatIsoToRingEquiv
  have he : B.presheaf.germ U (f.base p).val (f.base p).property s=
      E ((B.restrict U.isOpenEmbedding).presheaf.germ ⊤ (f.base p) (by trivial)
        ((openTopEquiv B U).symm s)) := by
    have ht := openTopEquiv_germ B U ((openTopEquiv B U).symm s) (f.base p)
    simp only [RingEquiv.apply_symm_apply] at ht
    exact ht
  have hi := congrArg E.symm he
  simp only [RingEquiv.symm_apply_apply] at hi
  exact hi.symm

theorem pullWindow_comp {A B C : LocallyRingedSpace}
    {W : Opens A.toTopCat} {U : Opens B.toTopCat} {V : Opens C.toTopCat}
    (f : A.restrict W.isOpenEmbedding ⟶ B.restrict U.isOpenEmbedding)
    (g : B.restrict U.isOpenEmbedding ⟶ C.restrict V.isOpenEmbedding) :
    pullWindowRingHom (f ≫ g)=(pullWindowRingHom f).comp (pullWindowRingHom g) := by
  apply RingHom.ext
  intro s
  change openTopEquiv A W (pullTopRingHom (f ≫ g) ((openTopEquiv C V).symm s))=
    openTopEquiv A W (pullTopRingHom f ((openTopEquiv B U).symm
      (openTopEquiv B U (pullTopRingHom g ((openTopEquiv C V).symm s)))))
  rw [RingEquiv.symm_apply_apply,pullTop_comp]

theorem pullWindow_id (A : LocallyRingedSpace) (W : Opens A.toTopCat) :
    pullWindowRingHom (𝟙 (A.restrict W.isOpenEmbedding))=RingHom.id (A.presheaf.obj (op W)).carrier := by
  apply RingHom.ext
  intro s
  change openTopEquiv A W (pullTopRingHom (𝟙 _) ((openTopEquiv A W).symm s))=s
  rw [pullTop_id,RingEquiv.apply_symm_apply]

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalWindowSectionPullback
