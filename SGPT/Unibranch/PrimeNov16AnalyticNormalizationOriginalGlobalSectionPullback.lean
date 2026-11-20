import SGPT.Unibranch.HironakaG11BlowupLocality

/-! Actual full global section ring pullback, genuine stalk compatibility, and original open-top dictionary.
Blueprint: prime-nov16-analytic-normalization-original-global-section-pullback.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback

def pullTopRingHom {A X : LocallyRingedSpace} (F : A ⟶ X) :
    (X.presheaf.obj (op ⊤)).carrier →+* (A.presheaf.obj (op ⊤)).carrier :=
  (A.presheaf.map (homOfLE (show (⊤ : Opens A.toTopCat) ≤ (Opens.map F.base).obj ⊤ from
    fun _ _ => trivial)).op).hom.comp (F.c.app (op ⊤)).hom

theorem pullTop_germ {A X : LocallyRingedSpace} (F : A ⟶ X)
    (s : (X.presheaf.obj (op ⊤)).carrier) (p : A) :
    A.presheaf.germ ⊤ p (by trivial) (pullTopRingHom F s)=
      F.stalkMap p (X.presheaf.germ ⊤ (F.base p) (by trivial) s) := by
  unfold pullTopRingHom
  exact (A.presheaf.germ_res_apply
    (homOfLE (show (⊤ : Opens A.toTopCat) ≤ (Opens.map F.base).obj ⊤ from fun _ _ => trivial))
    p (by trivial) (F.c.app (op ⊤) s)).trans
      (LocallyRingedSpace.stalkMap_germ_apply F ⊤ p (by trivial) s).symm

theorem pullTop_cleared_relation {A X : LocallyRingedSpace} (F : A ⟶ X)
    (k : ℕ) (c : Fin k → (X.presheaf.obj (op ⊤)).carrier)
    (g h : (X.presheaf.obj (op ⊤)).carrier)
    (heq : g^k+∑ i : Fin k,c i*h^(k-i.val)*g^i.val=0) :
    (pullTopRingHom F g)^k+∑ i : Fin k,
      pullTopRingHom F (c i)*(pullTopRingHom F h)^(k-i.val)*(pullTopRingHom F g)^i.val=0 := by
  have he := congrArg (pullTopRingHom F) heq
  simpa only [map_add,map_pow,map_sum,map_mul,map_zero] using he

private theorem image_top (A : LocallyRingedSpace) (U : Opens A.toTopCat) :
    U.isOpenEmbedding.functor.obj ⊤=U := by
  ext p
  constructor
  · rintro ⟨u,_hu,rfl⟩
    exact u.property
  · intro hp
    exact ⟨⟨p,hp⟩,trivial,rfl⟩

def openTopEquiv (A : LocallyRingedSpace) (U : Opens A.toTopCat) :
    ((A.restrict U.isOpenEmbedding).presheaf.obj (op ⊤)).carrier ≃+*
      (A.presheaf.obj (op U)).carrier :=
  (A.presheaf.mapIso (eqToIso (congrArg op (image_top A U)))).commRingCatIsoToRingEquiv

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
