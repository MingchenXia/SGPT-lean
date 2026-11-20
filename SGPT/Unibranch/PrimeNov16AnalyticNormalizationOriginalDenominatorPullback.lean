import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback
import SGPT.Unibranch.HironakaG10ChowNativeIsoCriterion

/-! Every genuine target denominator germ remains nonzero in EVERY original source stalk.
Blueprint: prime-nov16-analytic-normalization-original-denominator-pullback.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDenominatorPullback
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalGlobalSectionPullback

theorem original_pullback_nonzero_every_stalk {Y X : SourceReducedComplexSpace}
    (f : Y ⟶ X) (G : Set X.obj.left) (hIso : IsIsoOver f G)
    (hDense : Dense (f.hom.left.base ⁻¹' G))
    (h : (X.obj.left.presheaf.obj (op ⊤)).carrier)
    (ht : ∀ x : X.obj.left,X.obj.left.presheaf.germ ⊤ x (by trivial) h ≠ 0) :
    ∀ p : Y.obj.left,Y.obj.left.presheaf.germ ⊤ p (by trivial)
      (pullTopRingHom f.hom.left h) ≠ 0 := by
  intro p hp
  let F := Y.obj.left.presheaf
  let a := pullTopRingHom f.hom.left h
  have hp' : F.germ ⊤ p (by trivial) a=F.germ ⊤ p (by trivial) 0 := by
    rw [map_zero]
    exact hp
  obtain ⟨V,hpV,iV,_jV,hres⟩ := F.germ_eq p (by trivial) (by trivial) a 0 hp'
  have hres0 : F.map iV.op a=0 := by simpa only [map_zero] using hres
  obtain ⟨q,hqV,hqG⟩ := mem_closure_iff.mp (hDense p) V V.isOpen hpV
  have haq : F.germ ⊤ q (by trivial) a=0 := by
    have he := F.germ_res_apply iV q hqV a
    rw [hres0,map_zero] at he
    exact he.symm
  let : IsIso (f.hom.left.stalkMap q) :=
    HironakaG10ChowNativeIsoCriterion.isIso_stalkMap_of_isIsoOver hIso q hqG
  let E := (asIso (f.hom.left.stalkMap q)).commRingCatIsoToRingEquiv
  apply ht (f.hom.left.base q)
  apply E.injective
  rw [map_zero]
  change f.hom.left.stalkMap q (X.obj.left.presheaf.germ ⊤ (f.hom.left.base q) (by trivial) h)=0
  rw [← pullTop_germ]
  exact haq

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDenominatorPullback
