import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodIsomorphismCriterion
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFiniteBranchDescent

/-! Actual finite original coproduct inverse manufactured from true component inverses.
Blueprint: prime-nov16-analytic-normalization-original-coproduct-good-inverse.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCoproductGoodInverse
open SourceReducedComplexSpace
open HironakaG1NativeDisjointCoproduct
open HironakaG10ChowNativeIsoCriterion
open PrimeNov16AnalyticNormalizationOriginalFiniteBranchDescent
open PrimeNov16AnalyticNormalizationOriginalGoodIsomorphismCriterion

theorem coproduct_isIsoOver_actual_good {k : ℕ} (Y : Fin k → SourceReducedComplexSpace)
    {X : SourceReducedComplexSpace} (F : ∀ i,Y i ⟶ X)
    (hp : ∀ i,IsProperMap (F i).hom.left.base)
    (G : Opens X.obj.left) [ParacompactSpace G] (V : Fin k → Opens X.obj.left)
    (hcover : ∀ x : X.obj.left,x ∈ G → ∃ i,x ∈ V i)
    (hdisj : Pairwise (fun i j => Disjoint (V i : Set X.obj.left) (V j : Set X.obj.left)))
    (hgood : ∀ i,∀ p : (Y i).obj.left,(F i).hom.left.base p ∈ G → (F i).hom.left.base p ∈ V i)
    (hIso : ∀ i,IsIsoOver (F i) (V i)) : IsIsoOver (desc Y F) G := by
  let f := desc Y F
  have hpt (i : Fin k) (p : (Y i).obj.left) :
      f.hom.left.base ((inclusion Y i).hom.left.base p)=(F i).hom.left.base p :=
    congrArg (fun m : Y i ⟶ X => m.hom.left.base p) (inclusion_desc Y F i)
  apply isIsoOver_of_proper_bijOn_stalk f (desc_proper Y F hp) G
  · refine ⟨fun p hp => hp,?_,?_⟩
    · intro p hp q hq hpq
      obtain ⟨i,a,rfl⟩ := inclusion_jointly_surjective Y p
      obtain ⟨j,b,rfl⟩ := inclusion_jointly_surjective Y q
      have haG : (F i).hom.left.base a ∈ G := (hpt i a) ▸ hp
      have hbG : (F j).hom.left.base b ∈ G := (hpt j b) ▸ hq
      have hab : (F i).hom.left.base a=(F j).hom.left.base b :=
        (hpt i a).symm.trans (hpq.trans (hpt j b))
      have hij : i=j := by
        by_contra hij
        exact disjoint_left.mp (hdisj hij) (hgood i a haG) (hab.symm ▸ hgood j b hbG)
      subst j
      have he : a=b := injOn_of_isIsoOver (hIso i) (hgood i a haG) (hgood i b hbG) hab
      exact congrArg (inclusion Y i).hom.left.base he
    · intro x hx
      obtain ⟨i,hi⟩ := hcover x hx
      obtain ⟨p,hp⟩ := subset_range_of_isIsoOver (hIso i) hi
      refine ⟨(inclusion Y i).hom.left.base p,?_,(hpt i p).trans hp⟩
      change f.hom.left.base ((inclusion Y i).hom.left.base p) ∈ G
      exact ((hpt i p).trans hp).symm ▸ hx
  · intro p hp
    obtain ⟨i,a,rfl⟩ := inclusion_jointly_surjective Y p
    have haG : (F i).hom.left.base a ∈ G := (hpt i a) ▸ hp
    have hi : IsIso ((F i).hom.left.stalkMap a) :=
      isIso_stalkMap_of_isIsoOver (hIso i) a (hgood i a haG)
    have hc : IsIso (((inclusion Y i) ≫ f).hom.left.stalkMap a) :=
      (inclusion_desc Y F i).symm ▸ hi
    change IsIso (((inclusion Y i).hom.left ≫ f.hom.left).stalkMap a) at hc
    rw [LocallyRingedSpace.stalkMap_comp] at hc
    let := hc
    let : LocallyRingedSpace.IsOpenImmersion (inclusion Y i).hom.left := inclusion_isOpenImmersion Y i
    exact IsIso.of_isIso_comp_right _ ((inclusion Y i).hom.left.stalkMap a)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCoproductGoodInverse
