import SGPT.Unibranch.HironakaG1NativeDisjointCoproduct
import SGPT.Unibranch.HironakaG10ChowNativeIsoCriterion

/-! Actual disjoint open covers glue full maps on the SAME original source.
Blueprint: native-nov16-disjoint-source-cover-gluing.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16DisjointSourceCoverGluing
open SourceReducedComplexSpace HironakaG1NativeDisjointCoproduct

theorem coproduct_cover_isIso {ι : Type} (T : ι → SourceReducedComplexSpace)
    {A : SourceReducedComplexSpace} (j : ∀ i,T i ⟶ A)
    (hj : ∀ i,LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ x : A.obj.left,∃ (i : ι) (p : (T i).obj.left),(j i).hom.left.base p=x)
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base)
      (range (j k).hom.left.base))) : IsIso (desc T j) := by
  let J := desc T j
  have hpoint (i : ι) (p : (T i).obj.left) :
      J.hom.left.base ((inclusion T i).hom.left.base p)=(j i).hom.left.base p :=
    congrArg (fun f : T i ⟶ A => f.hom.left.base p) (inclusion_desc T j i)
  have hb : Function.Bijective J.hom.left.base := by
    constructor
    · intro p q hpq
      obtain ⟨i,a,rfl⟩ := inclusion_jointly_surjective T p
      obtain ⟨k,b,rfl⟩ := inclusion_jointly_surjective T q
      have he : (j i).hom.left.base a=(j k).hom.left.base b :=
        (hpoint i a).symm.trans (hpq.trans (hpoint k b))
      have hik : i=k := by
        by_contra hne
        exact disjoint_left.mp (hdisj hne) ⟨a,rfl⟩ ⟨b,he.symm⟩
      subst k
      exact congrArg (inclusion T i).hom.left.base ((hj i).base_open.injective he)
    · intro x
      obtain ⟨i,p,hp⟩ := hcover x
      exact ⟨(inclusion T i).hom.left.base p,(hpoint i p).trans hp⟩
  have hp : IsProperMap J.hom.left.base := by
    have h := desc_isProperMap_of_disjoint_cover T j hj hcover hdisj
      (fun i => 𝟙 (T i)) (fun _ => isProperMap_id)
    simpa only [Category.id_comp] using h
  apply HironakaG10ChowNativeIsoCriterion.isIso_of_isHomeomorph_of_isIso_stalkMap J
    (isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨J.hom.left.base.hom.continuous,hp.isClosedMap,hb⟩)
  intro p
  obtain ⟨i,a,rfl⟩ := inclusion_jointly_surjective T p
  let : LocallyRingedSpace.IsOpenImmersion (j i).hom.left := hj i
  have hi : IsIso ((j i).hom.left.stalkMap a) := inferInstance
  have hc : IsIso (((inclusion T i) ≫ J).hom.left.stalkMap a) :=
    (inclusion_desc T j i).symm ▸ hi
  change IsIso (((inclusion T i).hom.left ≫ J.hom.left).stalkMap a) at hc
  rw [LocallyRingedSpace.stalkMap_comp] at hc
  let := hc
  let : LocallyRingedSpace.IsOpenImmersion (inclusion T i).hom.left :=
    inclusion_isOpenImmersion T i
  exact IsIso.of_isIso_comp_right _ ((inclusion T i).hom.left.stalkMap a)

theorem exists_unique_morphism {ι : Type} (T : ι → SourceReducedComplexSpace)
    {A B : SourceReducedComplexSpace} (j : ∀ i,T i ⟶ A)
    (hj : ∀ i,LocallyRingedSpace.IsOpenImmersion (j i).hom.left)
    (hcover : ∀ x : A.obj.left,∃ (i : ι) (p : (T i).obj.left),(j i).hom.left.base p=x)
    (hdisj : Pairwise (fun i k => Disjoint (range (j i).hom.left.base)
      (range (j k).hom.left.base))) (f : ∀ i,T i ⟶ B) :
    ∃! F : A ⟶ B,∀ i,j i ≫ F=f i := by
  let J := desc T j
  let : IsIso J := coproduct_cover_isIso T j hj hcover hdisj
  refine ⟨inv J ≫ desc T f,?_,?_⟩
  · intro i
    rw [← inclusion_desc T j i,Category.assoc,IsIso.hom_inv_id_assoc,inclusion_desc]
  · intro K hK
    apply (cancel_epi J).mp
    rw [IsIso.hom_inv_id_assoc]
    apply HironakaG1NativeDisjointCoproduct.hom_ext T
    intro i
    rw [← Category.assoc,inclusion_desc,hK,inclusion_desc]

end SGPT.Unibranch.NativeNov16DisjointSourceCoverGluing
