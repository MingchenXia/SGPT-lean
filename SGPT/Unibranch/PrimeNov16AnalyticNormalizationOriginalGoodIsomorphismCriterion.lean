import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalProperRestriction
import SGPT.Unibranch.HironakaG10ChowNativeIsoCriterion

/-! Proper original point/stalk data internally construct the full original good inverse.
Blueprint: prime-nov16-analytic-normalization-original-good-isomorphism-criterion.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace Topology CategoryTheory AlgebraicGeometry
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodIsomorphismCriterion
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationOriginalProperRestriction

theorem isIsoOver_of_proper_bijOn_stalk {Y X : SourceReducedComplexSpace}
    (f : Y ⟶ X) (hp : IsProperMap f.hom.left.base) (G : Opens X.obj.left) [ParacompactSpace G]
    (hb : Set.BijOn f.hom.left.base (f.hom.left.base ⁻¹' (G : Set X.obj.left)) (G : Set X.obj.left))
    (hs : ∀ p : Y.obj.left,f.hom.left.base p ∈ G → IsIso (f.hom.left.stalkMap p)) :
    IsIsoOver f (G : Set X.obj.left) := by
  let A := restrictedSource f hp G
  let T := restrictedBase G
  let q : A ⟶ T := restrictedMap f hp G
  let i : A ⟶ Y := sourceInclusion f hp G
  let j : T ⟶ X := baseInclusion G
  have hsq : q ≫ j=i ≫ f := restrictedMap_square f hp G
  have hqbij : Function.Bijective q.hom.left.base := by
    constructor
    · intro p r hpr
      apply Subtype.ext
      apply hb.2.1 p.property r.property
      exact (restrictedMap_point f hp G p).symm.trans
        ((congrArg Subtype.val hpr).trans (restrictedMap_point f hp G r))
    · intro x
      obtain ⟨p,hpG,hpx⟩ := hb.2.2 x.property
      refine ⟨⟨p,hpG⟩,Subtype.ext ?_⟩
      exact (restrictedMap_point f hp G ⟨p,hpG⟩).trans hpx
  have hhome : IsHomeomorph q.hom.left.base :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
      ⟨q.hom.left.base.hom.continuous,(restrictedMap_proper f hp G).isClosedMap,hqbij⟩
  let K : A.obj.left ⟶ X.obj.left := i.hom.left ≫ f.hom.left
  have hK : K=q.hom.left ≫ j.hom.left := by
    exact (congrArg (fun F => F.hom.left) hsq).symm
  have hEmb : IsOpenEmbedding K.base := by
    rw [hK]
    exact (baseInclusion_isOpenImmersion G).base_open.comp hhome.isOpenEmbedding
  have hstalk : ∀ p : A.obj.left,IsIso (K.stalkMap p) := by
    intro p
    let : IsIso (f.hom.left.stalkMap (i.hom.left.base p)) := hs p.val p.property
    let : IsIso (i.hom.left.stalkMap p) := inferInstance
    change IsIso ((i.hom.left ≫ f.hom.left).stalkMap p)
    rw [LocallyRingedSpace.stalkMap_comp]
    infer_instance
  have hKO : LocallyRingedSpace.IsOpenImmersion K :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso K hEmb (stalk_iso := hstalk)
  refine ⟨A.obj.left,i.hom.left,sourceInclusion_isOpenImmersion f hp G,Subtype.range_coe,hKO,?_⟩
  change range K.base=(G : Set X.obj.left)
  rw [hK]
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact (q.hom.left.base p).property
  · intro hx
    obtain ⟨p,hp⟩ := hqbij.surjective (⟨x,hx⟩ : T.obj.left)
    exact ⟨p,congrArg Subtype.val hp⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGoodIsomorphismCriterion
