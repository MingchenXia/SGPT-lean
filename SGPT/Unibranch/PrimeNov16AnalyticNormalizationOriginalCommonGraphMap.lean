import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClosedLanding
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchRestriction

/-! Actual common-base component maps from single original graph opens.
Blueprint: prime-nov16-analytic-normalization-original-common-graph-map.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphRefinement
open PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalClosedLanding

variable {n : ℕ} {Z : Set (ComplexModel n)} (d : GraphPresentation n Z)
  {X : SourceReducedComplexSpace} (g : d.target ⟶ X) (U : Opens X.obj.left) [ParacompactSpace U]

abbrev commonGraph := refine d (commonBaseOpen d g U)

abbrev commonTargetMap : (commonGraph d g U).target ⟶ X :=
  targetEmbedding d _ (commonBaseOpen_le d g U) ≫ g

omit [ParacompactSpace U] in
private theorem commonTarget_lands : range (commonTargetMap d g U).hom.left.base ⊆ (U : Set X.obj.left) := by
  rintro _ ⟨p,rfl⟩
  obtain ⟨hb,hbU⟩ := (mem_commonBaseOpen d g U p.val).mp p.property
  have he : (targetEmbedding d _ (commonBaseOpen_le d g U)).hom.left.base p=
      (⟨p.val,hb⟩ : d.target.obj.left) :=
    Subtype.ext (targetEmbedding_point d _ (commonBaseOpen_le d g U) p)
  change g.hom.left.base ((targetEmbedding d _ (commonBaseOpen_le d g U)).hom.left.base p) ∈ U
  exact he.symm ▸ hbU

def commonComponent : (commonGraph d g U).target ⟶ restrictedBase U :=
  landingMap (commonTargetMap d g U) U (commonTarget_lands d g U)

theorem commonComponent_square : commonComponent d g U ≫ baseInclusion U=commonTargetMap d g U :=
  landingMap_square _ _ _

omit [ParacompactSpace U] in
theorem commonTarget_range :
    (Subtype.val : U → X.obj.left) ⁻¹' range (commonTargetMap d g U).hom.left.base=
      (Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base := by
  ext x
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨(targetEmbedding d _ (commonBaseOpen_le d g U)).hom.left.base p,hp⟩
  · rintro ⟨b,hb⟩
    have hbU : g.hom.left.base b ∈ U := hb.symm ▸ x.property
    have hbV : b.val ∈ commonBaseOpen d g U :=
      (mem_commonBaseOpen d g U b.val).mpr ⟨b.property,hbU⟩
    let p : (commonGraph d g U).target.obj.left := ⟨b.val,hbV⟩
    have he : (targetEmbedding d _ (commonBaseOpen_le d g U)).hom.left.base p=b :=
      Subtype.ext (targetEmbedding_point d _ (commonBaseOpen_le d g U) p)
    exact ⟨p,(congrArg g.hom.left.base he).trans hb⟩

theorem commonComponent_proper (hg : Topology.IsEmbedding g.hom.left.base)
    (hc : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base)) :
    IsProperMap (commonComponent d g U).hom.left.base := by
  apply landingMap_proper
  · exact hg.comp (targetEmbedding_isOpenImmersion d _ (commonBaseOpen_le d g U)).base_open.isEmbedding
  · rw [commonTarget_range]
    exact hc


def commonMap : (commonGraph d g U).source ⟶ restrictedBase U :=
  (commonGraph d g U).map ≫ commonComponent d g U

theorem commonMap_proper (hp : IsProperMap d.projection.hom.left.base)
    (hg : Topology.IsEmbedding g.hom.left.base)
    (hc : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base)) :
    IsProperMap (commonMap d g U).hom.left.base :=
  (commonComponent_proper d g U hg hc).comp (map_proper_of_projection (commonGraph d g U) hp)

private theorem finite_fibres_comp {A B T : Type} (f : A → B) (j : B → T)
    (hf : ∀ b,(f ⁻¹' {b}).Finite) (hj : Function.Injective j) (t : T) :
    ((j ∘ f) ⁻¹' {t}).Finite := by
  by_cases he : ∃ b,j b=t
  · obtain ⟨b,hb⟩ := he
    have hs : (j ∘ f) ⁻¹' {t}=f ⁻¹' {b} := by
      ext a
      change j (f a)=t ↔ f a=b
      rw [← hb,hj.eq_iff]
    exact hs.symm ▸ hf b
  · have hs : (j ∘ f) ⁻¹' {t}=∅ := by
      ext a
      simp only [mem_preimage,mem_singleton_iff,Function.comp_apply,mem_empty_iff_false,iff_false]
      exact fun h => he ⟨f a,h⟩
    rw [hs]
    exact finite_empty

theorem commonMap_fibres_finite (hp : IsProperMap d.projection.hom.left.base)
    (hf : ∀ b : d.base.obj.left,(d.projection.hom.left.base ⁻¹' {b}).Finite)
    (hg : Topology.IsEmbedding g.hom.left.base)
    (hc : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base))
    (x : (restrictedBase U).obj.left) : ((commonMap d g U).hom.left.base ⁻¹' {x}).Finite := by
  have he := landingMap_closed (commonTargetMap d g U) U (commonTarget_lands d g U)
    (hg.comp (targetEmbedding_isOpenImmersion d _ (commonBaseOpen_le d g U)).base_open.isEmbedding)
    ((commonTarget_range d g U).symm ▸ hc)
  exact finite_fibres_comp (commonGraph d g U).map.hom.left.base
    (commonComponent d g U).hom.left.base (map_finite_of_projection (commonGraph d g U) hp hf)
    he.injective x

omit [ParacompactSpace U] in
theorem commonMap_normal
    (hn : ∀ p : d.source.obj.left,IsDomain (d.source.obj.left.presheaf.stalk p).carrier ∧
      IsIntegrallyClosed (d.source.obj.left.presheaf.stalk p).carrier)
    (p : (commonGraph d g U).source.obj.left) :
    IsDomain ((commonGraph d g U).source.obj.left.presheaf.stalk p).carrier ∧
      IsIntegrallyClosed ((commonGraph d g U).source.obj.left.presheaf.stalk p).carrier :=
  refine_normal d _ (commonBaseOpen_le d g U) hn p

theorem commonMap_range (hs : Function.Surjective d.map.hom.left.base) :
    range (commonMap d g U).hom.left.base=
      (Subtype.val : U → X.obj.left) ⁻¹' range g.hom.left.base := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    have he := landingMap_point (commonTargetMap d g U) U (commonTarget_lands d g U)
      ((commonGraph d g U).map.hom.left.base p)
    exact ⟨(targetEmbedding d _ (commonBaseOpen_le d g U)).hom.left.base
      ((commonGraph d g U).map.hom.left.base p),he.symm⟩
  · intro hx
    have hx' := (Set.ext_iff.mp (commonTarget_range d g U) x).mpr hx
    obtain ⟨b,hb⟩ := hx'
    obtain ⟨p,hp⟩ := refine_surjective d _ (commonBaseOpen_le d g U) hs b
    refine ⟨p,Subtype.ext ?_⟩
    have he := landingMap_point (commonTargetMap d g U) U (commonTarget_lands d g U)
      ((commonGraph d g U).map.hom.left.base p)
    exact he.trans ((congrArg (commonTargetMap d g U).hom.left.base hp).trans hb)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
