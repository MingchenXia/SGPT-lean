import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphRefinement

/-! Full original target refinement and the literal single common base window.
Blueprint: prime-nov16-analytic-normalization-original-graph-target-refinement.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphRefinement
open PrimeNov16AnalyticNormalizationOriginalProperRestriction

variable {n : ℕ} {Z : Set (ComplexModel n)}

private theorem target_lands (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) : range (refine d V).baseInclusion.hom.left.base ⊆
      range d.baseInclusion.hom.left.base := by
  rintro _ ⟨p,rfl⟩
  let p0 : V := p
  exact ⟨⟨p0.val,hV p0.property⟩,rfl⟩

def targetEmbedding (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) : (refine d V).target ⟶ d.target := by
  let i := d.baseInclusion
  let j := (refine d V).baseInclusion
  let L := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left j.hom.left (target_lands d V hV)
  have hL := LocallyRingedSpace.IsOpenImmersion.lift_fac i.hom.left j.hom.left (target_lands d V hV)
  have hs : L ≫ d.target.obj.hom=(refine d V).target.obj.hom := by
    rw [← Over.w i.hom,← Category.assoc,hL]
    exact Over.w j.hom
  exact ObjectProperty.homMk (Over.homMk L hs)

theorem targetEmbedding_square (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) : targetEmbedding d V hV ≫ d.baseInclusion=(refine d V).baseInclusion := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (target_lands d V hV)

instance targetEmbedding_isOpenImmersion (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) : LocallyRingedSpace.IsOpenImmersion (targetEmbedding d V hV).hom.left := by
  have hc : LocallyRingedSpace.IsOpenImmersion
      ((targetEmbedding d V hV).hom.left ≫ d.baseInclusion.hom.left) := by
    have hs := congrArg (fun f => f.hom.left) (targetEmbedding_square d V hV)
    change (targetEmbedding d V hV).hom.left ≫ d.baseInclusion.hom.left=
      (refine d V).baseInclusion.hom.left at hs
    exact hs.symm ▸ GraphPresentation.baseInclusion_isOpenImmersion (refine d V)
  let := hc
  exact HironakaG10ChowStrictTransformCalculus.isOpenImmersion_of_comp
    (targetEmbedding d V hV).hom.left d.baseInclusion.hom.left

theorem targetEmbedding_point (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) (p : (refine d V).target.obj.left) :
    ((targetEmbedding d V hV).hom.left.base p).val=p.val :=
  congrArg (fun f => f.hom.left.base p) (targetEmbedding_square d V hV)

def commonBaseOpen (d : GraphPresentation n Z) {X : SourceReducedComplexSpace}
    (g : d.target ⟶ X) (U : Opens X.obj.left) : Opens d.base.obj.left :=
  ⟨d.baseInclusion.hom.left.base '' (sourceOpen g U : Set d.target.obj.left),
    (GraphPresentation.baseInclusion_isOpenImmersion d).base_open.isOpenMap _ (sourceOpen g U).isOpen⟩

theorem commonBaseOpen_le (d : GraphPresentation n Z) {X : SourceReducedComplexSpace}
    (g : d.target ⟶ X) (U : Opens X.obj.left) : commonBaseOpen d g U ≤ d.baseOpen := by
  rintro _ ⟨p,_hp,rfl⟩
  exact p.property

theorem mem_commonBaseOpen (d : GraphPresentation n Z) {X : SourceReducedComplexSpace}
    (g : d.target ⟶ X) (U : Opens X.obj.left) (b : d.base.obj.left) :
    b ∈ commonBaseOpen d g U ↔ ∃ hb : b ∈ d.baseOpen,g.hom.left.base ⟨b,hb⟩ ∈ U := by
  constructor
  · rintro ⟨p,hp,hpb⟩
    let p0 : d.baseOpen := p
    have hb : b ∈ d.baseOpen := hpb ▸ p0.property
    refine ⟨hb,?_⟩
    have he : p=(⟨b,hb⟩ : d.target.obj.left) := Subtype.ext hpb
    exact he ▸ hp
  · rintro ⟨hb,hbU⟩
    exact ⟨⟨b,hb⟩,hbU,rfl⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
