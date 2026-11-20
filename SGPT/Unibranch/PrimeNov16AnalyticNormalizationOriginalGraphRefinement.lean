import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphCoordinates

/-! Literal SAME graph, canonical full original refinement, and whole original geometry transport.
Blueprint: prime-nov16-analytic-normalization-original-graph-refinement.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphRefinement
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphCoordinates
open PrimeNov16AnalyticNormalizationOriginalProperRestriction

variable {n : ℕ} {Z : Set (ComplexModel n)}

def refine (d : GraphPresentation n Z) (V : Opens d.base.obj.left) : GraphPresentation n Z :=
  {d with baseOpen := V}

private theorem source_lands (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) : range (refine d V).sourceInclusion.hom.left.base ⊆
      range d.sourceInclusion.hom.left.base := by
  rintro _ ⟨p,rfl⟩
  let p0 : (refine d V).sourceDomain := p
  exact ⟨⟨p0.val,hV p0.property⟩,rfl⟩

def sourceEmbedding (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) : (refine d V).source ⟶ d.source := by
  let i := d.sourceInclusion
  let j := (refine d V).sourceInclusion
  let L := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left j.hom.left (source_lands d V hV)
  have hL := LocallyRingedSpace.IsOpenImmersion.lift_fac i.hom.left j.hom.left (source_lands d V hV)
  have hs : L ≫ d.source.obj.hom=(refine d V).source.obj.hom := by
    rw [← Over.w i.hom,← Category.assoc,hL]
    exact Over.w j.hom
  exact ObjectProperty.homMk (Over.homMk L hs)

theorem sourceEmbedding_square (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) : sourceEmbedding d V hV ≫ d.sourceInclusion=(refine d V).sourceInclusion := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ (source_lands d V hV)

instance sourceEmbedding_isOpenImmersion (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) : LocallyRingedSpace.IsOpenImmersion (sourceEmbedding d V hV).hom.left := by
  have hcomp : LocallyRingedSpace.IsOpenImmersion
      ((sourceEmbedding d V hV).hom.left ≫ d.sourceInclusion.hom.left) := by
    have hs := congrArg (fun f => f.hom.left) (sourceEmbedding_square d V hV)
    change (sourceEmbedding d V hV).hom.left ≫ d.sourceInclusion.hom.left=
      (refine d V).sourceInclusion.hom.left at hs
    exact hs.symm ▸ (GraphPresentation.sourceInclusion_isOpenImmersion (refine d V))
  let := hcomp
  exact HironakaG10ChowStrictTransformCalculus.isOpenImmersion_of_comp
    (sourceEmbedding d V hV).hom.left d.sourceInclusion.hom.left

theorem refine_normal (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen)
    (hn : ∀ p : d.source.obj.left,IsDomain (d.source.obj.left.presheaf.stalk p).carrier ∧
      IsIntegrallyClosed (d.source.obj.left.presheaf.stalk p).carrier)
    (p : (refine d V).source.obj.left) :
    IsDomain ((refine d V).source.obj.left.presheaf.stalk p).carrier ∧
      IsIntegrallyClosed ((refine d V).source.obj.left.presheaf.stalk p).carrier := by
  obtain ⟨hd,hc⟩ := hn ((sourceEmbedding d V hV).hom.left.base p)
  let := hd
  let := hc
  let E := (asIso ((sourceEmbedding d V hV).hom.left.stalkMap p)).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain E.symm E.symm.injective,IsIntegrallyClosed.of_equiv E⟩

theorem refine_surjective (d : GraphPresentation n Z) (V : Opens d.base.obj.left)
    (hV : V ≤ d.baseOpen) (hs : Function.Surjective d.map.hom.left.base) :
    Function.Surjective (refine d V).map.hom.left.base := by
  intro b
  let bOld : d.target.obj.left := ⟨b.val,hV b.property⟩
  obtain ⟨p,hp⟩ := hs bOld
  have hc : d.projection.hom.left.base p.val=b.val :=
    (map_point d p).symm.trans (congrArg Subtype.val hp)
  have hm : d.projection.hom.left.base p.val ∈ V := hc.symm ▸ b.property
  let pNew : (refine d V).source.obj.left := ⟨p.val,hm⟩
  exact ⟨pNew,Subtype.ext ((map_point (refine d V) pNew).trans hc)⟩

theorem map_proper_of_projection (d : GraphPresentation n Z)
    (hp : IsProperMap d.projection.hom.left.base) : IsProperMap d.map.hom.left.base := by
  let := d.baseOpen_pc
  exact restrictedMap_proper d.projection hp d.baseOpen

theorem map_finite_of_projection (d : GraphPresentation n Z)
    (hp : IsProperMap d.projection.hom.left.base)
    (hf : ∀ b : d.base.obj.left,(d.projection.hom.left.base ⁻¹' {b}).Finite)
    (b : d.target.obj.left) : (d.map.hom.left.base ⁻¹' {b}).Finite := by
  let := d.baseOpen_pc
  exact restrictedMap_fibres_finite d.projection hp d.baseOpen hf b

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphRefinement
