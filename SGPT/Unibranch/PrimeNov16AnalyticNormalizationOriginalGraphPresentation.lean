import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalInverse
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClosedLanding
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphDensity

/-! PRIMITIVE actual graph data only; all desired geometric properties are proved separately.
Blueprint: prime-nov16-analytic-normalization-original-graph-presentation.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open SourceReducedComplexSpace
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalClosedLanding
open PrimeNov16AnalyticNormalizationOriginalGraphInverse
open PrimeNov16AnalyticNormalizationOriginalNormalInverse
open PrimeNov16AnalyticNormalizationGraphDensity

structure GraphPresentation (n : ℕ) (Z : Set (ComplexModel n)) where
  arity : ℕ
  radius : ℝ
  denominator : ComplexModel n → ℂ
  numerator : Fin arity → ComplexModel n → ℂ
  denominator_holo : DifferentiableOn ℂ denominator (ballDomain (n := n) radius)
  numerator_holo : ∀ i,DifferentiableOn ℂ (numerator i) (ballDomain (n := n) radius)
  carrier_analytic : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) radius | z.val ∈ Z}
  baseOpen : Opens (sourceReducedComplexSpaceModel (ballDomain (n := n) radius)
    {z : ballDomain (n := n) radius | z.val ∈ Z} carrier_analytic).obj.left

namespace GraphPresentation
variable {n : ℕ} {Z : Set (ComplexModel n)} (d : GraphPresentation n Z)

abbrev base : SourceReducedComplexSpace := sourceReducedComplexSpaceModel (ballDomain (n := n) d.radius)
  {z : ballDomain (n := n) d.radius | z.val ∈ Z} d.carrier_analytic

abbrev graph : SourceReducedComplexSpace := sourceSpace (ballDomain (n := n) d.radius)
  d.carrier_analytic d.denominator d.numerator d.denominator_holo d.numerator_holo

abbrev projection : d.graph ⟶ d.base := PrimeNov16AnalyticNormalizationDenominatorGraph.projection
  (ballDomain (n := n) d.radius) d.carrier_analytic d.denominator d.numerator
    d.denominator_holo d.numerator_holo

theorem baseOpen_pc : ParacompactSpace d.baseOpen := by
  change ParacompactSpace {b : {z : ballDomain (n := n) d.radius | z.val ∈ Z} // b ∈ d.baseOpen}
  infer_instance

def sourceDomain : Opens d.graph.obj.left := sourceOpen d.projection d.baseOpen

theorem sourceDomain_pc : ParacompactSpace d.sourceDomain := by
  change ParacompactSpace {p : graphClosure (ballDomain (n := n) d.radius)
    {z : ballDomain (n := n) d.radius | z.val ∈ Z} d.denominator d.numerator |
      d.projection.hom.left.base p ∈ d.baseOpen}
  infer_instance

def target : SourceReducedComplexSpace := by
  let := d.baseOpen_pc
  exact restrictedBase d.baseOpen

def source : SourceReducedComplexSpace := by
  let := d.sourceDomain_pc
  exact HironakaG11BlowupLocality.openSubspace d.graph d.sourceDomain

def baseInclusion : d.target ⟶ d.base := by
  let := d.baseOpen_pc
  exact PrimeNov16AnalyticNormalizationOriginalProperRestriction.baseInclusion d.baseOpen

def sourceInclusion : d.source ⟶ d.graph := by
  let := d.sourceDomain_pc
  exact HironakaG11BlowupLocality.openSubspaceInclusion d.graph d.sourceDomain

instance baseInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion d.baseInclusion.hom.left := by
  let := d.baseOpen_pc
  exact PrimeNov16AnalyticNormalizationOriginalProperRestriction.baseInclusion_isOpenImmersion d.baseOpen

instance sourceInclusion_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion d.sourceInclusion.hom.left := by
  let := d.sourceDomain_pc
  exact HironakaG11BlowupLocality.openSubspaceInclusion_isOpenImmersion d.graph d.sourceDomain

private theorem lands : range (d.sourceInclusion ≫ d.projection).hom.left.base ⊆
    (d.baseOpen : Set d.base.obj.left) := by
  rintro _ ⟨p,rfl⟩
  let p0 : d.sourceDomain := p
  exact p0.property

def map : d.source ⟶ d.target := by
  let := d.baseOpen_pc
  exact landingMap (d.sourceInclusion ≫ d.projection) d.baseOpen d.lands

theorem map_square : d.map ≫ d.baseInclusion=d.sourceInclusion ≫ d.projection := by
  let := d.baseOpen_pc
  exact landingMap_square (d.sourceInclusion ≫ d.projection) d.baseOpen d.lands

theorem map_isIsoOver : IsIsoOver d.map {b | d.denominator b.val.val.val ≠ 0} := by
  apply OriginalLocalStrictWindowRegularity.isIsoOver_of_open_square d.projection d.map
    d.sourceInclusion d.baseInclusion d.sourceInclusion_isOpenImmersion d.baseInclusion_isOpenImmersion
    d.map_square _ _ (original_graph_isIsoOver (ballDomain (n := n) d.radius) d.carrier_analytic
      d.denominator d.numerator d.denominator_holo d.numerator_holo)
  change range (Subtype.val : d.sourceDomain → d.graph.obj.left)=
    d.projection.hom.left.base ⁻¹' range (Subtype.val : d.baseOpen → d.base.obj.left)
  ext p
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨⟨d.projection.hom.left.base v.val,v.property⟩,rfl⟩
  · rintro ⟨b,hb⟩
    have hp : d.projection.hom.left.base p ∈ d.baseOpen := hb ▸ b.property
    exact ⟨⟨p,hp⟩,rfl⟩

theorem source_denominator_dense :
    Dense {p : d.source.obj.left | d.denominator (baseProjection n d.arity p.val.val.val) ≠ 0} := by
  let S := graphClosure (ballDomain (n := n) d.radius)
    {z : ballDomain (n := n) d.radius | z.val ∈ Z} d.denominator d.numerator
  let f : S → d.base.obj.left := d.projection.hom.left.base
  let V : Opens S := ⟨{p | f p ∈ d.baseOpen},d.baseOpen.isOpen.preimage d.projection.hom.left.base.hom.continuous⟩
  change Dense {p : V | d.denominator (baseProjection n d.arity p.val.val.val) ≠ 0}
  exact denominator_nonzero_dense_on_open (ballDomain (n := n) d.radius)
    {z : ballDomain (n := n) d.radius | z.val ∈ Z} d.denominator d.numerator V

end GraphPresentation

theorem exists_original_normal_presentation {n : ℕ} {Z N : Set (ComplexModel n)}
    (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z) (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ d : GraphPresentation n Z,0<d.radius ∧ ball (0 : ComplexModel n) d.radius ⊆ N ∧
      (∃ b : d.base.obj.left,b.val.val=0 ∧ b ∈ d.baseOpen) ∧
      (∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ d.denominator z) ∧
      (¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ Z → d.denominator z=0) ∧
      IsProperMap d.map.hom.left.base ∧
      (∀ b : d.target.obj.left,(d.map.hom.left.base ⁻¹' {b}).Finite) ∧
      Function.Surjective d.map.hom.left.base ∧
      ∀ p : d.source.obj.left,IsDomain (d.source.obj.left.presheaf.stalk p).carrier ∧
        IsIntegrallyClosed (d.source.obj.left.presheaf.stalk p).carrier := by
  obtain ⟨k,r,H,G,hH,hG,hC,hr,hrN,hHg,hne,hp,b0,hb0,U,hbU,hPC,_hIso,hsurj,hproper,hfinite,hnormal,_hsq⟩ :=
    exists_original_normal_space_with_inverse hZ hN
  let d : GraphPresentation n Z := ⟨k,r,H,G,hH,hG,hC,U⟩
  exact ⟨d,hr,hrN,⟨b0,hb0,hbU⟩,hHg,hne,hproper,hfinite,hsurj,hnormal⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphPresentation
