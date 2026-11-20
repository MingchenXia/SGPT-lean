import SGPT.Unibranch.NativeNov16NormalSourceFamilyLift
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalSourceComponentData
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSectionDensity

/-! Actual normal-source lift to the SAME reduced local normalizer; selectors are manufactured.
Blueprint: native-nov16-normal-source-normalization-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16NormalSourceNormalizationLift
open NativeNov16SectionCoordinateMorphism
open PrimeNov16AnalyticNormalizationOriginalNormalSourceSelectors
open PrimeNov16AnalyticNormalizationOriginalNormalSourceComponentData
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphRefinement
open PrimeNov16AnalyticNormalizationOriginalGraphTargetRefinement
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationLocalGraph PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open PrimeNov16AnalyticNormalizationOriginalSectionDensity
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceResidue
open SourceReducedComplexSpace HironakaG1NativeDisjointCoproduct

theorem exists_unique_normal_source_lift {m n k : ℕ} {Z : Set (ComplexModel n)}
    (Ps : Opens (ComplexModel m)) (Cs : Set Ps) (hCs : IsComplexAnalyticSubset (n := m) Cs)
    (Ws : Opens (TopCat.of Cs)) (Pt : Opens (ComplexModel n))
    (hZ : IsComplexAnalyticSubset (n := n) ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z))
    (B : Fin k → Set (ComplexModel n))
    (hB : ∀ i,IsComplexAnalyticSubset (n := n) ((Subtype.val : Pt → ComplexModel n) ⁻¹' B i))
    (hBZ : ∀ i,((Subtype.val : Pt → ComplexModel n) ⁻¹' B i) ⊆ ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z))
    (hcover : ∀ b ∈ ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z),∃ i,b.val ∈ B i)
    (d : ∀ i,GraphPresentation n (B i)) (hDP : ∀ i,ballDomain (n := n) (d i).radius ≤ Pt)
    (g : ∀ i,(d i).target ⟶ sourceReducedComplexSpaceModel Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ)
    (U : Opens (sourceReducedComplexSpaceModel Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ).obj.left)
    [ParacompactSpace U]
    (hcoord : ∀ i,∀ t : (d i).target.obj.left,((g i).hom.left.base t).val.val=t.val.val.val)
    (hRange : ∀ i,∀ x : (sourceReducedComplexSpaceModel Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ).obj.left,
      x ∈ U → (x ∈ range (g i).hom.left.base ↔ x.val.val ∈ B i))
    (f : coordinateSource Ps Cs hCs Ws ⟶ coordinateSource Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ U)
    (Ω : Opens (ComplexModel n)) (Q : ComplexModel n → ℂ) (T : Fin k → ComplexModel n → ℂ)
    (hQ : DifferentiableOn ℂ Q Ω) (hT : ∀ i,DifferentiableOn ℂ (T i) Ω)
    (hH : ∀ i,DifferentiableOn ℂ (d i).denominator Ω)
    (hland : ∀ b : ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z),b ∈ U → b.val.val ∈ Ω)
    (hvan : ∀ i j,i ≠ j → ∀ b : Pt,b.val ∈ B j → b.val ∈ Ω → T i b.val=0)
    (hbranch : ∀ i,∀ b : Pt,b.val ∈ B i → b.val ∈ Ω → Q b.val=T i b.val*(d i).denominator b.val)
    (hnormal : ∀ x ∈ Ws,IsDomain ((actualSubspaceSheaf (n := m) Cs).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := m) Cs).presheaf.stalk x).carrier)
    (hreg : ∀ x (hx : x ∈ Ws),(actualSubspaceSheaf (n := m) Cs).presheaf.germ Ws x hx
      (pulledPartialScalar Ps Cs hCs Ws Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ U f Ω Q hQ hland) ≠ 0)
    (deg : ∀ i,Fin (d i).arity → ℕ)
    (a : ∀ i,Fin (d i).arity → ℕ → ComplexModel n → ℂ)
    (ha : ∀ i j l,l < deg i j → DifferentiableOn ℂ (a i j l) (ballDomain (n := n) (d i).radius))
    (hm : ∀ i,∀ p : (d i).graph.obj.left,∀ j,
      GermParametrizationData.monicEval (deg i j) (a i j)
        (baseProjection n (d i).arity p.val.val) (fibreProjection n (d i).arity p.val.val j)=0)
    (hs : ∀ i,Function.Surjective (d i).map.hom.left.base)
    (hGood : IsIsoOver
      (desc (fun i => (commonGraph (d i) (g i) U).source) (fun i => commonMap (d i) (g i) U))
      {x | Q x.val.val.val ≠ 0}) :
    ∃! L : coordinateSource Ps Cs hCs Ws ⟶ coproduct (fun i => (commonGraph (d i) (g i) U).source),
      L ≫ desc (fun i => (commonGraph (d i) (g i) U).source)
        (fun i => commonMap (d i) (g i) U)=f := by
  obtain ⟨V,hVW,_hClosed,hCover,hDisjoint,F,htri,hr⟩ :=
    exists_actual_component_data Ps Cs hCs Ws Pt hZ B hB hBZ hcover d hDP g U hcoord hRange f
      Ω Q T hQ hT hH hland hvan hbranch hnormal hreg
  let Ct := (Subtype.val : Pt → ComplexModel n) ⁻¹' Z
  let qs := pulledPartialScalar Ps Cs hCs Ws Pt Ct hZ U f Ω Q hQ hland
  have hd : Dense (f.hom.left.base ⁻¹' {x | Q x.val.val.val ≠ 0}) := by
    have hdn := original_section_nonzero_dense Cs Ws qs hreg
    have he : {p : Ws | actualSubspaceStalkEval (n := m) Cs p.val
        ((actualSubspaceSheaf (n := m) Cs).presheaf.germ Ws p.val p.property qs) ≠ 0}=
        f.hom.left.base ⁻¹' {x | Q x.val.val.val ≠ 0} := by
      ext p
      change original_value_hom Cs Ws p qs ≠ 0 ↔ Q (f.hom.left.base p).val.val.val ≠ 0
      rw [pulledPartialScalar_value]
    exact he ▸ hdn
  have hs' (i : Fin k) : Function.Surjective (commonGraph (d i) (g i) U).map.hom.left.base :=
    refine_surjective (d i) (commonBaseOpen (d i) (g i) U)
      (commonBaseOpen_le (d i) (g i) U) (hs i)
  exact NativeNov16NormalSourceFamilyLift.exists_unique_family_lift
    (fun i => commonGraph (d i) (g i) U) (fun i => commonComponent (d i) (g i) U)
    Ps Cs hCs Ws f hnormal V hVW hCover hDisjoint F htri hr deg a ha hm hs'
    {x | Q x.val.val.val ≠ 0} hGood hd

end SGPT.Unibranch.NativeNov16NormalSourceNormalizationLift
