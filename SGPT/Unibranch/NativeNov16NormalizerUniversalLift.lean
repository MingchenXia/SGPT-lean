import SGPT.Unibranch.NativeNov16NormalSourceNormalizationLift
import SGPT.Unibranch.NativeNov16ActualNormalSourceCharts
import SGPT.Unibranch.NativeNov16AnalyticCoverLiftGluing
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartDenominator

/-! Actual arbitrary original normal source lifts; no chart/selector/overlap certificates.
Blueprint: native-nov16-normalizer-universal-lift.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
open HironakaActualAnalyticSubspaceResidue
namespace SGPT.Unibranch.NativeNov16NormalizerUniversalLift
open SourceReducedComplexSpace NativeNov16SectionCoordinateMorphism
open NativeNov16ActualNormalSourceCharts NativeNov16PartialBaseScalarSections
open PrimeNov16AnalyticNormalizationOriginalNormalSourceSelectors
open PrimeNov16AnalyticNormalizationOriginalSelectorSections
open PrimeNov16AnalyticNormalizationOriginalSectionDensity
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalChartDenominator
open PrimeNov16AnalyticNormalizationLocalGraph PrimeNov16AnalyticNormalizationDenominatorGraph
open HironakaG1NativeDisjointCoproduct

theorem exists_unique_lift {n k : ℕ} {Z : Set (ComplexModel n)}
    {Y : SourceReducedComplexSpace} (Pt : Opens (ComplexModel n))
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
    (f : Y ⟶ coordinateSource Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ U)
    (Ω : Opens (ComplexModel n)) (Q : ComplexModel n → ℂ) (T : Fin k → ComplexModel n → ℂ)
    (hQ : DifferentiableOn ℂ Q Ω) (hT : ∀ i,DifferentiableOn ℂ (T i) Ω)
    (hH : ∀ i,DifferentiableOn ℂ (d i).denominator Ω)
    (hland : ∀ b : ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z),b ∈ U → b.val.val ∈ Ω)
    (hvan : ∀ i j,i ≠ j → ∀ b : Pt,b.val ∈ B j → b.val ∈ Ω → T i b.val=0)
    (hbranch : ∀ i,∀ b : Pt,b.val ∈ B i → b.val ∈ Ω → Q b.val=T i b.val*(d i).denominator b.val)
    (hnormal : ∀ y : Y.obj.left,IsDomain (Y.obj.left.presheaf.stalk y).carrier ∧
      IsIntegrallyClosed (Y.obj.left.presheaf.stalk y).carrier)
    (Gf : Set (coordinateSource Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) hZ U).obj.left)
    (hfIso : IsIsoOver f Gf) (hfDense : Dense (f.hom.left.base ⁻¹' Gf))
    (htarget : ∀ x (hx : x ∈ U),
      (actualSubspaceSheaf (n := n) ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z)).presheaf.germ U x hx
        (scalarSection Pt ((Subtype.val : Pt → ComplexModel n) ⁻¹' Z) U Ω Q hQ hland) ≠ 0)
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
    ∃! L : Y ⟶ coproduct (fun i => (commonGraph (d i) (g i) U).source),
      L ≫ desc (fun i => (commonGraph (d i) (g i) U).source)
        (fun i => commonMap (d i) (g i) U)=f := by
  classical
  let Ct := (Subtype.val : Pt → ComplexModel n) ⁻¹' Z
  let e := fun y : Y.obj.left => LocalEmbedding.ofPoint Y y
  let A := fun y : Y.obj.left => chartSource (e y)
  let j := fun y : Y.obj.left => chartInclusion (e y)
  let N := coproduct (fun i => (commonGraph (d i) (g i) U).source)
  let p : N ⟶ coordinateSource Pt Ct hZ U :=
    desc (fun i => (commonGraph (d i) (g i) U).source) (fun i => commonMap (d i) (g i) U)
  have hr (y : Y.obj.left) : ∀ x (hx : x ∈ (⊤ : Opens (TopCat.of (e y).carrier))),
      (actualSubspaceSheaf (n := (e y).dim) (e y).carrier).presheaf.germ ⊤ x hx
        (pulledPartialScalar (e y).ambient (e y).carrier (e y).analytic ⊤ Pt Ct hZ U
          (j y ≫ f) Ω Q hQ hland) ≠ 0 :=
    actual_chart_partial_pullback_nonzero (e y).ambient (e y).carrier (e y).analytic ⊤
      Pt Ct hZ U f Gf hfIso hfDense (j y) Ω Q hQ hland htarget
  have hl (y : Y.obj.left) : ∃! L : A y ⟶ N,L ≫ p=j y ≫ f :=
    NativeNov16NormalSourceNormalizationLift.exists_unique_normal_source_lift
      (e y).ambient (e y).carrier (e y).analytic ⊤ Pt hZ B hB hBZ hcover d hDP g U
      hcoord hRange (j y ≫ f) Ω Q T hQ hT hH hland hvan hbranch
      (chart_normal_stalks (e y) hnormal) (hr y) deg a ha hm hs hGood
  choose L hL _hLu using hl
  have hd (y : Y.obj.left) : Dense ((j y ≫ f).hom.left.base ⁻¹' {x | Q x.val.val.val ≠ 0}) := by
    let qs := pulledPartialScalar (e y).ambient (e y).carrier (e y).analytic ⊤ Pt Ct hZ U
      (j y ≫ f) Ω Q hQ hland
    have hdn := original_section_nonzero_dense (e y).carrier ⊤ qs (hr y)
    have he : {t : (⊤ : Opens (TopCat.of (e y).carrier)) |
        actualSubspaceStalkEval (n := (e y).dim) (e y).carrier t.val
          ((actualSubspaceSheaf (n := (e y).dim) (e y).carrier).presheaf.germ ⊤ t.val t.property qs) ≠ 0}=
        (j y ≫ f).hom.left.base ⁻¹' {x | Q x.val.val.val ≠ 0} := by
      ext t
      change original_value_hom (e y).carrier ⊤ t qs ≠ 0 ↔ Q ((j y ≫ f).hom.left.base t).val.val.val ≠ 0
      rw [pulledPartialScalar_value]
      rfl
    exact he ▸ hdn
  let jr := fun y => (j y).hom.left
  let : ∀ y,LocallyRingedSpace.IsOpenImmersion (jr y) := fun y => inferInstance
  have hcv : ∀ y : Y.obj.left,∃ (z : Y.obj.left) (t : (A z).obj.left),(jr z).base t=y := by
    intro y
    obtain ⟨t,ht⟩ := point_cover Y y
    exact ⟨y,t,ht⟩
  have hsc (y : Y.obj.left) : (L y).hom.left ≫ N.obj.hom=jr y ≫ Y.obj.hom :=
    (Over.w (L y).hom).trans (Over.w (j y).hom).symm
  have htr (y : Y.obj.left) : (L y).hom.left ≫ p.hom.left=jr y ≫ f.hom.left :=
    congrArg (fun F : A y ⟶ coordinateSource Pt Ct hZ U => F.hom.left) (hL y)
  obtain ⟨F,hF,hFu⟩ := NativeNov16AnalyticCoverLiftGluing.exists_unique_lift Y.obj.hom
    (fun y => (A y).obj.left) jr hcv (fun y => chart_analytic (e y))
    p {x | Q x.val.val.val ≠ 0} hGood f.hom.left (fun y => (L y).hom.left) hsc htr hd
  let M : Y ⟶ N := ObjectProperty.homMk (Over.homMk F hF.2)
  have hMp : M ≫ p=f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hF.1
  refine ⟨M,hMp,?_⟩
  intro K hK
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hFu K.hom.left ⟨congrArg (fun F : Y ⟶ coordinateSource Pt Ct hZ U => F.hom.left) hK,
    Over.w K.hom⟩

end SGPT.Unibranch.NativeNov16NormalizerUniversalLift
