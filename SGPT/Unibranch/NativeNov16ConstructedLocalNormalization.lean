import SGPT.Unibranch.NativeNov16NormalizerUniversalLift
import Mathlib.Topology.Metrizable.Basic
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalizationBaseCover
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalPartialScalarRegularity

/-! Local normalization objects are OUTPUTS of the actual original-point factory.
Blueprint: native-nov16-constructed-local-normalization.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.NativeNov16ConstructedLocalNormalization
open SourceReducedComplexSpace NativeNov16SectionCoordinateMorphism
open PrimeNov16AnalyticNormalizationOriginalNormalizationBaseCover
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalPartialScalarRegularity
open NativeNov16PartialBaseScalarSections
open HironakaG1NativeDisjointCoproduct
open PrimeNov16AnalyticNormalizationLocalGraph

/-- A package of already constructed local objects; existence below assumes ONLY X and x. -/
structure LocalNormalizer (X : SourceReducedComplexSpace) (x : X.obj.left) where
  base : SourceReducedComplexSpace
  source : SourceReducedComplexSpace
  into : base ⟶ X
  into_open : LocallyRingedSpace.IsOpenImmersion into.hom.left
  center : base.obj.left
  center_eq : into.hom.left.base center=x
  base_metrizable : MetrizableSpace base.obj.left
  projection : source ⟶ base
  proper : IsProperMap projection.hom.left.base
  finite : ∀ b : base.obj.left,(projection.hom.left.base ⁻¹' {b}).Finite
  onto : Function.Surjective projection.hom.left.base
  normal : ∀ y : source.obj.left,IsDomain (source.obj.left.presheaf.stalk y).carrier ∧
    IsIntegrallyClosed (source.obj.left.presheaf.stalk y).carrier
  bimeromorphic : IsProperBimeromorphic projection
  good : Set base.obj.left
  good_inverse : IsIsoOver projection good
  good_target_dense : Dense good
  good_source_dense : Dense (projection.hom.left.base ⁻¹' good)
  good_map_lift : ∀ (Y : SourceReducedComplexSpace),
    (∀ y : Y.obj.left,IsDomain (Y.obj.left.presheaf.stalk y).carrier ∧
      IsIntegrallyClosed (Y.obj.left.presheaf.stalk y).carrier) →
    ∀ (f : Y ⟶ base) (G : Set base.obj.left),IsIsoOver f G → Dense (f.hom.left.base ⁻¹' G) →
      ∃! L : Y ⟶ source,L ≫ projection=f

theorem exists_local_normalizer (X : SourceReducedComplexSpace) (x : X.obj.left) :
    Nonempty (LocalNormalizer X x) := by
  obtain ⟨n,Z,Ω,hΩ,hZ,h0,hΩ0,j,hOI,c,hc0,hjc,k,B,r,hC,hr,hrΩ,hB,hBC,hunion,hpair,
    d,deg,a,g,hcontain,hH,hHne,ha,hm,hs,hn,hg,hcoord,T,rQ,hCQ,hBCQ,hrQ,hQraw,hQinitial,
    hT,hHi,hQOn,hrel,hvan,hD,V,hV,hNZ,hNZi,hDense,hDensei,b0,hb0,U,hbU,hWindow,hRange,hPC,
    hFp,hFf,hGood,hBim,hTargetDense,hSourceDense,hProper,hFinite,hSurj,hNormal,J,hJ,hJx⟩ :=
    exists_original_normalization_base_cover X x
  let : ParacompactSpace U := hPC
  let P := ballDomain (n := n) r
  let O := ballDomain (n := n) rQ
  let Ct : Set P := {z | z.val ∈ Z}
  let Q : ComplexModel n → ℂ := fun z => ∑ i,T i z*(d i).denominator z
  let N := coproduct (fun i => (commonGraph (d i) (g i) U).source)
  let p : N ⟶ restrictedBase U :=
    desc (fun i => (commonGraph (d i) (g i) U).source) (fun i => commonMap (d i) (g i) U)
  have hland : ∀ b : Ct,b ∈ U → b.val.val ∈ O := by
    intro b hb
    obtain ⟨z,hz,_hzV⟩ := hWindow b hb
    exact hz ▸ z.property
  have hVland : ∀ b : Ct,∀ hb : b ∈ U,(⟨b.val.val,hland b hb⟩ : O) ∈ V := by
    intro b hb
    obtain ⟨z,hz,hzV⟩ := hWindow b hb
    exact (Subtype.ext hz : z=(⟨b.val.val,hland b hb⟩ : O)) ▸ hzV
  have htarget := (actual_partial_scalar_nonzero_dense Z P O hQinitial hC hCQ U V Q hQOn
    hland hVland hNZ).1
  have hBiZ (i : Fin k) : ((Subtype.val : P → ComplexModel n) ⁻¹' B i) ⊆ Ct := by
    intro b hb
    exact (hunion b.val b.property).mpr ⟨i,hb⟩
  have hCover : ∀ b ∈ Ct,∃ i,b.val ∈ B i := by
    intro b hb
    exact (hunion b.val b.property).mp hb
  have hMetric : MetrizableSpace (restrictedBase U).obj.left := by
    change MetrizableSpace {b : {z : P // z.val ∈ Z} // b ∈ U}
    have he : Topology.IsEmbedding
        (fun b : {b : {z : P // z.val ∈ Z} // b ∈ U} => b.val.val.val) :=
      (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (Subtype.val : P → ComplexModel n)).comp
        ((Topology.IsEmbedding.subtypeVal :
          Topology.IsEmbedding (Subtype.val : {z : P // z.val ∈ Z} → P)).comp
          (Topology.IsEmbedding.subtypeVal :
            Topology.IsEmbedding (Subtype.val : {b : {z : P // z.val ∈ Z} // b ∈ U} → {z : P // z.val ∈ Z})))
    exact he.metrizableSpace
  refine ⟨{
    base := restrictedBase U
    source := N
    into := J
    into_open := hJ
    center := ⟨b0,hbU⟩
    center_eq := hJx
    base_metrizable := hMetric
    projection := p
    proper := hProper
    finite := hFinite
    onto := hSurj
    normal := hNormal
    bimeromorphic := hBim
    good := {b | Q b.val.val.val ≠ 0}
    good_inverse := hGood
    good_target_dense := hTargetDense
    good_source_dense := hSourceDense
    good_map_lift := ?_ }⟩
  intro Y hY f Gf hfIso hfDense
  exact @NativeNov16NormalizerUniversalLift.exists_unique_lift n k Z Y P hC B hBC hBiZ hCover d hcontain g U hPC
    hcoord hRange f O Q T hQOn hT hHi hland
    (fun i l hil b hb hO => hvan b.val hO i l (Ne.symm hil) hb)
    (fun i b hb hO => hrel b.val hO i hb) hY Gf hfIso hfDense htarget deg a ha hm hs hGood

end SGPT.Unibranch.NativeNov16ConstructedLocalNormalization
