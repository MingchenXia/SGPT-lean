import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedPresentations
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCompleteSeparatedWindow
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFamilyGoodInverse
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralGeometry
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFiniteBranchDescent

/-! Source-only actual reduced normal coproduct retaining single SAME-graph windows.
Blueprint: prime-nov16-analytic-normalization-original-separated-common-family.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSeparatedCommonFamily
open PrimeNov16AnalyticNormalizationOriginalReducedPresentations
open PrimeNov16AnalyticNormalizationOriginalCompleteSeparatedWindow
open PrimeNov16AnalyticNormalizationOriginalFamilyGoodInverse
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalIntegralGeometry
open PrimeNov16AnalyticNormalizationOriginalFiniteBranchDescent
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph
open SourceReducedComplexSpace
open HironakaG1NativeDisjointCoproduct

theorem exists_original_separated_common_family {n : ℕ} {Z N : Set (ComplexModel n)}
    (hZ : AnalyticGermDecomposition.IsAnalyticGerm Z) (h0 : (0 : ComplexModel n) ∈ Z)
    (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ (k : ℕ) (B : Fin k → Set (ComplexModel n)) (r : ℝ)
      (hC : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ Z}),
      0<r ∧ ball (0 : ComplexModel n) r ⊆ N ∧
      (∀ i,AnalyticGermDecomposition.IsIrreducibleGerm (B i)) ∧
      (∀ i,IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r | z.val ∈ B i}) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,z ∈ Z ↔ ∃ i,z ∈ B i) ∧
      Pairwise (fun i j => ¬ (B i ≤ᶠ[𝓝 0] B j)) ∧
      let X := sourceReducedComplexSpaceModel (ballDomain (n := n) r)
        {z : ballDomain (n := n) r | z.val ∈ Z} hC
      ∃ (d : ∀ i,GraphPresentation n (B i)) (deg : ∀ i,Fin (d i).arity → ℕ)
        (a : ∀ i,Fin (d i).arity → ℕ → ComplexModel n → ℂ)
        (g : ∀ i,(d i).target ⟶ X),
        (∀ i,ball (0 : ComplexModel n) (d i).radius ⊆ ball 0 r) ∧
        (∀ i,∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (d i).denominator z) ∧
        (∀ i,¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → (d i).denominator z=0) ∧
        (∀ i j l,l < deg i j → DifferentiableOn ℂ (a i j l) (ballDomain (n := n) (d i).radius)) ∧
        (∀ i,∀ p : (d i).graph.obj.left,∀ j,GermParametrizationData.monicEval (deg i j) (a i j)
          (baseProjection n (d i).arity p.val.val) (fibreProjection n (d i).arity p.val.val j)=0) ∧
        (∀ i,Function.Surjective (d i).map.hom.left.base) ∧
        (∀ i,∀ p : (d i).source.obj.left,IsDomain ((d i).source.obj.left.presheaf.stalk p).carrier ∧
          IsIntegrallyClosed ((d i).source.obj.left.presheaf.stalk p).carrier) ∧
        (∀ i,Topology.IsEmbedding (g i).hom.left.base) ∧
        (∀ i,∀ t : (d i).target.obj.left,((g i).hom.left.base t).val.val=t.val.val.val) ∧
        ∃ (T : Fin k → ComplexModel n → ℂ) (rQ : ℝ)
          (_ : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) rQ | z.val ∈ Z})
          (_ : ∀ i,IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) rQ | z.val ∈ B i}),
        let Q : ComplexModel n → ℂ := fun z => ∑ i,T i z*(d i).denominator z
        0<rQ ∧
        (∀ i,ball (0 : ComplexModel n) rQ ⊆ ball 0 (d i).radius) ∧
        ball (0 : ComplexModel n) rQ ⊆ ball 0 r ∧
        (∀ i,DifferentiableOn ℂ (T i) (ball 0 rQ)) ∧
        (∀ i,DifferentiableOn ℂ (d i).denominator (ball 0 rQ)) ∧
        DifferentiableOn ℂ Q (ball 0 rQ) ∧
        (∀ z ∈ ball (0 : ComplexModel n) rQ,∀ i,z ∈ B i → Q z=T i z*(d i).denominator z) ∧
        (∀ z ∈ ball (0 : ComplexModel n) rQ,∀ i j,j ≠ i → z ∈ B j → T i z=0) ∧
        ∃ hD : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ (Q ∘ Subtype.val : ballDomain (n := n) rQ → ℂ),
        ∃ V : Set (ballDomain (n := n) rQ),IsOpen V ∧
          (∀ y : {z : ballDomain (n := n) rQ | z.val ∈ Z},y.val ∈ V →
            originalFunctionImage _ y (Q ∘ Subtype.val)
              (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z) ≠ 0) ∧
          (∀ i,∀ y : {z : ballDomain (n := n) rQ | z.val ∈ B i},y.val ∈ V →
            originalFunctionImage _ y (Q ∘ Subtype.val)
              (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z) ≠ 0) ∧
          (∀ y : {z : ballDomain (n := n) rQ | z.val ∈ Z},y.val ∈ V →
            y ∈ closure {z : {z : ballDomain (n := n) rQ | z.val ∈ Z} | Q z.val.val ≠ 0}) ∧
          (∀ i,∀ y : {z : ballDomain (n := n) rQ | z.val ∈ B i},y.val ∈ V →
            y ∈ closure {z : {z : ballDomain (n := n) rQ | z.val ∈ B i} | Q z.val.val ≠ 0}) ∧
        ∃ b0 : X.obj.left,b0.val.val=0 ∧ ∃ U : Opens X.obj.left,b0 ∈ U ∧
          (∀ x : X.obj.left,x ∈ U → ∃ z : ballDomain (n := n) rQ,z.val=x.val.val ∧ z ∈ V) ∧
          (∀ i,∀ x : X.obj.left,x ∈ U → (x ∈ range (g i).hom.left.base ↔ x.val.val ∈ B i)) ∧
          ∃ hPC : ParacompactSpace U,
          let _ : ParacompactSpace U := hPC
          let Y : Fin k → SourceReducedComplexSpace := fun i => (commonGraph (d i) (g i) U).source
          let F : ∀ i,Y i ⟶ restrictedBase U := fun i => commonMap (d i) (g i) U
          (∀ i,IsProperMap (F i).hom.left.base) ∧
          (∀ i,∀ x : (restrictedBase U).obj.left,((F i).hom.left.base ⁻¹' {x}).Finite) ∧
          IsIsoOver (desc Y F) {x | Q x.val.val.val ≠ 0} ∧
          IsProperMap (desc Y F).hom.left.base ∧
          (∀ x : (restrictedBase U).obj.left,((desc Y F).hom.left.base ⁻¹' {x}).Finite) ∧
          Function.Surjective (desc Y F).hom.left.base ∧
          ∀ y : (coproduct Y).obj.left,IsDomain ((coproduct Y).obj.left.presheaf.stalk y).carrier ∧
            IsIntegrallyClosed ((coproduct Y).obj.left.presheaf.stalk y).carrier := by
  obtain ⟨k,B,r,hC,hr,hrN,hB,hBC,hunion,hpair,d,deg,a,g,hdr,hcontain,hH,hHne,ha,hm,
    _hp,_hf,hs,hn,hg,hcoord,b0,hb0,Uold,hbOld,_hPCold,hRangeOld⟩ :=
    exists_original_reduced_presentations hZ h0 hN
  let X := sourceReducedComplexSpaceModel (ballDomain (n := n) r)
    {z : ballDomain (n := n) r | z.val ∈ Z} hC
  let U0 : Set {z : ballDomain (n := n) r | z.val ∈ Z} := fun x => x ∈ Uold
  have hU0 : IsOpen U0 := Uold.isOpen
  obtain ⟨O,hO,hOU⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hU0
  obtain ⟨Ω,hΩ,hΩO⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hO
  have hbΩ : b0.val.val ∈ Ω := by
    have hbo : b0.val ∈ O := by
      change b0 ∈ (Subtype.val : {z : ballDomain (n := n) r | z.val ∈ Z} → ballDomain (n := n) r) ⁻¹' O
      rw [hOU]
      exact hbOld
    exact (Set.ext_iff.mp hΩO b0.val).mpr hbo
  have h0Ω : (0 : ComplexModel n) ∈ Ω := hb0 ▸ hbΩ
  have hAllR : ∀ᶠ z in 𝓝 (0 : ComplexModel n),∀ i,z ∈ ball 0 (d i).radius :=
    eventually_all.mpr fun i => ball_mem_nhds 0 (hdr i)
  have hΩN : {z : ComplexModel n | z ∈ Ω ∧ z ∈ ball 0 r ∧ ∀ i,z ∈ ball 0 (d i).radius} ∈ 𝓝 0 :=
    Filter.inter_mem (hΩ.mem_nhds h0Ω) (Filter.inter_mem (ball_mem_nhds 0 hr) hAllR)
  have hcoverG : Z =ᶠ[𝓝 (0 : ComplexModel n)] (⋃ i,B i) := by
    filter_upwards [ball_mem_nhds 0 hr] with z hz
    apply propext
    change z ∈ Z ↔ z ∈ ⋃ i,B i
    simpa only [mem_iUnion] using hunion z hz
  obtain ⟨T,rQ,hCQ,hBCQ,hrQ,hrQΩ,hT,hHi,hQOn,_hQg,_hQne,hD,V,hV,
    ⟨v0,hv0,hvV⟩,hNZ,hNZi,hDense,hDensei,hrel,hvan,hzero,hunique⟩ :=
    exists_original_complete_separated_window hZ h0 B hB hcoverG hpair
      (fun i => (d i).denominator) hH hHne hΩN
  let Q : ComplexModel n → ℂ := fun z => ∑ i,T i z*(d i).denominator z
  let Unew : Opens X.obj.left :=
    ⟨{x | x.val.val ∈ (Subtype.val : ballDomain (n := n) rQ → ComplexModel n) '' V},
      ((ballDomain (n := n) rQ).isOpen.isOpenMap_subtype_val _ hV).preimage
        (continuous_subtype_val.comp continuous_subtype_val)⟩
  have hUnewU : Unew ≤ Uold := by
    rintro x ⟨z,hzV,hzx⟩
    have hxΩ : x.val.val ∈ Ω := hzx ▸ (hrQΩ z.property).1
    change (show {z : ballDomain (n := n) r | z.val ∈ Z} from x) ∈ U0
    rw [← hOU]
    change x.val ∈ O
    rw [← hΩO]
    exact hxΩ
  have hbNew : b0 ∈ Unew := ⟨v0,hvV,hv0.trans hb0.symm⟩
  have hWindow : ∀ x : X.obj.left,x ∈ Unew → ∃ z : ballDomain (n := n) rQ,z.val=x.val.val ∧ z ∈ V := by
    rintro x ⟨z,hz,hzx⟩
    exact ⟨z,hzx,hz⟩
  have hRangeNew : ∀ i,∀ x : X.obj.left,x ∈ Unew →
      (x ∈ range (g i).hom.left.base ↔ x.val.val ∈ B i) :=
    fun i x hx => hRangeOld i x (hUnewU hx)
  have hPCnew : ParacompactSpace Unew := by
    change ParacompactSpace {x : {z : ballDomain (n := n) r | z.val ∈ Z} // x ∈ Unew}
    infer_instance
  let U := Unew
  have hbU : b0 ∈ U := hbNew
  have hPC : ParacompactSpace U := hPCnew
  have hRange : ∀ i,∀ x : X.obj.left,x ∈ U → (x ∈ range (g i).hom.left.base ↔ x.val.val ∈ B i) := hRangeNew
  let : ParacompactSpace U := hPC
  have hclosed (i : Fin k) : IsClosed ((Subtype.val : U → X.obj.left) ⁻¹' range (g i).hom.left.base) := by
    have hc : IsClosed {x : X.obj.left | x.val.val ∈ B i} :=
      (hBC i).isClosed.preimage continuous_subtype_val
    convert hc.preimage (continuous_subtype_val : Continuous (Subtype.val : U → X.obj.left)) using 1
    ext x
    exact hRange i x.val x.property
  have hproj (i : Fin k) : IsProperMap (d i).projection.hom.left.base :=
    actual_graph_projection_proper (d i) (deg i) (a i) (ha i) (hm i)
  have hfinite (i : Fin k) : ∀ b : (d i).base.obj.left,((d i).projection.hom.left.base ⁻¹' {b}).Finite :=
    actual_graph_projection_finite (d i) (deg i) (a i) (ha i) (hm i)
  let Y : Fin k → SourceReducedComplexSpace := fun i => (commonGraph (d i) (g i) U).source
  let F : ∀ i,Y i ⟶ restrictedBase U := fun i => commonMap (d i) (g i) U
  have hFp : ∀ i,IsProperMap (F i).hom.left.base := fun i =>
    commonMap_proper (d i) (g i) U (hproj i) (hg i) (hclosed i)
  have hFf : ∀ i,∀ x : (restrictedBase U).obj.left,((F i).hom.left.base ⁻¹' {x}).Finite := fun i =>
    commonMap_fibres_finite (d i) (g i) U (hproj i) (hfinite i) (hg i) (hclosed i)
  have hLoc : ∀ x : (restrictedBase U).obj.left,x.val.val.val ∈ ball (0 : ComplexModel n) rQ := by
    intro x
    obtain ⟨z,hzx,_hzV⟩ := hWindow x.val x.property
    exact hzx ▸ z.property
  have hQCont : Continuous (fun x : (restrictedBase U).obj.left => Q x.val.val.val) :=
    hQOn.continuousOn.comp_continuous
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)) hLoc
  have hBiZ : ∀ i,((Subtype.val : ballDomain (n := n) r → ComplexModel n) ⁻¹' B i) ⊆
      ((Subtype.val : ballDomain (n := n) r → ComplexModel n) ⁻¹' Z) := by
    intro i x hx
    exact (hunion x.val x.property).mpr ⟨i,hx⟩
  have hCoverNew : ∀ x : (restrictedBase U).obj.left,∃ i,x.val.val.val ∈ B i :=
    fun x => (hunion x.val.val.val x.val.val.property).mp x.val.property
  have hGood : IsIsoOver (desc Y F) {x | Q x.val.val.val ≠ 0} := by
    exact @actual_family_common_good_inverse n k Z B (ballDomain (n := n) r) hBC hC hBiZ d hcontain g hg hcoord U hPC
      hRange hCoverNew deg a ha hm (fun x => Q x.val.val.val) hQCont
      (fun i j hij x hi hj => hzero x.val.val.val (hLoc x) i j hij hi hj)
      (fun i x hi hx => (hunique x.val.val.val (hLoc x) i hi hx).1)
  refine ⟨k,B,r,hC,hr,hrN,hB,hBC,hunion,hpair,d,deg,a,g,hcontain,hH,hHne,ha,hm,hs,hn,hg,hcoord,
    T,rQ,hCQ,hBCQ,hrQ,(fun i z hz => (hrQΩ hz).2.2 i),
    (fun z hz => (hrQΩ hz).2.1),hT,hHi,hQOn,hrel,hvan,hD,V,hV,hNZ,hNZi,hDense,hDensei,b0,hb0,U,hbU,hWindow,hRange,hPC,hFp,hFf,
    hGood,desc_proper Y F hFp,desc_fibres_finite Y F hFf,?_,coproduct_normal_stalks Y (fun i =>
      commonMap_normal (d i) (g i) U (hn i))⟩
  intro x
  let x0 : U := x
  obtain ⟨i,hi⟩ := (hunion x0.val.val.val x0.val.val.property).mp x0.val.property
  have hx : x ∈ range (F i).hom.left.base := by
    rw [commonMap_range (d i) (g i) U (hs i)]
    exact (hRange i x0.val x0.property).mpr hi
  obtain ⟨p,hp⟩ := hx
  refine ⟨(inclusion Y i).hom.left.base p,?_⟩
  exact (congrArg (fun q : Y i ⟶ restrictedBase U => q.hom.left.base p) (inclusion_desc Y F i)).trans hp

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSeparatedCommonFamily
