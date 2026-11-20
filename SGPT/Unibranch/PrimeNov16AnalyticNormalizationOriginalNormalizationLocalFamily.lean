import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSeparatedCommonFamily
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalFamilyBimeromorphic

/-! ONLY original germ inputs manufacture actual normal finite proper onto bimeromorphic local family.
Blueprint: prime-nov16-analytic-normalization-original-normalization-local-family.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalizationLocalFamily
open PrimeNov16AnalyticNormalizationOriginalSeparatedCommonFamily
open PrimeNov16AnalyticNormalizationOriginalFamilyBimeromorphic
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalCommonGraphMap
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph
open HironakaG1NativeDisjointCoproduct
open SourceReducedComplexSpace

theorem exists_original_normalization_local_family {n : ℕ} {Z N : Set (ComplexModel n)}
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
          IsProperBimeromorphic (desc Y F) ∧
          Dense {x : (restrictedBase U).obj.left | Q x.val.val.val ≠ 0} ∧
          Dense ((desc Y F).hom.left.base ⁻¹' {x | Q x.val.val.val ≠ 0}) ∧
          IsProperMap (desc Y F).hom.left.base ∧
          (∀ x : (restrictedBase U).obj.left,((desc Y F).hom.left.base ⁻¹' {x}).Finite) ∧
          Function.Surjective (desc Y F).hom.left.base ∧
          ∀ y : (coproduct Y).obj.left,IsDomain ((coproduct Y).obj.left.presheaf.stalk y).carrier ∧
            IsIntegrallyClosed ((coproduct Y).obj.left.presheaf.stalk y).carrier := by
  obtain ⟨k,B,r,hC,hr,hrN,hB,hBC,hunion,hpair,d,deg,a,g,hcontain,hH,hHne,ha,hm,hs,hn,hg,hcoord,
    T,rQ,hCQ,hBCQ,hrQ,hQraw,hQinitial,hT,hHi,hQOn,hrel,hvan,hD,V,hV,hNZ,hNZi,hDense,hDensei,
    b0,hb0,U,hbU,hWindow,hRange,hPC,hFp,hFf,hGood,hProper,hFinite,hSurj,hNormal⟩ :=
    exists_original_separated_common_family hZ h0 hN
  let : ParacompactSpace U := hPC
  let Q : ComplexModel n → ℂ := fun z => ∑ i,T i z*(d i).denominator z
  let Y : Fin k → SourceReducedComplexSpace := fun i => (commonGraph (d i) (g i) U).source
  let F : ∀ i,Y i ⟶ restrictedBase U := fun i => commonMap (d i) (g i) U
  have hland : ∀ p : {z : ballDomain (n := n) r | z.val ∈ Z},p ∈ U →
      p.val.val ∈ ballDomain (n := n) rQ := by
    intro p hp
    obtain ⟨z,hzp,_hzV⟩ := hWindow p hp
    exact hzp ▸ z.property
  have hVland : ∀ p : {z : ballDomain (n := n) r | z.val ∈ Z},∀ hp : p ∈ U,
      (⟨p.val.val,hland p hp⟩ : ballDomain (n := n) rQ) ∈ V := by
    intro p hp
    obtain ⟨z,hzp,hzV⟩ := hWindow p hp
    have he : z=(⟨p.val.val,hland p hp⟩ : ballDomain (n := n) rQ) := Subtype.ext hzp
    exact he ▸ hzV
  have hBim := @actual_family_bimeromorphic_of_original_window n k Z B
    (ballDomain (n := n) r) (ballDomain (n := n) rQ) hQinitial hC hCQ hBCQ d hQraw g hcoord U hPC
    V Q hQOn hland hVland hNZ hNZi hProper hGood
  exact ⟨k,B,r,hC,hr,hrN,hB,hBC,hunion,hpair,d,deg,a,g,hcontain,hH,hHne,ha,hm,hs,hn,hg,hcoord,
    T,rQ,hCQ,hBCQ,hrQ,hQraw,hQinitial,hT,hHi,hQOn,hrel,hvan,hD,V,hV,hNZ,hNZi,hDense,hDensei,
    b0,hb0,U,hbU,hWindow,hRange,hPC,hFp,hFf,hGood,hBim.1,hBim.2.1,hBim.2.2,hProper,hFinite,hSurj,hNormal⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalizationLocalFamily
