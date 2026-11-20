import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralComponentPacket
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchWindow

/-! Source-only finite reduced family retaining SAME literal integral graph presentations.
Blueprint: prime-nov16-analytic-normalization-original-reduced-presentations.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedPresentations
open PrimeNov16AnalyticNormalizationOriginalIntegralComponentPacket
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalBranchWindow
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph

theorem exists_original_reduced_presentations {n : ℕ} {Z N : Set (ComplexModel n)}
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
        (∀ i,0<(d i).radius) ∧
        (∀ i,ball (0 : ComplexModel n) (d i).radius ⊆ ball 0 r) ∧
        (∀ i,∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (d i).denominator z) ∧
        (∀ i,¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → (d i).denominator z=0) ∧
        (∀ i j l,l < deg i j → DifferentiableOn ℂ (a i j l) (ballDomain (n := n) (d i).radius)) ∧
        (∀ i,∀ p : (d i).graph.obj.left,∀ j,GermParametrizationData.monicEval (deg i j) (a i j)
          (baseProjection n (d i).arity p.val.val) (fibreProjection n (d i).arity p.val.val j)=0) ∧
        (∀ i,IsProperMap (d i).map.hom.left.base) ∧
        (∀ i,∀ t : (d i).target.obj.left,((d i).map.hom.left.base ⁻¹' {t}).Finite) ∧
        (∀ i,Function.Surjective (d i).map.hom.left.base) ∧
        (∀ i,∀ p : (d i).source.obj.left,IsDomain ((d i).source.obj.left.presheaf.stalk p).carrier ∧
          IsIntegrallyClosed ((d i).source.obj.left.presheaf.stalk p).carrier) ∧
        (∀ i,Topology.IsEmbedding (g i).hom.left.base) ∧
        (∀ i,∀ t : (d i).target.obj.left,((g i).hom.left.base t).val.val=t.val.val.val) ∧
        ∃ b0 : X.obj.left,b0.val.val=0 ∧ ∃ U : Opens X.obj.left,b0 ∈ U ∧
          ParacompactSpace U ∧
          ∀ i,∀ x : X.obj.left,x ∈ U → (x ∈ range (g i).hom.left.base ↔ x.val.val ∈ B i) := by
  obtain ⟨k,B,r,hr,hrN,hB,hC,hBC,hunion,hBZ,hpair⟩ := exists_original_branch_window hZ hN
  let X := sourceReducedComplexSpaceModel (ballDomain (n := n) r)
    {z : ballDomain (n := n) r | z.val ∈ Z} hC
  have packets := fun i : Fin k => exists_original_integral_component_packet (hB i) r hr hC (hBZ i)
  choose d deg a g hdr hcontain hH hHne ha hm hp hf hs hn hg hcoord O hO h0O _hOr hRange using packets
  let b0 : X.obj.left := ⟨⟨0,mem_ball_self hr⟩,h0⟩
  let U : Opens X.obj.left := ⟨{x | ∀ i,x.val.val ∈ O i},by
    have ho : IsOpen (⋂ i,{x : X.obj.left | x.val.val ∈ O i}) :=
      isOpen_iInter_of_finite fun i => (hO i).preimage
        (continuous_subtype_val.comp continuous_subtype_val)
    convert ho using 1
    ext x
    simp⟩
  have hPC : ParacompactSpace U := by
    change ParacompactSpace {x : {z : ballDomain (n := n) r | z.val ∈ Z} // ∀ i,x.val.val ∈ O i}
    infer_instance
  exact ⟨k,B,r,hC,hr,hrN,hB,hBC,hunion,hpair,d,deg,a,g,hdr,hcontain,hH,hHne,ha,hm,hp,hf,hs,hn,hg,
    hcoord,b0,rfl,U,h0O,hPC,fun i x hx => hRange i x (hx i)⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedPresentations
