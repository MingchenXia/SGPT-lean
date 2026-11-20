import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralPresentation
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNativeOpenImage

/-! Source-only actual integral component packet retaining the literal graph.
Blueprint: prime-nov16-analytic-normalization-original-integral-component-packet.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralComponentPacket
open PrimeNov16AnalyticNormalizationOriginalIntegralPresentation
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalNativeOpenImage
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph

theorem exists_original_integral_component_packet {n : ℕ} {Z B : Set (ComplexModel n)}
    (hB : AnalyticGermDecomposition.IsIrreducibleGerm B) (r0 : ℝ) (hr0 : 0<r0)
    (hZ : IsComplexAnalyticSubset (n := n) {z : ballDomain (n := n) r0 | z.val ∈ Z})
    (hBZ : ∀ z ∈ ball (0 : ComplexModel n) r0,z ∈ B → z ∈ Z) :
    let X := sourceReducedComplexSpaceModel (ballDomain (n := n) r0)
      {z : ballDomain (n := n) r0 | z.val ∈ Z} hZ
    ∃ d : GraphPresentation n B,∃ (deg : Fin d.arity → ℕ)
      (a : Fin d.arity → ℕ → ComplexModel n → ℂ) (g : d.target ⟶ X),
      0<d.radius ∧ ball (0 : ComplexModel n) d.radius ⊆ ball 0 r0 ∧
      (∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ d.denominator z) ∧
      (¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B → d.denominator z=0) ∧
      (∀ i j,j < deg i → DifferentiableOn ℂ (a i j) (ballDomain (n := n) d.radius)) ∧
      (∀ p : d.graph.obj.left,∀ i,GermParametrizationData.monicEval (deg i) (a i)
        (baseProjection n d.arity p.val.val) (fibreProjection n d.arity p.val.val i)=0) ∧
      IsProperMap d.map.hom.left.base ∧
      (∀ t : d.target.obj.left,(d.map.hom.left.base ⁻¹' {t}).Finite) ∧
      Function.Surjective d.map.hom.left.base ∧
      (∀ p : d.source.obj.left,IsDomain (d.source.obj.left.presheaf.stalk p).carrier ∧
        IsIntegrallyClosed (d.source.obj.left.presheaf.stalk p).carrier) ∧
      Topology.IsEmbedding g.hom.left.base ∧
      (∀ t : d.target.obj.left,(g.hom.left.base t).val.val=t.val.val.val) ∧
      ∃ O : Set (ComplexModel n),IsOpen O ∧ (0 : ComplexModel n) ∈ O ∧ O ⊆ ball 0 r0 ∧
        ∀ x : X.obj.left,x.val.val ∈ O →
          (x ∈ range g.hom.left.base ↔ x.val.val ∈ B) := by
  obtain ⟨d,deg,a,hr,hrN,⟨b0,hb0,hbU⟩,hH,hHne,ha,hm,hp,hf,hs,hn⟩ :=
    exists_original_integral_normal_presentation hB (ball_mem_nhds 0 hr0)
  let := d.baseOpen_pc
  have hUV : ballDomain (n := n) d.radius ≤ ballDomain (n := n) r0 := hrN
  have hCD : ∀ c : {z : ballDomain (n := n) d.radius | z.val ∈ B},
      (⟨c.val.val,hUV c.val.property⟩ : ballDomain (n := n) r0) ∈
        {z : ballDomain (n := n) r0 | z.val ∈ Z} :=
    fun c => hBZ c.val.val (hrN c.val.property) c.property
  let g := openNativeMap (ballDomain (n := n) d.radius) (ballDomain (n := n) r0)
    d.carrier_analytic hZ hUV hCD d.baseOpen
  obtain ⟨O,hO,hbO,hOU,hRange⟩ := exists_actual_ambient_range_window
    (ballDomain (n := n) d.radius) (ballDomain (n := n) r0) d.carrier_analytic hZ hUV hCD
    d.baseOpen ⟨b0,hbU⟩
  refine ⟨d,deg,a,g,hr,hrN,hH,hHne,ha,hm,hp,hf,hs,hn,
    openNativeMap_embedding _ _ _ _ _ _ _,?_,O,hO,?_,?_,?_⟩
  · exact openNativeMap_point _ _ _ _ _ _ _
  · simpa only [hb0] using hbO
  · exact fun z hz => hrN (hOU hz)
  · intro x hx
    refine (hRange x hx).trans ?_
    constructor
    · rintro ⟨u,hu,he⟩
      exact he ▸ hu
    · intro hxB
      exact ⟨⟨x.val.val,hOU hx⟩,hxB,rfl⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralComponentPacket
