import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalGraphPresentation
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralCanonicalStalk
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseOnto
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationProperNormalShrink

/-! Actual original monic data and SAME primitive normal graph are manufactured together.
Blueprint: prime-nov16-analytic-normalization-original-integral-presentation.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric TopologicalSpace CategoryTheory
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.HironakaReducedComplexAnalyticSpaces
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralPresentation
open AnalyticGermDecomposition HolGerm
open PrimeNov16AnalyticNormalizationOriginalGraphPresentation
open PrimeNov16AnalyticNormalizationOriginalProperRestriction
open PrimeNov16AnalyticNormalizationOriginalBaseOnto
open PrimeNov16AnalyticNormalizationProperNormalShrink
open PrimeNov16AnalyticNormalizationLocalGraph
open PrimeNov16AnalyticNormalizationDenominatorGraph
open PrimeNov16AnalyticNormalizationGraphFinite
open HironakaActualAnalyticSubspace

private theorem zero_mem_original_irreducible_germ {n : ℕ} {Z : Set (ComplexModel n)}
    (hZ : IsIrreducibleGerm Z) : (0 : ComplexModel n) ∈ Z := by
  by_contra h0
  obtain ⟨s,G,hG,hset⟩ := hZ.1
  have hn : ¬ ∀ i,G i 0=0 := fun h => h0 (hset.self_of_nhds.mpr h)
  push Not at hn
  obtain ⟨i,hi⟩ := hn
  have hne : ∀ᶠ z in 𝓝 (0 : ComplexModel n),G i z ≠ 0 :=
    ((hG i).self_of_nhds.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hi
  apply hZ.2.1
  apply eventuallyEq_set.mpr
  filter_upwards [hset,hne] with z hz hzi
  constructor
  · intro hzZ
    exact (hzi ((hz.mp hzZ) i)).elim
  · intro hzE
    exact hzE.elim

theorem exists_original_integral_normal_presentation {n : ℕ} {Z N : Set (ComplexModel n)}
    (hZ : IsIrreducibleGerm Z) (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ d : GraphPresentation n Z,∃ (deg : Fin d.arity → ℕ)
      (a : Fin d.arity → ℕ → ComplexModel n → ℂ),
      0<d.radius ∧ ball (0 : ComplexModel n) d.radius ⊆ N ∧
      (∃ b : d.base.obj.left,b.val.val=0 ∧ b ∈ d.baseOpen) ∧
      (∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ d.denominator z) ∧
      (¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ Z → d.denominator z=0) ∧
      (∀ i j,j < deg i → DifferentiableOn ℂ (a i j) (ballDomain (n := n) d.radius)) ∧
      (∀ p : d.graph.obj.left,∀ i,GermParametrizationData.monicEval (deg i) (a i)
        (baseProjection n d.arity p.val.val) (fibreProjection n d.arity p.val.val i)=0) ∧
      IsProperMap d.map.hom.left.base ∧
      (∀ b : d.target.obj.left,(d.map.hom.left.base ⁻¹' {b}).Finite) ∧
      Function.Surjective d.map.hom.left.base ∧
      ∀ p : d.source.obj.left,IsDomain (d.source.obj.left.presheaf.stalk p).carrier ∧
        IsIntegrallyClosed (d.source.obj.left.presheaf.stalk p).carrier := by
  obtain ⟨k,s,h,g,polys,hh,hs,hpolys,H,hH,G,hG,a,ha,r,hHOn,hGOn,hC,
    hr,hrN,hHclass,hGclass,_haclass,haOn,hnonzero,hrel,hproper,hfinite⟩ :=
    exists_original_proper_finite_generator_graph hZ hN
  have hm : ∀ x : {z : ballDomain (n := n) r | z.val ∈ Z},H x.val.val ≠ 0 → ∀ i,
      GermParametrizationData.monicEval (polys i).natDegree (a i) x.val.val (G i x.val.val/H x.val.val)=0 := by
    intro x hx i
    exact hrel x.val.val x.property x.val.property hx i
  have hcentral (p : graphClosure (ballDomain (n := n) r)
      {z : ballDomain (n := n) r | z.val ∈ Z} H G) (hp : baseProjection n k p.val.val=0) :
      IsDomain ((actualSubspaceSheaf (n := n+k) (graphClosure (ballDomain (n := n) r)
        {z : ballDomain (n := n) r | z.val ∈ Z} H G)).presheaf.stalk p).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := n+k) (graphClosure (ballDomain (n := n) r)
        {z : ballDomain (n := n) r | z.val ∈ Z} H G)).presheaf.stalk p).carrier := by
    obtain ⟨e,_he⟩ := PrimeNov16AnalyticNormalizationCentralCanonicalStalk.exists_actual_central_canonical_equiv
      hZ (ballDomain (n := n) r) hC H G hHOn hGOn hH hG p hp
        (fun i => (polys i).natDegree) a haOn hm h hh s hs hHclass (by
          intro i
          rw [hGclass]
          exact (hpolys i).1.symm)
    let : (vanishingIdeal Z).IsPrime := (isIrreducibleGerm_iff_isPrime hZ.1).mp hZ
    let : IsIntegrallyClosed (integralClosure (HolGerm (ComplexModel n) ⧸ vanishingIdeal Z)
        (FractionRing (HolGerm (ComplexModel n) ⧸ vanishingIdeal Z))) :=
      PrimeNov16AnalyticIntegralClosure.normal_analytic_germ_integralClosure (vanishingIdeal Z)
    exact ⟨Function.Injective.isDomain e e.injective,IsIntegrallyClosed.of_equiv e.symm⟩
  let B := (sourceReducedComplexSpaceModel (ballDomain (n := n) r)
    {z : ballDomain (n := n) r | z.val ∈ Z} hC).obj.left
  let S := graphClosure (ballDomain (n := n) r) {z : ballDomain (n := n) r | z.val ∈ Z} H G
  let f : S → B := (projection (ballDomain (n := n) r) hC H G hHOn hGOn).hom.left.base
  let b0 : B := ⟨⟨0,mem_ball_self hr⟩,zero_mem_original_irreducible_germ hZ⟩
  have hc : ∀ p : S,f p=b0 → p ∈ originalNormalLocus (n := n+k) S := by
    intro p hp
    have hproj : (f p).val.val=baseProjection n k p.val.val :=
      congrArg Subtype.val (projection_apply (ballDomain (n := n) r) hC H G hHOn hGOn p)
    have hz : (f p).val.val=0 := congrArg (fun b : B => b.val.val) hp
    exact hcentral p (hproj.symm.trans hz)
  obtain ⟨W,hW,hbW,honto⟩ := exists_original_open_onto hZ (ballDomain (n := n) r)
    hC b0 rfl H G hHOn hGOn hH hnonzero hproper
  have hWB : IsOpen {b : B | b.val ∈ W} := hW.preimage continuous_subtype_val
  obtain ⟨V,hV,hbV,hVN,_hpV,_hfV,hNormal⟩ := exists_actual_proper_finite_normal_full_preimage
    S (graphClosure_analytic (ballDomain (n := n) r) hC H G hHOn hGOn) f hproper hfinite b0 hc
      (hWB.mem_nhds hbW)
  let U : Opens B := ⟨V,hV⟩
  let d : GraphPresentation n Z := ⟨k,r,H,G,hHOn,hGOn,hC,U⟩
  let : ParacompactSpace U := d.baseOpen_pc
  have hsurj : Function.Surjective (restrictedMap
      (projection (ballDomain (n := n) r) hC H G hHOn hGOn) hproper U).hom.left.base := by
    intro b
    let b' : U := b
    obtain ⟨p,hp⟩ := honto b'.val (hVN b'.property)
    have hp' : f (show S from p)=b'.val := hp
    have hpV : (show S from p) ∈ f ⁻¹' V := by
      change f (show S from p) ∈ V
      exact hp'.symm ▸ b'.property
    let p' : sourceOpen (projection (ballDomain (n := n) r) hC H G hHOn hGOn) U := ⟨p,hpV⟩
    refine ⟨p',Subtype.ext ?_⟩
    exact (restrictedMap_point _ hproper U p').trans hp
  refine ⟨d,(fun i => (polys i).natDegree),a,hr,hrN,⟨b0,rfl,hbV⟩,hH,hnonzero,haOn,?_,
    restrictedMap_proper _ hproper U,restrictedMap_fibres_finite _ hproper U hfinite,hsurj,
    restrictedSource_normal_stalks _ hproper U hNormal⟩
  intro p i
  exact monic_on_graphClosure (ballDomain (n := n) r) H G
    (fun i => (polys i).natDegree) a haOn hm p.property i

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalIntegralPresentation
