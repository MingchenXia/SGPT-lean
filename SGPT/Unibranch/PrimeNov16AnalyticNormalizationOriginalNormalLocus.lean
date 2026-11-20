import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalNeighborhood
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDiscriminant
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartRegularity
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback

/-! Source-only normal locus openness for ENTIRE SAME original analytic carriers in ANY dimension.
Blueprint: prime-nov16-analytic-normalization-original-normal-locus.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalLocus
open PrimeNov16AnalyticNormalizationOriginalNormalNeighborhood
open PrimeNov16AnalyticNormalizationOriginalDiscriminant
open PrimeNov16AnalyticNormalizationOriginalChartVanishing
open PrimeNov16AnalyticNormalizationOriginalChartRegularity
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback
open HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceOpenRestriction
open HironakaHolomorphicJetRankLoci HironakaSmoothCentreRealDomainActualSheafStalk
open OkaRelationSheaf HolGerm AnalyticDescendingChain

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem exists_original_normal_locus_open (C : Set M)
    (hC : IsComplexAnalyticSubset (n := n) C) (x : C)
    [IsDomain ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier]
    [IsIntegrallyClosed ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier]
    {N : Set M} (hN : N ∈ 𝓝 x.val) :
    ∃ U : Set M,IsOpen U ∧ x.val ∈ U ∧ U ⊆ N ∧ ∀ y : C,y.val ∈ U →
      IsDomain ((actualSubspaceSheaf (n := n) C).presheaf.stalk y).carrier ∧
        IsIntegrallyClosed ((actualSubspaceSheaf (n := n) C).presheaf.stalk y).carrier := by
  let e := complexChartAt (n := n) x.val
  let Z := chartGerm (n := n) C x.val
  let PG := wholeChartStalkIdeal (vanishingIdeal (n := n) C) x.val x.val (mem_chart_source _ x.val)
  let E0 := actualSubspaceStalkChartEquiv (n := n) C x
  let : IsDomain (HolGerm (ComplexModel n) ⧸ PG) := Function.Injective.isDomain E0.symm E0.symm.injective
  have hPGprime : PG.IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hPG : PG=AnalyticGermDecomposition.vanishingIdeal Z := original_whole_chart_vanishing C x.val
  have hprime : (AnalyticGermDecomposition.vanishingIdeal Z).IsPrime := hPG ▸ hPGprime
  have hZg := isAnalyticGerm_chartGerm hC x.val
  have hIrr : AnalyticGermDecomposition.IsIrreducibleGerm Z :=
    (AnalyticGermDecomposition.isIrreducibleGerm_iff_isPrime hZg).mpr hprime
  obtain ⟨d,Δ,D,hΔ,h0Δ,_hΔN,hDg,hDn,_hDcarrier,_hdense,hregular⟩ :=
    exists_original_regular_discriminant hIrr (show (univ : Set (ComplexModel n)) ∈ 𝓝 0 from univ_mem)
  have hgood : ∃ z : ComplexModel n,z ∈ Z ∩ Δ ∧ D z ≠ 0 := by
    by_contra hbad
    apply hDn
    filter_upwards [hΔ.mem_nhds h0Δ] with z hz hzZ
    by_contra hzD
    exact hbad ⟨z,⟨hzZ,hz⟩,hzD⟩
  obtain ⟨z,hz,hzD⟩ := hgood
  have hdim : d ≤ n := (hregular z hz hzD).1
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hdim
  have hx : x.val ∈ e.val.source := mem_complexChartAt_source x.val
  let F : M → ℂ := fun y => D (e.val y-e.val x.val)
  have hD' : HolAt D (e.val x.val-e.val x.val) := by simpa only [sub_self] using hDg
  have hF : HolomorphicAt (d+t) F x.val := CartanLocalReduction.holomorphicAt_comp_chart hx
    (hD'.comp (φ := fun w : ComplexModel (d+t) => w-e.val x.val) (y := e.val x.val)
      (continuous_id.sub continuous_const) (fun _ => differentiableAt_id.sub (differentiableAt_const _)))
  have hcoord : Tendsto (fun y => e.val y-e.val x.val) (𝓝 x.val) (𝓝 (0 : ComplexModel (d+t))) := by
    simpa only [sub_self] using (e.val.continuousAt hx).sub_const (e.val x.val)
  have hFs : ∀ᶠ y in 𝓝 x.val,ContMDiffAt 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ F y :=
    hF.eventually.mono fun _y hy => contMDiffAt_of_eventually_mdifferentiableAt hy
  obtain ⟨U,hUe,hU,hxU⟩ := mem_nhds_iff.mp (hFs.and
    ((eventually_of_mem (e.val.open_source.mem_nhds hx) fun _ hy => hy).and
      ((hcoord.eventually (eventually_of_mem (hΔ.mem_nhds h0Δ) fun _ hy => hy)).and
        (eventually_of_mem hN fun _ hy => hy))))
  have hshift : Tendsto (fun w : ComplexModel (d+t) => w+e.val x.val) (𝓝 0) (𝓝 (e.val x.val)) :=
    (continuous_add_const (e.val x.val)).tendsto' 0 _ (zero_add _)
  have htarget : ∀ᶠ w in 𝓝 (0 : ComplexModel (d+t)),w+e.val x.val ∈ e.val.target :=
    hshift.eventually (e.val.open_target.mem_nhds (e.val.map_source hx))
  have hFread : chartTranslatedGerm x.val x.val (mem_chart_source _ x.val) F hF=HolGerm.mk D hDg := by
    have hFc : ∀ᶠ w in 𝓝 (0 : ComplexModel (d+t)),DifferentiableAt ℂ
        (fun w => F (e.val.symm (w+e.val x.val))) w :=
      translated_holomorphic (e.val x.val) (CartanLocalReduction.holAt_comp_chart_symm hx hF)
    change HolGerm.mk (fun w => F (e.val.symm (w+e.val x.val))) hFc=HolGerm.mk D hDg
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [htarget] with w hw
    change D (e.val (e.val.symm (w+e.val x.val))-e.val x.val)=D w
    rw [e.val.right_inv hw,add_sub_cancel_right]
  have hFnz : originalFunctionImage C x F hF ≠ 0 := by
    intro hz
    have he : E0 (originalFunctionImage C x F hF)=
        Ideal.Quotient.mk PG (chartTranslatedGerm x.val x.val (mem_chart_source _ x.val) F hF) :=
      E0.apply_symm_apply _
    have hzero : Ideal.Quotient.mk PG (chartTranslatedGerm x.val x.val (mem_chart_source _ x.val) F hF)=0 := by
      rw [← he,hz,map_zero]
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hPG,hFread] at hmem
    exact hDn (AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hmem)
  let V : Opens M := ⟨U,hU⟩
  let CV : Set V := (Subtype.val : V → M) ⁻¹' C
  let xv : CV := ⟨⟨x.val,hxU⟩,x.property⟩
  let Q : V → ℂ := F ∘ Subtype.val
  have hCV : IsComplexAnalyticSubset (n := d+t) CV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hC V
  have hQ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ Q := fun y =>
    contMDiffAt_subtype_iff.mpr (hUe y.property).1
  have hQreg : ∀ y ∈ CV,Q y ≠ 0 → RegularAtDim (n := d+t) CV y d := by
    intro y hy hyQ
    have hys := (hUe y.property).2.1
    have hwZ : e.val y.val-e.val x.val ∈ Z := by
      change e.val y.val-e.val x.val+e.val x.val ∈ e.val.target ∧
        e.val.symm (e.val y.val-e.val x.val+e.val x.val) ∈ C
      rw [sub_add_cancel,e.val.left_inv hys]
      exact ⟨e.val.map_source hys,hy⟩
    have hr := hregular _ ⟨hwZ,(hUe y.property).2.2.1⟩ hyQ
    have hrZ : RegularAtDim (n := d+t) Z (e.val y.val-e.val x.val) d :=
      RegularPointDimension.regularAtDim_of_inter_eq hΔ (hUe y.property).2.2.1
        (by rw [Set.inter_assoc,Set.inter_self]) hr
    have hrC := original_regular_of_chartGerm C x.val y.val hys hrZ
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hrC
  let E : ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier ≃+*
      ((actualSubspaceSheaf (n := d+t) CV).presheaf.stalk xv).carrier :=
    actualOpenSubspaceStalkEquiv (n := d+t) C V xv
  let : IsDomain ((actualSubspaceSheaf (n := d+t) CV).presheaf.stalk xv).carrier :=
    Function.Injective.isDomain E.symm E.symm.injective
  let : IsIntegrallyClosed ((actualSubspaceSheaf (n := d+t) CV).presheaf.stalk xv).carrier :=
    IsIntegrallyClosed.of_equiv E
  have hread : E (originalFunctionImage C x F hF)=originalFunctionImage CV xv Q
      (Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y) := original_open_function_image C V xv F hF
  have hQne : originalFunctionImage CV xv Q
      (Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y) ≠ 0 := by
    intro hz
    apply hFnz
    apply E.injective
    rw [map_zero,hread]
    exact hz
  obtain ⟨O,hO,hxO,hNormal⟩ := exists_actual_original_normal_neighborhood CV hCV Q hQ hQreg xv hQne
  refine ⟨(Subtype.val : V → M) '' O,hU.isOpenMap_subtype_val _ hO,⟨xv.val,hxO,rfl⟩,?_,?_⟩
  · rintro w ⟨v,_hv,rfl⟩
    exact (hUe v.property).2.2.2
  · intro y hy
    obtain ⟨v,hv,hvy⟩ := hy
    let yv : CV := ⟨v,by change v.val ∈ C; rw [hvy]; exact y.property⟩
    obtain ⟨hd,hn⟩ := hNormal yv hv
    let := hd
    let := hn
    let ey := actualOpenSubspaceStalkEquiv (n := d+t) C V yv
    have hd' : IsDomain ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk
        ((actualOpenSubspaceMap (n := d+t) C V).base yv)).carrier := Function.Injective.isDomain ey ey.injective
    have hn' : IsIntegrallyClosed ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk
        ((actualOpenSubspaceMap (n := d+t) C V).base yv)).carrier := IsIntegrallyClosed.of_equiv ey.symm
    have hpt : (actualOpenSubspaceMap (n := d+t) C V).base yv=y := Subtype.ext hvy
    exact Eq.mp (congrArg (fun p : C => IsDomain ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk p).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk p).carrier) hpt) ⟨hd',hn'⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalLocus
