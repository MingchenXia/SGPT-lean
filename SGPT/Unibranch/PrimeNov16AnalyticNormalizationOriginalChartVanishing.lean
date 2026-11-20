import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartDictionary
import SGPT.Foundations.Analysis.Pending.AnalyticDescendingChain

/-! Entire actual original carrier ideal is the literal actual centered chart-germ vanishing ideal.
Blueprint: prime-nov16-analytic-normalization-original-chart-vanishing.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartVanishing
open HironakaHolomorphicJetRankLoci HolGerm AnalyticDescendingChain OkaRelationSheaf
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem original_whole_chart_vanishing (C : Set M) (x : M) :
    wholeChartStalkIdeal (vanishingIdeal (n := n) C) x x (mem_chart_source _ x) =
      AnalyticGermDecomposition.vanishingIdeal (chartGerm (n := n) C x) := by
  let e := (complexChartAt (n := n) x).val
  let Inv := fun w : ComplexModel n => e.symm (w+e x)
  have hx : x ∈ e.source := mem_chart_source _ x
  have hshift : Tendsto (fun w : ComplexModel n => w+e x) (𝓝 0) (𝓝 (e x)) :=
    (continuous_add_const (e x)).tendsto' 0 _ (zero_add _)
  have htarget : ∀ᶠ w in 𝓝 (0 : ComplexModel n),w+e x ∈ e.target :=
    hshift.eventually (e.open_target.mem_nhds (e.map_source hx))
  have hInv : Tendsto Inv (𝓝 0) (𝓝 x) := by
    simpa only [Inv,Function.comp_def,e.left_inv hx] using
      (e.continuousAt_symm (e.map_source hx)).tendsto.comp hshift
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨F,hF,hFC,rfl⟩
    have hFc : ∀ᶠ w in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (fun w => F (e.symm (w+e x))) w :=
      translated_holomorphic (e x) (CartanLocalReduction.holAt_comp_chart_symm hx hF)
    change HolGerm.mk (fun w => F (e.symm (w+e x))) hFc ∈ _
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    filter_upwards [hInv.eventually hFC.2] with w hw hwC
    exact hw hwC.2
  · intro a ha
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk a
    let H : M → ℂ := fun y => f (e y-e x)
    have hf' : HolAt f (e x-e x) := by simpa only [sub_self] using hf
    have hH : HolomorphicAt n H x := CartanLocalReduction.holomorphicAt_comp_chart hx
      (hf'.comp (φ := fun w : ComplexModel n => w-e x) (y := e x)
        (continuous_id.sub continuous_const)
        (fun _ => differentiableAt_id.sub (differentiableAt_const _)))
    have hsub : Tendsto (fun y => e y-e x) (𝓝 x) (𝓝 (0 : ComplexModel n)) := by
      simpa only [sub_self] using (e.continuousAt hx).sub_const (e x)
    have hHC : (vanishingIdeal (n := n) C).mem x H := by
      refine ⟨hH,?_⟩
      filter_upwards [e.open_source.mem_nhds hx,
        hsub.eventually (AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp ha)] with y hy hfy hyC
      apply hfy
      change e y-e x+e x ∈ e.target ∧ e.symm (e y-e x+e x) ∈ C
      simpa only [sub_add_cancel,e.left_inv hy] using And.intro (e.map_source hy) hyC
    have hread : chartTranslatedGerm x x (mem_chart_source _ x) H hH=HolGerm.mk f hf := by
      have hHc : ∀ᶠ w in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (fun w => H (e.symm (w+e x))) w :=
        translated_holomorphic (e x) (CartanLocalReduction.holAt_comp_chart_symm hx hH)
      change HolGerm.mk (fun w => H (e.symm (w+e x))) hHc=HolGerm.mk f hf
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [htarget] with w hw
      change f (e (e.symm (w+e x))-e x)=f w
      rw [e.right_inv hw,add_sub_cancel_right]
    exact Ideal.subset_span ⟨H,hH,hHC,hread.symm⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalChartVanishing
