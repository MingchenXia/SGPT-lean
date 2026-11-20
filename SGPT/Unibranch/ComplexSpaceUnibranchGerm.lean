import SGPT.Unibranch.ComplexSpaceLocalEmbedding
import SGPT.Foundations.Analysis.Pending.AnalyticDescendingChain
import SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace

/-! Actual original unibranch stalks produce irreducibility of their SAME
analytic carrier germs. No Hironaka geometry is developed. Blueprint:
complex-space-unibranch-germ.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
open SGPT.Foundations.Analysis.Pending.HironakaActualAnalyticSubspace
open SGPT.Foundations.Analysis.Pending.AnalyticGermDecomposition
namespace SGPT.Unibranch
namespace AnalyticChartGerm
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Complete original ideal/germ dictionary; both actual representative
maps are retained. Generic analytic proof reused without engine credit. -/
theorem wholeChartStalkIdeal_eq_chartGerm (W : Set M) (p : M) :
    wholeChartStalkIdeal (vanishingIdeal (n := n) W) p p (mem_chart_source (ComplexModel n) p) =
      AnalyticGermDecomposition.vanishingIdeal (AnalyticDescendingChain.chartGerm (n := n) W p) := by
  let e := chartAt (ComplexModel n) p
  let q := e p
  have hpS : p ∈ e.source := mem_chart_source (ComplexModel n) p
  have hqT : q ∈ e.target := e.map_source hpS
  have htAdd : Tendsto (fun z : ComplexModel n => z+q) (𝓝 0) (𝓝 q) := by
    exact (continuous_add_const q).tendsto' 0 q (zero_add q)
  have htInv : Tendsto e.symm (𝓝 q) (𝓝 p) := by
    have h := (e.continuousAt_symm hqT).tendsto
    change Tendsto e.symm (𝓝 q) (𝓝 (e.symm (e p))) at h
    rw [e.left_inv hpS] at h
    exact h
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨f,hf,hfW,rfl⟩
    change HolGerm.mk (fun z => f (e.symm (z+q)))
      (translated_holomorphic q (CartanLocalReduction.holAt_comp_chart_symm hpS hf)) ∈ _
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    have ht := (htInv.comp htAdd).eventually hfW.2
    filter_upwards [ht] with z hz hzA
    exact hz hzA.2
  · intro g hg
    obtain ⟨f,hf,rfl⟩ := HolGerm.exists_eq_mk g
    have hv := AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hg
    let F : M → ℂ := fun x => f (e x-q)
    have htSub : Tendsto (fun w : ComplexModel n => w-q) (𝓝 q) (𝓝 0) := by
      have hc : Continuous (fun w : ComplexModel n => w-q) := continuous_id.sub continuous_const
      exact hc.tendsto' q 0 (sub_self q)
    have hfd : ∀ᶠ w in 𝓝 q, DifferentiableAt ℂ (fun z => f (z-q)) w := by
      filter_upwards [htSub.eventually hf] with w hw
      exact hw.comp w (differentiableAt_id.sub_const q)
    have hF : HolomorphicAt n F p := CartanLocalReduction.holomorphicAt_comp_chart hpS hfd
    have htChart : Tendsto (fun x : M => e x-q) (𝓝 p) (𝓝 0) := by
      have hc : ContinuousAt (fun _ : M => q) p := continuousAt_const
      have h := ((e.continuousAt hpS).sub hc).tendsto
      change Tendsto (fun x : M => e x-q) (𝓝 p) (𝓝 (e p-q)) at h
      simpa only [q,sub_self] using h
    have hFW : (vanishingIdeal (n := n) W).mem p F := by
      refine ⟨hF,?_⟩
      filter_upwards [htChart.eventually hv,e.open_source.mem_nhds hpS] with x hx hxs hxW
      apply hx
      change e x-q+q ∈ e.target ∩ e.symm ⁻¹' W
      rw [sub_add_cancel]
      exact ⟨e.map_source hxs,by simpa only [mem_preimage,e.left_inv hxs] using hxW⟩
    have he : chartTranslatedGerm p p (mem_chart_source (ComplexModel n) p) F hF = HolGerm.mk f hf := by
      unfold chartTranslatedGerm translatedGerm
      apply HolGerm.mk_eq_mk_iff.mpr
      filter_upwards [htAdd.eventually (e.open_target.mem_nhds hqT)] with z hz
      change f (e (e.symm (z+q))-q) = f z
      rw [e.right_inv hz,add_sub_cancel_right]
    exact Ideal.subset_span ⟨F,hF,hFW,he.symm⟩

end AnalyticChartGerm
namespace LocalEmbedding

/-- Original unibranchness internally supplies the prime whole quotient
and hence irreducibility of the SAME actual analytic carrier chart germ. -/
theorem isIrreducibleGerm_of_isUnibranch {X : SourceReducedComplexSpace}
    (hX : X.IsUnibranch) (e : LocalEmbedding X) (c : e.carrier) :
    IsIrreducibleGerm (AnalyticDescendingChain.chartGerm (n := e.dim) e.carrier c.val) := by
  let singularUnibranchChartImmersion : LocallyRingedSpace.IsOpenImmersion e.map := e.isOpenImmersion
  let E := ((asIso (e.map.stalkMap c)).commRingCatIsoToRingEquiv).trans
    (actualSubspaceStalkChartEquiv (n := e.dim) e.carrier c)
  let singularOriginalUnibranchStalkDomain :
      IsDomain (X.obj.left.presheaf.stalk (e.map.base c)).carrier := (hX (e.map.base c)).1
  have hquot : IsDomain (HolGerm (ComplexModel e.dim) ⧸
      wholeChartStalkIdeal (vanishingIdeal (n := e.dim) e.carrier) c.val c.val
        (mem_chart_source (ComplexModel e.dim) c.val)) :=
    Function.Injective.isDomain E.symm E.symm.injective
  have hprime := (Ideal.Quotient.isDomain_iff_prime _).mp hquot
  rw [AnalyticChartGerm.wholeChartStalkIdeal_eq_chartGerm] at hprime
  exact (isIrreducibleGerm_iff_isPrime
    (AnalyticDescendingChain.isAnalyticGerm_chartGerm e.analytic c.val)).mpr hprime

end LocalEmbedding
end SGPT.Unibranch
