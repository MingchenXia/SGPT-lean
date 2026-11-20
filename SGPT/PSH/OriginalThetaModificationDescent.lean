import SGPT.PSH.OriginalInverseHolomorphicPullback
import SGPT.Toric.RelativeThetaCriterion

/-! Whole original varying-atlas theta-PSH descent from compact actual
proper-bimeromorphic geometry, through genuine inverse/extension producers. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.VariableComplexAtlas
open Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology ContDiff
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {A : VariableComplexAtlas X} {B : VariableComplexAtlas Y}

/-- Actual closed image and dense analytic complement prove surjectivity
of an ORIGINAL proper modification, without countability or nonemptiness. -/
theorem IsAtlasAnalyticModification.surjective
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f) : Function.Surjective f := by
  have hproper := hf.2.1
  obtain ⟨_,_,E,S,s,_,_,_,hSi,_,_,hright,_⟩ := hf
  have hsub : Sᶜ⊆range f := fun y hy => ⟨s y,hright y hy⟩
  have hdense : Dense (range f) := (interior_eq_empty_iff_dense_compl.mp hSi).mono hsub
  have hclosed : IsClosed (range f) := by
    simpa only [image_univ] using hproper.isClosedMap univ isClosed_univ
  have hrange : range f=univ := hclosed.closure_eq.symm.trans hdense.closure_eq
  intro y
  have hy : y∈range f := by rw [hrange]; trivial
  exact hy

/-- Original universal theta-PSH supplies a genuine finite global upper
bound from compactness. The empty manifold is explicitly retained. -/
theorem IsThetaPSH.exists_global_upper_bound_original [CompactSpace X]
    {θ : AtlasClosedRealOneOneForm A} {w : X → EReal} (hw : A.IsThetaPSH θ w) :
    ∃ C : ℝ,∀ x,w x≤(C : EReal) := by
  rcases isEmpty_or_nonempty X with hX|hX
  · exact ⟨0,fun x => (hX.false x).elim⟩
  obtain ⟨x,_,hmax⟩ := (hw.upperSemicontinuous.upperSemicontinuousOn univ).exists_isMaxOn
    (Set.univ_nonempty : (univ : Set X).Nonempty) isCompact_univ
  obtain ⟨C,hC,_⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr (hw.1 x))
  exact ⟨C,fun y => (hmax (mem_univ y)).trans hC.le⟩

/-- Actual original theta-PSH functions agreeing off an analytic thin set
agree at EVERY original point. Genuine canonical extension and chart-null
rigidity prove the exceptional values, including all bottom poles. -/
theorem IsThetaPSH.eq_of_eq_off_original_analytic
    {θ : AtlasClosedRealOneOneForm A} {E : Set X} {w z : X → EReal}
    (hw : A.IsThetaPSH θ w) (hz : A.IsThetaPSH θ z)
    (hE : A.HasAnalyticChartEquations E) (hEi : interior E=∅)
    (heq : EqOn w z Eᶜ) : w=z := by
  have hoff := hw.isThetaPSHOn Eᶜ
  have hb : LocallyBoundedAboveOff E w := by
    intro x
    obtain ⟨C,hC,_⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr (hw.1 x))
    exact ⟨{y | w y<(C : EReal)},hw.upperSemicontinuous x C hC,C,
      fun _ hy _ => hy.le⟩
  have hwext := hoff.analyticExtension_unique hE hEi hb hw (fun _ _ => rfl)
  have hzext := hoff.analyticExtension_unique hE hEi hb hz (fun x hx => (heq hx).symm)
  exact hwext.trans hzext.symm

/-- The full source proper-bimeromorphic theta-PSH descent in independently
varying original charts. Actual inverse pullback, finite bounds, analytic
extension and all-fibre readback are produced from the original inputs. -/
theorem existsUnique_originalThetaPSH_descent [CompactSpace X]
    {f : X → Y} (hf : A.IsAtlasAnalyticModification B f)
    (θ : AtlasClosedRealOneOneForm B) {w : X → EReal}
    (hw : A.IsThetaPSH (θ.holomorphicPullback hf.1) w) :
    ∃! z : Y → EReal,B.IsThetaPSH θ z ∧ z ∘ f=w := by
  obtain ⟨E,S,hE,hEi,hS,hSi,e,heSource,heTarget,heval,hs⟩ :=
    hf.exists_offExceptional_openPartialHomeomorph
  let v : Y → EReal := w ∘ e.symm
  have hoff : B.IsThetaPSHOn θ v Sᶜ := by
    refine ⟨fun y _ => hw.1 (e.symm y),?_⟩
    intro U g hUS hg
    have hgF := hg.comp_holomorphic hf.1
    have hp := hw.2 (f ⁻¹' U) (g ∘ f) hgF
    have hUt : U⊆e.target := by rw [heTarget]; exact hUS
    have hmap : MapsTo e.symm U (f ⁻¹' U) := by
      intro y hy
      change f (e.symm y)∈U
      rw [← heval (e.symm y),e.right_inv (hUt hy)]
      exact hy
    have hhol : B.IsHolomorphicOn A e.symm e.target := by rwa [heTarget]
    have hpinv := hp.comp_openPartialHolomorphicInverse hgF.1 hg.1 hUt hmap hhol
    apply (isPSHOn_iff_chart_and_nondegenerate hg.1).mpr
    constructor
    · intro i z hz
      apply (hpinv.chartPlurisubharmonic i z hz).congr
      have hD := (B.chart i).isOpen_inter_preimage_symm hg.1
      filter_upwards [hD.mem_nhds hz] with y hy
      change w (e.symm ((B.chart i).symm y))+
          (g (f (e.symm ((B.chart i).symm y))) : EReal)=
        w (e.symm ((B.chart i).symm y))+(g ((B.chart i).symm y) : EReal)
      rw [← heval (e.symm ((B.chart i).symm y)),e.right_inv (hUt hy.2)]
    · intro y hy V hV hyV
      obtain ⟨x,hx,hfin⟩ := (hpinv.locallyNondegenerate hg.1) y hy V hV hyV
      refine ⟨x,hx,?_⟩
      change w (e.symm x)+(g x : EReal)≠⊥
      have hfx : f (e.symm x)=x := by
        rw [← heval (e.symm x),e.right_inv (hUt hx.1)]
      simpa only [Function.comp_apply,hfx] using hfin
  obtain ⟨C,hC⟩ := hw.exists_global_upper_bound_original
  have hb : LocallyBoundedAboveOff S v :=
    fun _ => ⟨univ,univ_mem,C,fun y _ _ => hC (e.symm y)⟩
  let z := analyticExtension S v
  have hz : B.IsThetaPSH θ z := hoff.analyticExtension_isThetaPSH hS hSi hb
  have hread : EqOn (z ∘ f) w Eᶜ := by
    intro x hx
    have hxsource : x∈e.source := by rwa [heSource]
    have hfxTarget : f x∈e.target := by
      rw [← heval x]
      exact e.map_source hxsource
    have hfxS : f x∉S := by rwa [heTarget] at hfxTarget
    change analyticExtension S v (f x)=w x
    rw [hoff.analyticExtension_eq_off (hS.isClosed B) hfxS]
    change w (e.symm (f x))=w x
    rw [← heval x,e.left_inv hxsource]
  have hevery : z ∘ f=w :=
    (hz.comp_atlasAnalyticModification hf).eq_of_eq_off_original_analytic hw hE hEi hread
  refine ⟨z,⟨hz,hevery⟩,?_⟩
  intro a ha
  funext y
  obtain ⟨x,rfl⟩ := hf.surjective y
  exact (congrFun ha.2 x).trans (congrFun hevery x).symm

end SGPT.PSH.VariableComplexAtlas
