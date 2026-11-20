import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartDictionary

/-! Whole original chart products and a genuinely constructed principal test ideal.
Blueprint: prime-nov16-analytic-normalization-coherent-chart-products.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartProducts
open PrimeNov16AnalyticNormalizationCoherentChartDictionary
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem chartTranslatedGerm_sum_mul (x : M) {s : ℕ} (a g : Fin s → M → ℂ)
    (ha : ∀ i,HolomorphicAt n (a i) x) (hg : ∀ i,HolomorphicAt n (g i) x) :
    chartTranslatedGerm x x (mem_chart_source _ x) (fun y => ∑ i,a i y*g i y)
        (HolomorphicAt.sum Finset.univ fun i _ => (ha i).mul (hg i)) =
      ∑ i,chartTranslatedGerm x x (mem_chart_source _ x) (a i) (ha i)*
        chartTranslatedGerm x x (mem_chart_source _ x) (g i) (hg i) := by
  simp only [chartTranslatedGerm,translatedGerm]
  rw [HolGerm.mk_sum Finset.univ]
  · exact Finset.sum_congr rfl fun i _ => HolGerm.mk_mul _ _ _ _
  · intro i
    exact translated_holomorphic _ (CartanLocalReduction.holAt_comp_chart_symm
      (mem_chart_source _ x) ((ha i).mul (hg i)))

theorem whole_chart_span_mem (x : M) (L : Ideal (HolGerm (ComplexModel n)))
    (S : (M → ℂ) → Prop) (hS : ∀ f,S f → HolomorphicAt n f x)
    (hmem : ∀ f (hf : S f),chartTranslatedGerm x x (mem_chart_source _ x) f (hS f hf) ∈ L)
    (f : M → ℂ) (hf : HolomorphicAt n f x) (hspan : IsInSpanAt (n := n) S x f) :
    chartTranslatedGerm x x (mem_chart_source _ x) f hf ∈ L := by
  obtain ⟨_hf,s,g,a,hg,ha,he⟩ := hspan
  have hgh : ∀ i,HolomorphicAt n (g i) x := fun i => hS (g i) (hg i)
  rw [chartTranslatedGerm_congr_original x f _ hf
    (HolomorphicAt.sum Finset.univ fun i _ => (ha i).mul (hgh i)) he,
    chartTranslatedGerm_sum_mul x a g ha hgh]
  exact L.sum_mem fun i _ => L.mul_mem_left _ (hmem (g i) (hg i))

theorem wholeChartStalkIdeal_product (I J : GermIdeal n M)
    (hI : I.IsCoherent) (hJ : J.IsCoherent) (x : M) :
    wholeChartStalkIdeal (I.mul J) x x (mem_chart_source _ x) =
      wholeChartStalkIdeal I x x (mem_chart_source _ x)*wholeChartStalkIdeal J x x (mem_chart_source _ x) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨f,hf,hfm,rfl⟩
    let S : (M → ℂ) → Prop := fun t => ∃ p q,I.mem x p ∧ J.mem x q ∧ t=p*q
    have hS : ∀ t,S t → HolomorphicAt n t x := by
      rintro t ⟨p,q,hp,hq,rfl⟩
      exact (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hp).mul
        (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hq)
    apply whole_chart_span_mem x _ S hS ?_ f hf hfm
    rintro t ⟨p,q,hp,hq,rfl⟩
    have hph := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hp
    have hqh := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hq
    change chartTranslatedGerm x x _ (fun y => p y*q y) (hph.mul hqh) ∈ _
    rw [chartTranslatedGerm_mul x p q hph hqh]
    exact Ideal.mul_mem_mul ((chart_mem_whole_iff I hI x p hph).mpr hp)
      ((chart_mem_whole_iff J hJ x q hqh).mpr hq)
  · apply Ideal.mul_le.mpr
    intro a ha b hb
    obtain ⟨f,hf,rfl⟩ := exists_original_function_chart x a
    obtain ⟨g,hg,rfl⟩ := exists_original_function_chart x b
    have hfI := (chart_mem_whole_iff I hI x f hf).mp ha
    have hgJ := (chart_mem_whole_iff J hJ x g hg).mp hb
    rw [← chartTranslatedGerm_mul]
    apply Ideal.subset_span
    refine ⟨(fun z => f z*g z),hf.mul hg,?_,rfl⟩
    change IsInSpanAt (n := n) (fun t => ∃ p q,I.mem x p ∧ J.mem x q ∧ t=p*q) x (fun z => f z*g z)
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨f,g,hfI,hgJ,rfl⟩ (hf.mul hg)

def principalIdeal (H : M → ℂ) : GermIdeal n M where
  mem x f := IsInSpanAt (n := n) (· ∈ range (fun _ : Fin 1 => H)) x f

omit [IsComplexManifold n M] in
theorem principalIdeal_coherent (H : M → ℂ)
    (hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ H) : (principalIdeal (n := n) H).IsCoherent :=
  fun x => ⟨univ,isOpen_univ,mem_univ x,1,fun _ => H,
    fun _ => (hH.mdifferentiable (by simp)).mdifferentiableOn,fun _ _ _ => Iff.rfl⟩

theorem wholeChartStalkIdeal_principal (H : M → ℂ)
    (hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ H) (x : M) :
    wholeChartStalkIdeal (principalIdeal (n := n) H) x x (mem_chart_source _ x) =
      Ideal.span {chartTranslatedGerm x x (mem_chart_source _ x) H
        (Eventually.of_forall fun y => hH.mdifferentiable (by simp) y)} := by
  let hHx : HolomorphicAt n H x := Eventually.of_forall fun y => hH.mdifferentiable (by simp) y
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨f,hf,hfm,rfl⟩
    apply whole_chart_span_mem x _ (· ∈ range (fun _ : Fin 1 => H))
      (fun g hg => by obtain ⟨i,rfl⟩ := hg; exact hHx) ?_ f hf hfm
    rintro g ⟨i,rfl⟩
    exact Ideal.subset_span (mem_singleton _)
  · apply Ideal.span_le.mpr
    rintro a (rfl : a = _)
    apply (chart_mem_whole_iff _ (principalIdeal_coherent H hH) x H hHx).mpr
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨0,rfl⟩ hHx

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartProducts
