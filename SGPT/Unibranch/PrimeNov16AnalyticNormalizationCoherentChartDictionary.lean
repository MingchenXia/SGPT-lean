import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentColonDictionary
import SGPT.Foundations.Analysis.Pending.HironakaAnalyticBaseChangeQuotientModel

/-! Entire coherent chart dictionaries on the actual original open manifold.
Blueprint: prime-nov16-analytic-normalization-coherent-chart-dictionary.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaSmoothCentreRealDomainActualSheafStalk
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartDictionary
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem chart_mem_whole_iff (I : GermIdeal n M) (hI : I.IsCoherent)
    (x : M) (f : M → ℂ) (hf : HolomorphicAt n f x) :
    chartTranslatedGerm x x (mem_chart_source _ x) f hf ∈
      wholeChartStalkIdeal I x x (mem_chart_source _ x) ↔ I.mem x f := by
  obtain ⟨U,_hU,hxU,s,G,hsource,_hG,hfamily⟩ := exists_coherent_whole_stalk_original_columns I hI x
  obtain ⟨_hGx,hmem,hwhole⟩ := hfamily x hxU
  rw [hwhole]
  exact (hmem f hf).symm

theorem exists_original_function_chart (x : M) (a : HolGerm (ComplexModel n)) :
    ∃ (f : M → ℂ) (hf : HolomorphicAt n f x),
      chartTranslatedGerm x x (mem_chart_source _ x) f hf = a := by
  obtain ⟨r,hr⟩ := (actualStalkChartEquiv (n := n) x).surjective a
  obtain ⟨U,hxU,s,rfl⟩ := (actualComplexStructureSheaf (n := n) M).presheaf.exists_germ_eq r
  refine ⟨sectionExtension U s,sectionExtension_holomorphicAt U s x hxU,?_⟩
  exact (actualStalkChartEquiv_germ U x hxU s).symm.trans hr

theorem chartTranslatedGerm_mul (x : M) (f g : M → ℂ)
    (hf : HolomorphicAt n f x) (hg : HolomorphicAt n g x) :
    chartTranslatedGerm x x (mem_chart_source _ x) (fun z => f z*g z) (hf.mul hg) =
      chartTranslatedGerm x x (mem_chart_source _ x) f hf *
        chartTranslatedGerm x x (mem_chart_source _ x) g hg := by
  simp only [chartTranslatedGerm,translatedGerm]
  exact HolGerm.mk_mul _ _ _ _

theorem wholeChartStalkIdeal_colon (I J : GermIdeal n M)
    (hI : I.IsCoherent) (hJ : J.IsCoherent) (x : M) :
    wholeChartStalkIdeal (InvertibleIdealQuotient.colon I J) x x (mem_chart_source _ x) =
      (wholeChartStalkIdeal I x x (mem_chart_source _ x)).colon
        (wholeChartStalkIdeal J x x (mem_chart_source _ x) : Set (HolGerm (ComplexModel n))) := by
  have hcolon := CoherentIdealColon.isCoherent_colon_of_isCoherent hI hJ
  ext a
  obtain ⟨f,hf,rfl⟩ := exists_original_function_chart x a
  rw [chart_mem_whole_iff _ hcolon x f hf]
  constructor
  · intro hfc
    apply Submodule.mem_colon.mpr
    intro b hb
    obtain ⟨g,hg,rfl⟩ := exists_original_function_chart x b
    have hJg := (chart_mem_whole_iff J hJ x g hg).mp hb
    have hm := (chart_mem_whole_iff I hI x (fun z => g z*f z) (hg.mul hf)).mpr (hfc.2 g hJg)
    rw [chartTranslatedGerm_mul] at hm
    simpa only [smul_eq_mul,mul_comm] using hm
  · intro hfc
    refine ⟨hf,?_⟩
    intro g hgJ
    have hg := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hgJ
    have hgmem := (chart_mem_whole_iff J hJ x g hg).mpr hgJ
    have hm := (Submodule.mem_colon.mp hfc) _ hgmem
    apply (chart_mem_whole_iff I hI x (fun z => g z*f z) (hg.mul hf)).mp
    rw [chartTranslatedGerm_mul]
    simpa only [smul_eq_mul,mul_comm] using hm

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartDictionary
