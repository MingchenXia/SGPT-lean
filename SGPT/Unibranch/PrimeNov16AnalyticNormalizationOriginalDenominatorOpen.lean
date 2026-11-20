import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentEqualityOpen

/-! Actual central multiplication kernel spreads by coherence to ONE original open.
Blueprint: prime-nov16-analytic-normalization-original-denominator-open.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDenominatorOpen
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationGraphStalkChart
open PrimeNov16AnalyticNormalizationCoherentChartDictionary
open PrimeNov16AnalyticNormalizationCoherentChartProducts
open PrimeNov16AnalyticNormalizationCoherentEqualityOpen
open HironakaActualAnalyticSubspace HironakaHolomorphicJetRankLoci
open HironakaSmoothCentreRealDomainActualSheafStalk

theorem quotient_regular_iff_colon {A : Type*} [CommRing A] (I : Ideal A) (d : A) :
    (∀ r : A ⧸ I,Ideal.Quotient.mk I d*r=0 → r=0) ↔ I.colon (Ideal.span {d} : Set A)=I := by
  constructor
  · intro hr
    ext a
    rw [Ideal.mem_colon_span_singleton]
    constructor
    · intro ha
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      apply hr
      rw [← map_mul,mul_comm]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    · exact I.mul_mem_right d
  · intro he r hr
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective r
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← he,Ideal.mem_colon_span_singleton]
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul,mul_comm]
    exact hr

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

theorem exists_original_open_quotient_regular (P : GermIdeal n M) (hP : P.IsCoherent)
    (D : M → ℂ) (hD : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ D) (x : M)
    (hx : ∀ r : HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal P x x (mem_chart_source _ x),
      Ideal.Quotient.mk _ (chartTranslatedGerm x x (mem_chart_source _ x) D
        (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y))*r=0 → r=0) :
    ∃ U : Set M,IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      ∀ r : HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal P y y (mem_chart_source _ y),
        Ideal.Quotient.mk _ (chartTranslatedGerm y y (mem_chart_source _ y) D
          (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z))*r=0 → r=0 := by
  let J := principalIdeal (n := n) D
  let K := InvertibleIdealQuotient.colon P J
  have hJ : J.IsCoherent := principalIdeal_coherent D hD
  have hK : K.IsCoherent := CoherentIdealColon.isCoherent_colon_of_isCoherent hP hJ
  have hcolon : wholeChartStalkIdeal K x x (mem_chart_source _ x) =
      wholeChartStalkIdeal P x x (mem_chart_source _ x) := by
    rw [wholeChartStalkIdeal_colon P J hP hJ,wholeChartStalkIdeal_principal D hD]
    exact (quotient_regular_iff_colon _ _).mp hx
  have heq : ∀ f,K.mem x f ↔ P.mem x f := by
    intro f
    constructor
    · intro hf
      have hfh := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hK hf
      apply (chart_mem_whole_iff P hP x f hfh).mp
      rw [← hcolon]
      exact (chart_mem_whole_iff K hK x f hfh).mpr hf
    · intro hf
      have hfh := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hP hf
      apply (chart_mem_whole_iff K hK x f hfh).mp
      rw [hcolon]
      exact (chart_mem_whole_iff P hP x f hfh).mpr hf
  obtain ⟨U,hU,hxU,hwhole⟩ := exists_open_coherent_equality K P hK hP x heq
  refine ⟨U,hU,hxU,fun y hy => (quotient_regular_iff_colon _ _).mpr ?_⟩
  rw [← wholeChartStalkIdeal_principal D hD,
    ← wholeChartStalkIdeal_colon P J hP hJ]
  ext a
  obtain ⟨f,hf,rfl⟩ := exists_original_function_chart y a
  rw [chart_mem_whole_iff K hK y f hf,chart_mem_whole_iff P hP y f hf]
  exact hwhole y hy f

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDenominatorOpen
