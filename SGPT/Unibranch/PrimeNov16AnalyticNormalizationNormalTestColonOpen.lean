import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartProducts
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentEqualityOpen
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationLiftedNormalColon

/-! Actual normal-central test-colon equality on ONE entire original open.
Blueprint: prime-nov16-analytic-normalization-normal-test-colon-open.tex.
No normal-neighbourhood conclusion without a separately proved test criterion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending.HironakaHolomorphicJetRankLoci
open SGPT.Foundations.Analysis.Pending.HironakaAnalyticBaseChangeQuotientModel
open RestrictedIdealExtension
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationNormalTestColonOpen
open PrimeNov16AnalyticNormalizationCoherentChartDictionary
open PrimeNov16AnalyticNormalizationCoherentChartProducts
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

def testColon (P J : GermIdeal n M) (H : M → ℂ) : GermIdeal n M :=
  InvertibleIdealQuotient.colon (sumIdeal (J.mul (principalIdeal (n := n) H)) P) J

def principalPlus (P : GermIdeal n M) (H : M → ℂ) : GermIdeal n M :=
  sumIdeal (principalIdeal (n := n) H) P

theorem exists_original_open_test_colon_equality
    (P J : GermIdeal n M) (hP : P.IsCoherent) (hJ : J.IsCoherent)
    (H : M → ℂ) (hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ H) (x : M)
    [IsDomain (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal P x x (mem_chart_source _ x))]
    [IsIntegrallyClosed (HolGerm (ComplexModel n) ⧸ wholeChartStalkIdeal P x x (mem_chart_source _ x))]
    (hJH : J.mem x H)
    (hneq : Ideal.Quotient.mk (wholeChartStalkIdeal P x x (mem_chart_source _ x))
      (chartTranslatedGerm x x (mem_chart_source _ x) H
        (Eventually.of_forall fun y => hH.mdifferentiable (by simp) y)) ≠ 0) :
    ∃ U : Set M,IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,∀ f,
      (testColon P J H).mem y f ↔ (principalPlus P H).mem y f := by
  let hHx : HolomorphicAt n H x := Eventually.of_forall fun y => hH.mdifferentiable (by simp) y
  have hPrin := principalIdeal_coherent H hH
  have hJP := IdealWeightPowers.isCoherent_mul hJ hPrin
  have hK := isCoherent_sumIdeal hJP hP
  have hT : (testColon P J H).IsCoherent := CoherentIdealColon.isCoherent_colon_of_isCoherent hK hJ
  have hL : (principalPlus P H).IsCoherent := isCoherent_sumIdeal hPrin hP
  let : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  have hwhole : wholeChartStalkIdeal (testColon P J H) x x (mem_chart_source _ x) =
      wholeChartStalkIdeal (principalPlus P H) x x (mem_chart_source _ x) := by
    change wholeChartStalkIdeal (InvertibleIdealQuotient.colon _ J) x x _ =
      wholeChartStalkIdeal (sumIdeal _ P) x x _
    rw [wholeChartStalkIdeal_colon _ _ hK hJ x,
      wholeChartStalkIdeal_sum _ _ hJP hP x,
      wholeChartStalkIdeal_product J _ hJ hPrin x,
      wholeChartStalkIdeal_principal H hH x,
      wholeChartStalkIdeal_sum _ _ hPrin hP x,
      wholeChartStalkIdeal_principal H hH x]
    exact PrimeNov16AnalyticNormalizationLiftedNormalColon.lifted_colon_eq
      (wholeChartStalkIdeal P x x (mem_chart_source _ x))
      (wholeChartStalkIdeal J x x (mem_chart_source _ x))
      (chartTranslatedGerm x x (mem_chart_source _ x) H hHx)
      ((chart_mem_whole_iff J hJ x H hHx).mpr hJH) hneq
  apply PrimeNov16AnalyticNormalizationCoherentEqualityOpen.exists_open_coherent_equality
    (testColon P J H) (principalPlus P H) hT hL x
  intro f
  by_cases hf : HolomorphicAt n f x
  · rw [← chart_mem_whole_iff _ hT x f hf,← chart_mem_whole_iff _ hL x f hf,hwhole]
  · constructor
    · intro hm
      exact (hf (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hT hm)).elim
    · intro hm
      exact (hf (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hL hm)).elim

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationNormalTestColonOpen
