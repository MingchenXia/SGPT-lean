import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalWholePower
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBranchRegular
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalQuotientTestRadical
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationRadicalTestEquiv
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationNormalTestColonOpen
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedTest
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentSupportPower
import SGPT.Foundations.Analysis.Pending.CodimOneSupport

/-! The full original analytic test actually proves ENTIRE original stalk normality.
Blueprint: prime-nov16-analytic-normalization-original-normal-test-caller.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalTestCaller
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalWholePower
open PrimeNov16AnalyticNormalizationOriginalBranchRegular
open PrimeNov16AnalyticNormalizationOriginalQuotientTestRadical
open PrimeNov16AnalyticNormalizationQuotientTestColon
open PrimeNov16AnalyticNormalizationRadicalTestEquiv
open PrimeNov16AnalyticNormalizationNormalTestColonOpen
open PrimeNov16AnalyticNormalizationOriginalReducedTest
open PrimeNov16AnalyticNormalizationCoherentChartDictionary
open PrimeNov16AnalyticNormalizationCoherentChartProducts
open PrimeNov16AnalyticNormalizationCoherentSupportPower
open HironakaActualAnalyticSubspace HironakaHolomorphicJetRankLoci
open RestrictedIdealExtension HironakaAnalyticBaseChangeQuotientModel

variable {d t : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

theorem original_stalk_normal_of_functional_test (C : Set M)
    (hC : IsComplexAnalyticSubset (n := d+t) C) (Q : M → ℂ)
    (hQ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ Q)
    (hregular : ∀ y ∈ C,Q y ≠ 0 → RegularAtDim (n := d+t) C y d) (x : C)
    (hNZD : originalFunctionImage C x Q (Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y) ∈
      nonZeroDivisors ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier)
    (htest : ∀ F,
      (testColon (vanishingIdeal (n := d+t) C) (vanishingIdeal (n := d+t) (C ∩ {y | Q y=0})) Q).mem x.val F ↔
      (principalPlus (vanishingIdeal (n := d+t) C) Q).mem x.val F) :
    IsDomain ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier ∧
      IsIntegrallyClosed ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier := by
  let n := d+t
  let P := vanishingIdeal (n := n) C
  let J := vanishingIdeal (n := n) (C ∩ {y | Q y=0})
  let L := principalIdeal (n := n) Q
  have hP : P.IsCoherent := CartanIrreducible.cartanCoherence C hC
  have hL : L.IsCoherent := principalIdeal_coherent Q hQ
  have hzeroQ : IsComplexAnalyticSubset (n := n) {y | Q y=0} := by
    rw [← principalIdeal_zeroLocus Q hQ]
    exact CodimOneSupport.isComplexAnalyticSubset_zeroLocus hL
  have hJ : J.IsCoherent := CartanIrreducible.cartanCoherence _ (hC.inter hzeroQ)
  have hJL : (J.mul L).IsCoherent := IdealWeightPowers.isCoherent_mul hJ hL
  have hSum : (sumIdeal (J.mul L) P).IsCoherent := isCoherent_sumIdeal hJL hP
  have hT : (testColon P J Q).IsCoherent := CoherentIdealColon.isCoherent_colon_of_isCoherent hSum hJ
  have hPlus : (principalPlus P Q).IsCoherent := isCoherent_sumIdeal hL hP
  let PG := wholeChartStalkIdeal P x.val x.val (mem_chart_source _ x.val)
  let JG := wholeChartStalkIdeal J x.val x.val (mem_chart_source _ x.val)
  let hQx : HolomorphicAt n Q x.val := Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y
  let gQ := chartTranslatedGerm x.val x.val (mem_chart_source _ x.val) Q hQx
  have hWhole : wholeChartStalkIdeal (testColon P J Q) x.val x.val (mem_chart_source _ x.val) =
      wholeChartStalkIdeal (principalPlus P Q) x.val x.val (mem_chart_source _ x.val) := by
    ext a
    obtain ⟨F,hF,rfl⟩ := exists_original_function_chart x.val a
    rw [chart_mem_whole_iff _ hT x.val F hF,chart_mem_whole_iff _ hPlus x.val F hF]
    exact htest F
  have hAmb : ((JG*Ideal.span {gQ}) ⊔ PG).colon (JG : Set (HolGerm (ComplexModel n))) =
      Ideal.span {gQ} ⊔ PG := by
    change wholeChartStalkIdeal (InvertibleIdealQuotient.colon (sumIdeal (J.mul L) P) J)
      x.val x.val (mem_chart_source _ x.val) =
      wholeChartStalkIdeal (sumIdeal L P) x.val x.val (mem_chart_source _ x.val) at hWhole
    rw [wholeChartStalkIdeal_colon _ _ hSum hJ,wholeChartStalkIdeal_sum _ _ hJL hP,
      wholeChartStalkIdeal_product J L hJ hL,wholeChartStalkIdeal_principal Q hQ,
      wholeChartStalkIdeal_sum L P hL hP,wholeChartStalkIdeal_principal Q hQ] at hWhole
    exact hWhole
  have hQuot := quotient_test_colon_of_lifted PG JG gQ hAmb
  have hJrad := original_quotient_test_radical C hC x.val Q hQx
  change JG.map (Ideal.Quotient.mk PG)=(Ideal.span {Ideal.Quotient.mk PG gQ}).radical at hJrad
  change ((JG.map (Ideal.Quotient.mk PG))*Ideal.span {Ideal.Quotient.mk PG gQ}).colon
    (JG.map (Ideal.Quotient.mk PG) : Set (HolGerm (ComplexModel n) ⧸ PG)) =
      Ideal.span {Ideal.Quotient.mk PG gQ} at hQuot
  rw [hJrad] at hQuot
  let A := ((actualSubspaceSheaf (n := n) C).presheaf.stalk x).carrier
  let E : A ≃+* HolGerm (ComplexModel n) ⧸ PG := actualSubspaceStalkChartEquiv (n := n) C x
  let q : A := originalFunctionImage C x Q hQx
  have hEq : E q=Ideal.Quotient.mk PG gQ := E.apply_symm_apply _
  have hqback : E.symm (Ideal.Quotient.mk PG gQ)=q := by rw [← hEq,E.symm_apply_apply]
  have hTestR := radical_test_ringEquiv E.symm (Ideal.Quotient.mk PG gQ) hQuot
  rw [hqback] at hTestR
  let X := SourceReducedComplexSpace.ofClosedAnalytic (n := n) C hC
  have hreg := normalBranchMap_regular_of_original_nzd A q hNZD
  have hpower := exists_original_whole_branch_power C hC Q hQ hregular x
  exact original_stalk_normal_of_actual_radical_test X (show X.obj.left from x) q hreg hpower hTestR

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalTestCaller
