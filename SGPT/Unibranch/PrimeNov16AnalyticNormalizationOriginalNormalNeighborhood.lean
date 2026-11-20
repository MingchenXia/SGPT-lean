import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalTestCaller
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen

/-! ONE actual original normal neighborhood, with ALL tests and powers INTERNALLY manufactured.
Blueprint: prime-nov16-analytic-normalization-original-normal-neighborhood.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalNeighborhood
open PrimeNov16AnalyticNormalizationOriginalNormalTestCaller
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalStalkDenominatorOpen
open PrimeNov16AnalyticNormalizationNormalTestColonOpen
open PrimeNov16AnalyticNormalizationCoherentChartProducts
open PrimeNov16AnalyticNormalizationCoherentSupportPower
open HironakaActualAnalyticSubspace HironakaHolomorphicJetRankLoci

variable {d t : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

theorem exists_actual_original_normal_neighborhood (C : Set M)
    (hC : IsComplexAnalyticSubset (n := d+t) C) (Q : M → ℂ)
    (hQ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ Q)
    (hregular : ∀ y ∈ C,Q y ≠ 0 → RegularAtDim (n := d+t) C y d) (x : C)
    [IsDomain ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier]
    [IsIntegrallyClosed ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier]
    (hQne : originalFunctionImage C x Q (Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y) ≠ 0) :
    ∃ U : Set M,IsOpen U ∧ x.val ∈ U ∧ ∀ y : C,y.val ∈ U →
      IsDomain ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk y).carrier ∧
        IsIntegrallyClosed ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk y).carrier := by
  let P := vanishingIdeal (n := d+t) C
  let J := vanishingIdeal (n := d+t) (C ∩ {y | Q y=0})
  have hP : P.IsCoherent := CartanIrreducible.cartanCoherence C hC
  have hzeroQ : IsComplexAnalyticSubset (n := d+t) {y | Q y=0} := by
    rw [← principalIdeal_zeroLocus Q hQ]
    exact CodimOneSupport.isComplexAnalyticSubset_zeroLocus (principalIdeal_coherent Q hQ)
  have hJ : J.IsCoherent := CartanIrreducible.cartanCoherence _ (hC.inter hzeroQ)
  let hQx : HolomorphicAt (d+t) Q x.val := Eventually.of_forall fun y => hQ.mdifferentiable (by simp) y
  let PG := wholeChartStalkIdeal P x.val x.val (mem_chart_source _ x.val)
  let E : ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier ≃+*
      HolGerm (ComplexModel (d+t)) ⧸ PG := actualSubspaceStalkChartEquiv (n := d+t) C x
  let : IsDomain (HolGerm (ComplexModel (d+t)) ⧸ PG) :=
    Function.Injective.isDomain E.symm E.symm.injective
  let : IsIntegrallyClosed (HolGerm (ComplexModel (d+t)) ⧸ PG) := IsIntegrallyClosed.of_equiv E
  have hQmem : J.mem x.val Q := ⟨hQx,Eventually.of_forall fun _y hy => hy.2⟩
  have hQquot : Ideal.Quotient.mk PG (chartTranslatedGerm x.val x.val (mem_chart_source _ x.val) Q hQx) ≠ 0 := by
    have he : E (originalFunctionImage C x Q hQx) =
        Ideal.Quotient.mk PG (chartTranslatedGerm x.val x.val (mem_chart_source _ x.val) Q hQx) :=
      E.apply_symm_apply _
    intro hz
    apply hQne
    apply E.injective
    rw [map_zero,he]
    exact hz
  obtain ⟨U,hU,hxU,hTest⟩ := exists_original_open_test_colon_equality P J hP hJ Q hQ x.val hQmem hQquot
  have hQreg : ∀ r : ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk x).carrier,
      originalFunctionImage C x Q hQx*r=0 → r=0 := by
    intro r hr
    exact (mul_eq_zero.mp hr).resolve_left hQne
  obtain ⟨V,hV,hxV,hReg⟩ := exists_original_open_entire_stalk_regular C hC x Q hQ hQreg
  refine ⟨U ∩ V,hU.inter hV,⟨hxU,hxV⟩,?_⟩
  intro y hy
  apply original_stalk_normal_of_functional_test C hC Q hQ hregular y
  · exact mem_nonZeroDivisors_iff_left.mpr (hReg y hy.2)
  · exact hTest y.val hy.1

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalNormalNeighborhood
