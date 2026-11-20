import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationStalkCalculus

/-! Actual irreducible original base germ gives SAME denominator stalk regularity.
Blueprint: prime-nov16-analytic-normalization-original-base-regular.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseRegular
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback
open PrimeNov16AnalyticNormalizationStalkCalculus
open HironakaActualAnalyticSubspace HironakaActualVanishingIntrinsicHSTransport
open HironakaHolomorphicJetRankLoci

theorem original_central_denominator_regular {n : ℕ} {Z : Set (ComplexModel n)}
    (hZ : AnalyticGermDecomposition.IsIrreducibleGerm Z)
    (U : Opens (ComplexModel n)) (p : ((Subtype.val : U → ComplexModel n) ⁻¹' Z))
    (hp : p.val.val=0) (H : ComplexModel n → ℂ)
    (hH : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ H z)
    (hne : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ Z → H z=0)
    (hH' : HolomorphicAt n (H ∘ Subtype.val) p.val) :
    ∀ r : ((actualSubspaceSheaf (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' Z)).presheaf.stalk p).carrier,
      originalFunctionImage _ p (H ∘ Subtype.val) hH'*r=0 → r=0 := by
  let C := (Subtype.val : U → ComplexModel n) ⁻¹' Z
  let P := wholeChartStalkIdeal (vanishingIdeal (n := n) C) p.val p.val (mem_chart_source _ p.val)
  have hP : P=AnalyticGermDecomposition.vanishingIdeal Z := by
    dsimp [P,C]
    rw [wholeChartStalkIdeal_vanishing_actual_open,wholeChart_vanishing_eq_translated]
    simp only [hp,add_zero]
    rfl
  let : P.IsPrime := hP.symm ▸ (AnalyticGermDecomposition.isIrreducibleGerm_iff_isPrime hZ.1).mp hZ
  let e := actualSubspaceStalkChartEquiv (n := n) C p
  let : IsDomain ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier :=
    Function.Injective.isDomain e e.injective
  have hHa : HolomorphicAt n H p.val.val := by
    rw [hp]
    exact hH.mono fun _ hy => hy.mdifferentiableAt
  have hread : chartTranslatedGerm p.val p.val (mem_chart_source _ p.val)
      (H ∘ Subtype.val) hH'=HolGerm.mk H hH := by
    rw [original_open_chart_function U p.val H hHa]
    simp only [chartTranslatedGerm,translatedGerm,chartAt_self_eq]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp [hp]
  have hnot : originalFunctionImage C p (H ∘ Subtype.val) hH' ≠ 0 := by
    intro hz
    have he : e (originalFunctionImage C p (H ∘ Subtype.val) hH')=
        Ideal.Quotient.mk P (chartTranslatedGerm p.val p.val (mem_chart_source _ p.val)
          (H ∘ Subtype.val) hH') := e.apply_symm_apply _
    have hzero : Ideal.Quotient.mk P (HolGerm.mk H hH)=0 := by
      rw [← hread,← he,hz,map_zero]
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hzero
    rw [hP] at hm
    exact hne (AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hm)
  intro r hr
  exact (mul_eq_zero.mp hr).resolve_left hnot

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseRegular
