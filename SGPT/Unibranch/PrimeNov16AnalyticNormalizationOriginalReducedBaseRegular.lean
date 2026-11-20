import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalBaseRegular

/-! ALL original branches manufacture SAME denominator regularity in ENTIRE reduced original stalk.
Blueprint: prime-nov16-analytic-normalization-original-reduced-base-regular.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedBaseRegular
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalOpenFunctionReadback
open PrimeNov16AnalyticNormalizationStalkCalculus
open HironakaActualAnalyticSubspace HironakaActualVanishingIntrinsicHSTransport
open HironakaHolomorphicJetRankLoci

theorem original_finite_union_ideal {n k : ℕ} (B : Fin k → Set (ComplexModel n)) :
    AnalyticGermDecomposition.vanishingIdeal (⋃ i,B i)=
      ⨅ i,AnalyticGermDecomposition.vanishingIdeal (B i) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    exact AnalyticGermDecomposition.vanishingIdeal_anti (subset_iUnion B i).eventuallyLE
  · intro g hg
    obtain ⟨F,hF,rfl⟩ := HolGerm.exists_eq_mk g
    apply AnalyticGermDecomposition.mem_vanishingIdeal_mk.mpr
    have hv : ∀ i,∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → F z=0 := fun i =>
      AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp (Ideal.mem_iInf.mp hg i)
    filter_upwards [eventually_all.mpr hv] with z hz hzB
    obtain ⟨i,hi⟩ := mem_iUnion.mp hzB
    exact hz i hi

theorem original_reduced_quotient_regular {n k : ℕ} (Z : Set (ComplexModel n))
    (B : Fin k → Set (ComplexModel n)) (hB : ∀ i,AnalyticGermDecomposition.IsIrreducibleGerm (B i))
    (hcover : Z =ᶠ[𝓝 (0 : ComplexModel n)] (⋃ i,B i))
    (q : HolGerm (ComplexModel n)) (hq : ∀ i,q ∉ AnalyticGermDecomposition.vanishingIdeal (B i)) :
    ∀ a : HolGerm (ComplexModel n) ⧸ AnalyticGermDecomposition.vanishingIdeal Z,
      Ideal.Quotient.mk _ q*a=0 → a=0 := by
  have hI : AnalyticGermDecomposition.vanishingIdeal Z=
      ⨅ i,AnalyticGermDecomposition.vanishingIdeal (B i) :=
    (AnalyticGermDecomposition.vanishingIdeal_congr hcover).trans (original_finite_union_ideal B)
  intro a ha
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hm : q*g ∈ AnalyticGermDecomposition.vanishingIdeal Z := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul] using ha
  rw [hI] at hm ⊢
  apply Ideal.mem_iInf.mpr
  intro i
  let : (AnalyticGermDecomposition.vanishingIdeal (B i)).IsPrime :=
    (AnalyticGermDecomposition.isIrreducibleGerm_iff_isPrime (hB i).1).mp (hB i)
  exact ((show (AnalyticGermDecomposition.vanishingIdeal (B i)).IsPrime from inferInstance).mem_or_mem (Ideal.mem_iInf.mp hm i)).resolve_left (hq i)

theorem original_central_reduced_denominator_regular {n k : ℕ} {Z : Set (ComplexModel n)}
    (B : Fin k → Set (ComplexModel n)) (hB : ∀ i,AnalyticGermDecomposition.IsIrreducibleGerm (B i))
    (hcover : Z =ᶠ[𝓝 (0 : ComplexModel n)] (⋃ i,B i))
    (U : Opens (ComplexModel n)) (p : ((Subtype.val : U → ComplexModel n) ⁻¹' Z))
    (hp : p.val.val=0) (Q : ComplexModel n → ℂ)
    (hQ : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ Q z)
    (hne : ∀ i,¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → Q z=0)
    (hQ' : HolomorphicAt n (Q ∘ Subtype.val) p.val) :
    ∀ r : ((actualSubspaceSheaf (n := n) ((Subtype.val : U → ComplexModel n) ⁻¹' Z)).presheaf.stalk p).carrier,
      originalFunctionImage _ p (Q ∘ Subtype.val) hQ'*r=0 → r=0 := by
  let C := (Subtype.val : U → ComplexModel n) ⁻¹' Z
  let P := wholeChartStalkIdeal (vanishingIdeal (n := n) C) p.val p.val (mem_chart_source _ p.val)
  have hP : P=AnalyticGermDecomposition.vanishingIdeal Z := by
    dsimp [P,C]
    rw [wholeChartStalkIdeal_vanishing_actual_open,wholeChart_vanishing_eq_translated]
    simp only [hp,add_zero]
    rfl
  let E := (actualSubspaceStalkChartEquiv (n := n) C p).trans (Ideal.quotEquivOfEq hP)
  have hQa : HolomorphicAt n Q p.val.val := by
    rw [hp]
    exact hQ.mono fun _ hy => hy.mdifferentiableAt
  have hread : chartTranslatedGerm p.val p.val (mem_chart_source _ p.val)
      (Q ∘ Subtype.val) hQ'=HolGerm.mk Q hQ := by
    rw [original_open_chart_function U p.val Q hQa]
    simp only [chartTranslatedGerm,translatedGerm,chartAt_self_eq]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by simp [hp]
  have hE : E (originalFunctionImage C p (Q ∘ Subtype.val) hQ')=
      Ideal.Quotient.mk (AnalyticGermDecomposition.vanishingIdeal Z) (HolGerm.mk Q hQ) := by
    change Ideal.quotEquivOfEq hP
      ((actualSubspaceStalkChartEquiv (n := n) C p)
        ((actualSubspaceStalkChartEquiv (n := n) C p).symm (Ideal.Quotient.mk P
          (chartTranslatedGerm p.val p.val (mem_chart_source _ p.val) (Q ∘ Subtype.val) hQ'))))=_
    rw [RingEquiv.apply_symm_apply,hread]
    exact Ideal.quotEquivOfEq_mk hP _
  intro r hr
  apply E.injective
  rw [map_zero]
  apply original_reduced_quotient_regular Z B hB hcover (HolGerm.mk Q hQ)
    (fun i hi => hne i (AnalyticGermDecomposition.mem_vanishingIdeal_mk.mp hi))
  have he := congrArg E hr
  rw [map_mul,hE,map_zero] at he
  exact he

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalReducedBaseRegular
