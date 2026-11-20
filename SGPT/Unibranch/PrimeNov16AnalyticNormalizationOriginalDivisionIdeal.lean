import SGPT.Unibranch.PrimeNov16AnalyticNormalizationRegularDivision
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkChart
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartProducts
import SGPT.Foundations.Analysis.Pending.CartanIrreducible

/-! Full original function-image division reads back to the actual functional ideal.
Blueprint: prime-nov16-analytic-normalization-original-division-ideal.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Polynomial
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationRegularDivision
open PrimeNov16AnalyticNormalizationGraphStalkChart
open PrimeNov16AnalyticNormalizationCoherentChartDictionary
open PrimeNov16AnalyticNormalizationCoherentChartProducts
open HironakaActualAnalyticSubspace HironakaHolomorphicJetRankLoci
open HironakaSmoothCentreRealDomainActualSheafStalk
open RestrictedIdealExtension HironakaAnalyticBaseChangeQuotientModel

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

def originalFunctionImage (C : Set M) (p : C) (F : M → ℂ) (hF : HolomorphicAt n F p.val) :=
  intrinsicGermMap C p (chartTranslatedGerm p.val p.val (mem_chart_source _ p.val) F hF)

theorem original_division_functional_mem (C : Set M) (hC : IsComplexAnalyticSubset (n := n) C)
    (p : C) (D G : M → ℂ)
    (hD : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ D) (hG : HolomorphicAt n G p.val)
    (hdiv : ∃ q : ((actualSubspaceSheaf (n := n) C).presheaf.stalk p).carrier,
      originalFunctionImage C p G hG =
        originalFunctionImage C p D (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y)*q) :
    (sumIdeal (principalIdeal (n := n) D) (vanishingIdeal (n := n) C)).mem p.val G := by
  let P := wholeChartStalkIdeal (vanishingIdeal (n := n) C) p.val p.val (mem_chart_source _ p.val)
  let hDx : HolomorphicAt n D p.val := Eventually.of_forall fun y => hD.mdifferentiable (by simp) y
  let dg := chartTranslatedGerm p.val p.val (mem_chart_source _ p.val) D hDx
  let gg := chartTranslatedGerm p.val p.val (mem_chart_source _ p.val) G hG
  let e := actualSubspaceStalkChartEquiv (n := n) C p
  obtain ⟨q,hq⟩ := hdiv
  obtain ⟨a,ha⟩ := Ideal.Quotient.mk_surjective (e q)
  have heq : Ideal.Quotient.mk P gg = Ideal.Quotient.mk P dg * Ideal.Quotient.mk P a := by
    calc
      _ = e (originalFunctionImage C p G hG) := (e.apply_symm_apply _).symm
      _ = e (originalFunctionImage C p D hDx*q) := congrArg e hq
      _ = _ := by rw [map_mul,show e (originalFunctionImage C p D hDx)=Ideal.Quotient.mk P dg
          from e.apply_symm_apply _,ha]
  have hdiff : gg-dg*a ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp (by
    rw [map_sub,map_mul,heq,sub_self])
  have hmem : gg ∈ Ideal.span {dg} ⊔ P := by
    have hm : dg*a ∈ (Ideal.span {dg} : Ideal (HolGerm (ComplexModel n))) :=
      Ideal.mul_mem_right a _ (Ideal.subset_span (mem_singleton dg))
    have hd : gg-dg*a ∈ Ideal.span {dg} ⊔ P := Submodule.mem_sup_right hdiff
    have hp : dg*a ∈ Ideal.span {dg} ⊔ P := Submodule.mem_sup_left hm
    simpa only [sub_add_cancel] using Ideal.add_mem _ hd hp
  have hPC : (vanishingIdeal (n := n) C).IsCoherent := CartanIrreducible.cartanCoherence C hC
  have hDC := principalIdeal_coherent D hD
  apply (chart_mem_whole_iff _ (isCoherent_sumIdeal hDC hPC) p.val G hG).mp
  rw [wholeChartStalkIdeal_sum _ _ hDC hPC,wholeChartStalkIdeal_principal D hD]
  exact hmem

theorem actual_regular_original_function_division {d t : ℕ} {X : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
    (C : Set X) (hC : IsComplexAnalyticSubset (n := d+t) C) (x : X)
    (hreg : RegularAtDim (n := d+t) C x d) (D G : X → ℂ)
    (hD : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ D) (hG : HolomorphicAt (d+t) G x)
    (hDn : originalFunctionImage C ⟨x,hreg.2.1⟩ D
      (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y) ≠ 0)
    (p : Polynomial ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk ⟨x,hreg.2.1⟩).carrier)
    (hp : p.Monic)
    (hrel : eval (originalFunctionImage C ⟨x,hreg.2.1⟩ G hG)
      (p.scaleRoots (originalFunctionImage C ⟨x,hreg.2.1⟩ D
        (Eventually.of_forall fun y => hD.mdifferentiable (by simp) y)))=0) :
    (sumIdeal (principalIdeal (n := d+t) D) (vanishingIdeal (n := d+t) C)).mem x G := by
  apply original_division_functional_mem C hC ⟨x,hreg.2.1⟩ D G hD hG
  exact actual_regular_original_stalk_division C x hreg _ _ hDn p hp hrel

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
