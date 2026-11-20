import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalClearedDivision
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentSupportPower

/-! Actual WHOLE monic equation and genuine regular complement manufacture colon support and power.
Blueprint: prime-nov16-analytic-normalization-monic-colon-support-power.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationMonicColonSupportPower
open PrimeNov16AnalyticNormalizationOriginalDivisionIdeal
open PrimeNov16AnalyticNormalizationOriginalClearedDivision
open PrimeNov16AnalyticNormalizationRegularOriginalStalk
open PrimeNov16AnalyticNormalizationCoherentChartProducts
open PrimeNov16AnalyticNormalizationCoherentSupportPower
open RestrictedIdealExtension HironakaActualAnalyticSubspace

variable {d t : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

theorem exists_original_monic_colon_support_power (C : Set M)
    (hC : IsComplexAnalyticSubset (n := d+t) C) {k : ℕ}
    (D G Q : M → ℂ) (c : Fin k → M → ℂ)
    (hD : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ D)
    (hG : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ G)
    (hQ : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ Q)
    (hc : ∀ i,ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ℂ) ∞ (c i))
    (hDreg : ∀ y : C,∀ r : ((actualSubspaceSheaf (n := d+t) C).presheaf.stalk y).carrier,
      originalFunctionImage C y D (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z)*r=0 → r=0)
    (hregular : ∀ y ∈ C,Q y ≠ 0 → RegularAtDim (n := d+t) C y d)
    (hrel : ∀ y ∈ C,G y^k+∑ i : Fin k,c i y*D y^(k-i.val)*G y^i.val=0) (x : M) :
    let J := sumIdeal (principalIdeal (n := d+t) D) (vanishingIdeal (n := d+t) C)
    let K := InvertibleIdealQuotient.colon J (principalIdeal (n := d+t) G)
    K.IsCoherent ∧ K.zeroLocus ⊆ {y | Q y=0} ∧
      ∃ U : Set M,IsOpen U ∧ x ∈ U ∧ ∃ N : ℕ,0<N ∧
        ∀ y ∈ U,J.mem y (fun z => G z*Q z^N) := by
  let P := vanishingIdeal (n := d+t) C
  let J := sumIdeal (principalIdeal (n := d+t) D) P
  let K := InvertibleIdealQuotient.colon J (principalIdeal (n := d+t) G)
  have hP : P.IsCoherent := CartanIrreducible.cartanCoherence C hC
  have hJ : J.IsCoherent := isCoherent_sumIdeal (principalIdeal_coherent D hD) hP
  have hK : K.IsCoherent := CoherentIdealColon.isCoherent_colon_of_isCoherent hJ
    (principalIdeal_coherent G hG)
  have hGh (y : M) : HolomorphicAt (d+t) G y :=
    Eventually.of_forall fun z => hG.mdifferentiable (by simp) z
  have hzero : K.zeroLocus ⊆ {y | Q y=0} := by
    intro y hy
    by_contra hyQ
    have hGJ : J.mem y G := by
      by_cases hyC : y ∈ C
      · have hr := hregular y hyC hyQ
        obtain ⟨hd,_hn⟩ := actual_regular_original_stalk_normal C y hr
        let := hd
        have hDn : originalFunctionImage C ⟨y,hyC⟩ D
            (Eventually.of_forall fun z => hD.mdifferentiable (by simp) z) ≠ 0 := by
          intro hz
          have h1 := hDreg ⟨y,hyC⟩ 1 (by rw [hz,zero_mul])
          exact one_ne_zero h1
        exact actual_regular_cleared_function_division C hC y hr D G c hD (hGh y)
          (fun i => Eventually.of_forall fun z => (hc i).mdifferentiable (by simp) z)
          hDn (Eventually.of_forall hrel)
      · apply le_sumIdeal_right hP
        refine ⟨hGh y,?_⟩
        filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hyC] with z hz hzC
        exact (hz hzC).elim
    have hOne : K.mem y (fun _ => 1) := by
      refine ⟨holomorphicAt_const 1,?_⟩
      intro f hf
      obtain ⟨hfh,s,a,b,ha,hb,he⟩ := hf
      have hfJ : J.mem y f := by
        apply HomogenizedIdeal.mem_of_isInSpanAt hJ
        refine ⟨hfh,s,a,b,?_,hb,he⟩
        intro i
        obtain ⟨j,hj⟩ := ha i
        rw [← hj]
        exact hGJ
      simpa only [mul_one] using hfJ
    exact one_ne_zero (hy (fun _ => 1) hOne)
  obtain ⟨U,hU,hxU,N,hN,hpow⟩ := exists_original_open_fixed_function_power K hK Q hQ hzero x
  refine ⟨hK,hzero,U,hU,hxU,N,hN,?_⟩
  intro y hy
  exact (hpow y hy).2 G (InvertibleIdealQuotient.isInSpanAt_self ⟨0,rfl⟩ (hGh y))

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationMonicColonSupportPower
