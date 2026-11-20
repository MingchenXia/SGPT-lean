import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalComponentSeparators

/-! ONE actual original analytic all-branch denominator and literal branch selection.
Blueprint: prime-nov16-analytic-normalization-original-separator-spread-complete.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSeparatorSpreadComplete
open AnalyticGermDecomposition HolGerm
open PrimeNov16AnalyticNormalizationOriginalComponentSeparators

theorem exists_original_separator_spread_complete {n k : ℕ} (B : Fin k → Set (ComplexModel n))
    (hB : ∀ i,IsIrreducibleGerm (B i))
    (hpair : Pairwise fun i j => ¬ (B i ≤ᶠ[𝓝 0] B j))
    (H : Fin k → ComplexModel n → ℂ)
    (hH : ∀ i,∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (H i) z)
    (hne : ∀ i,¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → H i z=0)
    {N : Set (ComplexModel n)} (hN : N ∈ 𝓝 (0 : ComplexModel n)) :
    ∃ (T : Fin k → ComplexModel n → ℂ) (r : ℝ),
      let Q : ComplexModel n → ℂ := fun z => ∑ i,T i z*H i z
      0<r ∧ ball (0 : ComplexModel n) r ⊆ N ∧
      (∀ i,DifferentiableOn ℂ (T i) (ball 0 r)) ∧
      (∀ i,DifferentiableOn ℂ (H i) (ball 0 r)) ∧
      DifferentiableOn ℂ Q (ball 0 r) ∧
      (∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ Q z) ∧
      (∀ i,¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → Q z=0) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,∀ i,z ∈ B i → Q z=T i z*H i z) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,∀ i j,j ≠ i → z ∈ B j → T i z=0) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,∀ i j,i ≠ j → z ∈ B i → z ∈ B j → Q z=0) ∧
      (∀ z ∈ ball (0 : ComplexModel n) r,∀ i,z ∈ B i → Q z ≠ 0 →
        H i z ≠ 0 ∧ ∀ j,j ≠ i → z ∉ B j) := by
  classical
  obtain ⟨t,ht⟩ := exists_original_component_separators B hB hpair
  choose T hT hTeq using fun i => HolGerm.exists_eq_mk (t i)
  let Q : ComplexModel n → ℂ := fun z => ∑ i,T i z*H i z
  have hprod (i : Fin k) : ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      DifferentiableAt ℂ (fun z => T i z*H i z) z := eventually_differentiableAt_mul (hT i) (hH i)
  have hQg : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ Q z :=
    eventually_differentiableAt_sum Finset.univ hprod
  have hQread : HolGerm.mk Q hQg=∑ i,t i*HolGerm.mk (H i) (hH i) := by
    rw [HolGerm.mk_sum _ _ hprod]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [HolGerm.mk_mul (T i) (H i) (hT i) (hH i),← hTeq i]
  have hQne (i : Fin k) : ¬ ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B i → Q z=0 := by
    intro hz
    have hm : HolGerm.mk Q hQg ∈ vanishingIdeal (B i) := mem_vanishingIdeal_mk.mpr hz
    rw [hQread] at hm
    exact weighted_separator_nonzero B hB t (fun j => HolGerm.mk (H j) (hH j)) ht
      (fun j hj => hne j (mem_vanishingIdeal_mk.mp hj)) i hm
  have hvan (i j : Fin k) (hji : j ≠ i) :
      ∀ᶠ z in 𝓝 (0 : ComplexModel n),z ∈ B j → T i z=0 := by
    apply mem_vanishingIdeal_mk.mp
    rw [← hTeq i]
    exact (ht i).2 j hji
  have hvanAll : ∀ᶠ z in 𝓝 (0 : ComplexModel n),∀ i j,j ≠ i → z ∈ B j → T i z=0 :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => by
      by_cases hji : j=i
      · exact Eventually.of_forall fun _ h => (h hji).elim
      · exact (hvan i j hji).mono fun _ hz _ => hz
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((eventually_all.mpr hT).and ((eventually_all.mpr hH).and (hvanAll.and
      (eventually_of_mem hN fun _ hz => hz))))
  have hbranch : ∀ z ∈ ball (0 : ComplexModel n) r,∀ i,z ∈ B i → Q z=T i z*H i z := by
    intro z hz i hi
    apply Finset.sum_eq_single i
    · intro j _hj hji
      rw [(hball z hz).2.2.1 j i (Ne.symm hji) hi,zero_mul]
    · intro hfalse
      exact (hfalse (Finset.mem_univ i)).elim
  have hinter : ∀ z ∈ ball (0 : ComplexModel n) r,∀ i j,i ≠ j → z ∈ B i → z ∈ B j → Q z=0 := by
    intro z hz i j hij hi hj
    rw [hbranch z hz i hi,(hball z hz).2.2.1 i j (Ne.symm hij) hj,zero_mul]
  refine ⟨T,r,hr,fun z hz => (hball z hz).2.2.2,?_,?_,?_,hQg,hQne,hbranch,(fun z hz => (hball z hz).2.2.1),hinter,?_⟩
  · intro i z hz
    exact ((hball z hz).1 i).differentiableWithinAt
  · intro i z hz
    exact ((hball z hz).2.1 i).differentiableWithinAt
  · intro z hz
    exact (DifferentiableAt.fun_sum (u := Finset.univ) fun i _ => ((hball z hz).1 i).mul ((hball z hz).2.1 i)).differentiableWithinAt
  · intro z hz i hi hq
    constructor
    · intro hhi
      exact hq (by change Q z=0; rw [hbranch z hz i hi,hhi,mul_zero])
    · intro j hji hj
      exact hq (hinter z hz i j (Ne.symm hji) hi hj)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalSeparatorSpreadComplete
