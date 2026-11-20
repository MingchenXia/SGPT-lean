import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentChartProducts
import SGPT.Foundations.Analysis.Pending.RueckertNullstellensatz

/-! Actual analytic zero-support, not a spectral shortcut, produces fixed-function powers.
Blueprint: prime-nov16-analytic-normalization-coherent-support-power.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentSupportPower
open PrimeNov16AnalyticNormalizationCoherentChartProducts IdealWeightPowers
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
theorem principalIdeal_zeroLocus (H : M → ℂ)
    (hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ H) :
    (principalIdeal (n := n) H).zeroLocus = {y | H y=0} := by
  ext y
  have hHy : HolomorphicAt n H y := Eventually.of_forall fun z => hH.mdifferentiable (by simp) z
  constructor
  · intro hy
    exact hy H (InvertibleIdealQuotient.isInSpanAt_self ⟨0,rfl⟩ hHy)
  · intro hy f hf
    obtain ⟨_hf,k,s,a,hs,_ha,he⟩ := hf
    rw [he.self_of_nhds]
    apply Finset.sum_eq_zero
    intro i _hi
    change H y=0 at hy
    obtain ⟨j,hj⟩ := hs i
    have hsi : s i y=0 := (congrFun hj y).symm.trans hy
    rw [hsi,mul_zero]

omit [IsComplexManifold n M] in
theorem literal_pow_mem_idealPow (I : GermIdeal n M) (f : M → ℂ) (x : M)
    (hf : I.mem x f) (hhol : HolomorphicAt n f x) (N : ℕ) :
    (idealPow I N).mem x (fun y => f y^N) := by
  induction N with
  | zero =>
    change HolomorphicAt n (fun y => f y^0) x
    simpa only [pow_zero] using (holomorphicAt_const (n := n) (x := x) 1)
  | succ N ih =>
    change IsInSpanAt (n := n)
      (fun s => ∃ a b,(idealPow I N).mem x a ∧ I.mem x b ∧ s=a*b) x (fun y => f y^(N+1))
    have hpow : HolomorphicAt n (fun y => f y^N) x := by
      filter_upwards [hhol] with y hy
      exact hy.pow N
    have hm := InvertibleIdealQuotient.isInSpanAt_self
      (S := fun s => ∃ a b,(idealPow I N).mem x a ∧ I.mem x b ∧ s=a*b)
      ⟨(fun y => f y^N),f,ih,hf,rfl⟩ (hpow.mul hhol)
    apply IdealWeightPowers.isInSpanAt_congr hm
    exact Eventually.of_forall fun y => pow_succ (f y) N

theorem exists_original_open_fixed_function_power (I : GermIdeal n M) (hI : I.IsCoherent)
    (H : M → ℂ) (hH : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) ∞ H)
    (hzero : I.zeroLocus ⊆ {y | H y=0}) (x : M) :
    ∃ U : Set M,IsOpen U ∧ x ∈ U ∧ ∃ N : ℕ,0<N ∧
      ∀ y ∈ U,I.mem y (fun z => H z^N) := by
  have hz : I.zeroLocus ⊆ (principalIdeal (n := n) H).zeroLocus := by
    rw [principalIdeal_zeroLocus H hH]
    exact hzero
  obtain ⟨U,hU,hxU,N,hN,hinc⟩ := RueckertNullstellensatz.exists_nhds_idealPow_le
    (principalIdeal_coherent H hH) hI hz x
  refine ⟨U,hU,hxU,N,hN,fun y hy => hinc y hy _ ?_⟩
  have hHy : HolomorphicAt n H y := Eventually.of_forall fun z => hH.mdifferentiable (by simp) z
  exact literal_pow_mem_idealPow _ H y (InvertibleIdealQuotient.isInSpanAt_self ⟨0,rfl⟩ hHy) hHy N

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationCoherentSupportPower
