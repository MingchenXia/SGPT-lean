import SGPT.Foundations.Analysis.Pending.RueckertNullstellensatz

/-! Entire genuine analytic test set equals the full algebraic radical ideal.
Blueprint: prime-nov16-analytic-normalization-germ-test-radical.tex. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
open SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationGermTestRadical
open AnalyticGermDecomposition HolGerm

theorem vanishing_germ_isRadical {n : ℕ} (Z : Set (ComplexModel n)) :
    (vanishingIdeal Z).IsRadical := by
  intro a ha
  obtain ⟨N,hN⟩ := Ideal.mem_radical_iff.mp ha
  obtain ⟨F,hF,rfl⟩ := HolGerm.exists_eq_mk a
  rw [← HolGerm.mk_pow F hF N] at hN
  apply mem_vanishingIdeal_mk.mpr
  filter_upwards [mem_vanishingIdeal_mk.mp hN] with z hz hzZ
  exact eq_zero_of_pow_eq_zero (hz hzZ)

theorem original_test_vanishing_eq_radical {n : ℕ} (Z : Set (ComplexModel n))
    (hZ : IsAnalyticGerm Z) (Q : ComplexModel n → ℂ)
    (hQ : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ Q z) :
    vanishingIdeal (Z ∩ {z | Q z=0}) =
      (vanishingIdeal Z ⊔ Ideal.span {HolGerm.mk Q hQ}).radical := by
  obtain ⟨s,G,hG,hset⟩ := hZ
  let I := vanishingIdeal Z ⊔ Ideal.span {HolGerm.mk Q hQ}
  have hGmem (i : Fin s) : HolGerm.mk (G i) (hG i) ∈ vanishingIdeal Z := by
    apply mem_vanishingIdeal_mk.mpr
    filter_upwards [hset] with z hz hzZ
    exact (hz.mp hzZ) i
  let F : Fin (s+1) → ComplexModel n → ℂ := Fin.cons Q G
  have hFI : ∀ i,∃ hf : ∀ᶠ z in 𝓝 0,DifferentiableAt ℂ (F i) z,
      HolGerm.mk (F i) hf ∈ I := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨hQ,Submodule.mem_sup_right (Ideal.subset_span (mem_singleton _))⟩
    · exact ⟨hG j,Submodule.mem_sup_left (hGmem j)⟩
  have hzero : ∀ᶠ z in 𝓝 0,(∀ i,F i z=0) → z ∈ Z ∩ {z | Q z=0} := by
    filter_upwards [hset] with z hz hFz
    have hq : Q z=0 := hFz 0
    have hg : ∀ i,G i z=0 := fun i => hFz i.succ
    exact ⟨hz.mpr hg,hq⟩
  apply le_antisymm
  · exact (vanishingIdeal_anti hzero).trans
      (RueckertNullstellensatz.vanishingIdeal_le_radical I F hFI)
  · apply (vanishing_germ_isRadical (Z ∩ {z | Q z=0})).radical_le_iff.mpr
    apply sup_le
    · exact vanishingIdeal_anti (Eventually.of_forall fun _z hz => hz.1)
    · apply Ideal.span_le.mpr
      rintro a (rfl : a=HolGerm.mk Q hQ)
      exact mem_vanishingIdeal_mk.mpr (Eventually.of_forall fun _z hz => hz.2)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationGermTestRadical
