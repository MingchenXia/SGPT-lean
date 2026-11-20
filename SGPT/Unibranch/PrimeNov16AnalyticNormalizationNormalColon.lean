import SGPT.Unibranch.PrimeNov16AnalyticNormalizationOriginalCentralNormal
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Ideal.Colon

/-! Actual normal-stalk test-colon identity, not a supplied equality.
Blueprint: prime-nov16-analytic-normalization-normal-colon.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationNormalColon

theorem colon_eq_principal_of_normal {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    (I : Ideal A) (h : A) (hh : h ≠ 0) (hhI : h ∈ I) :
    (I*Ideal.span {h}).colon (I : Set A) = Ideal.span {h} := by
  let K := FractionRing A
  let L : A →ₗ[A] K := Algebra.linearMap A K
  let N : Submodule A K := Submodule.map L I
  have hHF : algebraMap A K h ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A K).ne hh
  have hN : N ≠ ⊥ := by
    intro he
    have hm : algebraMap A K h ∈ N := ⟨h,hhI,rfl⟩
    rw [he] at hm
    exact hHF hm
  have hNfg : N.FG := Submodule.FG.map L I.fg_of_isNoetherianRing
  apply le_antisymm
  · intro a ha
    let z : K := algebraMap A K a/algebraMap A K h
    have hz : IsIntegral A z := by
      apply isIntegral_of_smul_mem_submodule N hN hNfg z
      intro u hu
      obtain ⟨v,hv,rfl⟩ := hu
      have hav : a*v ∈ I*Ideal.span {h} := (Submodule.mem_colon.mp ha) v hv
      obtain ⟨w,hw,hew⟩ := Ideal.mem_mul_span_singleton.mp hav
      refine ⟨w,hw,?_⟩
      change algebraMap A K w = (algebraMap A K a/algebraMap A K h)*algebraMap A K v
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hHF).mpr
      simpa only [map_mul] using congrArg (algebraMap A K) hew
    obtain ⟨r,hr⟩ := (isIntegrallyClosed_iff K).mp inferInstance hz
    apply Ideal.mem_span_singleton.mpr
    refine ⟨r,?_⟩
    apply IsFractionRing.injective A K
    rw [map_mul]
    have he := (eq_div_iff hHF).mp hr
    exact he.symm.trans (mul_comm _ _)
  · intro a ha
    apply Submodule.mem_colon.mpr
    intro u hu
    simpa only [smul_eq_mul,mul_comm a u] using Ideal.mul_mem_mul hu ha

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationNormalColon
