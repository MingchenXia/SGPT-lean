import SGPT.Unibranch.PrimeNov16AnalyticNormalizationNormalColon
import Mathlib.RingTheory.Ideal.GoingUp

/-! Literal canonical radical contraction via genuine integral lying-over.
Blueprint: prime-nov16-analytic-normalization-integral-radical-contraction.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationIntegralRadicalContraction

theorem canonical_radical_contraction {A : Type*} [CommRing A] [IsDomain A]
    (I : Ideal A) :
    ((I.map (algebraMap A (integralClosure A (FractionRing A)))).radical).comap
      (algebraMap A (integralClosure A (FractionRing A))) = I.radical := by
  let B := integralClosure A (FractionRing A)
  let f : A →+* B := algebraMap A B
  have hf : Function.Injective f := by
    intro a b he
    exact IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val he)
  apply le_antisymm
  · intro a ha
    rw [Ideal.radical_eq_sInf]
    apply Submodule.mem_sInf.mpr
    intro P hP
    let : Ideal.IsPrime P := hP.2
    have hker : RingHom.ker f ≤ P := by
      intro a ha
      have ha' : f a = 0 := ha
      have ha0 : a = 0 := hf (ha'.trans (map_zero f).symm)
      simpa only [ha0] using P.zero_mem
    obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
      (R := A) (S := B) P hker
    have hIQ : I.map f ≤ Q := (Ideal.map_le_iff_le_comap).mpr (by rw [hQP]; exact hP.1)
    have haQ : f a ∈ Q := (hQ.radical_le_iff.mpr hIQ) ha
    change a ∈ Q.comap f at haQ
    rw [hQP] at haQ
    exact haQ
  · intro a ha
    obtain ⟨m,hm⟩ := ha
    change f a ∈ (I.map f).radical
    refine ⟨m,?_⟩
    rw [← map_pow]
    exact Ideal.mem_map_of_mem f hm

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationIntegralRadicalContraction
