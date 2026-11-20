import SGPT.Unibranch.PrimeNov16AnalyticNormalizationIntegralRadicalContraction

/-! True integral radical contraction including reduced multibranch extensions.
Blueprint: prime-nov16-analytic-normalization-faithful-integral-radical.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationFaithfulIntegralRadical

theorem radical_contraction {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B]
    (hf : Function.Injective (algebraMap A B)) (I : Ideal A) :
    ((I.map (algebraMap A B)).radical).comap (algebraMap A B) = I.radical := by
  let f : A →+* B := algebraMap A B
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
    obtain ⟨Q,_hQ0,hQ,hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (R := A) (S := B) P (⊥ : Ideal B) (by
        simpa only [← RingHom.ker_eq_comap_bot] using hker)
    have hIQ : I.map f ≤ Q := Ideal.map_le_iff_le_comap.mpr (by rw [hQP]; exact hP.1)
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

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationFaithfulIntegralRadical
