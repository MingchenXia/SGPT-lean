import SGPT.Unibranch.PrimeNov16AnalyticNormalizationLiftedNormalColon

/-! The literal whole ambient test identity descends to the SAME actual quotient, with no domain premise.
Blueprint: prime-nov16-analytic-normalization-quotient-test-colon.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationQuotientTestColon

theorem quotient_test_colon_of_lifted {A : Type*} [CommRing A]
    (P J : Ideal A) (h : A)
    (heq : ((J*Ideal.span {h}) ⊔ P).colon (J : Set A)=Ideal.span {h} ⊔ P) :
    let q := Ideal.Quotient.mk P
    ((J.map q)*Ideal.span {q h}).colon (J.map q : Set (A ⧸ P))=Ideal.span {q h} := by
  let q := Ideal.Quotient.mk P
  let JB := J.map q
  apply le_antisymm
  · intro b hb
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective b
    have ha : a ∈ ((J*Ideal.span {h}) ⊔ P).colon (J : Set A) := by
      apply Submodule.mem_colon.mpr
      intro c hc
      have hprod : q a*q c ∈ JB*Ideal.span {q h} :=
        (Submodule.mem_colon.mp hb) _ (Ideal.mem_map_of_mem q hc)
      obtain ⟨v,hv,he⟩ := Ideal.mem_mul_span_singleton.mp hprod
      obtain ⟨r,hr,rfl⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hv
      have hdiff : a*c-r*h ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp (by
        rw [map_sub,map_mul,map_mul,he,sub_self])
      change a*c ∈ J*Ideal.span {h} ⊔ P
      apply Submodule.mem_sup.mpr
      exact ⟨r*h,Ideal.mem_mul_span_singleton.mpr ⟨r,hr,rfl⟩,a*c-r*h,hdiff,by ring⟩
    rw [heq] at ha
    obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp ha
    obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hu
    apply Ideal.mem_span_singleton.mpr
    refine ⟨q r,?_⟩
    rw [← huv,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr hv,add_zero,hr,map_mul]
  · intro b hb
    apply Submodule.mem_colon.mpr
    intro u hu
    change b*u ∈ JB*Ideal.span {q h}
    simpa only [mul_comm] using Ideal.mul_mem_mul hu hb

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationQuotientTestColon
