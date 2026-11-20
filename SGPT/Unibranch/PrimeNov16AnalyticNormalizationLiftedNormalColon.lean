import SGPT.Unibranch.PrimeNov16AnalyticNormalizationNormalColon

/-! Entire ambient lift of the actual normal quotient test-colon identity.
Blueprint: prime-nov16-analytic-normalization-lifted-normal-colon.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationLiftedNormalColon

theorem lifted_colon_eq {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P J : Ideal A) [IsDomain (A ⧸ P)] [IsIntegrallyClosed (A ⧸ P)]
    (h : A) (hhJ : h ∈ J) (hh : Ideal.Quotient.mk P h ≠ 0) :
    ((J*Ideal.span {h}) ⊔ P).colon (J : Set A) = Ideal.span {h} ⊔ P := by
  let q := Ideal.Quotient.mk P
  let B := A ⧸ P
  let JB := J.map q
  have hJB : q h ∈ JB := Ideal.mem_map_of_mem q hhJ
  have htest := PrimeNov16AnalyticNormalizationNormalColon.colon_eq_principal_of_normal JB (q h) hh hJB
  apply le_antisymm
  · intro a ha
    have ham : q a ∈ (JB*Ideal.span {q h}).colon (JB : Set B) := by
      apply Submodule.mem_colon.mpr
      intro u hu
      obtain ⟨v,hv,rfl⟩ := (Ideal.mem_map_iff_of_surjective q Ideal.Quotient.mk_surjective).mp hu
      have hav : a*v ∈ J*Ideal.span {h} ⊔ P := (Submodule.mem_colon.mp ha) v hv
      obtain ⟨w,hw,t,ht,hwt⟩ := Submodule.mem_sup.mp hav
      obtain ⟨c,hc,hcw⟩ := Ideal.mem_mul_span_singleton.mp hw
      apply Ideal.mem_mul_span_singleton.mpr
      refine ⟨q c,Ideal.mem_map_of_mem q hc,?_⟩
      change q c*q h = q a*q v
      calc
        q c*q h = q w := by rw [← map_mul,hcw]
        _ = q (a*v) := by
          rw [← hwt,map_add,Ideal.Quotient.eq_zero_iff_mem.mpr ht,add_zero]
        _ = q a*q v := map_mul q a v
    rw [htest] at ham
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp ham
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective b
    have hp : a-h*r ∈ P := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub,map_mul,hb,sub_self]
    apply Submodule.mem_sup.mpr
    exact ⟨h*r,Ideal.mem_span_singleton.mpr ⟨r,rfl⟩,a-h*r,hp,by ring⟩
  · intro a ha
    obtain ⟨b,hb,c,hc,hbc⟩ := Submodule.mem_sup.mp ha
    apply Submodule.mem_colon.mpr
    intro u hu
    change a*u ∈ J*Ideal.span {h} ⊔ P
    rw [← hbc,add_mul]
    apply Ideal.add_mem
    · apply (show J*Ideal.span {h} ≤ J*Ideal.span {h} ⊔ P from le_sup_left)
      simpa only [mul_comm b u] using Ideal.mul_mem_mul hu hb
    · exact (show P ≤ J*Ideal.span {h} ⊔ P from le_sup_right) (P.mul_mem_right u hc)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationLiftedNormalColon
