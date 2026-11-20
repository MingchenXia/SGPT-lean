import SGPT.Unibranch.PrimeNov16AnalyticNormalizationQuotientTestColon

/-! Genuine ring equivalences preserve ENTIRE colons, for full original stalk tests.
Blueprint: prime-nov16-analytic-normalization-ideal-colon-equiv.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationIdealColonEquiv

theorem map_colon_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I J : Ideal A) :
    (I.colon (J : Set A)).map e.toRingHom=(I.map e.toRingHom).colon (J.map e.toRingHom : Set B) := by
  have hm (K : Ideal A) (a : A) : e a ∈ K.map e.toRingHom ↔ a ∈ K :=
    Ideal.apply_mem_of_equiv_iff (f := e)
  ext b
  obtain ⟨a,rfl⟩ := e.surjective b
  rw [hm]
  constructor
  · intro ha
    apply Submodule.mem_colon.mpr
    intro u hu
    obtain ⟨v,hv,rfl⟩ := (Ideal.mem_map_of_equiv e u).mp hu
    change e a*e v ∈ I.map e.toRingHom
    rw [← map_mul,hm]
    exact (Submodule.mem_colon.mp ha) v hv
  · intro ha
    apply Submodule.mem_colon.mpr
    intro v hv
    apply (hm I (a*v)).mp
    rw [map_mul]
    exact (Submodule.mem_colon.mp ha) (e v) (Ideal.mem_map_of_mem e.toRingHom hv)

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationIdealColonEquiv
