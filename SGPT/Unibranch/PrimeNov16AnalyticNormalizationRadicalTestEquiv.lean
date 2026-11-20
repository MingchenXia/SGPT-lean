import SGPT.Unibranch.PrimeNov16AnalyticNormalizationIdealColonEquiv

/-! Genuine entire radical test transport for full original stalk/chart equivalences.
Blueprint: prime-nov16-analytic-normalization-radical-test-equiv.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationRadicalTestEquiv
open PrimeNov16AnalyticNormalizationIdealColonEquiv

theorem map_radical_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal A) :
    I.radical.map e.toRingHom=(I.map e.toRingHom).radical := by
  apply Ideal.map_radical_of_surjective e.surjective
  rw [(RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective]
  exact bot_le

theorem radical_test_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (h : A)
    (ht : (((Ideal.span {h}).radical)*Ideal.span {h}).colon ((Ideal.span {h}).radical : Set A)=Ideal.span {h}) :
    (((Ideal.span {e h}).radical)*Ideal.span {e h}).colon
      ((Ideal.span {e h}).radical : Set B)=Ideal.span {e h} := by
  have he := congrArg (fun I : Ideal A => I.map e.toRingHom) ht
  have hcoeff : e.toRingHom h=e h := rfl
  simpa only [map_colon_ringEquiv,Ideal.map_mul,map_radical_ringEquiv,Ideal.map_span,Set.image_singleton,hcoeff] using he

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationRadicalTestEquiv
