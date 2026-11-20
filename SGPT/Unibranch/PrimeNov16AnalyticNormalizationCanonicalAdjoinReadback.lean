import SGPT.Unibranch.PrimeNov16AnalyticNormalizationFractionEmbedding

/-! Canonical integral-closure equality manufactured from raw coordinate data.
Blueprint: prime-nov16-analytic-normalization-canonical-adjoin-readback.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationCanonicalAdjoinReadback

theorem exists_canonical_equiv {A R ι : Type*} [CommRing A] [IsDomain A]
    [CommRing R] [Algebra A R] [Module.Finite A R]
    (hf : Function.Injective (algebraMap A R)) (h : A) (hh : h ≠ 0)
    (x : ι → R) (g : ι → A)
    (hx : ∀ i,algebraMap A R h*x i = algebraMap A R (g i))
    (hsurj : Function.Surjective (MvPolynomial.eval₂ (algebraMap A R) x))
    (hreg : algebraMap A R h ∈ nonZeroDivisors R)
    (s : ι → integralClosure A (FractionRing A))
    (hs : Algebra.adjoin A (Set.range s) = ⊤)
    (hden : ∀ i,algebraMap A (FractionRing A) h*(s i : FractionRing A) =
      algebraMap A (FractionRing A) (g i)) :
    ∃ e : R ≃+* integralClosure A (FractionRing A),
      (∀ a : A,e (algebraMap A R a) = algebraMap A _ a) ∧ ∀ i,e (x i) = s i := by
  obtain ⟨j,hj,hjA⟩ := PrimeNov16AnalyticNormalizationFractionEmbedding.exists_fraction_embedding
    hf h hh x g hx hsurj hreg
  let J : R →ₐ[A] FractionRing A := { j with commutes' := hjA }
  have hint (r : R) : IsIntegral A (J r) :=
    (Algebra.IsIntegral.isIntegral (R := A) r).map J
  let F : R →ₐ[A] integralClosure A (FractionRing A) :=
    { toFun := fun r => ⟨J r,hint r⟩
      map_zero' := by apply Subtype.ext; exact map_zero J
      map_one' := by apply Subtype.ext; exact map_one J
      map_add' := fun r t => by apply Subtype.ext; exact map_add J r t
      map_mul' := fun r t => by apply Subtype.ext; exact map_mul J r t
      commutes' := fun a => by apply Subtype.ext; exact hjA a }
  have hF : Function.Injective F := fun r t he => hj (congrArg Subtype.val he)
  have hFcoords (i : ι) : F (x i) = s i := by
    apply Subtype.ext
    apply mul_left_cancel₀ (show algebraMap A (FractionRing A) h ≠ 0 from by
      simpa only [map_zero] using (IsFractionRing.injective A (FractionRing A)).ne hh)
    change algebraMap A (FractionRing A) h*j (x i) = _
    rw [← hjA h,← map_mul,hx i,hjA,hjA h,hden i]
  have htop : F.range = ⊤ := by
    apply top_unique
    rw [← hs]
    apply Algebra.adjoin_le
    rintro b ⟨i,rfl⟩
    exact ⟨x i,hFcoords i⟩
  have hsurjective : Function.Surjective F := by
    intro b
    have hb : b ∈ F.range := by rw [htop]; trivial
    exact hb
  let e : R ≃+* integralClosure A (FractionRing A) := RingEquiv.ofBijective F.toRingHom ⟨hF,hsurjective⟩
  exact ⟨e,F.commutes,hFcoords⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationCanonicalAdjoinReadback
