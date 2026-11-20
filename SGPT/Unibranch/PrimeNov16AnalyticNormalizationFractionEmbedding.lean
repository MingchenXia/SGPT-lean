import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCentralStalkInjective
import SGPT.Unibranch.PrimeNov16AnalyticNormalizationGraphStalkRegular
import Mathlib.RingTheory.Localization.Away.Basic

/-! Fraction embedding from actual polynomial coordinates and regular denominator.
Blueprint: prime-nov16-analytic-normalization-fraction-embedding.tex. -/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationFractionEmbedding

theorem polynomial_power_denominator {A R ι : Type*} [CommRing A] [CommRing R]
    (f : A →+* R) (h : A) (x : ι → R) (g : ι → A)
    (hx : ∀ i,f h*x i = f (g i)) (P : MvPolynomial ι A) :
    ∃ a : A,∃ m : ℕ,f a = f h^m*MvPolynomial.eval₂ f x P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨a,0,by simp⟩
  | add P Q hP hQ =>
    obtain ⟨a,m,ha⟩ := hP
    obtain ⟨b,n,hb⟩ := hQ
    refine ⟨a*h^n+b*h^m,m+n,?_⟩
    simp only [map_add,map_mul,map_pow,MvPolynomial.eval₂_add,ha,hb,pow_add]
    ring
  | mul_X P i hP =>
    obtain ⟨a,m,ha⟩ := hP
    refine ⟨a*g i,m+1,?_⟩
    rw [map_mul,ha,← hx i]
    simp only [MvPolynomial.eval₂_mul,MvPolynomial.eval₂_X,pow_succ]
    ring

def denominatorAwayEquiv {A R ι : Type*} [CommRing A] [CommRing R]
    (f : A →+* R) (hf : Function.Injective f) (h : A) (x : ι → R) (g : ι → A)
    (hx : ∀ i,f h*x i = f (g i))
    (hsurj : Function.Surjective (MvPolynomial.eval₂ f x)) :
    Localization.Away h ≃+* Localization.Away (f h) :=
  RingEquiv.ofBijective (Localization.awayMap f h) ⟨
    Localization.awayMap_injective_iff.mpr (fun a ha => ⟨0,by
      have hz : a=0 := hf (ha.trans (map_zero f).symm)
      simp [hz]⟩),
    Localization.awayMap_surjective_iff.mpr (fun r => by
      obtain ⟨P,rfl⟩ := hsurj r
      exact polynomial_power_denominator f h x g hx P)⟩

theorem exists_fraction_embedding {A R ι : Type*} [CommRing A] [IsDomain A]
    [CommRing R] [Algebra A R]
    (hf : Function.Injective (algebraMap A R)) (h : A) (hh : h ≠ 0)
    (x : ι → R) (g : ι → A) (hx : ∀ i,algebraMap A R h*x i = algebraMap A R (g i))
    (hsurj : Function.Surjective (MvPolynomial.eval₂ (algebraMap A R) x))
    (hreg : algebraMap A R h ∈ nonZeroDivisors R) :
    ∃ j : R →+* FractionRing A, Function.Injective j ∧
      ∀ a : A,j (algebraMap A R a) = algebraMap A (FractionRing A) a := by
  let e := denominatorAwayEquiv (algebraMap A R) hf h x g hx hsurj
  have hu : IsUnit (algebraMap A (FractionRing A) h) :=
    isUnit_iff_ne_zero.mpr (by simpa only [map_zero] using
      (IsFractionRing.injective A (FractionRing A)).ne hh)
  let L : Localization.Away h →+* FractionRing A := IsLocalization.Away.lift h hu
  have hL : Function.Injective L := by
    apply IsLocalization.injective_of_map_algebraMap_zero
      (M := Submonoid.powers h) (S := Localization.Away h) L
    intro a ha
    have hz : a = 0 := by
      apply IsFractionRing.injective A (FractionRing A)
      rw [map_zero]
      simpa only [L,IsLocalization.Away.lift_eq] using ha
    rw [hz,map_zero]
  have hR : Function.Injective (algebraMap R (Localization.Away (algebraMap A R h))) :=
    IsLocalization.injective (M := Submonoid.powers (algebraMap A R h))
      (S := Localization.Away (algebraMap A R h)) (by
      rintro r ⟨m,rfl⟩
      exact (nonZeroDivisors R).pow_mem hreg m)
  let j : R →+* FractionRing A := L.comp
    (e.symm.toRingHom.comp (algebraMap R (Localization.Away (algebraMap A R h))))
  refine ⟨j,hL.comp (e.symm.injective.comp hR),?_⟩
  intro a
  have he : e (algebraMap A (Localization.Away h) a) =
      algebraMap R (Localization.Away (algebraMap A R h)) (algebraMap A R a) := by
    change Localization.awayMap (algebraMap A R) h (algebraMap A (Localization.Away h) a) = _
    simp only [Localization.awayMap,IsLocalization.Away.map,IsLocalization.map_eq]
  change L (e.symm (algebraMap R (Localization.Away (algebraMap A R h)) (algebraMap A R a))) = _
  rw [← he,RingEquiv.symm_apply_apply]
  exact IsLocalization.Away.lift_eq h hu a

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationFractionEmbedding
