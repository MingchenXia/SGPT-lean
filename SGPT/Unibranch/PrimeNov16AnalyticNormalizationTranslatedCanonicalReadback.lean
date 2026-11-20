import SGPT.Unibranch.PrimeNov16AnalyticNormalizationCanonicalAdjoinReadback

/-! Actual translated-coordinate algebra; no geometric output certificates.
Blueprint: prime-nov16-analytic-normalization-translated-canonical-readback.tex. -/
set_option autoImplicit false
noncomputable section
open Set
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationTranslatedCanonicalReadback

theorem exists_translated_canonical_equiv {A R : Type*} [CommRing A] [IsDomain A]
    [CommRing R] [Algebra A R] [Module.Finite A R] {n k : ℕ}
    (hf : Function.Injective (algebraMap A R)) (h : A) (hh : h ≠ 0)
    (x : Fin (n+k) → R) (b : Fin n → A) (g c : Fin k → A)
    (hxbase : ∀ j,algebraMap A R (b j) = x (Fin.castAdd k j))
    (hxtail : ∀ i,algebraMap A R h*(x (Fin.natAdd n i)+algebraMap A R (c i)) = algebraMap A R (g i))
    (hsurj : Function.Surjective (MvPolynomial.eval₂ (algebraMap A R) x))
    (hreg : algebraMap A R h ∈ nonZeroDivisors R)
    (s : Fin k → integralClosure A (FractionRing A))
    (hs : Submodule.span A (range s) = ⊤)
    (hden : ∀ i,algebraMap A (FractionRing A) h*(s i : FractionRing A) = algebraMap A (FractionRing A) (g i)) :
    ∃ e : R ≃+* integralClosure A (FractionRing A),
      ∀ a : A,e (algebraMap A R a) = algebraMap A _ a := by
  let B := integralClosure A (FractionRing A)
  let t : Fin (n+k) → B := Fin.addCases (fun i => algebraMap A B (b i))
    (fun i => s i-algebraMap A B (c i))
  let num : Fin (n+k) → A := Fin.addCases (fun i => h*b i) (fun i => g i-h*c i)
  have hx : ∀ i,algebraMap A R h*x i = algebraMap A R (num i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [num,Fin.addCases_left,map_mul,hxbase]
    · intro j
      simp only [num,Fin.addCases_right,map_sub,map_mul]
      exact eq_sub_iff_add_eq.mpr (by simpa only [mul_add] using hxtail j)
  have ht : Algebra.adjoin A (range t) = ⊤ := by
    apply top_unique
    intro z _hz
    have hspan : Submodule.span A (range s) ≤ (Algebra.adjoin A (range t)).toSubmodule := by
      apply Submodule.span_le.mpr
      rintro z ⟨i,rfl⟩
      change s i ∈ Algebra.adjoin A (range t)
      have hti : t (Fin.natAdd n i) ∈ Algebra.adjoin A (range t) := Algebra.subset_adjoin (mem_range_self _)
      simp only [t,Fin.addCases_right] at hti
      simpa only [sub_add_cancel] using (Algebra.adjoin A (range t)).add_mem hti
        ((Algebra.adjoin A (range t)).algebraMap_mem (c i))
    apply hspan
    rw [hs]
    trivial
  have hnum : ∀ i,algebraMap A (FractionRing A) h*(t i : FractionRing A) = algebraMap A (FractionRing A) (num i) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp only [t,num,Fin.addCases_left]
      change algebraMap A (FractionRing A) h*algebraMap A (FractionRing A) (b j) = algebraMap A (FractionRing A) (h*b j)
      rw [map_mul]
    · intro j
      simp only [t,num,Fin.addCases_right]
      change algebraMap A (FractionRing A) h*((s j : FractionRing A)-algebraMap A (FractionRing A) (c j)) =
        algebraMap A (FractionRing A) (g j-h*c j)
      rw [mul_sub,hden j,map_sub,map_mul]
  obtain ⟨e,he,_hcoords⟩ := PrimeNov16AnalyticNormalizationCanonicalAdjoinReadback.exists_canonical_equiv
    hf h hh x num hx hsurj hreg t ht hnum
  exact ⟨e,he⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationTranslatedCanonicalReadback
