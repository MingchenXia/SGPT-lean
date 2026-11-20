import SGPT.Unibranch.PrimeNov16AnalyticNormalizationRegularDivision

/-! Primitive finite coefficient equations give division, without a supplied polynomial root.
Blueprint: prime-nov16-analytic-normalization-cleared-monic-division.tex. -/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationClearedMonicDivision

theorem exists_divisor_of_cleared_relation {A : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] {k : ℕ} (c : Fin k → A) (g h : A) (hh : h ≠ 0)
    (hrel : g^k+∑ i : Fin k,c i*h^(k-i.val)*g^i.val=0) : ∃ q : A,g=h*q := by
  let f := algebraMap A (FractionRing A)
  have hfn : f h ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective A (FractionRing A)).ne hh
  let u : FractionRing A := f g/f h
  have hrel' : f g^k+∑ i : Fin k,f (c i)*f h^(k-i.val)*f g^i.val=0 := by
    simpa only [map_add,map_sum,map_mul,map_pow,map_zero] using congrArg f hrel
  have he : f h^k*(u^k+∑ i : Fin k,f (c i)*u^i.val)=
      f g^k+∑ i : Fin k,f (c i)*f h^(k-i.val)*f g^i.val := by
    rw [mul_add,Finset.mul_sum]
    congr 1
    · dsimp only [u]
      rw [div_pow,mul_div_cancel₀ _ (pow_ne_zero _ hfn)]
    · apply Finset.sum_congr rfl
      intro i _hi
      have hpow : f h^k=f h^(k-i.val)*f h^i.val := by
        rw [← pow_add,Nat.sub_add_cancel i.isLt.le]
      rw [hpow]
      dsimp only [u]
      rw [div_pow]
      field_simp
  have hroot : u^k+∑ i : Fin k,f (c i)*u^i.val=0 :=
    (mul_eq_zero.mp (he.trans hrel')).resolve_left (pow_ne_zero _ hfn)
  let p : A[X] := X^k+∑ i : Fin k,C (c i)*X^i.val
  have hp : p.Monic := monic_X_pow_add (degree_sum_fin_lt c)
  have hi : IsIntegral A u := by
    refine ⟨p,hp,?_⟩
    simpa only [p,aeval_def,eval₂_add,eval₂_pow,eval₂_X,eval₂_finsetSum,eval₂_mul,eval₂_C] using hroot
  obtain ⟨q,hq⟩ := (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance hi
  refine ⟨q,IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul,hq]
  exact (mul_div_cancel₀ _ hfn).symm

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationClearedMonicDivision
