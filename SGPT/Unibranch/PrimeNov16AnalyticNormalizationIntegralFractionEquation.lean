import SGPT.Unibranch.PrimeNov16AnalyticNormalizationReducedCanonicalClosure
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! Actual integral total fraction, genuine NZD denominator, and whole monic relation.
Blueprint: prime-nov16-analytic-normalization-integral-fraction-equation.tex. -/
set_option autoImplicit false
noncomputable section
open Polynomial
namespace SGPT.Unibranch.PrimeNov16AnalyticNormalizationIntegralFractionEquation

theorem exists_actual_integral_fraction_equation (A : Type*) [CommRing A]
    (b : integralClosure A (FractionRing A)) :
    ∃ (g : A) (d : nonZeroDivisors A) (p : A[X]),
      IsLocalization.mk' (FractionRing A) g d = b.val ∧ p.Monic ∧ aeval b.val p=0 ∧
      g^p.natDegree + ∑ j ∈ Finset.range p.natDegree,
        p.coeff j*d.val^(p.natDegree-j)*g^j = 0 := by
  obtain ⟨⟨g,d⟩,hgd⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) b.val
  change IsLocalization.mk' (FractionRing A) g d = b.val at hgd
  obtain ⟨p,hp,hroot⟩ := b.property
  have heval : aeval (IsLocalization.mk' (FractionRing A) g d) p = 0 := by
    rw [hgd]
    exact hroot
  have hsc := scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero heval
  rw [aeval_algebraMap_apply,map_eq_zero_iff _ (IsFractionRing.injective A (FractionRing A))] at hsc
  rw [aeval_eq_sum_range' (n := p.natDegree+1) (by rw [natDegree_scaleRoots]; omega),
    Finset.sum_range_succ] at hsc
  simp only [coeff_scaleRoots,smul_eq_mul] at hsc
  rw [Nat.sub_self,pow_zero,mul_one,hp.coeff_natDegree,one_mul] at hsc
  exact ⟨g,d,p,hgd,hp,hroot,(add_comm _ _).trans hsc⟩

end SGPT.Unibranch.PrimeNov16AnalyticNormalizationIntegralFractionEquation
