import SGPT.Foundations.Schemes.IntegralExtensionKrullDimension
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.Height

/-!
# Actual prime height in normal-base integral domain extensions

Integral incomparability and the proved normal-base going-down theorem
retain the actual height of every contracted prime.
-/

open Order

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

/-- The actual prime contraction retains height in an injective integral
domain extension of an integrally closed domain. Going down is derived. -/
theorem normalIntegralExtension_primeHeight_eq (R A : Type*)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A] [Algebra.IsIntegral R A]
    (Q : PrimeSpectrum A) : Q.asIdeal.height = (Q.asIdeal.under R).height := by
  let f := PrimeSpectrum.comap (algebraMap R A)
  have hf : StrictMono f := fun _ _ h ↦ Ideal.IsIntegral.comap_lt_comap h
  have h := Order.height_eq_of_strictMono f hf (fun a b hab ↦ by
    obtain ⟨P, hPa, hP, hPb⟩ := Ideal.exists_ideal_lt_liesOver_of_lt a.asIdeal
      (show b.asIdeal < a.asIdeal.under R from hab)
    have : P.IsPrime := hP
    have : P.LiesOver b.asIdeal := hPb
    refine ⟨⟨P, hP⟩, hPa, ?_⟩
    exact PrimeSpectrum.ext (P.over_def b.asIdeal).symm) Q
  exact Q.height_eq_orderHeight.trans (h.trans (f Q).height_eq_orderHeight.symm)

end
end SGPT.Foundations.Schemes
