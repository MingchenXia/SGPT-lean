import SGPT.Foundations.Schemes.IntegralExtensionPrimeHeight
import SGPT.Foundations.Schemes.FiniteTypeDomainDimension
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Actual closed point heights of finite-type domains

Polynomial maximal-ideal heights are derived by induction. Genuine Noether
normalization then gives the full intrinsic dimension at every closed point.
-/

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- Every actual maximal ideal of a polynomial algebra over a field has
height equal to the actual number of variables. -/
theorem mvPolynomial_maximalIdeal_height (K : Type) [Field K] (d : ℕ)
    (M : Ideal (MvPolynomial (Fin d) K)) [M.IsMaximal] : M.height = d := by
  induction d with
  | zero =>
      have h : (M.height : WithBot ℕ∞) ≤ (↑(0 : ℕ∞) : WithBot ℕ∞) := by
        simpa [ringKrullDim_eq_zero_of_field] using M.height_le_ringKrullDim_of_isPrime
      exact le_antisymm (WithBot.coe_le_coe.mp h) bot_le
  | succ d ih =>
      let R := MvPolynomial (Fin d) K
      let e := (MvPolynomial.finSuccEquiv K d).toRingEquiv
      let P := M.map e
      have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
      let p : Ideal R := P.comap Polynomial.C
      have : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
      have : P.LiesOver p := ⟨rfl⟩
      have hp : p.height = d := ih p
      have h := Polynomial.height_eq_height_add_one p P
      rw [hp] at h
      exact (e.height_map M).symm.trans (by simpa only [Nat.cast_add, Nat.cast_one] using h)

/-- Every actual maximal ideal of a genuine finite-type domain over a
field has the full intrinsic Krull dimension of that original ring. -/
theorem finiteTypeDomain_maximalIdeal_height_eq_dimension (K A : Type)
    [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (M : Ideal A) [M.IsMaximal] : (M.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let P := MvPolynomial (Fin d) K
  let : Algebra P A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral P A := ⟨hint⟩
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  have : IsIntegrallyClosed P := UniqueFactorizationMonoid.instIsIntegrallyClosed
  have : (M.under P).IsMaximal := inferInstance
  have hM : M.height = d :=
    (normalIntegralExtension_primeHeight_eq P A ⟨M, inferInstance⟩).trans
      (mvPolynomial_maximalIdeal_height K d (M.under P))
  have hdim : ringKrullDim A = (d : WithBot ℕ∞) :=
    (integralExtension_ringKrullDim_eq P A).trans (by
      simp [P, ringKrullDim_eq_zero_of_field])
  rw [hM, hdim]
  rfl

end
end SGPT.Foundations.Schemes
