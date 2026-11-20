import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.HasGoingUp

/-! # Krull dimension of actual injective integral extensions -/

open Order

namespace SGPT.Foundations.Schemes

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Actual integral extensions cannot increase Krull dimension. -/
theorem integralExtension_ringKrullDim_le (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  apply krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  intro I J hIJ
  exact Ideal.IsIntegral.comap_lt_comap hIJ

/-- Lying over and going up retain all finite strict prime-chain lengths
for an actual injective integral extension. -/
theorem integralExtension_ringKrullDim_eq (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm (integralExtension_ringKrullDim_le R S)
  change (⨆ p : LTSeries (PrimeSpectrum R), (p.length : WithBot ℕ∞)) ≤ ringKrullDim S
  apply iSup_le
  intro p
  obtain ⟨Q, _, hQ, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    p.head.asIdeal (⊥ : Ideal S) (by
      simp [← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective R S)])
  have : Q.IsPrime := hQ
  have : Q.LiesOver p.head.asIdeal := ⟨hcomap.symm⟩
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp p Q
  change (p.length : WithBot ℕ∞) ≤
    ⨆ chain : LTSeries (PrimeSpectrum S), (chain.length : WithBot ℕ∞)
  exact le_iSup_of_le L (by rw [hlen])

end
end SGPT.Foundations.Schemes
