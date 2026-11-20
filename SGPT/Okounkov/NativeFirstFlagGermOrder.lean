import SGPT.Okounkov.NativeCurveFlagGermOrder
import Mathlib.RingTheory.Valuation.PrimeMultiplicity

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- The actual original tail ring is a domain, so the internally produced
whole restriction kernel gives a genuine prime original divisor equation. -/
theorem exists_originalFirstFlagGermPrimeParameter {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier) :
    ∃ t : NativeHolGerm (m + 1) F.carrier x.1, Prime t ∧ NativeHolGerm.eval t = 0 ∧
      RingHom.ker (originalFirstFlagGermRestriction F x) = Ideal.span {t} := by
  obtain ⟨t, htne, hteval, hker⟩ := exists_originalFirstFlagGermParameter F x
  have hprime := RingHom.ker_isPrime (originalFirstFlagGermRestriction F x)
  rw [hker] at hprime
  exact ⟨t, (Ideal.span_singleton_prime htne).mp hprime, hteval, hker⟩

/-- One actual original first-divisor equation, selected internally once for
the original flag and point and used for every original germ. -/
def originalFirstFlagGermParameter {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier) :
    NativeHolGerm (m + 1) F.carrier x.1 :=
  Classical.choose (exists_originalFirstFlagGermPrimeParameter F x)

theorem originalFirstFlagGermParameter_spec {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier) :
    Prime (originalFirstFlagGermParameter F x) ∧
      NativeHolGerm.eval (originalFirstFlagGermParameter F x) = 0 ∧
      RingHom.ker (originalFirstFlagGermRestriction F x) =
        Ideal.span {originalFirstFlagGermParameter F x} :=
  Classical.choose_spec (exists_originalFirstFlagGermPrimeParameter F x)

/-- Genuine additive first order on the actual original holomorphic germs in
any positive dimension, from the internally produced prime local equation. -/
def originalFirstFlagGermOrder {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier) :
    AddValuation (NativeHolGerm (m + 1) F.carrier x.1) ℕ∞ :=
  multiplicity_addValuation (originalFirstFlagGermParameter_spec F x).1

private theorem fixedParameter_finiteMultiplicity {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    FiniteMultiplicity (originalFirstFlagGermParameter F x) f := by
  let R := NativeHolGerm (m + 1) F.carrier x.1
  let M : Ideal R := IsLocalRing.maximalIdeal R
  have htM : originalFirstFlagGermParameter F x ∈ M := by
    change ¬IsUnit (originalFirstFlagGermParameter F x)
    rw [NativeHolGerm.isUnit_iff_eval_ne_zero]
    exact fun h => h (originalFirstFlagGermParameter_spec F x).2.1
  by_contra hnot
  have hall := FiniteMultiplicity.not_iff_forall.mp hnot
  have hmem : f ∈ ⨅ N : ℕ, M ^ N := by
    refine (Submodule.mem_iInf _).mpr fun N => ?_
    obtain ⟨q, hq⟩ := hall N
    rw [hq]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htM N)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing M (IsLocalRing.maximalIdeal.isMaximal R).ne_top]
    at hmem
  exact hf hmem

theorem originalFirstFlagGermOrder_eq_top_iff {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) :
    originalFirstFlagGermOrder F x f = ⊤ ↔ f = 0 := by
  change emultiplicity (originalFirstFlagGermParameter F x) f = ⊤ ↔ f = 0
  constructor
  · intro h
    by_contra hf
    exact (finiteMultiplicity_iff_emultiplicity_ne_top.mp
      (fixedParameter_finiteMultiplicity F x f hf)) h
  · rintro rfl
    exact emultiplicity_zero _

theorem originalFirstFlagGermOrder_eq_zero_iff {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) :
    originalFirstFlagGermOrder F x f = 0 ↔ originalFirstFlagGermRestriction F x f ≠ 0 := by
  change emultiplicity (originalFirstFlagGermParameter F x) f = 0 ↔ _
  rw [emultiplicity_eq_zero]
  have hdiv : originalFirstFlagGermParameter F x ∣ f ↔
      originalFirstFlagGermRestriction F x f = 0 := by
    constructor
    · intro h
      have hmem := Ideal.mem_span_singleton.mpr h
      rw [← (originalFirstFlagGermParameter_spec F x).2.2, RingHom.mem_ker] at hmem
      exact hmem
    · intro h
      have hmem : f ∈ RingHom.ker (originalFirstFlagGermRestriction F x) := h
      rw [(originalFirstFlagGermParameter_spec F x).2.2] at hmem
      exact Ideal.mem_span_singleton.mp hmem
  exact hdiv.not

/-- Every nonzero original germ is divided by the SAME internally selected
equation, yielding the actual first order, exact maximal-power criterion and
NONZERO literal original tail quotient needed for higher-rank recursion. -/
theorem exists_originalFirstFlagGermOrder_division {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier)
    (f : NativeHolGerm (m + 1) F.carrier x.1) (hf : f ≠ 0) :
    ∃ (a : ℕ) (q : NativeHolGerm (m + 1) F.carrier x.1),
      f = originalFirstFlagGermParameter F x ^ a * q ∧
      originalFirstFlagGermRestriction F x q ≠ 0 ∧
      originalFirstFlagGermOrder F x f = (a : ℕ∞) ∧
      ∀ b : ℕ, originalFirstFlagGermParameter F x ^ b ∣ f ↔ b ≤ a := by
  have hfinite := fixedParameter_finiteMultiplicity F x f hf
  obtain ⟨q, hfac, hnot⟩ := hfinite.exists_eq_pow_mul_and_not_dvd
  have hres : originalFirstFlagGermRestriction F x q ≠ 0 := by
    intro hzero
    have hmem : q ∈ RingHom.ker (originalFirstFlagGermRestriction F x) := hzero
    rw [(originalFirstFlagGermParameter_spec F x).2.2] at hmem
    exact hnot (Ideal.mem_span_singleton.mp hmem)
  exact ⟨multiplicity (originalFirstFlagGermParameter F x) f, q, hfac, hres,
    hfinite.emultiplicity_eq_multiplicity, fun _ => hfinite.pow_dvd_iff_le_multiplicity⟩

/-- Actual powers of the SAME selected original prime equation attain every
natural first-coordinate value in every positive dimension. -/
theorem originalFirstFlagGermOrder_natCast_surjective {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (x : F.tail.carrier) (a : ℕ) :
    ∃ f : NativeHolGerm (m + 1) F.carrier x.1,
      f ≠ 0 ∧ originalFirstFlagGermOrder F x f = (a : ℕ∞) := by
  have htprime := (originalFirstFlagGermParameter_spec F x).1
  exact ⟨originalFirstFlagGermParameter F x ^ a, pow_ne_zero a htprime.ne_zero,
    emultiplicity_pow_self_of_prime htprime a⟩

/-- The genuine any-dimension first-coordinate order recovers the whole
actual curve DVR order in dimension one. -/
theorem originalCurveGermOrder_eq_firstFlagGermOrder
    (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier) :
    originalCurveGermOrder F x = originalFirstFlagGermOrder F x := by
  let := originalCurveGerm_isDiscreteValuationRing F x
  let R := NativeHolGerm 1 F.carrier x.1
  have hprime := (originalFirstFlagGermParameter_spec F x).1
  have hassoc : Associated (Classical.choose (IsDiscreteValuationRing.exists_prime R))
      (originalFirstFlagGermParameter F x) :=
    IsDiscreteValuationRing.associated_of_irreducible R
      (Classical.choose_spec (IsDiscreteValuationRing.exists_prime R)).irreducible hprime.irreducible
  ext f
  change emultiplicity (Classical.choose (IsDiscreteValuationRing.exists_prime R)) f =
    emultiplicity (originalFirstFlagGermParameter F x) f
  exact emultiplicity_eq_of_associated_left hassoc.symm

end SGPT.Okounkov
