import SGPT.Okounkov.NativeFlagGermResidue
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

set_option autoImplicit false

noncomputable section

universe u

namespace SGPT.Okounkov

open Set Filter
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending

/-- The actual original curve maximal ideal is the whole kernel of literal
original tail restriction, by the genuine zero-dimensional scalar residue. -/
theorem originalCurveGerm_maximalIdeal_eq_ker
    (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier) :
    IsLocalRing.maximalIdeal (NativeHolGerm 1 F.carrier x.1) =
      RingHom.ker (originalFirstFlagGermRestriction F x) := by
  ext g
  rw [IsLocalRing.mem_maximalIdeal, RingHom.mem_ker]
  change ¬IsUnit g ↔ originalFirstFlagGermRestriction F x g = 0
  rw [NativeHolGerm.isUnit_iff_eval_ne_zero, not_not]
  have hs : NativeHolGerm.zeroDimensionEquiv x
      (originalFirstFlagGermRestriction F x g) = NativeHolGerm.eval g :=
    congrArg (fun b : NativeHolGerm 1 F.carrier x.1 →+* ℂ => b g)
      (originalCurveFlagGermRestriction_eq_eval F x)
  rw [← hs]
  constructor
  · intro h
    exact (NativeHolGerm.zeroDimensionEquiv x).injective
      (h.trans (map_zero _).symm)
  · intro h
    rw [h, map_zero]

/-- The actual original curve divisor internally gives a nonzero generator
of the actual original maximal ideal. -/
theorem exists_originalCurveGermUniformizer
    (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier) :
    ∃ t : NativeHolGerm 1 F.carrier x.1, t ≠ 0 ∧
      IsLocalRing.maximalIdeal (NativeHolGerm 1 F.carrier x.1) = Ideal.span {t} := by
  obtain ⟨t, htne, _, hker⟩ := exists_originalFirstFlagGermParameter F x
  exact ⟨t, htne, (originalCurveGerm_maximalIdeal_eq_ker F x).trans hker⟩

/-- Original curve regularity internally produces a genuine discrete
valuation ring on the actual original germs, without any DVR hypothesis. -/
theorem originalCurveGerm_isDiscreteValuationRing
    (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier) :
    IsDiscreteValuationRing (NativeHolGerm 1 F.carrier x.1) := by
  obtain ⟨t, htne, hmax⟩ := exists_originalCurveGermUniformizer F x
  let R := NativeHolGerm 1 F.carrier x.1
  have hprincipal : (IsLocalRing.maximalIdeal R).IsPrincipal := ⟨t, hmax⟩
  let : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 0 4).mpr hprincipal
  refine { not_a_field' := ?_ }
  intro hbot
  have htmem : t ∈ IsLocalRing.maximalIdeal R := by
    rw [hmax]
    exact Ideal.subset_span (Set.mem_singleton t)
  rw [hbot, Ideal.mem_bot] at htmem
  exact htne htmem

/-- Actual normalized curve order on the original holomorphic germ ring.
The discrete valuation ring is produced internally from the original flag. -/
def originalCurveGermOrder (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier) :
    AddValuation (NativeHolGerm 1 F.carrier x.1) ℕ∞ := by
  let := originalCurveGerm_isDiscreteValuationRing F x
  exact IsDiscreteValuationRing.addVal _

theorem originalCurveGermOrder_eq_top_iff
    (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier)
    (f : NativeHolGerm 1 F.carrier x.1) :
    originalCurveGermOrder F x f = ⊤ ↔ f = 0 := by
  let := originalCurveGerm_isDiscreteValuationRing F x
  exact IsDiscreteValuationRing.addVal_eq_top_iff

theorem originalCurveGermOrder_eq_zero_iff
    (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier)
    (f : NativeHolGerm 1 F.carrier x.1) :
    originalCurveGermOrder F x f = 0 ↔ NativeHolGerm.eval f ≠ 0 := by
  let := originalCurveGerm_isDiscreteValuationRing F x
  exact IsDiscreteValuationRing.addVal_eq_zero_iff.trans
    (NativeHolGerm.isUnit_iff_eval_ne_zero f)

/-- The actual order returns exactly the source's internally produced first
division exponent and its nonzero literal scalar tail quotient. -/
theorem exists_originalCurveGermOrder_division
    (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier)
    (f : NativeHolGerm 1 F.carrier x.1) (hf : f ≠ 0) :
    ∃ (t : NativeHolGerm 1 F.carrier x.1) (a : ℕ)
      (q : NativeHolGerm 1 F.carrier x.1),
      t ≠ 0 ∧ IsLocalRing.maximalIdeal (NativeHolGerm 1 F.carrier x.1) = Ideal.span {t} ∧
      f = t ^ a * q ∧ originalFirstFlagGermRestriction F x q ≠ 0 ∧
      originalCurveGermOrder F x f = (a : ℕ∞) ∧
      ∀ b : ℕ, t ^ b ∣ f ↔ b ≤ a := by
  let := originalCurveGerm_isDiscreteValuationRing F x
  obtain ⟨t, a, q, htne, _, hker, hfac, hres, hmaxpow⟩ :=
    exists_originalFirstFlagGermDivision F x f hf
  have hmax := (originalCurveGerm_maximalIdeal_eq_ker F x).trans hker
  have htirr := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal t htne hmax
  have hqunit : IsUnit q := by
    by_contra hnot
    have hmem : q ∈ IsLocalRing.maximalIdeal (NativeHolGerm 1 F.carrier x.1) := hnot
    rw [originalCurveGerm_maximalIdeal_eq_ker F x, RingHom.mem_ker] at hmem
    exact hres hmem
  obtain ⟨v, hv⟩ := hqunit
  refine ⟨t, a, q, htne, hmax, hfac, hres, ?_, hmaxpow⟩
  apply IsDiscreteValuationRing.addVal_def f v htirr a
  rw [hv, mul_comm]
  exact hfac

/-- Every natural value is attained by an actual nonzero original germ,
using powers of one internally produced original uniformizer. -/
theorem originalCurveGermOrder_natCast_surjective
    (F : OriginalFlagGeometry.{u} 1) (x : F.tail.carrier) (a : ℕ) :
    ∃ f : NativeHolGerm 1 F.carrier x.1,
      f ≠ 0 ∧ originalCurveGermOrder F x f = (a : ℕ∞) := by
  let := originalCurveGerm_isDiscreteValuationRing F x
  obtain ⟨t, htne, hmax⟩ := exists_originalCurveGermUniformizer F x
  have htirr := IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal t htne hmax
  exact ⟨t ^ a, pow_ne_zero a htne, htirr.addVal_pow a⟩

end SGPT.Okounkov
