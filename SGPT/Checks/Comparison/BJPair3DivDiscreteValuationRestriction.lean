import SGPT.Checks.Comparison.BJPair3DivGeometricDVRFiniteness
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

-- Lane BJ-PAIR (R5/thm:pshdetbydiv bridge): ported from `SGPT.Checks.Literature/SGPT.Checks.Literature/BJDivisorial/DiscreteValuationRestriction.lean`
-- (that library pins another SGPT.Foundations.Envelope revision and cannot be imported here); only the
-- imports, the `Alterations` namespace (now `SGPT.Support.Alterations`) and this file's namespace
-- (`Divisorial` -> `Pair3Div`, `ExternalClassStability` -> `Pair3ClassStability`) are changed.

/-!
# Actual restriction of a normalized DVR valuation

The restricted ring is the literal inverse image of the original DVR under
an actual field embedding. The comparison with its normalized valuation
ball is proved; nontrivial restriction then gives a DVR without a supplied
DVR or divisorial correspondence certificate.
-/

noncomputable section
open IsLocalRing
open scoped WithZero

namespace SGPT.NAPotential.BJ.Pair3Div

variable {k K F : Type*} [Field k] [Field K] [Field F]
  [Algebra k K] [Algebra k F] [Algebra K F] [IsScalarTower k K F]
  (W : Subalgebra k F) [IsDiscreteValuationRing W] [IsFractionRing W F]

/-- The actual inverse-image subalgebra under the given field embedding. -/
def restrictedRing : Subalgebra k K :=
  W.comap (IsScalarTower.toAlgHom k K F)

/-- The actual normalized valuation restricted along the given field embedding. -/
def restrictedValuation : Valuation K ℤᵐ⁰ :=
  ((IsDiscreteValuationRing.maximalIdeal W).valuation F).comap (algebraMap K F)

/-- Restriction retains exactly the original valuation ball. -/
theorem mem_restrictedRing_iff (x : K) :
    x ∈ restrictedRing (K := K) W ↔ restrictedValuation (K := K) W x ≤ 1 := by
  change algebraMap K F x ∈ W ↔
    ((IsDiscreteValuationRing.maximalIdeal W).valuation F) (algebraMap K F x) ≤ 1
  constructor
  · intro hx
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one
      (IsDiscreteValuationRing.maximalIdeal W) (⟨algebraMap K F x, hx⟩ : W)
  · intro hx
    obtain ⟨w, hw⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    change (w : F) = algebraMap K F x at hw
    exact hw ▸ w.2

/-- The actual inverse-image ring is the actual restricted valuation subring. -/
def restrictedRingEquiv : restrictedRing (K := K) W ≃+* (restrictedValuation (K := K) W).valuationSubring :=
  RingEquiv.subringCongr
    (s := (restrictedRing (K := K) W).toSubring)
    (t := (restrictedValuation (K := K) W).valuationSubring.toSubring) (by
    ext x
    exact mem_restrictedRing_iff W x)

/-- A nontrivial restriction of an integer-valued DVR valuation is a DVR. -/
theorem restrictedRing_isDVR (h : (restrictedValuation (K := K) W).IsNontrivial) :
    IsDiscreteValuationRing (restrictedRing (K := K) W) := by
  let : (restrictedValuation (K := K) W).IsNontrivial := h
  let : IsDiscreteValuationRing (restrictedValuation (K := K) W).valuationSubring := inferInstance
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (restrictedRingEquiv (K := K) W).symm

/-- Its actual field of fractions remains the restricted field. -/
theorem restrictedRing_isFractionRing : IsFractionRing (restrictedRing (K := K) W) K := by
  refine IsFractionRing.of_field _ _ fun x => ?_
  rcases (restrictedValuation (K := K) W).valuationSubring.mem_or_inv_mem x with hx | hx
  · refine ⟨⟨x, (mem_restrictedRing_iff W x).mpr hx⟩, 1, ?_⟩
    simp
  · refine ⟨1, ⟨x⁻¹, (mem_restrictedRing_iff W x⁻¹).mpr hx⟩, ?_⟩
    simp

end SGPT.NAPotential.BJ.Pair3Div
