import SGPT.Checks.Literature.BJDivisorial.NativeRestrictedGeometry
import SGPT.Checks.Literature.BJDivisorial.RationalDiscreteScale

/-!
# The actual nontrivial native restriction has an original rational weight

Its ring is the literal inverse image and its integer-ball map is the
identity on K. The actual geometric DVR and positive rational normalized
weight are derived internally, retaining every original field fraction.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped WithZero NNReal

namespace SGPT.NAPotential.BJ.Divisorial.Native
open SGPT.Foundations.PublishedEnvelope

universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ}
  (M : MultiModel k K r) (R' : BirationalDVR k (Polynomial M.S))

/-- The entire actual restricted ring is canonically its original integer
ball, and the canonical map is the identity on EVERY original element. -/
def nativeIntegerBallEquiv :
    nativeRestrictedRing M R' ≃+* (nativeIntegerFieldRestriction M R').valuationSubring where
  toFun a := ⟨a, (nativeRestrictedRing_mem_iff M R' a).mp a.2⟩
  invFun a := ⟨a, (nativeRestrictedRing_mem_iff M R' a).mpr a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Scaling and restriction commute on the actual entire field. -/
theorem scaledModelRestriction_eq_scale_integer (s : ℝ≥0) :
    scaledModelFieldRestriction M R' s =
      DiscreteValuationRealScale.valuation (nativeIntegerFieldRestriction M R') s := rfl

/-- Every nontrivial native restriction derives an ACTUAL positive rational
multiple of the true normalized original DVR valuation, on ALL fractions. -/
theorem nativeRestricted_positive_rationalScale [CharZero k] [Algebra.EssFiniteType k K]
    (h : (nativeIntegerFieldRestriction M R').IsNontrivial) (c : ℚ) (hc : 0 < c) :
    let := (nativeRestrictedRing_geometricDVR M R' h).1
    let := nativeRestrictedRing_isFractionRing M R'
    ∃ (d : ℚ) (hd : 0 < d),
      scaledModelFieldRestriction M R' ⟨(c : ℝ), (by exact_mod_cast hc.le)⟩ =
        DiscreteValuationRealScale.valuation
          ((IsDiscreteValuationRing.maximalIdeal (nativeRestrictedRing M R')).valuation K)
          ⟨(d : ℝ), (by exact_mod_cast hd.le)⟩ := by
  let := (nativeRestrictedRing_geometricDVR M R' h).1
  let := nativeRestrictedRing_isFractionRing M R'
  let ρ := (nativeIntegerBallEquiv M R').toRingHom
  let : IsLocalHom ρ := by
    constructor
    intro a ha
    change IsUnit ((nativeIntegerBallEquiv M R') a) at ha
    have hh := ha.map (nativeIntegerBallEquiv M R').symm.toRingHom
    change IsUnit a at hh
    exact hh
  rw [scaledModelRestriction_eq_scale_integer]
  exact exists_positive_rational_normalizedScale (nativeIntegerFieldRestriction M R') c hc ρ rfl

end SGPT.NAPotential.BJ.Divisorial.Native
