import SGPT.Checks.Literature.BJDivisorial.NativeDivisorialFieldValuation
import SGPT.Checks.Literature.BJDivisorial.GeometricDVRRestriction

/-!
# Genuine geometric restriction of the native divisorial Gauss DVR

Both the original ring and its normalized integer valuation are the literal
inverse images along the actual M3 field embedding. The previously proved
relative Abhyankar producer derives discreteness and essential finiteness;
neither is supplied as a divisorial correspondence assumption.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped WithZero

namespace SGPT.NAPotential.BJ.Divisorial.Native
open SGPT.Foundations.PublishedEnvelope

universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ}
  (M : MultiModel k K r) (R' : BirationalDVR k (Polynomial M.S))

/-- The actual inverse-image original coefficient ring. -/
def nativeRestrictedRing : Subalgebra k K := R'.ring.comap (modelFieldToGauss M)

/-- The actual normalized integer-valued field restriction. -/
def nativeIntegerFieldRestriction : Valuation K ℤᵐ⁰ := by
  let := R'.isFractionRing
  exact ((IsDiscreteValuationRing.maximalIdeal R'.ring).valuation
    (FractionRing (Polynomial M.S))).comap (modelFieldToGauss M).toRingHom

/-- Its literal ring is exactly its original integer ball. -/
theorem nativeRestrictedRing_mem_iff (x : K) :
    x ∈ nativeRestrictedRing M R' ↔ nativeIntegerFieldRestriction M R' x ≤ 1 := by
  let : Algebra K (FractionRing (Polynomial M.S)) := (modelFieldToGauss M).toRingHom.toAlgebra
  let : IsScalarTower k K (FractionRing (Polynomial M.S)) :=
    IsScalarTower.of_algebraMap_eq fun a => ((modelFieldToGauss M).commutes a).symm
  let := R'.isFractionRing
  exact mem_restrictedRing_iff R'.ring x

/-- This actual original restricted ring retains K as its fraction field. -/
theorem nativeRestrictedRing_isFractionRing : IsFractionRing (nativeRestrictedRing M R') K := by
  let : Algebra K (FractionRing (Polynomial M.S)) := (modelFieldToGauss M).toRingHom.toAlgebra
  let : IsScalarTower k K (FractionRing (Polynomial M.S)) :=
    IsScalarTower.of_algebraMap_eq fun a => ((modelFieldToGauss M).commutes a).symm
  let := R'.isFractionRing
  exact restrictedRing_isFractionRing (K := K) R'.ring

/-- A nontrivial native restriction produces a GENUINE original geometric
DVR by actual relative Abhyankar and finite curve-field arguments. -/
theorem nativeRestrictedRing_geometricDVR [CharZero k] [Algebra.EssFiniteType k K]
    (h : (nativeIntegerFieldRestriction M R').IsNontrivial) :
    IsDiscreteValuationRing (nativeRestrictedRing M R') ∧
      Algebra.EssFiniteType k (nativeRestrictedRing M R') := by
  let : Algebra K (FractionRing (Polynomial M.S)) := (modelFieldToGauss M).toRingHom.toAlgebra
  let : IsScalarTower k K (FractionRing (Polynomial M.S)) :=
    IsScalarTower.of_algebraMap_eq fun a => ((modelFieldToGauss M).commutes a).symm
  let := R'.isFractionRing
  exact restrictedRing_geometricDVR R'.ring h

end SGPT.NAPotential.BJ.Divisorial.Native
