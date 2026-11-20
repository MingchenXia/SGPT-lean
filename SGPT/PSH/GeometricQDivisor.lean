import SGPT.PSH.CartierPrimeOrders
import Mathlib.Topology.LocallyFinite

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff

/-- An actual codimension-one analytic prime, indexed canonically by its
literal carrier. No local equation or ideal-generation data are fields. -/
def GeometricPrimeCarrier (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] :=
  {A : Set M // ∃ V : ClosedIrreducibleAnalyticSubvariety n M,
    V.carrier = A ∧ V.dim + 1 = n}

namespace GeometricPrimeCarrier
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Recover the actual existing geometric subvariety from its carrier index. -/
def subvariety (P : GeometricPrimeCarrier n M) : ClosedIrreducibleAnalyticSubvariety n M :=
  Classical.choose P.property

theorem subvariety_carrier (P : GeometricPrimeCarrier n M) :
    P.subvariety.carrier = P.val := (Classical.choose_spec P.property).1

theorem subvariety_codimension (P : GeometricPrimeCarrier n M) :
    P.subvariety.dim + 1 = n := (Classical.choose_spec P.property).2

theorem nonempty (P : GeometricPrimeCarrier n M) : P.val.Nonempty := by
  rw [← P.subvariety_carrier]
  exact P.subvariety.nonempty

theorem isClosed (P : GeometricPrimeCarrier n M) : IsClosed P.val := by
  rw [← P.subvariety_carrier]
  exact P.subvariety.isClosed_carrier

/-- Canonical equality is exactly equality of the original carrier sets. -/
theorem ext {P Q : GeometricPrimeCarrier n M} (h : P.val = Q.val) : P = Q :=
  Subtype.ext h

end GeometricPrimeCarrier

/-- In dimension zero an actual geometric codimension-one prime cannot exist. -/
instance geometricPrimeCarrier_isEmpty_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M] :
    IsEmpty (GeometricPrimeCarrier 0 M) :=
  ⟨fun P => by have h := P.subvariety_codimension; omega⟩

/-- The source's effective geometric rational divisor: actual prime carriers,
original nonnegative rational coefficients, and locally finite nonzero carriers. -/
structure EffectiveGeometricQDivisor (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] where
  coefficient : GeometricPrimeCarrier n M → ℚ
  coefficient_nonneg : ∀ P, 0 ≤ coefficient P
  locallyFinite : LocallyFinite (fun P => if coefficient P = 0 then ∅ else P.val)

namespace EffectiveGeometricQDivisor
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- Literal support of the original nonzero geometric coefficients. -/
def support (D : EffectiveGeometricQDivisor n M) : Set M :=
  ⋃ P, if D.coefficient P = 0 then ∅ else P.val

theorem mem_support (D : EffectiveGeometricQDivisor n M) (x : M) :
    x ∈ D.support ↔ ∃ P, 0 < D.coefficient P ∧ x ∈ P.val := by
  classical
  constructor
  · intro hx
    obtain ⟨P, hxP⟩ := mem_iUnion.mp hx
    by_cases hzero : D.coefficient P = 0
    · simp only [hzero, ite_true, mem_empty_iff_false] at hxP
    · exact ⟨P, lt_of_le_of_ne (D.coefficient_nonneg P) (Ne.symm hzero),
        by simpa only [if_neg hzero] using hxP⟩
  · rintro ⟨P, hpos, hxP⟩
    exact mem_iUnion.mpr ⟨P, by simpa only [if_neg (ne_of_gt hpos)] using hxP⟩

theorem support_isClosed (D : EffectiveGeometricQDivisor n M) : IsClosed D.support := by
  classical
  exact D.locallyFinite.isClosed_iUnion (fun P => by
    split_ifs
    · exact isClosed_empty
    · exact P.isClosed)

/-- The SAME positive original coefficient subtype is locally finite. -/
theorem locallyFinite_positive (D : EffectiveGeometricQDivisor n M) :
    LocallyFinite (fun P : {P // 0 < D.coefficient P} => P.val.val) := by
  have h := D.locallyFinite.comp_injective
    (Subtype.val_injective : Function.Injective
      (Subtype.val : {P // 0 < D.coefficient P} → GeometricPrimeCarrier n M))
  have heq : (fun P : {P // 0 < D.coefficient P} =>
      if D.coefficient P.val = 0 then (∅ : Set M) else P.val.val) =
      (fun P : {P // 0 < D.coefficient P} => P.val.val) := by
    funext P
    exact if_neg (ne_of_gt P.property)
  simpa only [Function.comp_def, heq] using h

end EffectiveGeometricQDivisor
end SGPT.PSH
