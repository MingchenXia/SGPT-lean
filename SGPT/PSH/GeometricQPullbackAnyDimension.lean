import SGPT.PSH.GeometricQDivisorPullback

set_option autoImplicit false
noncomputable section
namespace SGPT.PSH
open Set Filter TopologicalSpace
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.AnalyticModificationLocalDiscrepancy
open scoped Topology Manifold ContDiff

universe u

/-- The literal empty family uses the EXISTING genuine grouping producer. -/
def emptyGeometricQDivisor (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] :
    EffectiveGeometricQDivisor n M :=
  geometricQDivisorOfLocallyFiniteFamily (fun i : Fin 0 => Fin.elim0 i)
    (fun _ => 0) (fun i => Fin.elim0 i) (locallyFinite_of_finite _)

theorem emptyGeometricQDivisor_coefficient {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    (P : GeometricPrimeCarrier n M) : (emptyGeometricQDivisor n M).coefficient P = 0 := by
  rw [emptyGeometricQDivisor, geometricQDivisorOfLocallyFiniteFamily_coefficient]
  apply Finset.sum_eq_zero
  intro i _hi
  exact Fin.elim0 i

theorem emptyGeometricQDivisor_support (n : ℕ) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] :
    (emptyGeometricQDivisor n M).support = ∅ := by
  rw [emptyGeometricQDivisor, geometricQDivisorOfLocallyFiniteFamily_support]
  simp

/-- Actual zero-dimensional codimension arithmetic empties the ENTIRE prime
index; the support of ANY original rational divisor is therefore empty. -/
theorem EffectiveGeometricQDivisor.support_eq_empty_of_dimension_zero
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel 0) M] [IsComplexManifold 0 M]
    (D : EffectiveGeometricQDivisor 0 M) : D.support = ∅ := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, _hpos, _hxP⟩ := (D.mem_support x).mp hx
    exact isEmptyElim P
  · intro hx
    exact hx.elim

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {π : Y → X}

/-- ORIGINAL native D and actual modification in ANY dimension. The successor
branch is EXACTLY the accepted genuine grouped ideal-image/order pullback;
zero uses the actual empty prime family, with no positive-dimension model. -/
def geometricQDivisorModificationPullbackAnyDimension
    (D : EffectiveGeometricQDivisor n X) (hπ : IsAnalyticModification (n := n) π) :
    EffectiveGeometricQDivisor n Y := by
  cases n with
  | zero => exact emptyGeometricQDivisor 0 Y
  | succ m => exact geometricQDivisorModificationPullback D hπ

/-- The ENTIRE existing positive-dimensional object is retained literally. -/
theorem geometricQDivisorModificationPullbackAnyDimension_succ
    {m : ℕ} {X Y : Type u}
    [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X] [IsComplexManifold (m + 1) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
    {π : Y → X} (D : EffectiveGeometricQDivisor (m + 1) X)
    (hπ : IsAnalyticModification (n := m + 1) π) :
    geometricQDivisorModificationPullbackAnyDimension D hπ =
      geometricQDivisorModificationPullback D hπ := rfl

/-- ENTIRE support preimage in every actual original dimension, including0. -/
theorem geometricQDivisorModificationPullbackAnyDimension_support
    (D : EffectiveGeometricQDivisor n X) (hπ : IsAnalyticModification (n := n) π) :
    (geometricQDivisorModificationPullbackAnyDimension D hπ).support = π ⁻¹' D.support := by
  cases n with
  | zero =>
    change (emptyGeometricQDivisor 0 Y).support = π ⁻¹' D.support
    rw [emptyGeometricQDivisor_support, D.support_eq_empty_of_dimension_zero, preimage_empty]
  | succ m =>
    exact geometricQDivisorModificationPullback_support D hπ

end SGPT.PSH
