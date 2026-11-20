import SGPT.Foundations.Schemes.NativeSmoothFunctionFieldDimension
import SGPT.Foundations.Schemes.FiniteTypeDomainDimension
import SGPT.Foundations.Schemes.PositiveProjectiveCechInputs
import SGPT.Foundations.Schemes.NativeFanoAlgebraicFiniteness

universe u
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace SGPT.Foundations.Schemes
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The SAME original structural algebra on each actual affine chart is
finite type, derived from the actual locally finite type structural map. -/
theorem affineChartAlgebra_finiteType {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] {V : X.Opens} (hV : IsAffineOpen V) :
    letI := affineChartAlgebra f V
    Algebra.FiniteType K Γ(X, V) := by
  let := affineChartAlgebra f V
  apply RingHom.finiteType_algebraMap.mp
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
  change LocallyOfFiniteType (affineStructuralMap K Γ(X, V))
  rw [← affineChartStructuralMap_eq_affineStructuralMap f hV]
  infer_instance

/-- The actual same affine coordinate ring has intrinsic transcendence
degree n, derived from its true fraction field and original scalar tower. -/
theorem SmoothProjectiveFano.affineChart_trdeg {n : ℕ} (F : SmoothProjectiveFano n)
    (V : F.scheme.Opens) [Nonempty V] (hV : IsAffineOpen V) :
    letI := affineChartAlgebra F.structureMap V
    Algebra.trdeg ℂ Γ(F.scheme, V) = (n : Cardinal) := by
  let := affineChartAlgebra F.structureMap V
  let := schemeFunctionFieldAlgebra F.structureMap
  have := schemeFunctionField_affineChartScalarTower F.structureMap V
  have : IsFractionRing Γ(F.scheme, V) F.scheme.functionField :=
    functionField_isFractionRing_of_isAffineOpen F.scheme V hV
  have : Algebra.IsAlgebraic Γ(F.scheme, V) F.scheme.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(F.scheme, V))
  have hz : Algebra.trdeg Γ(F.scheme, V) F.scheme.functionField = 0 :=
    trdeg_eq_zero_iff.mpr inferInstance
  have h := trdeg_add_eq ℂ Γ(F.scheme, V) (A := F.scheme.functionField)
  simpa only [hz, add_zero, F.functionField_trdeg] using h

/-- Original affine chart dimension is computed from actual finite type and
intrinsic function-field geometry, not a supplied dimension certificate. -/
theorem SmoothProjectiveFano.affineChart_ringKrullDim {n : ℕ} (F : SmoothProjectiveFano n)
    (V : F.scheme.Opens) [Nonempty V] (hV : IsAffineOpen V) :
    ringKrullDim Γ(F.scheme, V) = (n : WithBot ℕ∞) := by
  let := affineChartAlgebra F.structureMap V
  have := F.projective.locallyOfFiniteType
  have := affineChartAlgebra_finiteType F.structureMap hV
  exact finiteTypeDomain_ringKrullDim_of_trdeg ℂ Γ(F.scheme, V) n (F.affineChart_trdeg V hV)

/-- Empty affine opens have the actual zero section ring and dimension bottom;
all actual Fano affine opens therefore satisfy the same intrinsic upper bound. -/
theorem SmoothProjectiveFano.affineChart_ringKrullDim_le {n : ℕ} (F : SmoothProjectiveFano n)
    (V : F.scheme.Opens) (hV : IsAffineOpen V) :
    ringKrullDim Γ(F.scheme, V) ≤ (n : WithBot ℕ∞) := by
  classical
  by_cases h : Nonempty V
  · let := h
    exact le_of_eq (F.affineChart_ringKrullDim V hV)
  · have hV0 : V = ⊥ := by
      apply bot_unique
      intro x hx
      exact (h ⟨⟨x, hx⟩⟩).elim
    let : Subsingleton Γ(F.scheme, V) := CommRingCat.subsingleton_of_isTerminal
      (TopCat.Sheaf.isTerminalOfEqEmpty F.scheme.sheaf hV0)
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le

/-- The ORIGINAL projective coordinate intersections satisfy the intrinsic
Fano dimension upper bound, including empty geometric intersections. -/
theorem SmoothProjectiveFano.projectiveSubset_ringKrullDim_le {n : ℕ}
    (F : SmoothProjectiveFano n) (S : Finset (Fin (F.projective.ambientDimension + 1)))
    (hS : S.Nonempty) :
    ringKrullDim Γ(F.scheme,
      actualSchemeSubsetOpen (actualPolynomialProjectivePullbackCoordinateOpens F.projective.map) S) ≤
        (n : WithBot ℕ∞) :=
  F.affineChart_ringKrullDim_le _
    (actualPolynomialProjectivePullbackSubsetOpen_isAffine ℂ F.projective.ambientDimension
      F.projective.map S hS)

end
end SGPT.Foundations.Schemes
