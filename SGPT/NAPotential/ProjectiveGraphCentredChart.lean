import SGPT.NAPotential.ProjectiveGraphCoordinateCharts
import SGPT.NAPotential.ProjectiveGraphOriginalPivot

/-!
# Native original graph charts may be chosen to contain the original divisor centre

An arbitrary nonempty original projective coordinate chart gives the same full
homogeneous relation ideal and its native pivot open is the literal original A_j[b].
Blueprint: `projective-graph-centred-charts.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphCentredChart

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite MvPolynomial
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open ProjectiveGraphSegre ProjectiveGraphSegreEquations ProjectiveGraphSegreAlgebra
open ProjectiveGraphCoordinateCharts ProjectiveGraphPivotScheme
open ProjectiveGraphRelationCore

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) {s : ℕ}

omit [IsIntegral X] in
/-- An actual original projective coordinate chart contains any specified original scheme point. -/
theorem exists_coordOpen (z : X) : ∃ j : Fin (E.ambientDimension + 1), z ∈ coordOpen E j :=
  (hyperplaneAtlas E).covers z

/-- The original chosen chart's section image is exactly its actual generic-coordinate algebra. -/
theorem range_coordChart (j : Fin (E.ambientDimension + 1)) (hU : Nonempty (coordOpen E j)) :
    letI := hU
    letI := affineChartAlgebra f (coordOpen E j)
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
    (IsScalarTower.toAlgHom ℂ Γ(X, coordOpen E j) X.functionField).range =
      Algebra.adjoin ℂ (Set.range (chartGenericCoordinates E j hU)) := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨p, rfl⟩ := affinePresentation_surjective f E j a
    change X.presheaf.germ _ (genericPoint X) (generic_mem_coordOpen E j hU)
      (affinePresentation f E j p) ∈ Algebra.adjoin ℂ (Set.range (chartGenericCoordinates E j hU))
    rw [generic_affinePresentation E j hU]
    have hp : aeval (fun k => chartGenericCoordinates E j hU (j.succAbove k)) p ∈
        Algebra.adjoin ℂ (Set.range (fun k => chartGenericCoordinates E j hU (j.succAbove k))) := by
      rw [← aeval_range]
      exact ⟨p, rfl⟩
    exact Algebra.adjoin_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) hp
  · apply Algebra.adjoin_le
    rintro _ ⟨k, rfl⟩
    exact ⟨ratio E j k, rfl⟩

/-- The actual Segre coordinates in the chosen original chart generate the literal original A_j[b]. -/
theorem adjoin_coordGraph (j : Fin (E.ambientDimension + 1))
    (hU : Nonempty (coordOpen E j)) (b : Fin s → X.functionField) :
    letI := hU
    letI := affineChartAlgebra f (coordOpen E j)
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
    (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)).restrictScalars ℂ =
      Algebra.adjoin ℂ (Set.range (chartRationalSegreCoordinates E j hU b)) := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  rw [Algebra.Subalgebra.restrictScalars_adjoin, range_coordChart E j hU]
  have hb : Algebra.adjoin ℂ (Set.range (Fin.cons (1 : X.functionField) b : Fin (s + 1) → X.functionField)) =
      Algebra.adjoin ℂ (Set.range b) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨k, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) k
      · exact one_mem _
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
    · exact Algebra.adjoin_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, by simp⟩)
  symm
  change Algebra.adjoin ℂ (Set.range (segreVector (segreIdx E.ambientDimension s)
    (chartGenericCoordinates E j hU) (Fin.cons (1 : X.functionField) b))) = _
  rw [adjoin_segreVector (segreIdx E.ambientDimension s) (chartGenericCoordinates E j hU)
    (Fin.cons (1 : X.functionField) b) j 0 (chartGenericCoordinates_self E j hU) (by simp),
    Algebra.adjoin_union, hb]

/-- The actual original Segre pivot associated to any chosen original projective coordinate. -/
def coordSegrePivot (j : Fin (E.ambientDimension + 1)) (s : ℕ) :
    Fin (segreDim E.ambientDimension s + 1) := (segreIdx E.ambientDimension s).symm (j, 0)

theorem chartRationalSegreCoordinates_pivot (j : Fin (E.ambientDimension + 1))
    (hU : Nonempty (coordOpen E j)) (b : Fin s → X.functionField) :
    chartRationalSegreCoordinates E j hU b (coordSegrePivot E j s) = 1 := by
  simp [chartRationalSegreCoordinates, coordSegrePivot, segreVector]

/-- A native pivot chart of the original UNCHANGED full Segre relation quotient, in any nonempty original base chart. -/
def coordGlobalChartSchemeIso (j : Fin (E.ambientDimension + 1))
    (hU : Nonempty (coordOpen E j)) (b : Fin s → X.functionField) :
    letI := hU
    letI := affineChartAlgebra f (coordOpen E j)
    letI := schemeFunctionFieldAlgebra f
    (originalPivotOpen (A := ℂ) (rationalSegreCoordinates E b) (coordSegrePivot E j s)).toScheme ≅
      Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b))) := by
  let := hU
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  have halgebra : Algebra.adjoin ℂ (Set.range
      (pivotTail (chartRationalSegreCoordinates E j hU b) (coordSegrePivot E j s))) =
        (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)).restrictScalars ℂ := by
    rw [adjoin_pivotTail _ _ (chartRationalSegreCoordinates_pivot E j hU b)]
    exact (adjoin_coordGraph E j hU b).symm
  let e : Algebra.adjoin ℂ (Set.range
      (pivotTail (chartRationalSegreCoordinates E j hU b) (coordSegrePivot E j s))) ≃+*
        Algebra.adjoin Γ(X, coordOpen E j) (Set.range b) :=
    (Subalgebra.equivOfEq _ _ halgebra).toRingEquiv
  have native := originalPivotChartSchemeIso (A := ℂ) (chartRationalSegreCoordinates E j hU b)
    (coordSegrePivot E j s) (chartRationalSegreCoordinates_pivot E j hU b) ≪≫
      Scheme.Spec.mapIso e.toCommRingCatIso.symm.op
  let O : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule
      (Fin (segreDim E.ambientDimension s + 1)) ℂ) → Scheme := fun J =>
    (Proj.basicOpen (GradedGraphQuotient.grading
      (MvPolynomial.homogeneousSubmodule (Fin (segreDim E.ambientDimension s + 1)) ℂ) J.toIdeal)
      (Ideal.Quotient.mk J.toIdeal (MvPolynomial.X (coordSegrePivot E j s)))).toScheme
  have heq : (originalPivotOpen (A := ℂ) (chartRationalSegreCoordinates E j hU b)
      (coordSegrePivot E j s)).toScheme =
        (originalPivotOpen (A := ℂ) (rationalSegreCoordinates E b) (coordSegrePivot E j s)).toScheme :=
    congrArg O (relationCore_chartRationalSegre E j hU b)
  exact (eqToIso heq).symm ≪≫ native

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphCentredChart
