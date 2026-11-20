import SGPT.NAPotential.ProjectiveGraphGenericPrime
import SGPT.NAPotential.ProjectiveGraphLiteralImmersion

/-! # The SAME original graph-open image has exactly the original global relation closure
Blueprint: `projective-graph-generic-prime.tex`. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphOriginalClosure

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MvPolynomial Set
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open ProjectiveGraphRelationCore ProjectiveGraphGenericPrime ProjectiveGraphLiteralImmersion
open ProjectiveGraphCoordinateCharts ProjectiveGraphSegre
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual injective coefficient inclusion preserves EXACTLY the entire original homogeneous relation ideal. -/
theorem relationCore_injective {B K : Type} [CommRing B] [CommRing K] [Algebra ℂ B] [Algebra ℂ K]
    (φ : B →ₐ[ℂ] K) (hφ : Function.Injective φ) {N : ℕ} (v : Fin (N + 1) → B) :
    relationCore (A := ℂ) (fun k => φ (v k)) = relationCore (A := ℂ) v := by
  have hker : RingHom.ker (aeval (R := ℂ) (fun k => φ (v k))).toRingHom =
      RingHom.ker (aeval (R := ℂ) v).toRingHom := by
    ext q
    change aeval (fun k => φ (v k)) q = 0 ↔ aeval v q = 0
    rw [← comp_aeval_apply]
    constructor
    · intro h
      exact hφ (h.trans (map_zero φ).symm)
    · intro h
      rw [h, map_zero]
  exact congrArg (Ideal.homogeneousCore (homogeneousSubmodule (Fin (N + 1)) ℂ)) hker

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) (j : Fin (E.ambientDimension + 1))
  [hU : Nonempty (coordOpen E j)] {s : ℕ} (b : Fin s → X.functionField)

/-- The literal coordinates in SAME B have exactly the SAME full ORIGINAL global Segre ideal. -/
theorem relationCore_literalCoordinates :
    letI := affineChartAlgebra f (coordOpen E j)
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
    relationCore (A := ℂ) (literalCoordinates E j hU b) = relationCore (A := ℂ) (rationalSegreCoordinates E b) := by
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  let B := Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)
  have h := relationCore_injective (B.restrictScalars ℂ).val Subtype.val_injective (literalCoordinates E j hU b)
  change relationCore (A := ℂ) (chartRationalSegreCoordinates E j hU b) =
    relationCore (A := ℂ) (literalCoordinates E j hU b) at h
  exact h.symm.trans (relationCore_chartRationalSegre E j hU b)

/-- **EVERY SAME prescribed nonempty actual graph open has precisely the ORIGINAL global graph relation zero locus as native image closure**. -/
theorem closure_range_literalOpenProjectiveMap
    (W : (Spec (.of (Algebra.adjoin Γ(X, coordOpen E j) (Set.range b)))).Opens) [Nonempty W] :
    letI := schemeFunctionFieldAlgebra f
    closure (Set.range (literalOpenProjectiveMap E j hU b W)) =
      ProjectiveSpectrum.zeroLocus (homogeneousSubmodule (Fin (segreDim E.ambientDimension s + 1)) ℂ)
        ((relationCore (A := ℂ) (rationalSegreCoordinates E b)).toIdeal : Set _) := by
  let := affineChartAlgebra f (coordOpen E j)
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E j)
  change closure (Set.range (W.ι ≫ ProjectiveGraphAffineImmersion.projectiveMap
    (literalCoordinates E j hU b) (ProjectiveGraphCentredChart.coordSegrePivot E j s))) = _
  rw [closure_range_openProjectiveMap _ _ (literalCoordinates_pivot E j hU b) W,
    relationCore_literalCoordinates E j b]

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphOriginalClosure
