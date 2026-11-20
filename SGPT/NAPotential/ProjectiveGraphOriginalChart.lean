import SGPT.NAPotential.ProjectiveGraphSegreAlgebra
import SGPT.NAPotential.ProjectiveGraphRegularFractions
import SGPT.NAPotential.ProjectiveGraphQuotient
import SGPT.Foundations.Schemes.NativeSmoothFunctionFieldDimension

/-!
# The native global Segre pivot chart is the literal original A[b]

The original section ring acts through the actual original generic germ. The
actual affine presentation and normalized Segre coordinates identify the same
subalgebra, and the native homogeneous-localization chart gives the scheme iso.
Blueprint: `projective-graph-pivot-algebra.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.NAPotential.AlgPrimes3.ProjectiveGraphOriginalChart

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Set Filter Opposite MvPolynomial
open SGPT.GAGA.H0S SGPT.GAGA.ChowBl SGPT.NAPotential.FSPos
open ProjectiveGraphSegre ProjectiveGraphRegularFractions ProjectiveGraphSegreEquations
open ProjectiveGraphSegreAlgebra ProjectiveGraphQuotient

variable {X : Scheme.{0}} [IsIntegral X] {f : X ⟶ Spec (.of ℂ)}
  (E : ClosedProjectiveEmbedding f) {s : ℕ}

local instance originalChartNonempty : Nonempty (coordOpen E (genericCoordinateIndex E)) :=
  ⟨⟨genericPoint X, genericCoordinateIndex_mem E⟩⟩

/-- The image of the actual original affine section ring is exactly the original coordinate-ratio algebra. -/
theorem range_originalChart :
    letI := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionField_affineChartScalarTower f (coordOpen E (genericCoordinateIndex E))
    (IsScalarTower.toAlgHom ℂ Γ(X, coordOpen E (genericCoordinateIndex E)) X.functionField).range =
      Algebra.adjoin ℂ (Set.range (genericCoordinates E)) := by
  let := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E (genericCoordinateIndex E))
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨p, rfl⟩ := affinePresentation_surjective f E (genericCoordinateIndex E) a
    change X.presheaf.germ _ (genericPoint X) (genericCoordinateIndex_mem E)
      (affinePresentation f E (genericCoordinateIndex E) p) ∈ Algebra.adjoin ℂ (Set.range (genericCoordinates E))
    rw [generic_affinePresentation E]
    have hp : aeval (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k)) p ∈
        Algebra.adjoin ℂ (Set.range (fun k => genericCoordinates E ((genericCoordinateIndex E).succAbove k))) := by
      rw [← aeval_range]
      exact ⟨p, rfl⟩
    exact Algebra.adjoin_mono (by rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩) hp
  · apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    exact ⟨ratio E (genericCoordinateIndex E) j, rfl⟩

/-- The actual global Segre coordinate algebra is exactly the literal original A[b], with original coefficients. -/
theorem adjoin_originalGraph (b : Fin s → X.functionField) :
    letI := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionField_affineChartScalarTower f (coordOpen E (genericCoordinateIndex E))
    (Algebra.adjoin Γ(X, coordOpen E (genericCoordinateIndex E)) (Set.range b)).restrictScalars ℂ =
      Algebra.adjoin ℂ (Set.range (rationalSegreCoordinates E b)) := by
  let := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E (genericCoordinateIndex E))
  rw [Algebra.Subalgebra.restrictScalars_adjoin, range_originalChart E]
  have hb : Algebra.adjoin ℂ (Set.range (Fin.cons (1 : X.functionField) b : Fin (s + 1) → X.functionField)) =
      Algebra.adjoin ℂ (Set.range b) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨j, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) j
      · exact one_mem _
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
    · exact Algebra.adjoin_mono (by rintro _ ⟨i, rfl⟩; exact ⟨i.succ, by simp⟩)
  symm
  change Algebra.adjoin ℂ (Set.range (segreVector (segreIdx E.ambientDimension s)
    (genericCoordinates E) (Fin.cons (1 : X.functionField) b))) = _
  rw [adjoin_segreVector (segreIdx E.ambientDimension s) (genericCoordinates E)
    (Fin.cons (1 : X.functionField) b) (genericCoordinateIndex E) 0 (genericCoordinates_self E) (by simp),
    Algebra.adjoin_union, hb]

/-- The actual original Segre coordinate (generic original base pivot, distinguished rational-map coordinate). -/
def segrePivot (s : ℕ) : Fin (segreDim E.ambientDimension s + 1) :=
  (segreIdx E.ambientDimension s).symm (genericCoordinateIndex E, 0)

theorem rationalSegreCoordinates_pivot (b : Fin s → X.functionField) :
    rationalSegreCoordinates E b (segrePivot E s) = 1 := by
  simp [rationalSegreCoordinates, segrePivot]

/-- The original normalized rational Segre vector with exactly its pivot coordinate removed. -/
def originalSegreTail (b : Fin s → X.functionField) : Fin (segreDim E.ambientDimension s) → X.functionField :=
  pivotTail (rationalSegreCoordinates E b) (segrePivot E s)

/-- Its actual generated algebra is the same original affine graph algebra. -/
theorem adjoin_originalSegreTail (b : Fin s → X.functionField) :
    letI := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
    letI := schemeFunctionFieldAlgebra f
    letI := schemeFunctionField_affineChartScalarTower f (coordOpen E (genericCoordinateIndex E))
    Algebra.adjoin ℂ (Set.range (originalSegreTail E b)) =
      (Algebra.adjoin Γ(X, coordOpen E (genericCoordinateIndex E)) (Set.range b)).restrictScalars ℂ := by
  let := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E (genericCoordinateIndex E))
  rw [originalSegreTail, adjoin_pivotTail _ _ (rationalSegreCoordinates_pivot E b)]
  exact (adjoin_originalGraph E b).symm

/-- **Native affine chart of the original full Segre relation quotient**, in its actual pivot coordinates. -/
def originalSegreChartSchemeIso (b : Fin s → X.functionField) :
    letI := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
    letI := schemeFunctionFieldAlgebra f
    (graphChartOpen (A := ℂ) (originalSegreTail E b)).toScheme ≅
      Spec (.of (Algebra.adjoin Γ(X, coordOpen E (genericCoordinateIndex E)) (Set.range b))) := by
  let := affineChartAlgebra f (coordOpen E (genericCoordinateIndex E))
  let := schemeFunctionFieldAlgebra f
  let := schemeFunctionField_affineChartScalarTower f (coordOpen E (genericCoordinateIndex E))
  let e : Algebra.adjoin ℂ (Set.range (originalSegreTail E b)) ≃+*
      Algebra.adjoin Γ(X, coordOpen E (genericCoordinateIndex E)) (Set.range b) :=
    (Subalgebra.equivOfEq _ _ (adjoin_originalSegreTail E b)).toRingEquiv
  exact graphChartSchemeIso (A := ℂ) (originalSegreTail E b) ≪≫
    Scheme.Spec.mapIso e.toCommRingCatIso.symm.op

end SGPT.NAPotential.AlgPrimes3.ProjectiveGraphOriginalChart
