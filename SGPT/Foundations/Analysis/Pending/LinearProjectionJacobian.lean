import SGPT.Foundations.Analysis.Pending.ProjectedPatchJacobian

set_option autoImplicit false

/-!
# An ARBITRARY linear projection of a regular patch, and its Jacobian

`Pending.ProjectedPatchJacobian` does this for the `binom n k` COORDINATE
projections `π_I` of a chart, because `Pending.CauchyBinet` expands the flat
density over the coordinate `k`-subsets.  Demailly's own organisation of CADG
III.2.6 does not: he writes the density against a basis of `Λ^{p,p}` made of
DECOMPOSABLE forms `β_s = i β_{s,1}∧\bar β_{s,1}∧…∧i β_{s,p}∧\bar β_{s,p}`, and
then perturbs the `β_{s,j}` ONCE PER `s`, so that the projection attached to `s`
becomes a ramified covering while `(β_s)` remains a basis.  The projection
attached to `s` is `z ↦ (β_{s,1}(z), …, β_{s,p}(z))`, an arbitrary surjective
`ℂ`-linear map `ℂⁿ → ℂ^p`, not a coordinate projection.

This module is the differential-geometric half of that reorganisation: for an
arbitrary `B : ℂⁿ →L[ℂ] ℂ^k`, the composite `B ∘ e ∘ γ_P` is strictly
differentiable where the chart sees the patch, and its REAL Jacobian is the
squared modulus of `det (B·L)` with `L = D(e∘γ_P)`.  For `B = π_I` this is
`Pending.ProjectedPatchJacobian.det_projectedDerivative`, recovered in
`det_linearProjectedDerivative_subsetProjection`.

The algebraic half — that a spanning family of such `B` controls the Gram
determinant — is `Pending.PluckerSpanningBound`.
-/

noncomputable section

open scoped Matrix ContDiff

namespace SGPT.Foundations.Analysis.Pending.LinearProjectionJacobian

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
  FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.FlatPatchDensityComparison
  SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.SubsetProjection
  SGPT.Foundations.Analysis.Pending.FlatDensityGramDeterminant
  SGPT.Foundations.Analysis.Pending.ProjectedPatchJacobian

section Algebra

variable {k n : ℕ}

/-- **The `k × n` matrix of a `ℂ`-linear map `ℂⁿ → ℂ^k`** in the standard bases.
This is the rectangular companion of `MongeAmpere.standardMatrix`, with the
source index on the right. -/
def rectMatrix (B : ComplexModel n →L[ℂ] ComplexModel k) : Matrix (Fin k) (Fin n) ℂ :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin k) ℂ).toBasis (B : ComplexModel n →ₗ[ℂ] ComplexModel k)

theorem rectMatrix_apply (B : ComplexModel n →L[ℂ] ComplexModel k) (i : Fin k) (j : Fin n) :
    rectMatrix B i j = B (coordinateVector j) i := by
  simp [rectMatrix, LinearMap.toMatrix_apply, coordinateVector]

/-- `standardRectMatrix` of a scalar restriction is the matrix of the underlying
`ℂ`-linear map in the standard bases. -/
theorem standardRectMatrix_restrictScalars (L : ComplexModel k →L[ℂ] ComplexModel n) :
    standardRectMatrix (L.restrictScalars ℝ) =
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
        (L : ComplexModel k →ₗ[ℂ] ComplexModel n) := by
  ext p j
  simp [standardRectMatrix, LinearMap.toMatrix_apply, coordinateVector]

/-- **The matrix of `B ∘ L` is `rectMatrix B` times `standardRectMatrix L`.** -/
theorem standardMatrix_comp (B : ComplexModel n →L[ℂ] ComplexModel k)
    (L : ComplexModel k →L[ℂ] ComplexModel n) :
    standardMatrix ((B.comp L : ComplexModel k →L[ℂ] ComplexModel k) :
        ComplexModel k →ₗ[ℂ] ComplexModel k) =
      rectMatrix B * standardRectMatrix (L.restrictScalars ℝ) := by
  rw [rectMatrix, standardRectMatrix_restrictScalars, standardMatrix,
    ← LinearMap.toMatrix_comp (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin k) ℂ).toBasis]
  rfl

/-- **The real Jacobian of an arbitrary linear projection of a holomorphic frame.**
For `ℂ`-linear `B : ℂⁿ → ℂ^k` and `L : ℂ^k → ℂⁿ`, the real determinant of
`B ∘ L`, an endomorphism of `ℂ^k = ℝ^{2k}`, is `‖det (B·L)‖²`. -/
theorem det_comp_linear (B : ComplexModel n →L[ℂ] ComplexModel k)
    (L : ComplexModel k →L[ℂ] ComplexModel n) :
    (((B.restrictScalars ℝ).comp (L.restrictScalars ℝ)).det) =
      ‖(rectMatrix B * standardRectMatrix (L.restrictScalars ℝ)).det‖ ^ 2 := by
  have hcoe : ((((B.restrictScalars ℝ).comp (L.restrictScalars ℝ) :
        ComplexModel k →L[ℝ] ComplexModel k) : ComplexModel k →ₗ[ℝ] ComplexModel k)) =
      ((((B.comp L : ComplexModel k →L[ℂ] ComplexModel k) :
        ComplexModel k →ₗ[ℂ] ComplexModel k).restrictScalars ℝ)) := rfl
  rw [ContinuousLinearMap.det, hcoe, normSq_det_eq_realDet, ← det_standardMatrix,
    standardMatrix_comp, Complex.normSq_eq_norm_sq]

/-- The `I`-th coordinate projection selects the `I`-rows: `rectMatrix π_I * A` is
the `I`-minor block of `A`. -/
theorem rectMatrix_subsetProjection_mul (I : CardSubset k n) (A : Matrix (Fin n) (Fin k) ℂ) :
    rectMatrix (subsetProjection I) * A = A.submatrix I.emb id := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (I.emb i)]
  · simp [rectMatrix_apply, coordinateVector]
  · intro q _ hq
    have : (coordinateVector q : ComplexModel n) (I.emb i) = 0 := by
      simp [coordinateVector, Ne.symm hq]
    simp [rectMatrix_apply, this]
  · simp

end Algebra

section Patch

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The parametrization read in the chart `e` and then projected by `B`. -/
def linearProjectedParametrization (B : ComplexModel n →L[ℂ] ComplexModel V.dim)
    (e : ComplexChart n M) (P : RegularPatch V) : ComplexModel V.dim → ComplexModel V.dim :=
  fun w => B (chartParametrization e P w)

/-- Its real derivative. -/
def linearProjectedDerivative (B : ComplexModel n →L[ℂ] ComplexModel V.dim)
    (e : ComplexChart n M) (P : RegularPatch V) (w : ComplexModel V.dim) :
    ComplexModel V.dim →L[ℝ] ComplexModel V.dim :=
  ((B.restrictScalars ℝ).comp (chartPullbackDerivative e P w))

theorem hasFDerivAt_linearProjectedParametrization
    (B : ComplexModel n →L[ℂ] ComplexModel V.dim) {e : ComplexChart n M}
    {P : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) :
    HasFDerivAt (linearProjectedParametrization B e P)
      (linearProjectedDerivative B e P w) w := by
  have h := (differentiableAt_chartParametrization hw).hasFDerivAt.restrictScalars ℝ
  rw [← chartPullbackDerivative_eq hw] at h
  exact (B.restrictScalars ℝ).hasFDerivAt.comp w h

/-- **Strict differentiability**: the composite is holomorphic where the chart sees
the patch, hence `C^∞` over `ℝ`. -/
theorem hasStrictFDerivAt_linearProjectedParametrization
    (B : ComplexModel n →L[ℂ] ComplexModel V.dim) {e : ComplexChart n M}
    {P : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) :
    HasStrictFDerivAt (linearProjectedParametrization B e P)
      (linearProjectedDerivative B e P w) w := by
  have hdiff : DifferentiableOn ℂ (linearProjectedParametrization B e P) (chartDomain e P) :=
    fun u hu => (B.differentiableAt.comp u
      (differentiableAt_chartParametrization hu)).differentiableWithinAt
  have hC : ContDiffAt ℝ ∞ (linearProjectedParametrization B e P) w :=
    contDiffAt_real_of_differentiableOn_complex hdiff (isOpen_chartDomain e P) hw
  exact hC.hasStrictFDerivAt' (hasFDerivAt_linearProjectedParametrization B hw) (by simp)

/-- **The real Jacobian of the `B`-projected parametrization** is `‖det (B·L)‖²`
with `L` the chart-pullback derivative: the `s`-summand of Demailly's expansion
against a decomposable basis of `Λ^{k,k}`. -/
theorem det_linearProjectedDerivative (B : ComplexModel n →L[ℂ] ComplexModel V.dim)
    {e : ComplexChart n M} {P : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ chartDomain e P) :
    (linearProjectedDerivative B e P w).det =
      ‖(rectMatrix B * standardRectMatrix (chartPullbackDerivative e P w)).det‖ ^ 2 := by
  rw [linearProjectedDerivative, chartPullbackDerivative_eq hw, det_comp_linear]

/-- For `B = π_I` this is `ProjectedPatchJacobian.det_projectedDerivative`. -/
theorem det_linearProjectedDerivative_subsetProjection (I : CardSubset V.dim n)
    {e : ComplexChart n M} {P : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ chartDomain e P) :
    (linearProjectedDerivative (subsetProjection I) e P w).det =
      (projectedDerivative I e P w).det := by
  rw [det_linearProjectedDerivative _ hw, det_projectedDerivative I hw,
    rectMatrix_subsetProjection_mul]

end Patch

end SGPT.Foundations.Analysis.Pending.LinearProjectionJacobian
