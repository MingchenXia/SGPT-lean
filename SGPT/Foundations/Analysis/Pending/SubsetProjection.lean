import SGPT.Foundations.Analysis.Pending.FlatDensityMinorExpansion

set_option autoImplicit false

/-!
# The coordinate projection onto a `k`-element set of coordinates

`Pending.FlatDensityMinorExpansion` writes the flat parameter density as the sum,
over the `k`-element subsets `I` of the `n` coordinates of a chart, of the squared
moduli of the `I`-minors of the derivative.  This module identifies each such
minor as the Jacobian of an honest map: the projection

  `π_I : ℂⁿ → ℂ^k`,  `z ↦ (z_{I(0)}, …, z_{I(k-1)})`

composed with the parametrization.  The identity that the area formula consumes
is `det_comp_subsetProjection`: for a `ℂ`-linear `L : ℂ^k → ℂⁿ`, the REAL
determinant of `π_I ∘ L` — an endomorphism of `ℂ^k = ℝ^{2k}` — is exactly the
squared modulus of the `I`-minor of `L`.  So Demailly's sum of minors is a sum of
real Jacobians, one per coordinate projection, which is what
`Pending.MultiplicityAreaBound.sum_lintegral_abs_det_le` integrates.
-/

noncomputable section

open scoped Matrix

namespace SGPT.Foundations.Analysis.Pending.SubsetProjection

open FirstPass FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.FlatDensityGramDeterminant

variable {k n : ℕ}

/-- **The projection of `ℂⁿ` onto the coordinates in `I`**, read off in the
increasing enumeration of `I`. -/
def subsetProjection (I : CardSubset k n) : ComplexModel n →L[ℂ] ComplexModel k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun i : Fin k => z (I.emb i))
      map_add' := by intro z z'; ext i; simp
      map_smul' := by intro c z; ext i; simp }

@[simp]
theorem subsetProjection_apply (I : CardSubset k n) (z : ComplexModel n) (i : Fin k) :
    subsetProjection I z i = z (I.emb i) := rfl

/-- The matrix of `π_I ∘ L` in the standard bases is the `I`-minor of the matrix
of `L`. -/
theorem standardMatrix_comp_subsetProjection (I : CardSubset k n)
    (L : ComplexModel k →L[ℂ] ComplexModel n) :
    standardMatrix (((subsetProjection I).comp L : ComplexModel k →L[ℂ] ComplexModel k) :
        ComplexModel k →ₗ[ℂ] ComplexModel k) =
      (standardRectMatrix (L.restrictScalars ℝ)).submatrix I.emb id := by
  ext p j
  rw [standardMatrix_apply]
  rfl

/-- **The real Jacobian of a coordinate projection of a holomorphic frame.**  For
a `ℂ`-linear `L : ℂ^k → ℂⁿ`, the real determinant of `π_I ∘ L` is the squared
modulus of the `I`-minor of `L`.  In particular it is nonnegative, as it must be
for a holomorphic map. -/
theorem det_comp_subsetProjection (I : CardSubset k n)
    (L : ComplexModel k →L[ℂ] ComplexModel n) :
    (((subsetProjection I).restrictScalars ℝ).comp (L.restrictScalars ℝ)).det =
      ‖((standardRectMatrix (L.restrictScalars ℝ)).submatrix I.emb id).det‖ ^ 2 := by
  have hcoe : ((((subsetProjection I).restrictScalars ℝ).comp (L.restrictScalars ℝ) :
        ComplexModel k →L[ℝ] ComplexModel k) : ComplexModel k →ₗ[ℝ] ComplexModel k) =
      ((((subsetProjection I).comp L : ComplexModel k →L[ℂ] ComplexModel k) :
        ComplexModel k →ₗ[ℂ] ComplexModel k).restrictScalars ℝ) := rfl
  rw [ContinuousLinearMap.det, hcoe, normSq_det_eq_realDet, ← det_standardMatrix,
    standardMatrix_comp_subsetProjection, Complex.normSq_eq_norm_sq]

end SGPT.Foundations.Analysis.Pending.SubsetProjection
