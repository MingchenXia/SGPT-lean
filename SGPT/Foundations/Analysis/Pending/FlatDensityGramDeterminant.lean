import SGPT.Foundations.Analysis.Pending.CoordinateDensityGeneral
import SGPT.Foundations.Analysis.Pending.FlatPatchDensityComparison

set_option autoImplicit false

/-!
# The flat parameter density is a Gram determinant

`Pending.FlatPatchDensityComparison` reduces the local finite-volume bound for a
Kähler form to the FLAT parameter density of one chart,

  `flatPatchDensity e P w = (L^⋆ω)^{∧k}` evaluated on the standard real frame,

where `L = D(e ∘ P.toManifold)_w : ℂ^k → ℂⁿ` is complex linear and `ω` is the
standard Hermitian form of `ℂⁿ`.  That is still an exterior-power expression,
and Demailly's proof of the local finite-volume theorem (CADG III.2.6) needs it
as a sum over the `k`-element sets of coordinates of the squared moduli of the
corresponding minors of `L`.

This module takes the first step: it replaces the exterior power by a
DETERMINANT, with no reference to the wedge framework.  For every complex linear
`L : ℂ^k → ℂⁿ`,

  `(L^⋆ω)^{∧k} = k! · Re det G(L)`,   `G(L)_{ij} = ⟪L eᵢ, L e_j⟫`,

the Gram matrix of the images of the standard basis (`actualTopPowerDensity_standard_comp_eq_gram`).
`Pending.CoordinateDensityGeneral` had this for a SQUARE `L`, where the Gram
determinant collapses to `|det_ℂ L|²`; the point here is that the argument never
used squareness.  The route is the same: the pullback of `ω` is a semipositive
real `(1,1)`-form, so its genuine top power equals its normalized determinant
density, and its complex coefficient matrix is `π` times the conjugate Gram
matrix.

**What this leaves.**  With `G(L) = LᴴL`, the identity Demailly's proof needs is
now a statement of pure matrix algebra and no longer touches this project's
exterior-power framework:

  `det (Aᴴ A) = ∑_{I ⊆ Fin n, |I| = k} ‖det (A_I)‖²`   (Cauchy--Binet),

for `A : Matrix (Fin n) (Fin k) ℂ` and `A_I` the `k × k` submatrix on the rows
`I`.  Mathlib has no Cauchy--Binet.  That identity, plus a proper branched
projection with a uniform sheet number for each `I`, is what
`Pending.LocalFlatVolumeBound.exists_localFlatVolumeBound` still needs.
-/

noncomputable section

open scoped ComplexOrder Matrix

namespace SGPT.Foundations.Analysis.Pending.FlatDensityGramDeterminant

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.NumericalRestrictedVolume

variable {k n : ℕ}

/-- The Gram matrix `⟪L eᵢ, L e_j⟫` of the images of the standard basis of `ℂ^k`
under a real-linear map to `ℂⁿ`.  For a complex linear `L` it is `LᴴL`. -/
def rectGram (L : ComplexModel k →L[ℝ] ComplexModel n) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j =>
    inner ℂ (L (coordinateVector i)) (L (coordinateVector j))

private theorem conj_eq_re_sub_I_mul_im (z : ℂ) :
    (starRingEnd ℂ) z = (z.re : ℂ) - Complex.I * (z.im : ℂ) := by
  apply Complex.ext <;> simp

private theorem comp_apply (A : CoordinateRealTwoForm n)
    (L : ComplexModel k →L[ℝ] ComplexModel n) (u v : ComplexModel k) :
    (A.compContinuousLinearMap L) ![u, v] = A ![L u, L v] := by
  refine congrArg A ?_
  funext i
  fin_cases i <;> rfl

/-- The pullback of the standard Hermitian form along a complex linear map is a
real `(1,1)`-form. -/
theorem isOneOne_standard_comp (L : ComplexModel k →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    IsOneOne ((standardHermitianTwoForm n).compContinuousLinearMap L) := by
  intro u v
  rw [comp_apply, comp_apply, hL, hL]
  exact standardHermitianTwoForm_isOneOne n _ _

/-- It is semipositive: on a complex line it is the squared norm of the image. -/
theorem coefficientSemipositive_standard_comp (L : ComplexModel k →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    CoefficientSemipositive ((standardHermitianTwoForm n).compContinuousLinearMap L) := by
  intro v
  rw [comp_apply, hL, standardHermitianTwoForm_apply_I_smul_self]
  positivity

/-- **The complex coefficient matrix of a pullback of the standard form is `π`
times the conjugate Gram matrix**, with no squareness assumption. -/
theorem normalizedHermitianMatrix_standard_comp (L : ComplexModel k →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    normalizedHermitianMatrix ((standardHermitianTwoForm n).compContinuousLinearMap L) =
      (Real.pi : ℂ) • (rectGram L).map (starRingEnd ℂ) := by
  ext i j
  have h1 : (standardHermitianTwoForm n).compContinuousLinearMap L
        ![coordinateVector i, Complex.I • coordinateVector j] =
      (inner ℂ (L (coordinateVector i)) (L (coordinateVector j)) : ℂ).re := by
    rw [comp_apply, hL, standardHermitianTwoForm_apply, inner_smul_right]
    simp [Complex.mul_im]
  have h2 : (standardHermitianTwoForm n).compContinuousLinearMap L
        ![coordinateVector i, coordinateVector j] =
      (inner ℂ (L (coordinateVector i)) (L (coordinateVector j)) : ℂ).im := by
    rw [comp_apply, standardHermitianTwoForm_apply]
  rw [normalizedHermitianMatrix, h1, h2]
  simp only [Matrix.smul_apply, Matrix.map_apply, rectGram, Matrix.of_apply, smul_eq_mul,
    conj_eq_re_sub_I_mul_im]

/-- **The flat density of a complex linear map is its Gram determinant.**  For
every complex linear `L : ℂ^k → ℂⁿ`, the genuine top exterior power of the
pullback of the standard Hermitian form, evaluated on the standard real frame of
`ℂ^k`, is `k!` times the real part of the determinant of the Gram matrix
`⟪L eᵢ, L e_j⟫`.

For `k = n` this is `Pending.CoordinateDensityGeneral`'s
`actualTopPowerDensity_standardPullback`, the Gram determinant being `|det_ℂ L|²`
there; the argument never used squareness. -/
theorem actualTopPowerDensity_standard_comp_eq_gram
    (L : ComplexModel k →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    actualTopPowerDensity ((standardHermitianTwoForm n).compContinuousLinearMap L) =
      (k.factorial : ℝ) * ((rectGram L).det).re := by
  have hpi : ((Real.pi : ℝ) ^ k) ≠ 0 := by positivity
  have hconj : ((rectGram L).map (starRingEnd ℂ)).det =
      starRingEnd ℂ ((rectGram L).det) :=
    (RingHom.map_det (starRingEnd ℂ) (rectGram L)).symm
  have hdet : (normalizedHermitianMatrix
      ((standardHermitianTwoForm n).compContinuousLinearMap L)).det =
      ((Real.pi : ℂ) ^ k) * starRingEnd ℂ ((rectGram L).det) := by
    rw [normalizedHermitianMatrix_standard_comp L hL, Matrix.det_smul, hconj,
      Fintype.card_fin]
  rw [actualTopPowerDensity_eq_normalizedTopPowerDensity_of_semipositive _
      (isOneOne_standard_comp L hL) (coefficientSemipositive_standard_comp L hL),
    normalizedTopPowerDensity, complexTopCoefficient_eq, hdet]
  rw [← mul_assoc]
  have hcoe : (((k.factorial : ℝ) / Real.pi ^ k : ℝ) : ℂ) * ((Real.pi : ℂ) ^ k) =
      ((k.factorial : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hcoe, Complex.mul_re]
  simp

/-- The `n × k` matrix of a real-linear map `ℂ^k → ℂⁿ` in the standard bases. -/
def standardRectMatrix (L : ComplexModel k →L[ℝ] ComplexModel n) :
    Matrix (Fin n) (Fin k) ℂ :=
  Matrix.of fun p j => L (coordinateVector j) p

/-- **The Gram matrix is `LᴴL`.**  This is the form the remaining algebraic step
(Cauchy--Binet) consumes: it mentions no exterior power and no manifold. -/
theorem rectGram_eq (L : ComplexModel k →L[ℝ] ComplexModel n) :
    rectGram L = (standardRectMatrix L)ᴴ * standardRectMatrix L := by
  ext i j
  simp only [rectGram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    standardRectMatrix, PiLp.inner_apply, RCLike.inner_apply]
  exact Finset.sum_congr rfl fun x _ => by rw [Complex.star_def]; ring

section Patch

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **The flat parameter density of a chart, as a Gram determinant.**  At a
parameter whose image is seen by the chart `e`, the flat density of the
parametrization is `k!` times the real part of the determinant of `LᴴL`, with
`L = D(e ∘ γ)` the derivative of the parametrization read in `e`. -/
theorem flatPatchDensity_eq_gram (e : ComplexChart n M) (P : RegularPatch V)
    {w : ComplexModel V.dim}
    (hw : w ∈ FlatPatchDensityComparison.chartDomain e P) :
    FlatPatchDensityComparison.flatPatchDensity e P w =
      (V.dim.factorial : ℝ) *
        ((rectGram (FlatPatchDensityComparison.chartPullbackDerivative e P w)).det).re :=
  actualTopPowerDensity_standard_comp_eq_gram _
    (fun v => FlatPatchDensityComparison.chartPullbackDerivative_I_smul hw v)

end Patch

end SGPT.Foundations.Analysis.Pending.FlatDensityGramDeterminant
