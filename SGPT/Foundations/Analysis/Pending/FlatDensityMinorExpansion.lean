import SGPT.Foundations.Analysis.Pending.FlatDensityGramDeterminant
import SGPT.Foundations.Analysis.Pending.CauchyBinet

set_option autoImplicit false

/-!
# The flat parameter density is the sum of the squared coordinate Jacobians

`Pending.FlatDensityGramDeterminant` writes the flat parameter density of a
chart as `k! · Re det (LᴴL)`, `L = D(e ∘ γ)_w : ℂ^k → ℂⁿ`.  Applying
`Pending.CauchyBinet` to that Gram determinant gives Demailly's expansion
(CADG III.2.6):

  `flatPatchDensity e P w = k! · ∑_{I ⊆ Fin n, |I| = k} ‖det (L_I)‖²`,

where `L_I` is the `k × k` minor of `L` on the rows `I`, i.e. the complex
Jacobian of `π_I ∘ e ∘ γ` — the composition of the parametrization with the
coordinate projection of `ℂⁿ` onto the `k` coordinates in `I`.

This is the step that turns the local finite-volume bound into `binom n k`
separate one-projection statements: each summand integrates, by the complex
change-of-variables formula, to the volume of the image polydisc counted with
the multiplicity of the branched covering `π_I : V → ℂ^I`.

That multiplicity is NOT available for the fixed chart.
`Pending.GermParametrizationData.SetsData.ncard_fibre` gives an exact fibre
count, but only for the ONE projection its adapted coordinates are built for,
and only off the discriminant.  Making all `binom n k` projections finite at
once requires a generic linear change of coordinates, which is the content of
`Pending.GenericProjectionSheetBound.exists_genericProjectionSheetBound`, the
single classical input left under
`Pending.LocalFlatVolumeBound.exists_localFlatVolumeBound`.
-/

noncomputable section

open scoped Matrix

namespace SGPT.Foundations.Analysis.Pending.FlatDensityMinorExpansion

open FirstPass FirstPass.PositiveClasses FirstPass.MongeAmpere
  FirstPass.NumericalRestrictedVolume
open SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.FlatDensityGramDeterminant

variable {k n : ℕ}

/-- The `I`-minor of the standard matrix of `L` is the matrix of `π_I ∘ L`: its
`(i, j)` entry is the `I i`-th coordinate of `L eⱼ`. -/
theorem submatrix_standardRectMatrix_apply (L : ComplexModel k →L[ℝ] ComplexModel n)
    (I : CardSubset k n) (i j : Fin k) :
    ((standardRectMatrix L).submatrix I.emb id) i j = L (coordinateVector j) (I.emb i) :=
  rfl

/-- **The Gram determinant expanded over the `k`-element coordinate sets.**  The
real part is automatic: by `CauchyBinet.im_det_conjTranspose_mul_self` the
determinant of `LᴴL` is real. -/
theorem re_det_rectGram (L : ComplexModel k →L[ℝ] ComplexModel n) :
    ((rectGram L).det).re =
      ∑ I : CardSubset k n, ‖((standardRectMatrix L).submatrix I.emb id).det‖ ^ 2 := by
  rw [rectGram_eq, re_det_conjTranspose_mul_self]

/-- The determinant of the Gram matrix of a complex frame is real. -/
theorem im_det_rectGram (L : ComplexModel k →L[ℝ] ComplexModel n) :
    ((rectGram L).det).im = 0 := by
  rw [rectGram_eq, im_det_conjTranspose_mul_self]

/-- **Demailly's expansion of the flat density of a complex linear map.** -/
theorem actualTopPowerDensity_standard_comp_eq_sum_minors
    (L : ComplexModel k →L[ℝ] ComplexModel n)
    (hL : ∀ v, L (Complex.I • v) = Complex.I • L v) :
    actualTopPowerDensity ((standardHermitianTwoForm n).compContinuousLinearMap L) =
      (k.factorial : ℝ) *
        ∑ I : CardSubset k n, ‖((standardRectMatrix L).submatrix I.emb id).det‖ ^ 2 := by
  rw [actualTopPowerDensity_standard_comp_eq_gram L hL, re_det_rectGram]

section Patch

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **The flat parameter density of a chart as a sum of squared minors.**  At a
parameter whose image is seen by the chart `e`, the flat density is `k!` times
the sum, over the `k`-element sets `I` of coordinates of `ℂⁿ`, of the squared
modulus of the complex Jacobian of `π_I ∘ e ∘ γ`. -/
theorem flatPatchDensity_eq_sum_minors (e : ComplexChart n M) (P : RegularPatch V)
    {w : ComplexModel V.dim}
    (hw : w ∈ FlatPatchDensityComparison.chartDomain e P) :
    FlatPatchDensityComparison.flatPatchDensity e P w =
      (V.dim.factorial : ℝ) *
        ∑ I : CardSubset V.dim n,
          ‖((standardRectMatrix
              (FlatPatchDensityComparison.chartPullbackDerivative e P w)).submatrix
                I.emb id).det‖ ^ 2 := by
  rw [flatPatchDensity_eq_gram e P hw, re_det_rectGram]

end Patch

end SGPT.Foundations.Analysis.Pending.FlatDensityMinorExpansion
