import SGPT.Foundations.Analysis.Pending.CoordinateDensityGeneral
import SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

set_option autoImplicit false

/-!
# The regular-patch density is the determinant density in every dimension

`Pending.FullSpaceLowDimDensity` rewrites the *actual* exterior-power density
`patchDensity` as the normalized determinant coefficient in parameter dimensions
zero, one and two, because the underlying algebraic identity was only available
there.  `Pending.CoordinateDensityGeneral` now proves that identity for every
semipositive real `(1,1)`-form in every dimension, and an admissible
presentation supplies exactly that positivity at a regular parameter point off
its pole set.  So the dimension restriction disappears.

The statement is the dimension-free version of
`FullSpaceLowDimDensity.patchDensity_eq_normalizedTopPowerDensity_of_dim_eq_two`,
with the same two geometric hypotheses (`w` is a genuine parameter of the patch
and its image avoids the pole set) and no dimension hypothesis at all.  It makes
no claim that the resulting parameter measure is the ambient global measure;
that is still the chart/pushforward compatibility step.
-/

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.FullSpaceGeneralDensity

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- **The regular-patch density is the determinant density, in every parameter
dimension.**  At a regular parameter point whose image avoids the pole set, the
pulled-back current form is a semipositive real `(1,1)`-form, so the genuine
exterior-power density used by `acTopMass` coincides with the Bedford--Taylor
determinant coefficient. -/
theorem patchDensity_eq_normalizedTopPowerDensity
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) (w : ComplexModel V.dim) (hw : w ∈ P.parameterDomain)
    (hpole : (complexChartAt (n := n) P.center).val.symm
      (P.coordinateParametrization w) ∉ poleSet p.potential) :
    patchDensity p P w =
      normalizedTopPowerDensity
        ((coordinateCurrentForm p (complexChartAt (n := n) P.center)
          (P.coordinateParametrization w)).compContinuousLinearMap
          (fderiv ℝ P.coordinateParametrization w)) := by
  let e := complexChartAt (n := n) P.center
  have hz : P.coordinateParametrization w ∈ e.val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  have hL := RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hw
  obtain ⟨hA, hpos⟩ := coordinateCurrentForm_isOneOne_and_semipositive p e hz hpole
  have hpullOneOne : IsOneOne
      ((coordinateCurrentForm p e (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w)) :=
    isOneOne_compContinuousLinearMap hA _ hL
  have hpullPos : CoefficientSemipositive
      ((coordinateCurrentForm p e (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w)) :=
    coefficientSemipositive_compContinuousLinearMap hpos _ hL
  unfold patchDensity
  change actualTopPowerDensity
      ((coordinateCurrentForm p e (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w)) =
    normalizedTopPowerDensity
      ((coordinateCurrentForm p e (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w))
  exact actualTopPowerDensity_eq_normalizedTopPowerDensity_of_semipositive _ hpullOneOne hpullPos

end SGPT.Foundations.Analysis.Pending.FullSpaceGeneralDensity
