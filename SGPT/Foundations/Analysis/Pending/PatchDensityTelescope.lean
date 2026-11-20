import SGPT.Foundations.Analysis.Pending.CoordinateDensityTelescope
import SGPT.Foundations.Analysis.Pending.CoordinateDensityMixedPullback
import SGPT.Foundations.Analysis.Pending.ACTopMassComparison
import SGPT.Foundations.Analysis.FirstPass.HolomorphicDDC
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff
import SGPT.Foundations.Analysis.FirstPass.TopPowerDensityPositivity
import SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

set_option autoImplicit false

/-!
# The Stokes difference of two parameter densities, slot by slot

`Pending.CoordinateDensityTelescope` expands the exterior-power density of a sum of
two real two-forms on one parameter space.  This module carries that expansion to the
parameter densities the regular-piece masses are built from, and then to the exact two
forms the Stokes obligation
`Pending.SubvarietyStokesMassInterfaces.iSup_formPieceMass_currentForm_eq` compares:
`β + ddᶜv` and `β`.

The only fact needed to transport the expansion is that
`Pending.RegularPatchTransition.patchCoordinateForm` is additive in the form: it is the
chart coefficient composed with the derivative of the parametrization, and both
operations are additive.  Hence, if the coefficients of `c` are the sums of those of `a`
and `b`, then

`patchFormDensity c P w − patchFormDensity a P w
  = ∑_{j < k} actualMixedTopDensity (telescopeFamily A B j)`,  `k = dim V`,

with `A` and `B` the patch coordinate forms of `a` and `b` at `w`.  Every summand carries
the coordinate form of `b` in exactly one slot.

For the Stokes obligation `a` is the background `β` (the presentation has zero
representative and unit error, so its perturbed representative IS `β`), `b` is `ddᶜv`
bundled by `Pending.SmoothDDCForm.ddcForm`, and `c` is
`Pending.ACTopMassComparison.currentForm`.  The resulting identity
`patchFormDensity_currentForm_sub` is the pointwise form of
`(β + ddᶜv)^k − β^k = ddᶜv ∧ ∑_j (β + ddᶜv)^j ∧ β^{k−1−j}` in patch parameters.

What this does NOT do is reduce the Stokes obligation to the classical theorem.  That
obligation, `Pending.SubvarietyStokesMassInterfaces.iSup_formPieceMass_currentForm_eq`, is
an equality of two `ENNReal` SUPREMA of sums of `lintegral`s of `ENNReal.ofReal` of the
parameter densities; what is proved here is a pointwise identity of SIGNED REAL densities.
Three separate things stand between them, and only the last two are classical analysis:

* the `ENNReal`-to-signed bridge: nonnegativity of both densities (proved below,
  `patchFormDensity_kahler_nonneg` and `patchFormDensity_currentForm_nonneg`) together with
  finiteness and the interchange of the sum with the difference, which is NOT written;
* the cut-off: the pieces of a regular-piece family must first be refined so that each
  lies inside one neighbourhood on which the background has a local potential, and the
  per-piece identities must then be summed with a PARTITION OF UNITY subordinate to the
  patches -- disjoint pieces have no cancelling boundary terms.  Note also that the
  coordinate integration by parts available here hypothesises smoothness on all of `ℂ^k`,
  so the local potentials have to be extended;
* the collar estimate near `V_sing`, which is the genuine remainder.

The `dim V = 0` case is an exception: there the two densities are EQUAL, so no analysis is
needed, and `formPieceMass_eq_of_dim_eq_zero` below closes that branch of the obligation
outright.  It is also the one dimension the coordinate integration by parts excludes.
-/

namespace SGPT.Foundations.Analysis.Pending.PatchDensityTelescope

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolumeScaffold
open SGPT.Foundations.Analysis.FirstPass.NumericalRestrictedVolume
open SGPT.Foundations.Analysis.Pending.CoordinateDensityTelescope

open scoped ContDiff

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- **The patch coordinate form is additive in the two-form.** -/
theorem patchCoordinateForm_add (a b c : SmoothRealForm n M 2)
    (hc : ∀ (e : ComplexChart n M) (z : ComplexModel n), c.coeff e z = a.coeff e z + b.coeff e z)
    (P : RegularPatch V) (w : ComplexModel V.dim) :
    RegularPatchTransition.patchCoordinateForm c P w =
      RegularPatchTransition.patchCoordinateForm a P w +
        RegularPatchTransition.patchCoordinateForm b P w := by
  unfold RegularPatchTransition.patchCoordinateForm
  rw [hc]
  exact CoordinateDensityTelescope.compContinuousLinearMap_add _ _ _

/-- **The telescoping expansion of a parameter density.**  If the coefficients of `c`
are the sums of those of `a` and `b`, the parameter densities of `c` and of `a` on a
regular patch differ by the `dim V` mixed densities in which the coordinate form of `b`
occupies exactly one slot. -/
theorem patchFormDensity_sub (a b c : SmoothRealForm n M 2)
    (hc : ∀ (e : ComplexChart n M) (z : ComplexModel n), c.coeff e z = a.coeff e z + b.coeff e z)
    (P : RegularPatch V) (w : ComplexModel V.dim) :
    PatchFormMass.patchFormDensity c P w - PatchFormMass.patchFormDensity a P w =
      ∑ j : Fin V.dim, actualMixedTopDensity
        (telescopeFamily (RegularPatchTransition.patchCoordinateForm a P w)
          (RegularPatchTransition.patchCoordinateForm b P w) j) := by
  unfold PatchFormMass.patchFormDensity
  rw [patchCoordinateForm_add a b c hc P w]
  exact actualTopPowerDensity_add_sub _ _

/-- With zero representative and unit error, the perturbed representative of a
presentation over the background `beta` has the coefficients of `beta` itself. -/
theorem coeff_perturbedRepresentative_of_representative_eq_zero
    {beta : KahlerBackground n M} {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    (q : AdmissibleRestrictedCurrentPresentation beta alpha V ⟨1, one_pos⟩)
    (hq : q.representative = 0) (e : ComplexChart n M) (z : ComplexModel n) :
    (perturbedRepresentative q).val.coeff e z = beta.form.val.coeff e z := by
  unfold perturbedRepresentative
  rw [hq]
  simp

/-- **The Stokes difference in patch parameters.**  For a presentation of the zero class
with zero representative, unit error and chart-smooth real potential `v`, the parameter
density of `β + ddᶜv` minus that of `β` is the sum of the `dim V` mixed densities in
which the coordinate form of `ddᶜv` occupies exactly one slot, `β + ddᶜv` the slots
below it and `β` the slots above.

This is the pointwise algebraic content of
`(β + ddᶜv)^k − β^k = ddᶜv ∧ ∑_{j<k} (β + ddᶜv)^j ∧ β^{k−1−j}`, read in the parameters
of a regular patch.  It is the first step of Stokes against the integration current of
`V`, and after it the ALGEBRA of the
obligation `Pending.SubvarietyStokesMassInterfaces.iSup_formPieceMass_currentForm_eq` is
discharged.  What is left is not algebra but is also not only the classical theorem; the
three steps -- the passage from these signed real densities to the `ENNReal` suprema of the
obligation, the cut-off, and the collar estimate -- are recorded on the hgraph node of
that declaration. -/
theorem patchFormDensity_currentForm_sub (beta : KahlerBackground n M)
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (P : RegularPatch V) (w : ComplexModel V.dim) :
    PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) P w -
        PatchFormMass.patchFormDensity beta.form.val P w =
      ∑ j : Fin V.dim, actualMixedTopDensity
        (telescopeFamily (RegularPatchTransition.patchCoordinateForm beta.form.val P w)
          (RegularPatchTransition.patchCoordinateForm (SmoothDDCForm.ddcForm v hvs) P w) j) := by
  refine patchFormDensity_sub beta.form.val (SmoothDDCForm.ddcForm v hvs)
    (ACTopMassComparison.currentForm q hvs) (fun e z => ?_) P w
  rw [ACTopMassComparison.currentForm_coeff,
    coeff_perturbedRepresentative_of_representative_eq_zero q hq e z,
    SmoothDDCForm.ddcForm_coeff]

/-! ## The Stokes defect is a density on the regular locus

The regular-piece masses are patch-independent because the parameter density of a form
transforms by the real Jacobian of a patch transition
(`Pending.RegularPatchTransition.actualTopPowerDensity_patchCoordinateForm_transition`).
The telescope expansion of the Stokes defect obeys the SAME law, term by term, so the
defect is a genuine density on `V_reg` and can be integrated patch by patch over an
exhaustion. -/

/-- **The Jacobian law for the telescope of the Stokes defect.**  On a transition overlap
the telescope sum in `Q`-parameters is the real determinant of the transition times the
telescope sum in `P`-parameters at the transported point -- the same change-of-variables
factor that the exterior-power densities carry. -/
theorem sum_actualMixedTopDensity_telescopeFamily_transition (a b : SmoothRealForm n M 2)
    {P Q : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ RegularPatchTransition.transitionDomain P Q) :
    (∑ j : Fin V.dim, actualMixedTopDensity
        (telescopeFamily (RegularPatchTransition.patchCoordinateForm a Q w)
          (RegularPatchTransition.patchCoordinateForm b Q w) j)) =
      LinearMap.det
          ((fderiv ℝ (RegularPatchTransition.transition P Q) w :
            ComplexModel V.dim →ₗ[ℝ] ComplexModel V.dim)) *
        ∑ j : Fin V.dim, actualMixedTopDensity
          (telescopeFamily
            (RegularPatchTransition.patchCoordinateForm a P
              (RegularPatchTransition.transition P Q w))
            (RegularPatchTransition.patchCoordinateForm b P
              (RegularPatchTransition.transition P Q w)) j) := by
  rw [RegularPatchTransition.patchCoordinateForm_transition a hw,
    RegularPatchTransition.patchCoordinateForm_transition b hw]
  exact CoordinateDensityTelescope.sum_actualMixedTopDensity_telescopeFamily_compContinuousLinearMap
    _ _ _


/-! ## The potential slot is a genuine `dd^c` in the parameters

The telescope leaves `dd^c v` in one slot of every term. On a regular patch that slot is
not merely the pullback of an ambient two-form: because the parametrization is
holomorphic, it is the `dd^c` OF THE RESTRICTION of `v` to the branch, computed in the
parameter space. This identification is what puts the Stokes defect inside the
coordinate mixed Monge--Ampere formalism of `Pending.MixedHessian`, where integration by
parts against a compactly supported test function is proved. -/

/-- The patch parametrization is `C^∞` over `ℂ` on its parameter domain: it is
`ℂ`-differentiable there, and complex differentiability on an open subset of a
finite-dimensional complex space implies smoothness.  The real-scalar form of this is
`Pending.PatchDensityMeasurability.contDiffOn_coordinateParametrization`, which is
`restrict_scalars ℝ` of this statement; the `ℂ`-version is what the chain rule for the
normalized `dd^c` needs. -/
theorem contDiffOn_complex_coordinateParametrization (P : RegularPatch V) :
    ContDiffOn ℂ ∞ P.coordinateParametrization P.parameterDomain :=
  contDiffOn_of_differentiableOn_complex
    (fun _ hw =>
      (AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
        P hw).differentiableWithinAt)
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P)

/-- **The `dd^c` slot, read in patch parameters, is the `dd^c` of the restriction.**  For a
chart-smooth real function `v` on `X` and a parameter `w` of a regular patch `P` of `V`,
the patch coordinate form of the bundled two-form `dd^c v` is `dd^c (v ∘ P)` computed in
the parameter space.

The parametrization is holomorphic, so the chain rule for the normalized `dd^c`
(`FirstPass.HolomorphicDDC.smoothDDC_comp`) applies. -/
theorem patchCoordinateForm_ddcForm (P : RegularPatch V) {v : M → ℝ}
    (hvs : ChartSmooth (n := n) v) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain) :
    RegularPatchTransition.patchCoordinateForm (SmoothDDCForm.ddcForm v hvs) P w =
      smoothDDC (fun w' => v (P.toManifold w')) w := by
  set eP := complexChartAt (n := n) P.center with heP
  have hmaps : Set.MapsTo P.coordinateParametrization P.parameterDomain eP.val.target :=
    fun w' hw' => P.source_subset (P.flattening.mapsTo_invFun hw')
  have hcomp := HolomorphicDDC.smoothDDC_comp
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P)
    eP.val.open_target (contDiffOn_complex_coordinateParametrization P) (hvs eP) hmaps hw
  rw [RegularPatchTransition.patchCoordinateForm, SmoothDDCForm.ddcForm_coeff]
  exact hcomp.symm

/-- **The Stokes defect in patch parameters, with the potential slot as a `dd^c`.**  The
difference of the parameter densities of `β + dd^cv` and of `β` on a regular patch is the
sum of the `dim V` mixed densities in which `dd^c(v ∘ P)`, the `dd^c` of the restriction of
`v` to the branch computed in the parameter space, occupies exactly one slot.

Every ingredient of the right-hand side now lives in the parameter space: the pullback of
the background and the `dd^c` of a real function of `dim V` complex variables. -/
theorem patchFormDensity_currentForm_sub_ddc (beta : KahlerBackground n M)
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (P : RegularPatch V) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain) :
    PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) P w -
        PatchFormMass.patchFormDensity beta.form.val P w =
      ∑ j : Fin V.dim, actualMixedTopDensity
        (telescopeFamily (RegularPatchTransition.patchCoordinateForm beta.form.val P w)
          (smoothDDC (fun w' => v (P.toManifold w')) w) j) := by
  rw [patchFormDensity_currentForm_sub beta q hq hvs P w,
    patchCoordinateForm_ddcForm P hvs hw]


/-! ## Both sides of the Stokes obligation have nonnegative parameter densities

The regular-piece masses are `ENNReal.ofReal` of the parameter densities, so any use of the
signed telescope identity above has first to know that no truncation occurs. It does not:
the background is K\"ahler and an admissible presentation is positive off its pole set, and
the derivative of the parametrization is complex linear, so both pulled-back coordinate
forms are `(1,1)` and semipositive and their top exterior densities are nonnegative. -/

/-- The pulled-back coordinate form of a closed real `(1,1)`-form is `(1,1)`, and it is
semipositive when the form is. -/
theorem isOneOne_and_semipositive_patchCoordinateForm (a : SmoothRealForm n M 2)
    (P : RegularPatch V) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain)
    (h11 : IsOneOne (a.coeff (complexChartAt (n := n) P.center)
      (P.coordinateParametrization w)))
    (hpos : CoefficientSemipositive (a.coeff (complexChartAt (n := n) P.center)
      (P.coordinateParametrization w))) :
    IsOneOne (RegularPatchTransition.patchCoordinateForm a P w) ∧
      CoefficientSemipositive (RegularPatchTransition.patchCoordinateForm a P w) := by
  have hL := AdmissibleCurrentFormPositivity.RegularPatchDerivative.fderiv_coordinateParametrization_I_smul
    P hw
  exact ⟨RestrictedMassEnvelopeMonotone.isOneOne_compContinuousLinearMap h11 _ hL,
    RestrictedMassEnvelopeMonotone.coefficientSemipositive_compContinuousLinearMap hpos _ hL⟩

/-- **The background parameter density is nonnegative.** -/
theorem patchFormDensity_kahler_nonneg (beta : KahlerBackground n M) (P : RegularPatch V)
    {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain) :
    0 ≤ PatchFormMass.patchFormDensity beta.form.val P w := by
  have hz : P.coordinateParametrization w ∈ (complexChartAt (n := n) P.center).val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  obtain ⟨h11, hpos⟩ := isOneOne_and_semipositive_patchCoordinateForm beta.form.val P hw
    (fun a b => beta.form.property.2 _ _ hz a b) (fun v => beta.isSemipositive _ _ hz v)
  exact MongeAmpere.actualTopPowerDensity_nonneg h11 hpos

/-- **The parameter density of a smooth-potential presentation is nonnegative.**  An
admissible presentation with a real potential has empty pole set, so its coordinate current
form is `(1,1)` and semipositive at every parameter. -/
theorem patchFormDensity_currentForm_nonneg {beta : KahlerBackground n M}
    {alpha : RealBottChern n M} {V : ClosedIrreducibleAnalyticSubvariety n M}
    {epsilon : PositiveError}
    (q : AdmissibleRestrictedCurrentPresentation beta alpha V epsilon)
    {v : M → ℝ} (hvs : ChartSmooth (n := n) v)
    (hpot : q.potential = fun x => ((v x : ℝ) : EReal))
    (P : RegularPatch V) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain) :
    0 ≤ PatchFormMass.patchFormDensity (ACTopMassComparison.currentForm q hvs) P w := by
  have hz : P.coordinateParametrization w ∈ (complexChartAt (n := n) P.center).val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  have hpole : (complexChartAt (n := n) P.center).val.symm
      (P.coordinateParametrization w) ∉ poleSet q.potential := by
    rw [ACTopMassComparison.poleSet_eq_empty q hpot]
    simp
  obtain ⟨h11, hpos⟩ :=
    AdmissibleCurrentFormPositivity.coordinateCurrentForm_isOneOne_and_semipositive q
      (complexChartAt (n := n) P.center) hz hpole
  rw [ACTopMassComparison.coordinateCurrentForm_eq q hvs hpot] at h11 hpos
  obtain ⟨h11', hpos'⟩ := isOneOne_and_semipositive_patchCoordinateForm
    (ACTopMassComparison.currentForm q hvs) P hw h11 hpos
  exact MongeAmpere.actualTopPowerDensity_nonneg h11' hpos'


/-! ## The zero-dimensional case of the Stokes obligation

In complex dimension zero the genuine top exterior power is the empty wedge, whose value on
the empty frame is `1`, for EVERY two-form.  So all parameter densities are `1` and the two
sides of the Stokes obligation coincide, with no analysis at all.  This is the one fragment
of that obligation the telescope closes outright, and it is also the one dimension in which
the coordinate integration by parts of `Pending.MixedHessian` is unavailable. -/

/-- In complex dimension zero every parameter density is `1`. -/
theorem patchFormDensity_eq_one_of_dim_eq_zero (a : SmoothRealForm n M 2)
    {V : ClosedIrreducibleAnalyticSubvariety n M} (hV : V.dim = 0)
    (P : RegularPatch V) (w : ComplexModel V.dim) :
    PatchFormMass.patchFormDensity a P w = 1 := by
  cases V
  subst hV
  unfold PatchFormMass.patchFormDensity
  exact actualTopPowerDensity_zero _

/-- **In complex dimension zero the regular-piece mass does not see the form.** -/
theorem formPieceMass_eq_of_dim_eq_zero (a b : SmoothRealForm n M 2)
    {V : ClosedIrreducibleAnalyticSubvariety n M} (hV : V.dim = 0) {avoid : Set M}
    (F : RegularPieceFamily V avoid) :
    PatchFormMass.formPieceMass a F = PatchFormMass.formPieceMass b F := by
  unfold PatchFormMass.formPieceMass
  refine Finset.sum_congr rfl fun i _ => MeasureTheory.lintegral_congr fun w => ?_
  rw [patchFormDensity_eq_one_of_dim_eq_zero a hV (F.patch i) w,
    patchFormDensity_eq_one_of_dim_eq_zero b hV (F.patch i) w]


end

end SGPT.Foundations.Analysis.Pending.PatchDensityTelescope
