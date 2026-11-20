import SGPT.Foundations.Analysis.Pending.RegularPatchDensityContinuity
import SGPT.Foundations.Analysis.Pending.TopPowerDensityUpperBound

set_option autoImplicit false

/-!
# The parameter density of a smooth form against the flat density of one chart

The local finite-volume statement for an analytic subvariety is a statement in
ONE chart: the flat `2k`-volume of `V` inside a small coordinate ball is finite
(Demailly, *Complex analytic and differential geometry*, III.2.6).  The mass
`Pending.SubvarietyBackgroundMass` bounds is instead that of a global Kähler
form, and its parameter density is read in the chart at the CENTRE OF EACH
PATCH, a chart that varies with the patch.

This module removes both discrepancies.  Fix any chart `e`.  For a regular patch
`P` whose image meets the source of `e`, the composite

  `chartPullbackDerivative e P w = D(τ)_{γ_P(w)} ∘ D(γ_P)_w`,

with `τ` the transition from the chart at `P.center` to `e`, is the derivative of
`e ∘ P.toManifold` read in the parameters, and

* `patchCoordinateForm_eq_chart` — the pulled-back coordinate two-form of ANY
  smooth real two-form is the coefficient of that form in the FIXED chart `e`,
  at the `e`-coordinate of the parametrized point, composed with that derivative.
  The chart at `P.center` has disappeared;
* `flatPatchDensity e P w` — the same construction for the standard Hermitian
  form, i.e. the flat parameter density of the chart `e`;
* `formPatchDensity_le_flatPatchDensity` — if the coefficient of a semipositive
  `(1,1)`-form is bounded by `c` in the chart `e` at the relevant point, then its
  parameter density is at most `c^{dim V}` times the flat one.

The comparison constant always exists pointwise (the operator norm), so the only
thing a neighbourhood has to supply is its uniformity, which is continuity of the
coefficient on the chart target.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.FlatPatchDensityComparison

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.RegularPatchNeighborhood FirstPass.MongeAmpere

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The parameters of `P` at which the parametrized point is seen by the chart
`e`. -/
def chartDomain (e : ComplexChart n M) (P : RegularPatch V) : Set (ComplexModel V.dim) :=
  {w | w ∈ P.parameterDomain ∧ P.toManifold w ∈ e.val.source}

theorem chartDomain_subset_parameterDomain (e : ComplexChart n M) (P : RegularPatch V) :
    chartDomain e P ⊆ P.parameterDomain := fun _ hw => hw.1

/-- On `chartDomain e P` the coordinates of the parametrized point lie in the
source of the transition from the chart at `P.center` to `e`. -/
theorem mem_chartTransition_source {e : ComplexChart n M} {P : RegularPatch V}
    {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) :
    P.coordinateParametrization w ∈
      (chartTransition (complexChartAt (n := n) P.center) e).source := by
  refine ⟨P.source_subset (RegularPatch.coordinateParametrization_mem_source P hw.1), ?_⟩
  show (complexChartAt (n := n) P.center).val.symm (P.coordinateParametrization w) ∈ e.val.source
  exact hw.2

/-- The transition from the chart at `P.center` to `e` takes the coordinates of
the parametrized point to its `e`-coordinates. -/
theorem chartTransition_coordinateParametrization (e : ComplexChart n M) (P : RegularPatch V)
    (w : ComplexModel V.dim) :
    chartTransition (complexChartAt (n := n) P.center) e (P.coordinateParametrization w) =
      e.val (P.toManifold w) := rfl

/-- **The derivative of `e ∘ P.toManifold` in the parameters.** -/
def chartPullbackDerivative (e : ComplexChart n M) (P : RegularPatch V)
    (w : ComplexModel V.dim) : ComplexModel V.dim →L[ℝ] ComplexModel n :=
  (chartTransitionDerivative (complexChartAt (n := n) P.center) e
      (P.coordinateParametrization w)).comp (fderiv ℝ P.coordinateParametrization w)

/-- The chart-pullback derivative is complex linear: both factors are derivatives
of holomorphic maps. -/
theorem chartPullbackDerivative_I_smul {e : ComplexChart n M} {P : RegularPatch V}
    {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) (v : ComplexModel V.dim) :
    chartPullbackDerivative e P w (Complex.I • v) =
      Complex.I • chartPullbackDerivative e P w v := by
  set eP := complexChartAt (n := n) P.center with heP
  set z := P.coordinateParametrization w with hz
  have hsrc := mem_chartTransition_source hw
  have hdiff : DifferentiableAt ℂ (chartTransition eP e) z :=
    (differentiableOn_chartTransition eP e z hsrc).differentiableAt
      ((chartTransition eP e).open_source.mem_nhds hsrc)
  have hre : chartTransitionDerivative eP e z =
      (fderiv ℂ (chartTransition eP e) z).restrictScalars ℝ := by
    rw [chartTransitionDerivative, hdiff.fderiv_restrictScalars ℝ]
  simp only [chartPullbackDerivative, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [AdmissibleCurrentFormPositivity.RegularPatchDerivative.fderiv_coordinateParametrization_I_smul
    P hw.1 v, hre]
  exact (fderiv ℂ (chartTransition eP e) z).map_smul Complex.I _

/-- **The coordinate two-form read in a FIXED chart.**  On `chartDomain e P` the
pulled-back coordinate two-form of `a` along `P` is the coefficient of `a` in the
chart `e`, at the `e`-coordinate of the parametrized point, composed with the
chart-pullback derivative. -/
theorem patchCoordinateForm_eq_chart (a : SmoothRealForm n M 2) {e : ComplexChart n M}
    {P : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) :
    RegularPatchTransition.patchCoordinateForm a P w =
      ContinuousAlternatingMap.compContinuousLinearMap
        (a.coeff e (e.val (P.toManifold w))) (chartPullbackDerivative e P w) := by
  set eP := complexChartAt (n := n) P.center with heP
  have hsrc := mem_chartTransition_source hw
  have hcoeff : a.coeff eP (P.coordinateParametrization w) =
      ContinuousAlternatingMap.compContinuousLinearMap
        (a.coeff e (e.val (P.toManifold w)))
        (chartTransitionDerivative eP e (P.coordinateParametrization w)) := by
    ext v
    exact a.compatible eP e _ hsrc v
  simp only [RegularPatchTransition.patchCoordinateForm, chartPullbackDerivative]
  rw [hcoeff]
  ext v
  rfl

/-- **The flat parameter density of a chart.**  The parameter density of the
standard Hermitian form of the chart `e`: the Jacobian of `e ∘ P.toManifold`
measured against the flat metric of `e`. -/
def flatPatchDensity (e : ComplexChart n M) (P : RegularPatch V)
    (w : ComplexModel V.dim) : ℝ :=
  actualTopPowerDensity
    ((standardHermitianTwoForm n).compContinuousLinearMap (chartPullbackDerivative e P w))

/-- **The comparison.**  If the coefficient of the `(1,1)`-form `a` in the chart
`e`, at the `e`-coordinate of the parametrized point, is dominated on complex
lines by `c‖·‖²`, then the parameter density of `a` along `P` is at most
`c^{dim V}` times the flat parameter density of `e`. -/
theorem actualTopPowerDensity_patchCoordinateForm_le (a : SmoothRealForm n M 2)
    (ha : a.IsTypeOneOne) (hapos : a.IsSemipositive) {e : ComplexChart n M}
    {P : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P)
    {c : ℝ}
    (hle : ∀ z : ComplexModel n,
      a.coeff e (e.val (P.toManifold w)) ![z, Complex.I • z] ≤ c * ‖z‖ ^ 2) :
    actualTopPowerDensity (RegularPatchTransition.patchCoordinateForm a P w) ≤
      c ^ V.dim * flatPatchDensity e P w := by
  have htgt : e.val (P.toManifold w) ∈ e.val.target := e.val.map_source hw.2
  rw [patchCoordinateForm_eq_chart a hw]
  exact TopPowerDensityUpperBound.actualTopPowerDensity_comp_le_pow_mul
    (ha e _ htgt) (fun z => hapos e _ htgt z) (chartPullbackDerivative e P w)
    (fun v => chartPullbackDerivative_I_smul hw v) hle

/-- The comparison with the pointwise operator norm as the constant. -/
theorem actualTopPowerDensity_patchCoordinateForm_le_norm (a : SmoothRealForm n M 2)
    (ha : a.IsTypeOneOne) (hapos : a.IsSemipositive) {e : ComplexChart n M}
    {P : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) :
    actualTopPowerDensity (RegularPatchTransition.patchCoordinateForm a P w) ≤
      ‖a.coeff e (e.val (P.toManifold w))‖ ^ V.dim * flatPatchDensity e P w :=
  actualTopPowerDensity_patchCoordinateForm_le a ha hapos hw
    (TopPowerDensityUpperBound.apply_I_smul_self_le_norm_mul _)

end

end SGPT.Foundations.Analysis.Pending.FlatPatchDensityComparison
