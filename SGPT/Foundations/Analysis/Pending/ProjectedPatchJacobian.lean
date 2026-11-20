import SGPT.Foundations.Analysis.Pending.SubsetProjection
import SGPT.Foundations.Analysis.FirstPass.HolomorphicContDiff

set_option autoImplicit false

/-!
# The projected parametrization of a regular patch and its Jacobian

For a fixed chart `e`, a regular patch `P` of `V` and a `k`-element set `I` of the
`n` coordinates of `e` (`k = dim V`), this module studies the map

  `π_I ∘ e ∘ γ_P : ℂ^k → ℂ^k`

from the parameters of the patch to the `I`-coordinates.  It is holomorphic where
the chart sees the patch, hence `C^∞` over `ℝ`
(`FirstPass.contDiffAt_real_of_differentiableOn_complex`, this project's
several-variable Goursat), so it is strictly differentiable there — the hypothesis
`Pending.MultiplicityAreaBound` needs — and its REAL Jacobian is the squared
modulus of the `I`-minor of `chartPullbackDerivative`
(`Pending.SubsetProjection.det_comp_subsetProjection`), which is the `I`-summand
of `Pending.FlatDensityMinorExpansion.flatPatchDensity_eq_sum_minors`.
-/

noncomputable section

open Set
open scoped Matrix ContDiff

namespace SGPT.Foundations.Analysis.Pending.ProjectedPatchJacobian

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
  FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.FlatPatchDensityComparison
  SGPT.Foundations.Analysis.Pending.CauchyBinet
  SGPT.Foundations.Analysis.Pending.SubsetProjection
  SGPT.Foundations.Analysis.Pending.FlatDensityGramDeterminant

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The parametrization of `V` read in a FIXED chart: `e ∘ P.toManifold`.  It is
definitionally the chart transition applied to the coordinate parametrization. -/
def chartParametrization (e : ComplexChart n M) (P : RegularPatch V) :
    ComplexModel V.dim → ComplexModel n := fun w => e.val (P.toManifold w)

theorem chartParametrization_eq (e : ComplexChart n M) (P : RegularPatch V) :
    chartParametrization e P =
      fun w => chartTransition (complexChartAt (n := n) P.center) e
        (P.coordinateParametrization w) := rfl

/-- The set of parameters seen by the chart is open. -/
theorem isOpen_chartDomain (e : ComplexChart n M) (P : RegularPatch V) :
    IsOpen (chartDomain e P) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  have hpd : P.parameterDomain ∈ nhds w :=
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain
      P).mem_nhds hw.1
  have hcont : ContinuousAt P.coordinateParametrization w :=
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      P hw.1).continuousAt
  have hpre : P.coordinateParametrization ⁻¹'
      (chartTransition (complexChartAt (n := n) P.center) e).source ∈ nhds w :=
    hcont.preimage_mem_nhds
      ((chartTransition (complexChartAt (n := n) P.center) e).open_source.mem_nhds
        (mem_chartTransition_source hw))
  filter_upwards [hpd, hpre] with u hu1 hu2
  exact ⟨hu1, hu2.2⟩

theorem differentiableAt_chartParametrization {e : ComplexChart n M} {P : RegularPatch V}
    {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) :
    DifferentiableAt ℂ (chartParametrization e P) w := by
  have h1 : DifferentiableAt ℂ P.coordinateParametrization w :=
    AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      P hw.1
  have hsrc := mem_chartTransition_source hw
  have h2 : DifferentiableAt ℂ (chartTransition (complexChartAt (n := n) P.center) e)
      (P.coordinateParametrization w) :=
    (differentiableOn_chartTransition (complexChartAt (n := n) P.center) e _
      hsrc).differentiableAt
      ((chartTransition (complexChartAt (n := n) P.center) e).open_source.mem_nhds hsrc)
  exact h2.comp w h1

theorem differentiableOn_chartParametrization (e : ComplexChart n M) (P : RegularPatch V) :
    DifferentiableOn ℂ (chartParametrization e P) (chartDomain e P) :=
  fun _ hw => (differentiableAt_chartParametrization hw).differentiableWithinAt

/-- **The chart-pullback derivative is the restriction of scalars of the complex
derivative of `e ∘ γ_P`.** -/
theorem chartPullbackDerivative_eq {e : ComplexChart n M} {P : RegularPatch V}
    {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) :
    chartPullbackDerivative e P w =
      (fderiv ℂ (chartParametrization e P) w).restrictScalars ℝ := by
  set eP := complexChartAt (n := n) P.center with heP
  set z := P.coordinateParametrization w with hz
  have hsrc := mem_chartTransition_source hw
  have hγ : DifferentiableAt ℂ P.coordinateParametrization w :=
    AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      P hw.1
  have hτ : DifferentiableAt ℂ (chartTransition eP e) z :=
    (differentiableOn_chartTransition eP e _ hsrc).differentiableAt
      ((chartTransition eP e).open_source.mem_nhds hsrc)
  have hchain : fderiv ℂ (chartParametrization e P) w =
      (fderiv ℂ (chartTransition eP e) z).comp (fderiv ℂ P.coordinateParametrization w) := by
    rw [chartParametrization_eq]
    exact fderiv_comp w hτ hγ
  rw [chartPullbackDerivative, chartTransitionDerivative, hτ.fderiv_restrictScalars ℝ,
    hγ.fderiv_restrictScalars ℝ, hchain]
  rfl

/-- The parametrization followed by the projection onto the coordinates in `I`. -/
def projectedParametrization (I : CardSubset V.dim n) (e : ComplexChart n M)
    (P : RegularPatch V) : ComplexModel V.dim → ComplexModel V.dim :=
  fun w => subsetProjection I (chartParametrization e P w)

/-- Its real derivative. -/
def projectedDerivative (I : CardSubset V.dim n) (e : ComplexChart n M) (P : RegularPatch V)
    (w : ComplexModel V.dim) : ComplexModel V.dim →L[ℝ] ComplexModel V.dim :=
  ((subsetProjection I).restrictScalars ℝ).comp (chartPullbackDerivative e P w)

theorem hasFDerivAt_projectedParametrization (I : CardSubset V.dim n) {e : ComplexChart n M}
    {P : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) :
    HasFDerivAt (projectedParametrization I e P) (projectedDerivative I e P w) w := by
  have h := (differentiableAt_chartParametrization hw).hasFDerivAt.restrictScalars ℝ
  rw [← chartPullbackDerivative_eq hw] at h
  exact (subsetProjection I).restrictScalars ℝ |>.hasFDerivAt.comp w h

/-- **The projected parametrization is strictly differentiable** where the chart
sees the patch: it is holomorphic there, hence `C^∞` over `ℝ`. -/
theorem hasStrictFDerivAt_projectedParametrization (I : CardSubset V.dim n)
    {e : ComplexChart n M} {P : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ chartDomain e P) :
    HasStrictFDerivAt (projectedParametrization I e P) (projectedDerivative I e P w) w := by
  have hdiff : DifferentiableOn ℂ (projectedParametrization I e P) (chartDomain e P) :=
    fun u hu => ((subsetProjection I).differentiableAt.comp u
      (differentiableAt_chartParametrization hu)).differentiableWithinAt
  have hC : ContDiffAt ℝ ∞ (projectedParametrization I e P) w :=
    contDiffAt_real_of_differentiableOn_complex hdiff (isOpen_chartDomain e P) hw
  exact hC.hasStrictFDerivAt' (hasFDerivAt_projectedParametrization I hw) (by simp)

/-- **The real Jacobian of the projected parametrization is the squared modulus of
the `I`-minor** of the chart-pullback derivative: the `I`-summand of Demailly's
expansion of the flat density. -/
theorem det_projectedDerivative (I : CardSubset V.dim n) {e : ComplexChart n M}
    {P : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ chartDomain e P) :
    (projectedDerivative I e P w).det =
      ‖((standardRectMatrix (chartPullbackDerivative e P w)).submatrix I.emb id).det‖ ^ 2 := by
  rw [projectedDerivative, chartPullbackDerivative_eq hw, det_comp_subsetProjection]

end SGPT.Foundations.Analysis.Pending.ProjectedPatchJacobian
