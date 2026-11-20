import SGPT.Foundations.Analysis.Pending.RegularPatchDensityContinuity
import SGPT.Foundations.Analysis.Pending.LogWeightFactorization

set_option autoImplicit false

/-!
# The patch density of an admissible presentation is measurable

`Pending.RegularPatchDensityContinuity` proves that the parameter density of a
**smooth** real two-form is continuous on the whole parameter domain of a regular
patch.  The density that `acTopMass` integrates is not of that kind: its
coordinate two-form is `θ + εω + ddᶜu` with `u` a `θ`-PSH potential with smooth
analytic singularities, so it is a genuine form only off the pole set of `u`.

Off that pole set, however, `u` is locally a smooth real function
(`FirstPass.SmoothOffPoleSet`), and `Pending.LogWeightFactorization.smoothDDC_contDiffOn`
makes `ddᶜ` of a locally smooth function smooth.  Hence:

* `continuousAt_patchDensity` — `patchDensity p P` is continuous at every
  parameter of the patch domain whose point is not a pole of the potential;
* `aestronglyMeasurable_patchDensity` / `aemeasurable_ofReal_patchDensity` — the
  integrand of `acTopMass` is measurable on every measurable parameter set whose
  image avoids the pole set, in particular on every piece of a
  `RegularPieceFamily V (poleSet p.potential)`.

This is the input recorded as missing in `Pending.RegularPieceFamilyRefinement`
(the metric exhaustion of a piece) and in I-0373 (the Fatou form of the mass
comparison across a blowup centre): both need the density to be an honest
measurable integrand, not merely a pointwise value.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.PatchDensityMeasurability

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.MongeAmpere
  FirstPass.AdmissibleCurrentFormPositivity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- **`ddᶜ` of a potential is continuous off the pole set.**  The potential is
locally a smooth real function there, and `ddᶜ` only depends on the germ. -/
theorem continuousAt_smoothDDC_chartFunction {u : M → EReal}
    (hu : SmoothOffPoleSet (n := n) u) (e : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ e.val.target) (hpole : e.val.symm z ∉ poleSet u) :
    ContinuousAt (smoothDDC fun y => (u (e.val.symm y)).toReal) z := by
  obtain ⟨g, hg, hug⟩ := hu e z hz hpole
  have hmem : {y | ContDiffAt ℝ ∞ g y ∧ chartFunction u e y = (g y : EReal)} ∈ 𝓝 z :=
    hg.and hug
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp hmem
  have hgU : ContDiffOn ℝ ∞ g U := fun y hy => (hUsub hy).1.contDiffWithinAt
  have hcont : ContinuousOn (smoothDDC g) U :=
    (LogWeightFactorization.smoothDDC_contDiffOn hU hgU).continuousOn
  have heq : EqOn (smoothDDC fun y => (u (e.val.symm y)).toReal) (smoothDDC g) U := by
    intro y hy
    refine smoothDDC_congr ?_
    filter_upwards [hU.mem_nhds hy] with y' hy'
    have hy'' := (hUsub hy').2
    show (u (e.val.symm y')).toReal = g y'
    rw [show u (e.val.symm y') = chartFunction u e y' from rfl, hy'', EReal.toReal_coe]
  exact (hcont.congr heq).continuousAt (hU.mem_nhds hzU)

variable {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

/-- **The coordinate two-form of `T + εω` is continuous off the pole set.** -/
theorem continuousAt_coordinateCurrentForm
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (e : ComplexChart n M) {z : ComplexModel n} (hz : z ∈ e.val.target)
    (hpole : e.val.symm z ∉ poleSet p.potential) :
    ContinuousAt (coordinateCurrentForm p e) z := by
  have h1 : ContinuousAt ((perturbedRepresentative p).val.coeff e) z :=
    ((perturbedRepresentative p).val.smooth e).continuousOn.continuousAt
      (e.val.open_target.mem_nhds hz)
  have h2 := continuousAt_smoothDDC_chartFunction
    (SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole
      p.smoothAnalyticSingularities)
    e hz hpole
  exact h1.add h2

/-- The patch parametrization is smooth on the parameter domain. -/
theorem contDiffOn_coordinateParametrization (P : RegularPatch V) :
    ContDiffOn ℝ ∞ P.coordinateParametrization P.parameterDomain := by
  have hinv : ContDiffOn ℝ ∞ P.flattening.invFun P.flattening.target :=
    contDiffOn_real_of_differentiableOn_complex P.flattening.invFun_holomorphic
      P.flattening.isOpen_target
  exact hinv.comp
    ((planeInclusionCLM V.dim n).restrictScalars ℝ).contDiff.contDiffOn fun w hw => hw

/-- Its real derivative is continuous on the parameter domain. -/
theorem continuousOn_fderiv_coordinateParametrization (P : RegularPatch V) :
    ContinuousOn (fderiv ℝ P.coordinateParametrization) P.parameterDomain :=
  (contDiffOn_coordinateParametrization P).continuousOn_fderiv_of_isOpen
    (RegularPatchDerivative.isOpen_parameterDomain P) (by simp)

/-- **The parameter density of an admissible presentation is continuous at every
parameter whose point is not a pole of the potential.** -/
theorem continuousAt_patchDensity
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) {w : ComplexModel V.dim} (hw : w ∈ P.parameterDomain)
    (hpole : P.toManifold w ∉ poleSet p.potential) :
    ContinuousAt (patchDensity p P) w := by
  set e : ComplexChart n M := complexChartAt (n := n) P.center with he
  have hopen := RegularPatchDerivative.isOpen_parameterDomain P
  have hphi : ContinuousAt P.coordinateParametrization w :=
    ((contDiffOn_coordinateParametrization P).continuousOn).continuousAt (hopen.mem_nhds hw)
  have hderiv : ContinuousAt (fderiv ℝ P.coordinateParametrization) w :=
    (continuousOn_fderiv_coordinateParametrization P).continuousAt (hopen.mem_nhds hw)
  have hz : P.coordinateParametrization w ∈ e.val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  have hform : ContinuousAt
      (fun x => coordinateCurrentForm p e (P.coordinateParametrization x)) w :=
    (continuousAt_coordinateCurrentForm p e hz hpole).comp hphi
  have hpull : ContinuousAt (fun x =>
      (coordinateCurrentForm p e (P.coordinateParametrization x)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization x)) w := by
    change ContinuousAt (fun x =>
      (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (fderiv ℝ P.coordinateParametrization x))
          (coordinateCurrentForm p e (P.coordinateParametrization x))) w
    exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.continuousAt.comp
      hderiv).clm_apply hform
  exact ((RegularPatchTransition.continuous_topPowerDensity V.dim).continuousAt).comp hpull

/-- The density is continuous on any parameter set inside the patch domain whose
image avoids the pole set. -/
theorem continuousOn_patchDensity
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) {S : Set (ComplexModel V.dim)} (hS : S ⊆ P.parameterDomain)
    (hpole : ∀ w ∈ S, P.toManifold w ∉ poleSet p.potential) :
    ContinuousOn (patchDensity p P) S := fun w hw =>
  (continuousAt_patchDensity p P (hS hw) (hpole w hw)).continuousWithinAt

/-- **The integrand of `acTopMass` is measurable on such a set.** -/
theorem aestronglyMeasurable_patchDensity
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) {S : Set (ComplexModel V.dim)} (hSm : MeasurableSet S)
    (hS : S ⊆ P.parameterDomain)
    (hpole : ∀ w ∈ S, P.toManifold w ∉ poleSet p.potential) :
    AEStronglyMeasurable (patchDensity p P) (volume.restrict S) :=
  (continuousOn_patchDensity p P hS hpole).aestronglyMeasurable hSm

/-- The `ℝ≥0∞`-valued integrand of `acTopMass` is measurable on such a set. -/
theorem aemeasurable_ofReal_patchDensity
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) {S : Set (ComplexModel V.dim)} (hSm : MeasurableSet S)
    (hS : S ⊆ P.parameterDomain)
    (hpole : ∀ w ∈ S, P.toManifold w ∉ poleSet p.potential) :
    AEMeasurable (fun w => ENNReal.ofReal (patchDensity p P w)) (volume.restrict S) :=
  ENNReal.measurable_ofReal.comp_aemeasurable
    (aestronglyMeasurable_patchDensity p P hSm hS hpole).aemeasurable

/-- **Every piece of a regular-piece family carries a measurable density.**  A
family avoiding `poleSet p.potential` has, by construction, all three
hypotheses. -/
theorem aemeasurable_ofReal_patchDensity_piece
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (F : RegularPieceFamily V (poleSet p.potential)) (i : Fin F.size) :
    AEMeasurable (fun w => ENNReal.ofReal (patchDensity p (F.patch i) w))
      (volume.restrict (F.piece i)) := by
  refine aemeasurable_ofReal_patchDensity p (F.patch i) (F.measurableSet_piece i)
    (F.piece_subset i) fun w hw => ?_
  have hmem : (F.patch i).toManifold w ∈ (F.patch i).toManifold '' F.piece i :=
    mem_image_of_mem _ hw
  exact fun hpole => (F.image_disjoint_avoid i).le_bot ⟨hmem, hpole⟩

end

end SGPT.Foundations.Analysis.Pending.PatchDensityMeasurability
