import SGPT.Foundations.Analysis.FirstPass.RegularLocusDense
import SGPT.Foundations.Analysis.FirstPass.CoordinateWedgePullback
import SGPT.Foundations.Analysis.FirstPass.StandardHermitianTwoForm
import SGPT.Foundations.Analysis.Pending.PatchParameterNull

set_option autoImplicit false

/-!
# The transition map between two regular patches of the same subvariety

Two regular patches `P`, `Q` of the same subvariety `V` parametrize the same
germ of `V` wherever their images meet, so their parameters are related by a
biholomorphism of open subsets of `ℂ^{dim V}`.  This module constructs that map
explicitly and proves the geometric identity `P ∘ τ = Q` it satisfies.

The map is
`τ(w) = pr(Φ_P(φ_P(Q(w))))`,
where `φ_P` is the preferred chart at the centre of `P`, `Φ_P` its flattening of
`V`, and `pr : ℂⁿ → ℂ^{dim V}` the projection onto the coordinate plane that
`Φ_P` flattens `V` onto.  The point of the construction is that no inverse of
`Q` is taken: `τ` is a composition of maps that are given, and the identity
`P.toManifold (τ w) = Q.toManifold w` comes from `P.flattens` alone — the image
point lies on `V`, so its `Φ_P`-image lies in the coordinate plane and `pr` loses
nothing.

This is the patch-independence input that the restricted-mass machinery of this
project still lacks on a subvariety.  In the FULL-SPACE case the corresponding
comparison is made against an ambient measure
(`Pending.FullSpaceAmbientComparison.lintegral_patchDensity_eq_globalMixedMeasure_image`);
on a proper subvariety there is no ambient measure to compare with, so the
patch-to-patch transition has to be built, and its Jacobian is what will turn
the parameter integrals of `formPatchDensity` into a single measure on `V_reg`.
This module supplies the map, its geometry, the density transformation law
`patchCoordinateForm_transition`, and the resulting change of variables
`lintegral_actualTopPowerDensity_transition`.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RegularPatchTransition

open FirstPass FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
  FirstPass.RegularLocusDense
open PatchParameterNull

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The `Q`-parameters at which the transition to `P` is defined: the image point
must lie in the preferred chart at the centre of `P` and its coordinates in the
source of the flattening of `P`. -/
def transitionDomain (P Q : RegularPatch V) : Set (ComplexModel V.dim) :=
  {w | w ∈ Q.parameterDomain ∧
    Q.toManifold w ∈ (complexChartAt (n := n) P.center).val.source ∧
    (complexChartAt (n := n) P.center).val (Q.toManifold w) ∈ P.flattening.source}

/-- The transition map from `Q`-parameters to `P`-parameters. -/
def transition (P Q : RegularPatch V) : ComplexModel V.dim → ComplexModel V.dim :=
  fun w => planeProjection V.dim n
    (P.flattening.toFun ((complexChartAt (n := n) P.center).val (Q.toManifold w)))

theorem transitionDomain_subset_parameterDomain (P Q : RegularPatch V) :
    transitionDomain P Q ⊆ Q.parameterDomain := fun _ hw => hw.1

theorem isOpen_transitionDomain (P Q : RegularPatch V) :
    IsOpen (transitionDomain P Q) := by
  have hdom : IsOpen Q.parameterDomain :=
    AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain Q
  have hcont : ContinuousOn Q.toManifold Q.parameterDomain :=
    RegularPatch.continuousOn_toManifold Q
  have h2 : IsOpen (Q.parameterDomain ∩ Q.toManifold ⁻¹'
      ((complexChartAt (n := n) P.center).val.source ∩
        (complexChartAt (n := n) P.center).val ⁻¹' P.flattening.source)) := by
    refine hcont.isOpen_inter_preimage hdom ?_
    exact (complexChartAt (n := n) P.center).val.continuousOn.isOpen_inter_preimage
      (complexChartAt (n := n) P.center).val.open_source P.flattening.isOpen_source
  convert h2 using 1
  ext w
  simp only [transitionDomain, Set.mem_ofPred_eq, mem_inter_iff, mem_preimage]

/-- On the transition domain, the flattened image of `Q.toManifold w` lies in the
coordinate plane that `P` flattens `V` onto. -/
theorem flattening_mem_plane {P Q : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ transitionDomain P Q) :
    P.flattening.toFun ((complexChartAt (n := n) P.center).val (Q.toManifold w)) ∈
      complexCoordinatePlane n V.dim :=
  (P.flattens hw.2.1 hw.2.2).mp (RegularPatch.toManifold_mem_carrier Q hw.1)

theorem planeInclusion_transition {P Q : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ transitionDomain P Q) :
    planeInclusion V.dim n (transition P Q w) =
      P.flattening.toFun ((complexChartAt (n := n) P.center).val (Q.toManifold w)) :=
  planeInclusion_planeProjection (flattening_mem_plane hw)

/-- The transition lands in the parameter domain of `P`. -/
theorem transition_mem_parameterDomain {P Q : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ transitionDomain P Q) : transition P Q w ∈ P.parameterDomain := by
  show planeInclusion V.dim n (transition P Q w) ∈ P.flattening.target
  rw [planeInclusion_transition hw]
  exact P.flattening.mapsTo_toFun hw.2.2

/-- **The geometric identity.**  The two parametrizations agree after the
transition: `P ∘ τ = Q` on the transition domain. -/
theorem toManifold_transition {P Q : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ transitionDomain P Q) :
    P.toManifold (transition P Q w) = Q.toManifold w := by
  show (complexChartAt (n := n) P.center).val.symm
      (P.flattening.invFun (planeInclusion V.dim n (transition P Q w))) = _
  rw [planeInclusion_transition hw, P.flattening.left_inv _ hw.2.2,
    (complexChartAt (n := n) P.center).val.left_inv hw.2.1]

/-- A matched pair of parameters lies in the transition domain, and the
transition takes one to the other.  This is the form in which the transition is
produced: whenever the images of the two patches meet. -/
theorem mem_transitionDomain_and_transition_eq {P Q : RegularPatch V}
    {w : ComplexModel V.dim} (hw : w ∈ Q.parameterDomain)
    {v : ComplexModel V.dim} (hv : v ∈ P.parameterDomain)
    (h : Q.toManifold w = P.toManifold v) :
    w ∈ transitionDomain P Q ∧ transition P Q w = v := by
  have hsrc : P.toManifold v ∈ (complexChartAt (n := n) P.center).val.source :=
    RegularPatch.toManifold_mem_chart_source P hv
  have hchart : (complexChartAt (n := n) P.center).val (P.toManifold v) =
      P.coordinateParametrization v := RegularPatch.chart_toManifold P hv
  have hflat : P.coordinateParametrization v ∈ P.flattening.source :=
    P.flattening.mapsTo_invFun hv
  have hmem : w ∈ transitionDomain P Q := by
    refine ⟨hw, ?_, ?_⟩
    · rw [h]; exact hsrc
    · rw [h, hchart]; exact hflat
  refine ⟨hmem, ?_⟩
  have : planeInclusion V.dim n (transition P Q w) = planeInclusion V.dim n v := by
    rw [planeInclusion_transition hmem, h, hchart]
    change P.flattening.toFun (P.flattening.invFun (planeInclusion V.dim n v)) = _
    exact P.flattening.right_inv _ hv
  exact AdmissibleCurrentFormPositivity.planeInclusion_injective V.dim_le this

/-- The transition read in the two charts: it is the chart transition followed by
the flattening of `P` and the coordinate projection. -/
theorem transition_eq_comp (P Q : RegularPatch V) :
    transition P Q = fun w => coordinateProjection n V.dim
      (P.flattening.toFun
        (chartTransition (complexChartAt (n := n) Q.center)
          (complexChartAt (n := n) P.center) (Q.coordinateParametrization w))) := rfl

theorem coordinateParametrization_mem_chartTransition_source
    {P Q : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ transitionDomain P Q) :
    Q.coordinateParametrization w ∈
      (chartTransition (complexChartAt (n := n) Q.center)
        (complexChartAt (n := n) P.center)).source := by
  refine ⟨Q.source_subset (RegularPatch.coordinateParametrization_mem_source Q hw.1), ?_⟩
  exact hw.2.1

/-- **The transition is holomorphic.**  It is a composition of the parametrization
of `Q`, the chart transition, the flattening of `P`, and a linear projection. -/
theorem differentiableAt_transition {P Q : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ transitionDomain P Q) : DifferentiableAt ℂ (transition P Q) w := by
  set eQ := complexChartAt (n := n) Q.center
  set eP := complexChartAt (n := n) P.center
  have h1 : DifferentiableAt ℂ Q.coordinateParametrization w :=
    AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      Q hw.1
  have hsrc := coordinateParametrization_mem_chartTransition_source hw
  have h2 : DifferentiableAt ℂ (chartTransition eQ eP) (Q.coordinateParametrization w) :=
    (differentiableOn_chartTransition eQ eP _ hsrc).differentiableAt
      ((chartTransition eQ eP).open_source.mem_nhds hsrc)
  have h3 : DifferentiableAt ℂ P.flattening.toFun
      (chartTransition eQ eP (Q.coordinateParametrization w)) :=
    (P.flattening.toFun_holomorphic _ hw.2.2).differentiableAt
      (P.flattening.isOpen_source.mem_nhds hw.2.2)
  rw [transition_eq_comp]
  exact ((coordinateProjection n V.dim).differentiableAt).comp w
    (h3.comp w (h2.comp w h1))

theorem differentiableOn_transition (P Q : RegularPatch V) :
    DifferentiableOn ℂ (transition P Q) (transitionDomain P Q) :=
  fun _ hw => (differentiableAt_transition hw).differentiableWithinAt

/-- In the chart at the centre of `P`, the transition is the chart transition:
`φ_P(Q(w)) = γ_P(τ w)`. -/
theorem chartTransition_coordinateParametrization {P Q : RegularPatch V}
    {w : ComplexModel V.dim} (hw : w ∈ transitionDomain P Q) :
    chartTransition (complexChartAt (n := n) Q.center) (complexChartAt (n := n) P.center)
        (Q.coordinateParametrization w) =
      P.coordinateParametrization (transition P Q w) := by
  have h1 : chartTransition (complexChartAt (n := n) Q.center)
      (complexChartAt (n := n) P.center) (Q.coordinateParametrization w) =
      (complexChartAt (n := n) P.center).val (Q.toManifold w) := rfl
  rw [h1, ← toManifold_transition hw,
    RegularPatch.chart_toManifold P (transition_mem_parameterDomain hw)]

/-- `γ_P ∘ τ` and the chart transition applied to `γ_Q` agree near any point of the
transition domain. -/
theorem eventuallyEq_coordinateParametrization_transition {P Q : RegularPatch V}
    {w : ComplexModel V.dim} (hw : w ∈ transitionDomain P Q) :
    (fun x => P.coordinateParametrization (transition P Q x)) =ᶠ[nhds w]
      fun x => chartTransition (complexChartAt (n := n) Q.center)
        (complexChartAt (n := n) P.center) (Q.coordinateParametrization x) := by
  filter_upwards [(isOpen_transitionDomain P Q).mem_nhds hw] with x hx
  exact (chartTransition_coordinateParametrization hx).symm

/-- **The chain rule across the transition.**  The derivative of `γ_Q`, followed by
the derivative of the chart transition, factors as the derivative of `γ_P` at the
transported parameter, followed by the derivative of `τ`. -/
theorem fderiv_chartTransition_comp {P Q : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ transitionDomain P Q) :
    (chartTransitionDerivative (complexChartAt (n := n) Q.center)
        (complexChartAt (n := n) P.center) (Q.coordinateParametrization w)).comp
        (fderiv ℝ Q.coordinateParametrization w) =
      (fderiv ℝ P.coordinateParametrization (transition P Q w)).comp
        (fderiv ℝ (transition P Q) w) := by
  set eQ := complexChartAt (n := n) Q.center
  set eP := complexChartAt (n := n) P.center
  have hsrc := coordinateParametrization_mem_chartTransition_source hw
  have hQ : DifferentiableAt ℝ Q.coordinateParametrization w :=
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      Q hw.1).restrictScalars ℝ
  have hT : DifferentiableAt ℝ (chartTransition eQ eP) (Q.coordinateParametrization w) :=
    ((differentiableOn_chartTransition eQ eP _ hsrc).differentiableAt
      ((chartTransition eQ eP).open_source.mem_nhds hsrc)).restrictScalars ℝ
  have hP : DifferentiableAt ℝ P.coordinateParametrization (transition P Q w) :=
    (AdmissibleCurrentFormPositivity.RegularPatchDerivative.differentiableAt_coordinateParametrization
      P (transition_mem_parameterDomain hw)).restrictScalars ℝ
  have hτ : DifferentiableAt ℝ (transition P Q) w :=
    (differentiableAt_transition hw).restrictScalars ℝ
  have hleft : fderiv ℝ (fun x => chartTransition eQ eP (Q.coordinateParametrization x)) w =
      (fderiv ℝ (chartTransition eQ eP) (Q.coordinateParametrization w)).comp
        (fderiv ℝ Q.coordinateParametrization w) := fderiv_comp w hT hQ
  have hright : fderiv ℝ (fun x => P.coordinateParametrization (transition P Q x)) w =
      (fderiv ℝ P.coordinateParametrization (transition P Q w)).comp
        (fderiv ℝ (transition P Q) w) := fderiv_comp w hP hτ
  rw [chartTransitionDerivative, ← hleft, ← hright,
    (eventuallyEq_coordinateParametrization_transition hw).fderiv_eq]

/-- Associativity of precomposition of an alternating map by continuous linear
maps.  (The same one-line fact is proved in `Pending.RegularPatchPullback`; it is
repeated privately here to keep this module's import closure small.) -/
private theorem compContinuousLinearMap_comp {ι : Type*} [Fintype ι] {k m : ℕ}
    (f : (ComplexModel n) [⋀^ι]→L[ℝ] ℝ) (A : ComplexModel m →L[ℝ] ComplexModel n)
    (B : ComplexModel k →L[ℝ] ComplexModel m) :
    ContinuousAlternatingMap.compContinuousLinearMap f (A.comp B) =
      ContinuousAlternatingMap.compContinuousLinearMap
        (ContinuousAlternatingMap.compContinuousLinearMap f A) B := by
  ext v
  rfl

/-- Abbreviation for the coordinate two-form of a smooth real form pulled back
along the parametrization of a regular patch.  `formPatchDensity` is its
`actualTopPowerDensity`. -/
def patchCoordinateForm (a : SmoothRealForm n M 2) (P : RegularPatch V)
    (w : ComplexModel V.dim) : MongeAmpere.CoordinateRealTwoForm V.dim :=
  ContinuousAlternatingMap.compContinuousLinearMap
    (a.coeff (complexChartAt (n := n) P.center) (P.coordinateParametrization w))
    (fderiv ℝ P.coordinateParametrization w)

/-- **The density transformation law.**  The coordinate two-form pulled back along
`Q` is the one pulled back along `P` at the transported parameter, composed with
the derivative of the transition. -/
theorem patchCoordinateForm_transition (a : SmoothRealForm n M 2)
    {P Q : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ transitionDomain P Q) :
    patchCoordinateForm a Q w =
      ContinuousAlternatingMap.compContinuousLinearMap
        (patchCoordinateForm a P (transition P Q w)) (fderiv ℝ (transition P Q) w) := by
  set eQ := complexChartAt (n := n) Q.center
  set eP := complexChartAt (n := n) P.center
  have hsrc := coordinateParametrization_mem_chartTransition_source hw
  have hcoeff : a.coeff eQ (Q.coordinateParametrization w) =
      ContinuousAlternatingMap.compContinuousLinearMap
        (a.coeff eP (P.coordinateParametrization (transition P Q w)))
        (chartTransitionDerivative eQ eP (Q.coordinateParametrization w)) := by
    ext v
    rw [← chartTransition_coordinateParametrization hw]
    exact a.compatible eQ eP _ hsrc v
  simp only [patchCoordinateForm]
  rw [hcoeff, ← compContinuousLinearMap_comp, ← compContinuousLinearMap_comp,
    fderiv_chartTransition_comp hw]

/-- **The Jacobian law for the parameter density.**  The top-power density of a
smooth real form in `Q`-parameters is the real determinant of the transition
times its density in `P`-parameters at the transported point.  This is the
change-of-variables factor that makes the parameter integrals of two patches
agree on the overlap. -/
theorem actualTopPowerDensity_patchCoordinateForm_transition (a : SmoothRealForm n M 2)
    {P Q : RegularPatch V} {w : ComplexModel V.dim} (hw : w ∈ transitionDomain P Q) :
    MongeAmpere.actualTopPowerDensity (patchCoordinateForm a Q w) =
      LinearMap.det
          ((fderiv ℝ (transition P Q) w : ComplexModel V.dim →ₗ[ℝ] ComplexModel V.dim)) *
        MongeAmpere.actualTopPowerDensity (patchCoordinateForm a P (transition P Q w)) := by
  rw [patchCoordinateForm_transition a hw,
    MongeAmpere.actualTopPowerDensity_compContinuousLinearMap]

/-- The parametrization of a regular patch is injective on its parameter domain.

This is the third copy of this lemma in the project (`SubvarietyStokesMass`,
`RestrictedVolumePullbackLower`); both of those modules import this one, so the
triplication is forced by the import order and the fix is to hoist the lemma
into `FirstPass.RegularPatchNeighborhood`, which is human-only.  It is kept
private here so that this module stays low in the import order. -/
private theorem toManifold_injOn (Q : RegularPatch V) :
    InjOn Q.toManifold Q.parameterDomain := by
  intro w hw w' hw' hEq
  have h : Q.coordinateParametrization w = Q.coordinateParametrization w' := by
    rw [← RegularPatch.chart_toManifold Q hw, ← RegularPatch.chart_toManifold Q hw', hEq]
  have h2 : planeInclusion V.dim n w = planeInclusion V.dim n w' := by
    have e1 := Q.flattening.right_inv _ hw
    have e2 := Q.flattening.right_inv _ hw'
    change Q.flattening.toFun (Q.coordinateParametrization w) = _ at e1
    change Q.flattening.toFun (Q.coordinateParametrization w') = _ at e2
    rw [← e1, ← e2, h]
  exact AdmissibleCurrentFormPositivity.planeInclusion_injective V.dim_le h2

/-- The transition is injective on its domain: it is a parameter change. -/
theorem injOn_transition (P Q : RegularPatch V) :
    InjOn (transition P Q) (transitionDomain P Q) := by
  intro w hw w' hw' hEq
  have h1 := toManifold_transition hw
  have h2 := toManifold_transition hw'
  rw [hEq] at h1
  exact toManifold_injOn Q hw.1 hw'.1 (h1.symm.trans h2)

/-- The real Jacobian of the transition is nonnegative: the transition is
holomorphic, so its real determinant is the squared modulus of the complex one. -/
theorem det_fderiv_transition_nonneg {P Q : RegularPatch V} {w : ComplexModel V.dim}
    (hw : w ∈ transitionDomain P Q) :
    0 ≤ LinearMap.det
      ((fderiv ℝ (transition P Q) w : ComplexModel V.dim →ₗ[ℝ] ComplexModel V.dim)) := by
  have hC : DifferentiableAt ℂ (transition P Q) w := differentiableAt_transition hw
  have hre : fderiv ℝ (transition P Q) w =
      (fderiv ℂ (transition P Q) w).restrictScalars ℝ :=
    (hC.hasFDerivAt.restrictScalars ℝ).fderiv
  rw [hre]
  rw [show ((((fderiv ℂ (transition P Q) w).restrictScalars ℝ :
        ComplexModel V.dim →L[ℝ] ComplexModel V.dim)) :
        ComplexModel V.dim →ₗ[ℝ] ComplexModel V.dim) =
      ((fderiv ℂ (transition P Q) w : ComplexModel V.dim →ₗ[ℂ] ComplexModel V.dim).restrictScalars
        ℝ) from rfl,
    MongeAmpere.normSq_det_eq_realDet]
  exact Complex.normSq_nonneg _

/-- **Change of variables between two patches.**  The parameter integral of the
top-power density of a smooth real form over a measurable piece of `Q` equals its
parameter integral over the transported piece of `P`.

This is the patch-independence statement: the two patches compute the same mass
on the part of `V` they both see.  It is what turns the parameter integrals of
`formPatchDensity` into a single measure on `V_reg`. -/
theorem lintegral_actualTopPowerDensity_transition (a : SmoothRealForm n M 2)
    {P Q : RegularPatch V} {S : Set (ComplexModel V.dim)} (hS : MeasurableSet S)
    (hSsub : S ⊆ transitionDomain P Q) :
    ∫⁻ v in transition P Q '' S,
        ENNReal.ofReal (MongeAmpere.actualTopPowerDensity (patchCoordinateForm a P v)) =
      ∫⁻ w in S,
        ENNReal.ofReal (MongeAmpere.actualTopPowerDensity (patchCoordinateForm a Q w)) := by
  have hderiv : ∀ w ∈ S, HasFDerivWithinAt (transition P Q)
      (fderiv ℝ (transition P Q) w) S w := fun w hw =>
    ((differentiableAt_transition (hSsub hw)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  rw [MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul MeasureTheory.volume hS
    hderiv ((injOn_transition P Q).mono hSsub)]
  refine MeasureTheory.setLIntegral_congr_fun hS fun w hw => ?_
  have hnn := det_fderiv_transition_nonneg (hSsub hw)
  have habs : |((fderiv ℝ (transition P Q) w).det)| =
      LinearMap.det
        ((fderiv ℝ (transition P Q) w : ComplexModel V.dim →ₗ[ℝ] ComplexModel V.dim)) :=
    abs_of_nonneg hnn
  rw [habs, ← ENNReal.ofReal_mul hnn,
    ← actualTopPowerDensity_patchCoordinateForm_transition a (hSsub hw)]


end

end SGPT.Foundations.Analysis.Pending.RegularPatchTransition
