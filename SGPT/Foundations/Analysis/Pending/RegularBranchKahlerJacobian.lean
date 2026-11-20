import SGPT.Foundations.Analysis.Pending.SubvarietyStokesMass
import SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone
import SGPT.Foundations.Analysis.FirstPass.TopPowerDensityPositivity

set_option autoImplicit false

/-!
# Weighted measures of compact regular branches

The unweighted pushforwards in `CountableRegularBranchMeasure` record only
Lebesgue measure in a parameter ball.  For a genuine top-degree mass one must
weight that Lebesgue measure by the pullback density of the relevant `(1,1)`
form.  This file makes that step explicit for one compact regular branch.

For any nonnegative parameter weight `rho`, its weighted pushforward is a
Borel measure on the ambient manifold and ambient nonnegative test integrals
pull back to the weighted parameter measure.  Instantiating `rho` with
`ofReal (patchDensity p P)` gives the local top-density mass used by
`acTopMass`; for a zero-potential presentation this is exactly the pullback of
the perturbed smooth representative.  The standard Hermitian form also gives
a strictly positive Kähler Jacobian density for every regular parametrization.

This is a local measure construction only.  It neither proves the required
global locally finite cover nor identifies the resulting sum with the closed
integration current `[V]`.
-/

open Set Filter MeasureTheory
open scoped ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.RegularBranchKahlerJacobian

noncomputable section

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.ManifoldBorelFoundation
open SGPT.Foundations.Analysis.Pending.CountableRegularBranchMeasure
open SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone
open SGPT.Foundations.Analysis.Pending.SubvarietyStokesMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

namespace RegularPatch

variable {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The parameter Lebesgue measure on a closed ball, weighted by `rho`. -/
def closedBallWeightedParameterMeasure (_P : RegularPatch V) (r : ℝ)
    (rho : ComplexModel V.dim → ℝ≥0∞) : Measure (ComplexModel V.dim) :=
  (volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r)).withDensity rho

/-- The Borel pushforward of a weighted compact regular branch. -/
def closedBallWeightedPushforwardBorel (P : RegularPatch V) (r : ℝ)
    (rho : ComplexModel V.dim → ℝ≥0∞) : @Measure M (manifoldBorel M) :=
  by
    let _ : MeasurableSpace M := manifoldBorel M
    exact Measure.map P.toManifold (closedBallWeightedParameterMeasure P r rho)

/-- A regular parametrization remains a.e.-measurable after weighting its
parameter measure: the weighted measure is absolutely continuous with respect
to the unweighted parameter measure. -/
theorem aemeasurable_toManifold_closedBallWeightedParameterMeasure
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain)
    (rho : ComplexModel V.dim → ℝ≥0∞) :
    @AEMeasurable (ComplexModel V.dim) M (manifoldBorel M) _ P.toManifold
      (closedBallWeightedParameterMeasure P r rho) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  exact (regularPatchAEMeasurableToManifoldRestrictClosedBallBorel P hr).mono_ac
    (withDensity_absolutelyContinuous _ _)

/-- Ambient integration against a weighted compact branch is integration of
the pulled-back test function against its weighted parameter measure. -/
theorem lintegral_closedBallWeightedPushforwardBorel
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain)
    (rho : ComplexModel V.dim → ℝ≥0∞) (f : M → ℝ≥0∞)
    (hf : @AEMeasurable M ℝ≥0∞ _ (manifoldBorel M) f
      (closedBallWeightedPushforwardBorel P r rho)) :
    ∫⁻ x, f x ∂closedBallWeightedPushforwardBorel P r rho =
      ∫⁻ w, f (P.toManifold w) ∂closedBallWeightedParameterMeasure P r rho := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  simpa only [closedBallWeightedPushforwardBorel] using MeasureTheory.lintegral_map' hf
    (aemeasurable_toManifold_closedBallWeightedParameterMeasure P hr rho)

/-- The total mass of a weighted compact branch is the parameter Lebesgue
integral of its weight.  No measurability hypothesis on `rho` is hidden here:
the equality is the defining `withDensity` formula on the measurable whole
space. -/
theorem closedBallWeightedPushforwardBorel_univ
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain)
    (rho : ComplexModel V.dim → ℝ≥0∞) :
    closedBallWeightedPushforwardBorel P r rho Set.univ =
      ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r, rho w := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  rw [closedBallWeightedPushforwardBorel,
    Measure.map_apply_of_aemeasurable
      (aemeasurable_toManifold_closedBallWeightedParameterMeasure P hr rho)
      MeasurableSet.univ]
  simp only [Set.preimage_univ]
  change ((volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r)).withDensity rho)
      Set.univ = _
  rw [withDensity_apply rho MeasurableSet.univ]
  simp only [Measure.restrict_univ]

/-- The standard Hermitian top density pulled back by the derivative of a
regular parametrization.  This is the local Kähler Jacobian factor of the
branch relative to parameter Lebesgue measure. -/
def kahlerJacobianDensity (P : RegularPatch V) (w : ComplexModel V.dim) : ℝ :=
  actualTopPowerDensity
    ((standardHermitianTwoForm n).compContinuousLinearMap
      (fderiv ℝ P.coordinateParametrization w))

/-- The genuine top-power density is continuous as a function of a coordinate
two-form.  The pairing-sum formula makes this a finite polynomial in the
values of the form on the fixed standard frame. -/
theorem continuous_actualTopPowerDensity (n : ℕ) :
    Continuous (fun A : CoordinateRealTwoForm n => actualTopPowerDensity A) := by
  have hformula : (fun A : CoordinateRealTwoForm n => actualTopPowerDensity A) =
      fun A => ((2 : ℝ) ^ n)⁻¹ *
        coordinatePairingSum A
          (finProdFinEquiv : Fin n × Fin 2 → Fin (n * 2)) coordinateRealFrame := by
    funext A
    exact coordinateWedgePower_apply_eq_pairingSum A n coordinateRealFrame
  rw [hformula]
  unfold coordinatePairingSum
  fun_prop

/-- Pullback by a continuously varying real linear map preserves continuity of
the actual top-power density.  The map of alternating forms is handled through
the bundled continuous-linear pullback operator, so no unproved Jacobian
regularity is hidden in this statement. -/
theorem continuousOn_actualTopPowerDensity_compContinuousLinearMap
    {X : Type*} [TopologicalSpace X] {k : ℕ} {s : Set X}
    (A : X → CoordinateRealTwoForm n)
    (L : X → ComplexModel k →L[ℝ] ComplexModel n)
    (hA : ContinuousOn A s) (hL : ContinuousOn L s) :
    ContinuousOn (fun x =>
      actualTopPowerDensity ((A x).compContinuousLinearMap (L x))) s := by
  have hpull : ContinuousOn (fun x =>
      (A x).compContinuousLinearMap (L x)) s := by
    change ContinuousOn (fun x =>
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (L x)) (A x)) s
    exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn
      hL).clm_apply hA
  exact (continuous_actualTopPowerDensity k).comp_continuousOn hpull

/-- The Kähler Jacobian of a regular parametrization is continuous on its
parameter domain.  This uses actual smoothness of the inverse flattening map,
not merely pointwise differentiability. -/
theorem continuousOn_kahlerJacobianDensity (P : RegularPatch V) :
    ContinuousOn (kahlerJacobianDensity P) P.parameterDomain := by
  have hparam : ContDiffOn ℝ ∞ P.coordinateParametrization P.parameterDomain := by
    have hinv : ContDiffOn ℝ ∞ P.flattening.invFun P.flattening.target :=
      contDiffOn_real_of_differentiableOn_complex P.flattening.invFun_holomorphic
        P.flattening.isOpen_target
    exact hinv.comp ((planeInclusionCLM V.dim n).restrictScalars ℝ).contDiff.contDiffOn
      fun w hw => hw
  have hderiv : ContinuousOn (fderiv ℝ P.coordinateParametrization) P.parameterDomain :=
    hparam.continuousOn_fderiv_of_isOpen
      (RegularPatchDerivative.isOpen_parameterDomain P) (by simp)
  have hpull : ContinuousOn (fun w : ComplexModel V.dim =>
      (standardHermitianTwoForm n).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w)) P.parameterDomain := by
    change ContinuousOn (fun w : ComplexModel V.dim =>
      (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (fderiv ℝ P.coordinateParametrization w)) (standardHermitianTwoForm n))
      P.parameterDomain
    exact (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_continuousOn
      hderiv).clm_apply continuousOn_const
  change ContinuousOn (fun w => actualTopPowerDensity
    ((standardHermitianTwoForm n).compContinuousLinearMap
      (fderiv ℝ P.coordinateParametrization w))) P.parameterDomain
  exact (continuous_actualTopPowerDensity V.dim).comp_continuousOn hpull

/-- A regular parametrization has strictly positive Kähler Jacobian density
at every parameter in its domain.  The proof uses the already formalized
injectivity and complex linearity of its derivative. -/
theorem kahlerJacobianDensity_pos (P : RegularPatch V) {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) :
    0 < kahlerJacobianDensity P w := by
  let L : ComplexModel V.dim →L[ℝ] ComplexModel n :=
    fderiv ℝ P.coordinateParametrization w
  have hL : ∀ v, L (Complex.I • v) = Complex.I • L v := by
    intro v
    exact RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hw v
  have hinj : Function.Injective L :=
    RegularPatchDerivative.fderiv_coordinateParametrization_injective P hw
  apply actualTopPowerDensity_pos
    (isOneOne_compContinuousLinearMap (standardHermitianTwoForm_isOneOne n) L hL)
  intro v hv
  have hLv : L v ≠ 0 := by
    intro hzero
    exact hv (hinj (by simpa only [map_zero] using hzero))
  change 0 < (standardHermitianTwoForm n) ![L v, L (Complex.I • v)]
  rw [hL, standardHermitianTwoForm_apply_I_smul_self]
  exact sq_pos_of_pos (norm_pos_iff.mpr hLv)

/-- The Kähler-Jacobian weight is measurable for the restricted Lebesgue
measure of every compact parameter ball contained in the regular domain. -/
theorem aemeasurable_closedBall_kahlerJacobianDensity
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    AEMeasurable (fun w => ENNReal.ofReal (kahlerJacobianDensity P w))
      (volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r)) :=
  ((continuousOn_kahlerJacobianDensity P).mono hr).aemeasurable
    (isCompact_closedBall (0 : ComplexModel V.dim) r).measurableSet |>.ennreal_ofReal

/-- The Kähler-Jacobian weight has finite Lebesgue integral on every compact
parameter ball lying in the regular domain. -/
theorem lintegral_closedBall_kahlerJacobianDensity_lt_top
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r,
      ENNReal.ofReal (kahlerJacobianDensity P w) < ⊤ := by
  let K := Metric.closedBall (0 : ComplexModel V.dim) r
  have hK : IsCompact K := isCompact_closedBall _ _
  have hint : Integrable (kahlerJacobianDensity P) (volume.restrict K) :=
    ((continuousOn_kahlerJacobianDensity P).mono hr).integrableOn_compact hK
  have hnonneg : 0 ≤ᵐ[volume.restrict K] kahlerJacobianDensity P := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with w hw
    exact (kahlerJacobianDensity_pos P (hr hw)).le
  exact lt_top_iff_ne_top.2
    ((lintegral_ofReal_ne_top_iff_integrable hint.aestronglyMeasurable hnonneg).2 hint)

/-- The weighted Borel measure of the compact branch for its Kähler Jacobian. -/
def closedBallKahlerJacobianPushforwardBorel (P : RegularPatch V) (r : ℝ) :
    @Measure M (manifoldBorel M) :=
  closedBallWeightedPushforwardBorel P r (fun w => ENNReal.ofReal (kahlerJacobianDensity P w))

/-- The Kähler-Jacobian mass of a compact regular branch is the corresponding
parameter integral. -/
theorem closedBallKahlerJacobianPushforwardBorel_univ
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    closedBallKahlerJacobianPushforwardBorel P r Set.univ =
      ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r,
        ENNReal.ofReal (kahlerJacobianDensity P w) :=
  closedBallWeightedPushforwardBorel_univ P hr _

/-- The weighted Borel measure of a compact regular branch has finite total
Kähler-Jacobian mass. -/
theorem closedBallKahlerJacobianPushforwardBorel_univ_lt_top
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    closedBallKahlerJacobianPushforwardBorel P r Set.univ < ⊤ := by
  rw [closedBallKahlerJacobianPushforwardBorel_univ P hr]
  exact lintegral_closedBall_kahlerJacobianDensity_lt_top P hr

/-- The coordinate realization of the Kähler volume density induced on one
regular branch by an ambient Kähler background.  It is the actual top wedge of
the pullback of `beta.form`, so it is the local quantity that a future
Wirtinger theorem must identify with intrinsic regular-locus volume. -/
def inducedKahlerDensity (beta : KahlerBackground n M) (P : RegularPatch V)
    (w : ComplexModel V.dim) : ℝ :=
  actualTopPowerDensity
    ((beta.form.val.coeff (complexChartAt (n := n) P.center)
      (P.coordinateParametrization w)).compContinuousLinearMap
      (fderiv ℝ P.coordinateParametrization w))

/-- The induced Kähler density is continuous throughout the parameter domain
of a regular branch. -/
theorem continuousOn_inducedKahlerDensity
    (beta : KahlerBackground n M) (P : RegularPatch V) :
    ContinuousOn (inducedKahlerDensity beta P) P.parameterDomain := by
  have hparam : ContDiffOn ℝ ∞ P.coordinateParametrization P.parameterDomain := by
    have hinv : ContDiffOn ℝ ∞ P.flattening.invFun P.flattening.target :=
      contDiffOn_real_of_differentiableOn_complex P.flattening.invFun_holomorphic
        P.flattening.isOpen_target
    exact hinv.comp ((planeInclusionCLM V.dim n).restrictScalars ℝ).contDiff.contDiffOn
      fun w hw => hw
  have hderiv : ContinuousOn (fderiv ℝ P.coordinateParametrization) P.parameterDomain :=
    hparam.continuousOn_fderiv_of_isOpen
      (RegularPatchDerivative.isOpen_parameterDomain P) (by simp)
  have hcoeff : ContinuousOn (fun w =>
      beta.form.val.coeff (complexChartAt (n := n) P.center)
        (P.coordinateParametrization w)) P.parameterDomain := by
    refine (beta.form.val.smooth _).continuousOn.comp hparam.continuousOn ?_
    intro w hw
    exact P.source_subset (P.flattening.mapsTo_invFun hw)
  exact continuousOn_actualTopPowerDensity_compContinuousLinearMap _ _ hcoeff hderiv

/-- The induced Kähler density of a regular branch is strictly positive on its
parameter domain. -/
theorem inducedKahlerDensity_pos
    (beta : KahlerBackground n M) (P : RegularPatch V) {w : ComplexModel V.dim}
    (hw : w ∈ P.parameterDomain) :
    0 < inducedKahlerDensity beta P w := by
  let L : ComplexModel V.dim →L[ℝ] ComplexModel n :=
    fderiv ℝ P.coordinateParametrization w
  have hL : ∀ v, L (Complex.I • v) = Complex.I • L v := by
    intro v
    exact RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hw v
  have hinj : Function.Injective L :=
    RegularPatchDerivative.fderiv_coordinateParametrization_injective P hw
  have hz : P.coordinateParametrization w ∈
      (complexChartAt (n := n) P.center).val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  apply actualTopPowerDensity_pos
    (isOneOne_compContinuousLinearMap
      (beta.isKahler.1 _ _ hz).1 L hL)
  intro v hv
  have hLv : L v ≠ 0 := by
    intro hzero
    exact hv (hinj (by simpa only [map_zero] using hzero))
  have hpos := (beta.isKahler.1 _ _ hz).2 (L v) hLv
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hvec : L ∘ ![v, Complex.I • v] = ![L v, Complex.I • L v] := by
    funext i
    fin_cases i <;> simp [hL]
  rw [hvec]
  exact hpos

/-- On every compact parameter ball in the regular domain, the induced
Kähler density admits a finite nonnegative upper bound. -/
theorem exists_upper_bound_inducedKahlerDensity_closedBall
    (beta : KahlerBackground n M) (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall (0 : ComplexModel V.dim) r,
      inducedKahlerDensity beta P w ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ComplexModel V.dim) r).exists_bound_of_continuousOn
    ((continuousOn_inducedKahlerDensity beta P).mono hr)
  refine ⟨max C 0, le_max_right _ _, fun w hw => ?_⟩
  calc
    inducedKahlerDensity beta P w ≤ |inducedKahlerDensity beta P w| := le_abs_self _
    _ = ‖inducedKahlerDensity beta P w‖ := (Real.norm_eq_abs _).symm
    _ ≤ C := hC w hw
    _ ≤ max C 0 := le_max_left _ _

/-- On every nonempty compact parameter ball in the regular domain, the
induced Kähler density has a strictly positive lower bound. -/
theorem exists_pos_lower_bound_inducedKahlerDensity_closedBall
    (beta : KahlerBackground n M) (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Metric.closedBall (0 : ComplexModel V.dim) r,
      c ≤ inducedKahlerDensity beta P w := by
  let K := Metric.closedBall (0 : ComplexModel V.dim) r
  have hK : IsCompact K := isCompact_closedBall _ _
  rcases K.eq_empty_or_nonempty with hKempty | hKnonempty
  · refine ⟨1, one_pos, ?_⟩
    intro w hw
    change w ∈ K at hw
    rw [hKempty] at hw
    exact hw.elim
  · obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hKnonempty
      ((continuousOn_inducedKahlerDensity beta P).mono hr)
    exact ⟨inducedKahlerDensity beta P w,
      inducedKahlerDensity_pos beta P (hr hw), fun z hz => hmin hz⟩

/-- The induced Kähler density is integrable on every compact parameter ball
in the regular domain. -/
theorem lintegral_closedBall_inducedKahlerDensity_lt_top
    (beta : KahlerBackground n M) (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r,
      ENNReal.ofReal (inducedKahlerDensity beta P w) < ⊤ := by
  let K := Metric.closedBall (0 : ComplexModel V.dim) r
  have hK : IsCompact K := isCompact_closedBall _ _
  have hint : Integrable (inducedKahlerDensity beta P) (volume.restrict K) :=
    ((continuousOn_inducedKahlerDensity beta P).mono hr).integrableOn_compact hK
  have hnonneg : 0 ≤ᵐ[volume.restrict K] inducedKahlerDensity beta P := by
    filter_upwards [ae_restrict_mem hK.measurableSet] with w hw
    exact (inducedKahlerDensity_pos beta P (hr hw)).le
  exact lt_top_iff_ne_top.2
    ((lintegral_ofReal_ne_top_iff_integrable hint.aestronglyMeasurable hnonneg).2 hint)

/-- At a point where the ambient Kähler coefficient is the standard Hermitian
form, its induced branch density is the Kähler Jacobian already constructed
above.  This isolates exactly the local normal-coordinate comparison needed
for a future Wirtinger identification. -/
theorem inducedKahlerDensity_eq_kahlerJacobianDensity_of_coeff_eq
    (beta : KahlerBackground n M) (P : RegularPatch V) (w : ComplexModel V.dim)
    (hcoeff : beta.form.val.coeff (complexChartAt (n := n) P.center)
      (P.coordinateParametrization w) = standardHermitianTwoForm n) :
    inducedKahlerDensity beta P w = kahlerJacobianDensity P w := by
  unfold inducedKahlerDensity kahlerJacobianDensity
  rw [hcoeff]

/-- For a zero-class, zero-potential presentation at error one, the
restricted-current density is exactly the pullback density of the ambient
Kähler background.  This is a direct density equality; it does not invoke
Stokes, a global cover, or a putative subvariety measure. -/
theorem patchDensity_eq_inducedKahlerDensity_of_zero_data
    (beta : KahlerBackground n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) (hv : q.potential = fun _ => 0)
    (P : RegularPatch V) (w : ComplexModel V.dim) :
    patchDensity q P w = inducedKahlerDensity beta P w := by
  simp [patchDensity, coordinateCurrentForm, perturbedRepresentative,
    inducedKahlerDensity, hq, hv]

/-- The nonnegative top-density weight of an admissible presentation on a
regular parameter branch. -/
def currentTopDensityWeight
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {epsilon : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) (w : ComplexModel V.dim) : ℝ≥0∞ :=
  ENNReal.ofReal (patchDensity p P w)

/-- The ambient Borel measure obtained by weighting a compact regular branch
with its induced Kähler top density. -/
def closedBallInducedKahlerPushforwardBorel
    (beta : KahlerBackground n M) (P : RegularPatch V) (r : ℝ) :
    @Measure M (manifoldBorel M) :=
  closedBallWeightedPushforwardBorel P r
    (fun w => ENNReal.ofReal (inducedKahlerDensity beta P w))

/-- Its mass is the parameter integral of the induced Kähler density. -/
theorem closedBallInducedKahlerPushforwardBorel_univ
    (beta : KahlerBackground n M) (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    closedBallInducedKahlerPushforwardBorel beta P r Set.univ =
      ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r,
        ENNReal.ofReal (inducedKahlerDensity beta P w) :=
  closedBallWeightedPushforwardBorel_univ P hr _

/-- The induced Kähler measure of every compact regular branch has finite
total mass. -/
theorem closedBallInducedKahlerPushforwardBorel_univ_lt_top
    (beta : KahlerBackground n M) (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    closedBallInducedKahlerPushforwardBorel beta P r Set.univ < ⊤ := by
  rw [closedBallInducedKahlerPushforwardBorel_univ beta P hr]
  exact lintegral_closedBall_inducedKahlerDensity_lt_top beta P hr

/-- The local top-density measure associated with a presentation, as a Borel
measure on the image of a compact regular branch. -/
def closedBallCurrentTopDensityPushforwardBorel
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {epsilon : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) (r : ℝ) : @Measure M (manifoldBorel M) :=
  closedBallWeightedPushforwardBorel P r (currentTopDensityWeight p P)

/-- On a zero-class, zero-potential presentation, the compact branch current
measure agrees as a Borel measure with the branch measure weighted by the
induced Kähler density. -/
theorem closedBallCurrentTopDensityPushforwardBorel_eq_inducedKahler
    (beta : KahlerBackground n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) (hv : q.potential = fun _ => 0)
    (P : RegularPatch V) (r : ℝ) :
    closedBallCurrentTopDensityPushforwardBorel q P r =
      closedBallInducedKahlerPushforwardBorel beta P r := by
  change closedBallWeightedPushforwardBorel P r
      (fun w => ENNReal.ofReal (patchDensity q P w)) =
    closedBallWeightedPushforwardBorel P r
      (fun w => ENNReal.ofReal (inducedKahlerDensity beta P w))
  apply congrArg (closedBallWeightedPushforwardBorel P r)
  funext w
  exact congrArg ENNReal.ofReal
    (patchDensity_eq_inducedKahlerDensity_of_zero_data beta q hq hv P w)

/-- In particular, every compact branch has finite local current mass for a
zero-class, zero-potential presentation. -/
theorem closedBallCurrentTopDensityPushforwardBorel_univ_lt_top_of_zero_data
    (beta : KahlerBackground n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) (hv : q.potential = fun _ => 0)
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    closedBallCurrentTopDensityPushforwardBorel q P r Set.univ < ⊤ := by
  rw [closedBallCurrentTopDensityPushforwardBorel_eq_inducedKahler beta q hq hv P r]
  exact closedBallInducedKahlerPushforwardBorel_univ_lt_top beta P hr

/-- The mass of the local top-density measure is exactly the parameter integral
used by the `acTopMass` construction. -/
theorem closedBallCurrentTopDensityPushforwardBorel_univ
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {epsilon : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    closedBallCurrentTopDensityPushforwardBorel p P r Set.univ =
      ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r,
        ENNReal.ofReal (patchDensity p P w) :=
  closedBallWeightedPushforwardBorel_univ P hr _

/-- Thus the local current mass of a zero-class, zero-potential presentation
is exactly the pullback Kähler-volume integral on the compact regular branch. -/
theorem closedBallCurrentTopDensityPushforwardBorel_univ_eq_inducedKahler
    (beta : KahlerBackground n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) (hv : q.potential = fun _ => 0)
    (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    closedBallCurrentTopDensityPushforwardBorel q P r Set.univ =
      ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r,
        ENNReal.ofReal (inducedKahlerDensity beta P w) := by
  rw [closedBallCurrentTopDensityPushforwardBorel_eq_inducedKahler beta q hq hv P r]
  exact closedBallInducedKahlerPushforwardBorel_univ beta P hr

/-- For a zero-potential presentation, the compact branch mass is precisely
the parameter integral of the pullback top density of the perturbed smooth
representative.  This is the local Jacobian/density bridge; Stokes and global
local-finiteness are deliberately not used. -/
theorem closedBallCurrentTopDensityPushforwardBorel_univ_eq_perturbedRepresentative
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {epsilon : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (hp : p.potential = fun _ => 0) (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    closedBallCurrentTopDensityPushforwardBorel p P r Set.univ =
      ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r,
        ENNReal.ofReal
          (actualTopPowerDensity
            (((perturbedRepresentative p).val.coeff (complexChartAt (n := n) P.center)
              (P.coordinateParametrization w)).compContinuousLinearMap
              (fderiv ℝ P.coordinateParametrization w))) := by
  rw [closedBallCurrentTopDensityPushforwardBorel_univ p P hr]
  apply lintegral_congr
  intro w
  exact congrArg ENNReal.ofReal
    (patchDensity_eq_perturbedRepresentative_of_potential_eq_zero p hp P w)

end RegularPatch

/-! ## Countable gluing of induced Kähler branch measures

The preceding local construction supplies a finite measure on each compact
regular branch.  The following assembly is deliberately conditional only on
the genuinely needed summability statement for those *actual weighted branch
masses*.  It turns such data into a finite Borel measure and a linear testing
functional, while retaining the separate analytic obligation of constructing
the summable cover from finite branched projections.
-/

namespace CountableKahlerBranchAssembly

open RegularPatch
open CountableCompactRegularBranchCover

variable {V : ClosedIrreducibleAnalyticSubvariety n M}

/-- The induced Kähler measure of the `i`-th compact branch of a supplied
countable regular-branch cover. -/
def branchInducedKahlerMeasure (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V) (i : ℕ) :
    @Measure M (manifoldBorel M) :=
  closedBallInducedKahlerPushforwardBorel beta (A.patch i) (A.radius i)

/-- The Borel measure obtained by summing the induced Kähler measures of all
compact branches. -/
def assembledInducedKahlerMeasure (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V) : @Measure M (manifoldBorel M) :=
  Measure.sum (branchInducedKahlerMeasure beta A)

/-- Evaluation of the assembled Kähler measure is the countable series of
the corresponding branch evaluations. -/
theorem assembledInducedKahlerMeasure_apply (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V) (s : Set M) :
    assembledInducedKahlerMeasure beta A s =
      ∑' i, branchInducedKahlerMeasure beta A i s := by
  exact Measure.sum_apply_of_countable (branchInducedKahlerMeasure beta A) s

/-- Each weighted compact branch is carried by its declared branch image. -/
theorem ae_mem_branchImage (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V) (i : ℕ) :
    ∀ᵐ x ∂branchInducedKahlerMeasure beta A i, x ∈ A.branchImage i := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  let rho : ComplexModel V.dim → ℝ≥0∞ :=
    fun w => ENNReal.ofReal (inducedKahlerDensity beta (A.patch i) w)
  have hsource : ∀ᵐ w ∂closedBallWeightedParameterMeasure (A.patch i) (A.radius i) rho,
      w ∈ Metric.closedBall (0 : ComplexModel V.dim) (A.radius i) := by
    exact (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem Metric.isClosed_closedBall.measurableSet)
  change ∀ᵐ x ∂Measure.map (A.patch i).toManifold
      (closedBallWeightedParameterMeasure (A.patch i) (A.radius i) rho),
      x ∈ (A.patch i).toManifold ''
        Metric.closedBall (0 : ComplexModel V.dim) (A.radius i)
  apply (ae_map_iff
    (aemeasurable_toManifold_closedBallWeightedParameterMeasure (A.patch i)
      (A.closedBall_subset_parameterDomain i) rho)
    (A.branchImage_measurableSet i)).2
  filter_upwards [hsource] with w hw
  exact ⟨w, hw, rfl⟩

/-- The assembled Kähler measure is carried by the regular locus. -/
theorem ae_mem_regularLocus (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V) :
    ∀ᵐ x ∂assembledInducedKahlerMeasure beta A,
      x ∈ regularLocus (n := n) V.carrier V.dim := by
  change ∀ᵐ x ∂Measure.sum (branchInducedKahlerMeasure beta A),
    x ∈ regularLocus (n := n) V.carrier V.dim
  rw [Measure.ae_sum_iff]
  intro i
  filter_upwards [ae_mem_branchImage beta A i] with x hx
  exact A.branchImage_subset_regularLocus i hx

/-- Summability of the actual induced Kähler masses makes the assembled Borel
measure finite.  This is the exact gluing hypothesis required by the measure
construction; no global cover existence theorem is asserted here. -/
theorem assembledInducedKahlerMeasure_univ_lt_top (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V)
    (hsum : ∑' i, branchInducedKahlerMeasure beta A i Set.univ < ⊤) :
    assembledInducedKahlerMeasure beta A Set.univ < ⊤ := by
  rw [assembledInducedKahlerMeasure_apply]
  exact hsum

/-- In particular, summability makes the glued Kähler measure finite on every
compact ambient set.  This is the local-finiteness bridge needed by compactly
supported testing, obtained from the actual finite total mass rather than from
an unproved assertion about analytic covers. -/
theorem assembledInducedKahlerMeasure_isFiniteMeasureOnCompacts
    (beta : KahlerBackground n M) (A : CountableCompactRegularBranchCover V)
    (hsum : ∑' i, branchInducedKahlerMeasure beta A i Set.univ < ⊤) :
    IsFiniteMeasureOnCompacts (assembledInducedKahlerMeasure beta A) where
  lt_top_of_isCompact K _ :=
    (measure_mono (Set.subset_univ K)).trans_lt
      (assembledInducedKahlerMeasure_univ_lt_top beta A hsum)

/-- The countably glued induced Kähler measure, packaged for finite-measure
APIs once its actual branch masses are summable. -/
def finiteAssembledInducedKahlerMeasure (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V)
    (hsum : ∑' i, branchInducedKahlerMeasure beta A i Set.univ < ⊤) :
    @FiniteMeasure M (manifoldBorel M) :=
  ⟨assembledInducedKahlerMeasure beta A,
    ⟨assembledInducedKahlerMeasure_univ_lt_top beta A hsum⟩⟩

@[simp]
theorem finiteAssembledInducedKahlerMeasure_coe (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V)
    (hsum : ∑' i, branchInducedKahlerMeasure beta A i Set.univ < ⊤) :
    (finiteAssembledInducedKahlerMeasure beta A hsum : @Measure M (manifoldBorel M)) =
      assembledInducedKahlerMeasure beta A :=
  rfl

/-- A bounded continuous real test function is integrable against the glued
Kähler measure whenever the branch masses are summable. -/
theorem integrable_boundedContinuousTest (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V)
    (hsum : ∑' i, branchInducedKahlerMeasure beta A i Set.univ < ⊤)
    (f : BoundedContinuousFunction M ℝ) :
    Integrable (fun x => f x) (assembledInducedKahlerMeasure beta A) := by
  let _ : MeasurableSpace M := manifoldBorel M
  let _ : BorelSpace M := ⟨rfl⟩
  let _ : IsFiniteMeasure (assembledInducedKahlerMeasure beta A) :=
    ⟨assembledInducedKahlerMeasure_univ_lt_top beta A hsum⟩
  apply Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
  exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm x

/-- A bounded-continuous test integral splits as the convergent series of the
compact induced-Kähler branch integrals. -/
theorem integral_assembledInducedKahlerMeasure (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V)
    (hsum : ∑' i, branchInducedKahlerMeasure beta A i Set.univ < ⊤)
    (f : BoundedContinuousFunction M ℝ) :
    ∫ x, f x ∂assembledInducedKahlerMeasure beta A =
      ∑' i, ∫ x, f x ∂branchInducedKahlerMeasure beta A i := by
  change ∫ x, f x ∂Measure.sum (branchInducedKahlerMeasure beta A) =
    ∑' i, ∫ x, f x ∂branchInducedKahlerMeasure beta A i
  exact integral_sum_measure (integrable_boundedContinuousTest beta A hsum f)

/-- The real linear functional obtained by testing the finite glued Kähler
measure against bounded continuous functions.  It is a measure-theoretic
precursor of the integration current, not an assertion that it is closed. -/
def inducedKahlerTestFunctional (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V)
    (hsum : ∑' i, branchInducedKahlerMeasure beta A i Set.univ < ⊤) :
    BoundedContinuousFunction M ℝ →ₗ[ℝ] ℝ where
  toFun := fun f => ∫ x, f x ∂assembledInducedKahlerMeasure beta A
  map_add' := by
    intro f g
    simpa using integral_add (integrable_boundedContinuousTest beta A hsum f)
      (integrable_boundedContinuousTest beta A hsum g)
  map_smul' := by
    intro c f
    simpa using (integrable_boundedContinuousTest beta A hsum f).integral_smul c

/-- The glued Kähler test functional is insensitive to modifications off the
regular locus. -/
theorem inducedKahlerTestFunctional_congr_on_regularLocus
    (beta : KahlerBackground n M) (A : CountableCompactRegularBranchCover V)
    (hsum : ∑' i, branchInducedKahlerMeasure beta A i Set.univ < ⊤)
    (f g : BoundedContinuousFunction M ℝ)
    (hfg : Set.EqOn (fun x => f x) (fun x => g x)
      (regularLocus (n := n) V.carrier V.dim)) :
    inducedKahlerTestFunctional beta A hsum f =
      inducedKahlerTestFunctional beta A hsum g := by
  apply integral_congr_ae
  filter_upwards [ae_mem_regularLocus beta A] with x hx
  exact hfg hx

/-- Evaluation of the glued Kähler test functional is the convergent sum of
the compact branch test integrals. -/
theorem inducedKahlerTestFunctional_eq_tsum (beta : KahlerBackground n M)
    (A : CountableCompactRegularBranchCover V)
    (hsum : ∑' i, branchInducedKahlerMeasure beta A i Set.univ < ⊤)
    (f : BoundedContinuousFunction M ℝ) :
    inducedKahlerTestFunctional beta A hsum f =
      ∑' i, ∫ x, f x ∂branchInducedKahlerMeasure beta A i :=
  integral_assembledInducedKahlerMeasure beta A hsum f

end CountableKahlerBranchAssembly

end

end SGPT.Foundations.Analysis.Pending.RegularBranchKahlerJacobian
