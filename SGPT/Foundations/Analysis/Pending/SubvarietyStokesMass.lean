import SGPT.Foundations.Analysis.Pending.CountableRegularBranchMeasure
import SGPT.Foundations.Analysis.Pending.SubvarietyStokesMassInterfaces

set_option autoImplicit false

/-!
# Stokes' theorem and finite volume on an irreducible subvariety

Source: Lelong, *Intégration sur un ensemble analytique complexe* (1957): the
current of integration `[V]` over an irreducible `k`-dimensional analytic
subvariety `V` of a complex manifold is well defined (`V_reg` has locally finite
volume) and closed; Demailly, *Complex analytic and differential geometry*,
Ch. III, Theorems 2.7 and 2.10; blueprint `ana:subvariety-stokes-mass`.

Let `(X, β)` be compact Kähler and `V ⊆ X` an irreducible analytic subvariety of
dimension `k`.  In the first-pass encoding a presentation of the zero class at
error `1` for `β` with zero representative and a chart-smooth real potential `v`
is a smooth function with `β + ddᶜv ≥ 0`, and its `acTopMass` is
`∫_{V_reg} ((β + ddᶜv)|_{V_reg})^k`.

* `acTopMass_eq_of_smooth` (**Stokes against `[V]`**): this integral does not depend
  on `v`.  Indeed `(β + ddᶜv)^k - β^k = ddᶜv ∧ S = d(dᶜv ∧ S)` for a closed smooth
  form `S`, and `∫_V dη = ⟨[V], dη⟩ = 0` because `[V]` is closed.
* `acTopMass_ne_top_of_zero_potential` (**Lelong's finiteness**):
  `∫_{V_reg} β^k = k! vol_β(V_reg) < ∞` since `V_reg` has locally finite `2k`-volume
  and `X` is compact.

Both statements concern smooth forms only: no potential here has poles.
`Pending.KahlerRestrictedMassBound.exists_acTopMass_le_of_zero_representative` is
PROVED from them by smooth truncation of potentials with poles
(`Pending.KahlerMassTruncation`).

**What is missing.**  Both obligations are now DERIVED from the two named
interfaces of `Pending.SubvarietyStokesMassInterfaces`, which speak about a
single quantity `backgroundMass beta V` built from the background Kähler form
and the regular patches of `V` alone:

* `backgroundMass_ne_top` (Lelong) still needs the analytic theorem supplying a
  countable compact regular-branch cover with summable **parameter** masses — a
  proper finite branched projection of `V` onto a `k`-dimensional polydisc near
  every point, a uniform sheet bound, and Wirtinger's inequality, including the
  Jacobian comparison identifying the parameter construction with intrinsic
  volume.  `CountableRegularBranchMeasure` turns such a supplied cover into a
  finite auxiliary Borel measure.
* `acTopMass_eq_backgroundMass` (Stokes) still needs the cut-off argument near
  `V_sing` (which has locally finite `2k - 2`-volume) showing that the
  integration current of `V_reg` is closed.
-/

open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SubvarietyStokesMass

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.RegularPatchNeighborhood
open MeasureTheory

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `acTopMass` is independent of the proof fields in an admissible
presentation once its smooth representative and potential are fixed. -/
theorem acTopMass_congr
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}
    (p q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (hrep : p.representative = q.representative)
    (hpot : p.potential = q.potential) :
    acTopMass p = acTopMass q := by
  cases p
  cases q
  cases hrep
  cases hpot
  rfl

/-- A presentation with the zero extended-real potential has no polar set. -/
theorem poleSet_eq_empty_of_potential_eq_zero
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (hp : p.potential = fun _ => 0) : poleSet p.potential = ∅ := by
  rw [hp]
  ext x
  simp [poleSet]

/-- A regular-patch parametrization is injective on its parameter domain.
This is the point-set prerequisite for pushing Lebesgue measure forward along a
regular branch when constructing the integration current of a subvariety. -/
theorem RegularPatch.toManifold_injectiveOn
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) :
    Set.InjOn P.toManifold P.parameterDomain := by
  intro w hw z hz hwz
  have hcoord : P.coordinateParametrization w = P.coordinateParametrization z := by
    calc
      P.coordinateParametrization w =
          (complexChartAt (n := n) P.center).val (P.toManifold w) :=
        (FirstPass.RegularPatchNeighborhood.RegularPatch.chart_toManifold P hw).symm
      _ = (complexChartAt (n := n) P.center).val (P.toManifold z) := by rw [hwz]
      _ = P.coordinateParametrization z :=
        FirstPass.RegularPatchNeighborhood.RegularPatch.chart_toManifold P hz
  have hplane : planeInclusion V.dim n w = planeInclusion V.dim n z := by
    calc
      planeInclusion V.dim n w = P.flattening.toFun (P.coordinateParametrization w) :=
        (P.flattening.right_inv _ hw).symm
      _ = P.flattening.toFun (P.coordinateParametrization z) := by rw [hcoord]
      _ = planeInclusion V.dim n z := P.flattening.right_inv _ hz
  exact FirstPass.AdmissibleCurrentFormPositivity.planeInclusion_injective V.dim_le hplane

/-- Every regular patch contains a closed parameter ball of finite Lebesgue
volume.  Together with `toManifold_injectiveOn`, this supplies the local finite
pieces from which a future integration current `[V]` can be assembled. -/
theorem RegularPatch.exists_closedBall_subset_parameterDomain
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain ∧
      volume (Metric.closedBall (0 : ComplexModel V.dim) r) < ⊤ := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp
    (FirstPass.AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P)
    (0 : ComplexModel V.dim)
    (FirstPass.RegularPatchNeighborhood.RegularPatch.zero_mem_parameterDomain P)
  refine ⟨R / 2, half_pos hR, ?_, measure_closedBall_lt_top⟩
  exact (Metric.closedBall_subset_ball (by linarith)).trans hball

/-- The image of a closed parameter ball contained in a regular patch is
compact.  Thus the finite-volume parameter pieces above give genuine compact
regular branches in the ambient manifold, independently of any choice of a
global analytic-subvariety measure. -/
theorem RegularPatch.isCompact_image_closedBall
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    IsCompact (P.toManifold '' Metric.closedBall (0 : ComplexModel V.dim) r) :=
  (isCompact_closedBall (0 : ComplexModel V.dim) r).image_of_continuousOn
    ((FirstPass.RegularPatchNeighborhood.RegularPatch.continuousOn_toManifold P).mono hr)

section LocalBranchMeasure

variable [MeasurableSpace M] [BorelSpace M]

/-- The measure carried by one compact regular branch.  It is the pushforward
of Lebesgue measure on a closed parameter ball; no global cover of the regular
locus and no putative ambient measure on the analytic subvariety are used. -/
def RegularPatch.closedBallPushforward
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) (r : ℝ) :
    Measure M :=
  Measure.map P.toManifold (volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r))

/-- The regular-patch parametrization is measurable for the restricted
Lebesgue measure on every closed ball contained in its parameter domain. -/
theorem RegularPatch.aemeasurable_toManifold_restrict_closedBall
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    AEMeasurable P.toManifold
      (volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r)) :=
  ((FirstPass.RegularPatchNeighborhood.RegularPatch.continuousOn_toManifold P).mono hr).aemeasurable
    Metric.isClosed_closedBall.measurableSet

/-- Every compact regular branch has finite mass.  This is the finite local
measure input needed before one can assemble the integration current `[V]`. -/
theorem RegularPatch.closedBallPushforward_univ_lt_top
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain) :
    RegularPatch.closedBallPushforward P r Set.univ < ⊤ := by
  rw [closedBallPushforward,
    Measure.map_apply_of_aemeasurable
      (RegularPatch.aemeasurable_toManifold_restrict_closedBall P hr) MeasurableSet.univ]
  simpa only [Set.preimage_univ, Measure.restrict_apply_univ] using
    (measure_closedBall_lt_top :
      volume (Metric.closedBall (0 : ComplexModel V.dim) r) < ⊤)

/-- Integration against a compact regular-branch measure is the parameter
integral.  The measurability requirement is deliberately relative to this
branch measure, so the statement does not assume a global analytic cover. -/
theorem RegularPatch.lintegral_closedBallPushforward
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain)
    (f : M → ENNReal) (hf : AEMeasurable f (RegularPatch.closedBallPushforward P r)) :
    ∫⁻ x, f x ∂RegularPatch.closedBallPushforward P r =
      ∫⁻ w, f (P.toManifold w) ∂
        (volume.restrict (Metric.closedBall (0 : ComplexModel V.dim) r)) := by
  exact MeasureTheory.lintegral_map' hf
    (RegularPatch.aemeasurable_toManifold_restrict_closedBall P hr)

end LocalBranchMeasure

/-- A continuous ambient test function is integrable along every compact
regular branch.  This gives the local real-valued integration interface
independently of the still-open global finite-cover construction. -/
theorem RegularPatch.integrableOn_comp_toManifold_closedBall_of_continuousOn_image
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V) {r : ℝ}
    (hr : Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain)
    {E : Type*} [NormedAddCommGroup E] (f : M → E)
    (hf : ContinuousOn f (P.toManifold '' Metric.closedBall (0 : ComplexModel V.dim) r)) :
    IntegrableOn (f ∘ P.toManifold) (Metric.closedBall (0 : ComplexModel V.dim) r) volume := by
  apply ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : ComplexModel V.dim) r)
  exact hf.comp
    ((FirstPass.RegularPatchNeighborhood.RegularPatch.continuousOn_toManifold P).mono hr)
    (fun w hw => Set.mem_image_of_mem P.toManifold hw)

/-- On a zero-potential presentation, the local density is exactly the top
density of its perturbed closed representative pulled back by the regular-patch
parametrization.  This is the coordinate-level bridge needed before a future
integration-current/Stokes construction can compare the finite-piece sums. -/
theorem patchDensity_eq_perturbedRepresentative_of_potential_eq_zero
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (hp : p.potential = fun _ => 0) (P : RegularPatch V) (w : ComplexModel V.dim) :
    patchDensity p P w =
      MongeAmpere.actualTopPowerDensity
        (((perturbedRepresentative p).val.coeff (complexChartAt (n := n) P.center)
          (P.coordinateParametrization w)).compContinuousLinearMap
          (fderiv ℝ P.coordinateParametrization w)) := by
  simp [patchDensity, coordinateCurrentForm, hp]

/-- Every finite regular-piece sum of a zero-potential presentation is the sum
of the coordinate top densities of its perturbed closed representative.  No
Stokes assertion or finiteness is used here. -/
theorem regularPieceFamily_mass_eq_perturbedRepresentative_of_potential_eq_zero
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (hp : p.potential = fun _ => 0) (F : RegularPieceFamily V (poleSet p.potential)) :
    (∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity p (F.patch i) w)) =
      ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal
        (MongeAmpere.actualTopPowerDensity
          (((perturbedRepresentative p).val.coeff (complexChartAt (n := n) (F.patch i).center)
            ((F.patch i).coordinateParametrization w)).compContinuousLinearMap
            (fderiv ℝ (F.patch i).coordinateParametrization w))) := by
  apply Finset.sum_congr rfl
  intro i _
  apply MeasureTheory.lintegral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    exact congrArg ENNReal.ofReal
      (patchDensity_eq_perturbedRepresentative_of_potential_eq_zero p hp (F.patch i) w)

/-- If two presentations have the same pole set and identical coordinate densities,
their `acTopMass` values agree.  This isolates the finite-piece bookkeeping from
the analytic comparison of the densities. -/
theorem acTopMass_eq_of_poleSet_eq_of_patchDensity_eq
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}
    (p q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (hpole : poleSet p.potential = poleSet q.potential)
    (hdensity : ∀ (P : RegularPatch V) (w : ComplexModel V.dim),
      patchDensity p P w = patchDensity q P w) :
    acTopMass p = acTopMass q := by
  classical
  unfold acTopMass
  rw [hpole]
  apply iSup_congr
  intro F
  apply Finset.sum_congr rfl
  intro i _
  apply MeasureTheory.lintegral_congr_ae
  exact Filter.Eventually.of_forall fun w => by
    change ENNReal.ofReal (patchDensity p (F.patch i) w) =
      ENNReal.ofReal (patchDensity q (F.patch i) w)
    exact congrArg ENNReal.ofReal (hdensity (F.patch i) w)

/-- A coordinate-density inequality compares `acTopMass` after shrinking the
exceptional pole set.  Each finite regular-piece family avoiding the larger pole
set is reused as a family avoiding the smaller one. -/
theorem acTopMass_le_of_poleSet_subset_of_patchDensity_le
    {omega : KahlerBackground n M} {alpha : RealBottChern n M}
    {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}
    (p q : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (hpole : poleSet q.potential ⊆ poleSet p.potential)
    (hdensity : ∀ (P : RegularPatch V) (w : ComplexModel V.dim),
      patchDensity p P w ≤ patchDensity q P w) :
    acTopMass p ≤ acTopMass q := by
  classical
  unfold acTopMass
  refine iSup_le fun F => ?_
  let G : RegularPieceFamily V (poleSet q.potential) :=
    { F with
      image_disjoint_avoid := fun i => (F.image_disjoint_avoid i).mono_right hpole }
  calc
    (∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity p (F.patch i) w)) ≤
        ∑ i, ∫⁻ w in G.piece i, ENNReal.ofReal (patchDensity q (G.patch i) w) := by
      dsimp only [G]
      apply Finset.sum_le_sum
      intro i _
      apply MeasureTheory.lintegral_mono_ae
      exact Filter.Eventually.of_forall fun w =>
        ENNReal.ofReal_mono (hdensity (F.patch i) w)
    _ ≤ ⨆ F : RegularPieceFamily V (poleSet q.potential),
        ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity q (F.patch i) w) :=
      le_iSup (fun F : RegularPieceFamily V (poleSet q.potential) =>
        ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (patchDensity q (F.patch i) w)) G

/-- Stokes' theorem against the closed current `[V]` (Lelong).  For two smooth
`β`-psh potentials `v, v'` on a compact manifold,
`∫_{V_reg} (β + ddᶜv)^{dim V} = ∫_{V_reg} (β + ddᶜv')^{dim V}`.

Both sides are now compared with the single fixed quantity
`SubvarietyStokesMassInterfaces.backgroundMass beta V`, so the remaining
classical input is the NAMED one-potential interface
`SubvarietyStokesMassInterfaces.acTopMass_eq_backgroundMass`. -/
theorem acTopMass_eq_of_smooth [CompactSpace M]
    (beta : KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q q' : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) (hq' : q'.representative = 0)
    (hv : ∃ v : M → ℝ, ChartSmooth (n := n) v ∧ q.potential = fun x => (v x : EReal))
    (hv' : ∃ v : M → ℝ, ChartSmooth (n := n) v ∧ q'.potential = fun x => (v x : EReal)) :
    acTopMass q = acTopMass q' := by
  rw [SubvarietyStokesMassInterfaces.acTopMass_eq_backgroundMass beta V q hq hv,
    SubvarietyStokesMassInterfaces.acTopMass_eq_backgroundMass beta V q' hq' hv']

/-- Lelong: the regular part of an analytic subvariety of a compact manifold has
finite volume, `∫_{V_reg} β^{dim V} < ∞`.

Derived from the SINGLE named interface
`SubvarietyStokesMassInterfaces.backgroundMass_ne_top`: with a zero potential
there is nothing to move, so
`SubvarietyStokesMassInterfaces.acTopMass_eq_backgroundMass_of_potential_eq_zero`
identifies the mass with the background mass unconditionally.  In particular
this statement does NOT depend on the Stokes interface. -/
theorem acTopMass_ne_top_of_zero_potential [CompactSpace M]
    (beta : KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (q : AdmissibleRestrictedCurrentPresentation beta
      (RealBottChern.ofRepresentative 0) V ⟨1, one_pos⟩)
    (hq : q.representative = 0) (hv : q.potential = fun _ => 0) :
    acTopMass q ≠ ⊤ := by
  rw [SubvarietyStokesMassInterfaces.acTopMass_eq_backgroundMass_of_potential_eq_zero
    beta V q hq hv]
  exact SubvarietyStokesMassInterfaces.backgroundMass_ne_top beta V

end

end SGPT.Foundations.Analysis.Pending.SubvarietyStokesMass
