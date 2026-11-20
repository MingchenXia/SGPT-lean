import SGPT.Foundations.Analysis.Pending.RegularPatchDensityContinuity
import SGPT.Foundations.Analysis.Pending.LocalFlatVolumeBound

set_option autoImplicit false

/-!
# The background regular-piece mass of a subvariety, and its localization

This module is the lower half of `Pending.SubvarietyStokesMassInterfaces`: it
carries the definition of the background mass `backgroundMass β V` (the
project's encoding of `∫_{V_reg} β^{dim V}`) together with the reduction of its
finiteness to a purely LOCAL statement.

`docs/stokes_formalization_audit_20260920.md` records that the finiteness of
that number is Lelong's theorem on the locally finite volume of an analytic set.
Lelong's theorem is local: what it really produces is, near every point of `V`,
a neighbourhood on which the `2 dim V`-volume of `V` is bounded (by the sheet
number of a branched projection onto a polydisc, times the volume of the
polydisc).  The passage from that local bound to the global finiteness of
`backgroundMass` is elementary and is **proved here**:

* `measurableSet_inter_toManifold_preimage` — a measurable parameter piece meets
  the preimage of an open set of `M` in a measurable set, because
  `RegularPatch.toManifold` is continuous on the (open) parameter domain;
* `restrictOpenFamily` — restricting every piece of a regular-piece
  family to such a preimage is again a regular-piece family, with the same
  patches and with all images inside the open set;
* `backgroundMass_ne_top_of_localBounds` — a finite subcover of the compact
  carrier `V` by neighbourhoods carrying local bounds, subadditivity of the
  Lebesgue integral over the finite cover of each piece, and exchanging the two
  finite sums, bound `backgroundMass β V` by the finite sum of the local
  constants.

What is left is the local bound, and only at the SINGULAR points:
`exists_localBackgroundBound_of_mem_regularLocus` PROVES it at every regular
point of `V`, using the change of patch of `Pending.RegularPatchTransition` to
transport every piece of every family into a single compact parameter ball of
one patch, where the pieces stay disjoint and the density is continuous.  The
named classical input is therefore
`exists_localBackgroundBound_of_notMem_regularLocus` — one singular point at a
time, no compactness, no global structure.

The next step towards `exists_localBackgroundBound` is the patch-independence of
the parameter integral, for which `Pending.RegularPatchTransition` supplies the
holomorphic change of parameters `τ` between two regular patches of `V` together
with the identity `P ∘ τ = Q`.

**What this does and does not buy.**  `localBackgroundBound_univ_of_backgroundMass_ne_top`
below proves the converse implication with `U = univ`, so the local input is
EQUIVALENT to the global `backgroundMass_ne_top`, not logically weaker.  The
value of the split is that the classical input is now literally the statement in
which Lelong's theorem is proved — locally finite volume near a single point,
via a branched projection with a uniform sheet bound and Wirtinger — instead of
a global aggregate of this project's own making, and that the compactness and
measure-theoretic glue between the two is done and verified.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.SubvarietyStokesMassInterfaces

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolume
  FirstPass.RegularPatchNeighborhood

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The parameter density of a closed real `(1,1)`-form on a regular patch.
For the background Kähler form this is the Wirtinger density of the branch:
`patchDensity` of a zero-potential presentation is this function. -/
def formPatchDensity (theta : ClosedRealOneOneForm n M)
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V)
    (w : ComplexModel V.dim) : ℝ :=
  MongeAmpere.actualTopPowerDensity
    ((theta.val.coeff (complexChartAt (n := n) P.center)
      (P.coordinateParametrization w)).compContinuousLinearMap
      (fderiv ℝ P.coordinateParametrization w))

/-- The parameter density in the sense of `RegularPatchTransition`. -/
theorem formPatchDensity_eq_actualTopPowerDensity (theta : ClosedRealOneOneForm n M)
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V)
    (w : ComplexModel V.dim) :
    formPatchDensity theta P w =
      MongeAmpere.actualTopPowerDensity
        (RegularPatchTransition.patchCoordinateForm theta.val P w) := rfl

/-- **Change of patch for the parameter density.**  On the transition domain the
density in `Q`-parameters is the Jacobian of the transition times the density in
`P`-parameters at the transported point.  This is the patch-independence the
subvariety restricted mass needs; see `Pending.RegularPatchTransition`. -/
theorem formPatchDensity_transition (theta : ClosedRealOneOneForm n M)
    {V : ClosedIrreducibleAnalyticSubvariety n M} {P Q : RegularPatch V}
    {w : ComplexModel V.dim} (hw : w ∈ RegularPatchTransition.transitionDomain P Q) :
    formPatchDensity theta Q w =
      LinearMap.det ((fderiv ℝ (RegularPatchTransition.transition P Q) w :
          ComplexModel V.dim →ₗ[ℝ] ComplexModel V.dim)) *
        formPatchDensity theta P (RegularPatchTransition.transition P Q w) :=
  RegularPatchTransition.actualTopPowerDensity_patchCoordinateForm_transition theta.val hw

/-- The total regular-piece mass of the background Kähler form on `V`.  This is
the project's encoding of `∫_{V_reg} β^{dim V}`: it involves only the compact
Kähler manifold, the subvariety, and its regular patches. -/
def backgroundMass (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) : ℝ≥0∞ :=
  ⨆ F : RegularPieceFamily V (∅ : Set M),
    ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w)

/-- The finite sum attached to one regular-piece family by the background form. -/
def backgroundPieceMass (beta : KahlerBackground n M)
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    (F : RegularPieceFamily V (∅ : Set M)) : ℝ≥0∞ :=
  ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w)

theorem backgroundMass_eq_iSup (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) :
    backgroundMass beta V = ⨆ F : RegularPieceFamily V (∅ : Set M),
      backgroundPieceMass beta F := rfl

/-- `C` bounds the background mass of every regular-piece family whose pieces all
map into `U`.  This is the local form of Lelong's finite-volume statement. -/
def LocalBackgroundBound (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) (U : Set M) (C : ℝ≥0∞) : Prop :=
  ∀ F : RegularPieceFamily V (∅ : Set M),
    (∀ i, (F.patch i).toManifold '' F.piece i ⊆ U) → backgroundPieceMass beta F ≤ C

/-- A measurable parameter piece inside the parameter domain meets the preimage
of an open subset of `M` in a measurable set: `RegularPatch.toManifold` is
continuous on the parameter domain, which is open. -/
theorem measurableSet_inter_toManifold_preimage
    {V : ClosedIrreducibleAnalyticSubvariety n M} (P : RegularPatch V)
    {s : Set (ComplexModel V.dim)} (hs : MeasurableSet s)
    (hsub : s ⊆ P.parameterDomain) {U : Set M} (hU : IsOpen U) :
    MeasurableSet (s ∩ P.toManifold ⁻¹' U) := by
  have hopen : IsOpen (P.parameterDomain ∩ P.toManifold ⁻¹' U) :=
    (RegularPatch.continuousOn_toManifold P).isOpen_inter_preimage
      (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P) hU
  have hrw : s ∩ P.toManifold ⁻¹' U = s ∩ (P.parameterDomain ∩ P.toManifold ⁻¹' U) := by
    ext w
    exact ⟨fun hw => ⟨hw.1, hsub hw.1, hw.2⟩, fun hw => ⟨hw.1, hw.2.2⟩⟩
  rw [hrw]
  exact hs.inter hopen.measurableSet

/-- Restricting every piece of a regular-piece family to the preimage of an open
set `U` gives a regular-piece family with the same patches, all of whose images
lie in `U`. -/
def restrictOpenFamily {V : ClosedIrreducibleAnalyticSubvariety n M}
    (F : RegularPieceFamily V (∅ : Set M)) {U : Set M} (hU : IsOpen U) :
    RegularPieceFamily V (∅ : Set M) where
  size := F.size
  patch := F.patch
  piece := fun i => F.piece i ∩ (F.patch i).toManifold ⁻¹' U
  measurableSet_piece := fun i =>
    measurableSet_inter_toManifold_preimage (F.patch i) (F.measurableSet_piece i)
      (F.piece_subset i) hU
  piece_subset := fun i => inter_subset_left.trans (F.piece_subset i)
  image_subset_regularLocus := fun i =>
    (Set.image_mono inter_subset_left).trans (F.image_subset_regularLocus i)
  image_disjoint_avoid := fun i => by simp
  pairwise_disjoint_image := fun _ _ hij =>
    (F.pairwise_disjoint_image hij).mono (Set.image_mono inter_subset_left)
      (Set.image_mono inter_subset_left)

@[simp] theorem restrictOpenFamily_piece
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    (F : RegularPieceFamily V (∅ : Set M)) {U : Set M} (hU : IsOpen U) (i : Fin F.size) :
    (restrictOpenFamily F hU).piece i = F.piece i ∩ (F.patch i).toManifold ⁻¹' U := rfl

theorem restrictOpenFamily_image_subset
    {V : ClosedIrreducibleAnalyticSubvariety n M}
    (F : RegularPieceFamily V (∅ : Set M)) {U : Set M} (hU : IsOpen U)
    (i : Fin (restrictOpenFamily F hU).size) :
    ((restrictOpenFamily F hU).patch i).toManifold '' (restrictOpenFamily F hU).piece i ⊆ U := by
  rintro _ ⟨w, hw, rfl⟩
  exact hw.2

/-- The regular patch supplied by a point of the regular locus: `RegularAtDim`
is exactly the data of a `RegularPatch` centred there. -/
def patchOfMemRegularLocus {V : ClosedIrreducibleAnalyticSubvariety n M} {x : M}
    (hx : x ∈ regularLocus (n := n) V.carrier V.dim) : RegularPatch V where
  center := x
  center_mem := hx.2.1
  flattening := hx.2.2.choose
  source_subset := hx.2.2.choose_spec.1
  center_to_zero := hx.2.2.choose_spec.2.1
  flattens := hx.2.2.choose_spec.2.2

@[simp] theorem patchOfMemRegularLocus_center
    {V : ClosedIrreducibleAnalyticSubvariety n M} {x : M}
    (hx : x ∈ regularLocus (n := n) V.carrier V.dim) :
    (patchOfMemRegularLocus hx).center = x := rfl

/-- **The local finite-volume bound at a REGULAR point, proved.**  Near a regular
point of `V` a single patch parametrizes all of `V`, so the change-of-patch
theorem transports every piece of every family into one parameter ball of that
patch, where the pieces stay disjoint and the density is continuous.

This is the half of Lelong's local statement that needs no branched covering:
`Pending.RegularPatchTransition` supplies the transition and its Jacobian, and
the bound is the integral of the density over a compact parameter ball. -/
theorem exists_localBackgroundBound_of_mem_regularLocus
    (beta : KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    {x : M} (hx : x ∈ regularLocus (n := n) V.carrier V.dim) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ LocalBackgroundBound beta V U C := by
  classical
  set P : RegularPatch V := patchOfMemRegularLocus hx with hP
  obtain ⟨r, hr0, hrball⟩ :
      ∃ r > (0 : ℝ), Metric.closedBall (0 : ComplexModel V.dim) r ⊆ P.parameterDomain := by
    obtain ⟨ρ, hρ0, hρ⟩ := Metric.isOpen_iff.mp
      (AdmissibleCurrentFormPositivity.RegularPatchDerivative.isOpen_parameterDomain P) 0
      (RegularPatch.zero_mem_parameterDomain P)
    exact ⟨ρ / 2, by positivity,
      (Metric.closedBall_subset_ball (by linarith)).trans hρ⟩
  have hΩsub : Metric.ball (0 : ComplexModel V.dim) r ⊆ P.parameterDomain :=
    Metric.ball_subset_closedBall.trans hrball
  obtain ⟨U, hUo, himg, hVU⟩ :=
    PatchParameterNull.exists_isOpen_carrier_inter_subset_image P Metric.isOpen_ball hΩsub
  refine ⟨U, hUo, ?_, ∫⁻ w in Metric.closedBall (0 : ComplexModel V.dim) r,
    ENNReal.ofReal (formPatchDensity beta.form P w), ?_, ?_⟩
  · have h0 : P.toManifold 0 ∈ P.toManifold '' Metric.ball (0 : ComplexModel V.dim) r :=
      ⟨0, Metric.mem_ball_self hr0, rfl⟩
    have hU := himg h0
    rwa [RegularPatch.toManifold_zero] at hU
  · exact (RegularPatchTransition.lintegral_closedBall_actualTopPowerDensity_lt_top
      beta.form.val P hrball).ne
  intro F hFU
  set tau : ∀ i : Fin F.size, ComplexModel V.dim → ComplexModel V.dim :=
    fun i => RegularPatchTransition.transition P (F.patch i) with htau
  have main : ∀ (i : Fin F.size), ∀ w ∈ F.piece i,
      w ∈ RegularPatchTransition.transitionDomain P (F.patch i) ∧
        tau i w ∈ Metric.ball (0 : ComplexModel V.dim) r := by
    intro i w hw
    have hcar : (F.patch i).toManifold w ∈ V.carrier :=
      FirstPass.regularLocus_subset _ _ (F.image_subset_regularLocus i ⟨w, hw, rfl⟩)
    have hU : (F.patch i).toManifold w ∈ U := hFU i ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hveq⟩ := hVU ⟨hcar, hU⟩
    obtain ⟨hmem, heq⟩ :=
      RegularPatchTransition.mem_transitionDomain_and_transition_eq
        (F.piece_subset i hw) (hΩsub hv) hveq.symm
    refine ⟨hmem, ?_⟩
    simp only [htau]
    rw [heq]
    exact hv
  have hsub : ∀ i : Fin F.size,
      F.piece i ⊆ RegularPatchTransition.transitionDomain P (F.patch i) :=
    fun i w hw => (main i w hw).1
  have hmeas : ∀ i : Fin F.size, MeasurableSet (tau i '' F.piece i) := by
    intro i
    refine (F.measurableSet_piece i).image_of_continuousOn_injOn ?_ ?_
    · exact fun w hw =>
        (RegularPatchTransition.differentiableAt_transition
          (hsub i hw)).continuousAt.continuousWithinAt
    · exact (RegularPatchTransition.injOn_transition P (F.patch i)).mono (hsub i)
  have hdisj : Pairwise (Function.onFun Disjoint fun i : Fin F.size => tau i '' F.piece i) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    rintro v ⟨w, hw, rfl⟩ ⟨w', hw', hvw'⟩
    have h1 : P.toManifold (tau i w) = (F.patch i).toManifold w :=
      RegularPatchTransition.toManifold_transition (hsub i hw)
    have h2 : P.toManifold (tau j w') = (F.patch j).toManifold w' :=
      RegularPatchTransition.toManifold_transition (hsub j hw')
    rw [hvw'] at h2
    refine Set.disjoint_left.mp (F.pairwise_disjoint_image hij) ⟨w, hw, h1.symm⟩ ?_
    exact ⟨w', hw', h2.symm⟩
  have hterm : ∀ i : Fin F.size,
      (∫⁻ w in F.piece i, ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w)) =
        ∫⁻ v in tau i '' F.piece i, ENNReal.ofReal (formPatchDensity beta.form P v) :=
    fun i => (RegularPatchTransition.lintegral_actualTopPowerDensity_transition
      beta.form.val (F.measurableSet_piece i) (hsub i)).symm
  calc backgroundPieceMass beta F
      = ∑ i, ∫⁻ v in tau i '' F.piece i,
          ENNReal.ofReal (formPatchDensity beta.form P v) :=
        Finset.sum_congr rfl fun i _ => hterm i
    _ = ∫⁻ v in ⋃ i, tau i '' F.piece i,
          ENNReal.ofReal (formPatchDensity beta.form P v) := by
        rw [lintegral_iUnion hmeas hdisj, tsum_fintype]
    _ ≤ ∫⁻ v in Metric.closedBall (0 : ComplexModel V.dim) r,
          ENNReal.ofReal (formPatchDensity beta.form P v) := by
        refine lintegral_mono_set ?_
        refine Set.iUnion_subset fun i => ?_
        rintro v ⟨w, hw, rfl⟩
        exact Metric.ball_subset_closedBall (main i w hw).2

set_option linter.unusedVariables false in
/-- **NAMED CLASSICAL INPUT (Lelong, local form, SINGULAR points only).**  Near
every point of `V` that is NOT a regular point of the certified dimension there
is a neighbourhood on which the background regular-piece mass of `V` is bounded.

This is what is left of Lelong's local finite-volume theorem after
`exists_localBackgroundBound_of_mem_regularLocus`: at a singular point no single
patch parametrizes `V`, and the bound needs the genuine analytic input — a basis
of decomposable `(k,k)`-forms, one ramified projection of `V` onto a polydisc
per basis form with its own uniform sheet number, and the Wirtinger comparison
(Demailly, *Complex analytic and differential geometry*, III.2.6; blueprint
`ana:background-mass-local-singular`).  See also
`docs/stokes_formalization_audit_20260920.md`.

It is no longer a bare `sorry`: the Kähler form has been removed from it.  The
coefficient of `β` in the preferred chart at `x` is continuous on the chart
target, hence bounded on a closed coordinate ball inside it; on the
corresponding neighbourhood of `x` the parameter density of `β` along ANY
regular patch is at most that bound to the power `dim V` times the FLAT
parameter density of that one chart (`Pending.FlatPatchDensityComparison`).
What is left is the flat local volume bound itself, the named classical input
`Pending.LocalFlatVolumeBound.exists_localFlatVolumeBound`.

The singularity hypothesis `hxs` is not used by this proof, which works at every
point of `V`; the statement is kept unchanged, and the hypothesis with it. -/
theorem exists_localBackgroundBound_of_notMem_regularLocus
    (beta : KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    {x : M} (hx : x ∈ V.carrier)
    (hxs : x ∉ regularLocus (n := n) V.carrier V.dim) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ LocalBackgroundBound beta V U C := by
  classical
  set e := complexChartAt (n := n) x with he
  set z0 := e.val x with hz0
  have hz0t : z0 ∈ e.val.target := e.val.map_source (mem_complexChartAt_source x)
  have htargetopen : IsOpen (e.val.target : Set (ComplexModel n)) := e.val.open_target
  obtain ⟨r, hr0, hr⟩ := Metric.isOpen_iff.1 htargetopen z0 hz0t
  -- a uniform bound for the coefficient of `β` on a closed coordinate ball
  have hballsub : Metric.closedBall z0 (r / 2) ⊆ e.val.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hr
  have hcont : ContinuousOn (fun z => ‖beta.form.val.coeff e z‖)
      (Metric.closedBall z0 (r / 2)) :=
    (((beta.form.val.smooth e).continuousOn).mono hballsub).norm
  obtain ⟨zm, _, hmax⟩ := (isCompact_closedBall z0 (r / 2)).exists_isMaxOn
    ⟨z0, Metric.mem_closedBall_self (by linarith)⟩ hcont
  set C0 := ‖beta.form.val.coeff e zm‖ with hC0
  have hC0nonneg : 0 ≤ C0 := norm_nonneg _
  -- the neighbourhood on which that bound applies
  set U1 := e.val.source ∩ e.val ⁻¹' Metric.ball z0 (r / 2) with hU1
  have hU1open : IsOpen U1 :=
    e.val.continuousOn.isOpen_inter_preimage e.val.open_source Metric.isOpen_ball
  have hz0ball : z0 ∈ Metric.ball z0 (r / 2) :=
    Metric.mem_ball_self (by linarith : (0:ℝ) < r / 2)
  have hxU1 : x ∈ U1 := ⟨mem_complexChartAt_source x, hz0ball⟩
  -- the flat local volume bound
  obtain ⟨U2, hU2open, hxU2, _hU2sub, N, hNtop, hN⟩ :=
    LocalFlatVolumeBound.exists_localFlatVolumeBound V hx
  refine ⟨U1 ∩ U2, hU1open.inter hU2open, ⟨hxU1, hxU2⟩,
    ENNReal.ofReal (C0 ^ V.dim) * N, ?_, ?_⟩
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNtop
  intro F hF
  have hdens : ∀ (i : Fin F.size) {w : ComplexModel V.dim}, w ∈ F.piece i →
      ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w) ≤
        ENNReal.ofReal (C0 ^ V.dim) *
          ENNReal.ofReal
            (FlatPatchDensityComparison.flatPatchDensity e (F.patch i) w) := by
    intro i w hw
    have hmem : (F.patch i).toManifold w ∈ U1 ∩ U2 := hF i ⟨w, hw, rfl⟩
    have hchart : w ∈ FlatPatchDensityComparison.chartDomain e (F.patch i) :=
      ⟨F.piece_subset i hw, hmem.1.1⟩
    have hzball : e.val ((F.patch i).toManifold w) ∈ Metric.closedBall z0 (r / 2) :=
      Metric.ball_subset_closedBall hmem.1.2
    have hnorm : ‖beta.form.val.coeff e (e.val ((F.patch i).toManifold w))‖ ≤ C0 :=
      hmax hzball
    have hle : ∀ z : ComplexModel n,
        beta.form.val.coeff e (e.val ((F.patch i).toManifold w)) ![z, Complex.I • z] ≤
          C0 * ‖z‖ ^ 2 := by
      intro z
      refine (TopPowerDensityUpperBound.apply_I_smul_self_le_norm_mul _ z).trans ?_
      exact mul_le_mul_of_nonneg_right hnorm (by positivity)
    have hcomp := FlatPatchDensityComparison.actualTopPowerDensity_patchCoordinateForm_le
      beta.form.val beta.form.property.2 beta.isSemipositive hchart hle
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hcomp
  calc backgroundPieceMass beta F
      ≤ ∑ i, ∫⁻ w in F.piece i, ENNReal.ofReal (C0 ^ V.dim) *
          ENNReal.ofReal
            (FlatPatchDensityComparison.flatPatchDensity e (F.patch i) w) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem (F.measurableSet_piece i)] with w hw
        exact hdens i hw
    _ = ENNReal.ofReal (C0 ^ V.dim) * ∑ i, ∫⁻ w in F.piece i,
          ENNReal.ofReal
            (FlatPatchDensityComparison.flatPatchDensity e (F.patch i) w) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ =>
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C0 ^ V.dim) * N :=
        mul_le_mul' le_rfl (hN F fun i => (hF i).trans Set.inter_subset_right)

/-- The local finite-volume bound at every point of `V`: the regular points are
discharged by `exists_localBackgroundBound_of_mem_regularLocus`, the singular
ones are the remaining classical input. -/
theorem exists_localBackgroundBound (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) {x : M} (hx : x ∈ V.carrier) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ LocalBackgroundBound beta V U C := by
  by_cases hxr : x ∈ regularLocus (n := n) V.carrier V.dim
  · exact exists_localBackgroundBound_of_mem_regularLocus beta V hxr
  · exact exists_localBackgroundBound_of_notMem_regularLocus beta V hx hxr

/-- **The global-to-local reduction for Lelong finiteness (proved).**  If every
point of `V` has a neighbourhood carrying a finite background bound, then
`backgroundMass β V` is finite.

The carrier of `V` is closed in a compact manifold, hence compact, so finitely
many of the neighbourhoods cover it.  Every piece of a regular-piece family maps
into `V_reg ⊆ V`, hence is covered by the corresponding finitely many preimages;
subadditivity of the Lebesgue integral over that finite cover, and exchanging
the two finite sums, bound the family's mass by the sum of the local constants,
uniformly in the family. -/
theorem backgroundMass_ne_top_of_localBounds [CompactSpace M]
    (beta : KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M)
    (h : ∀ x ∈ V.carrier, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ LocalBackgroundBound beta V U C) :
    backgroundMass beta V ≠ ⊤ := by
  classical
  choose! U hUopen hUmem C hCtop hCbound using h
  have hcpt : IsCompact V.carrier := V.isClosed_carrier.isCompact
  obtain ⟨t, htsub, htfin, htcover⟩ :=
    hcpt.elim_finite_subcover_image (fun x hx => hUopen x hx)
      (fun x hx => Set.mem_biUnion hx (hUmem x hx))
  have hmem : ∀ x : ↥htfin.toFinset, (x : M) ∈ V.carrier :=
    fun x => htsub (htfin.mem_toFinset.mp x.2)
  refine ne_top_of_le_ne_top (b := ∑ x : ↥htfin.toFinset, C (x : M)) ?_ ?_
  · exact (ENNReal.sum_lt_top.2 fun x _ => lt_top_iff_ne_top.2 (hCtop _ (hmem x))).ne
  refine iSup_le fun F => ?_
  have hpiece_carrier : ∀ (i : Fin F.size) {w : ComplexModel V.dim}, w ∈ F.piece i →
      (F.patch i).toManifold w ∈ V.carrier := by
    intro i w hw
    exact FirstPass.regularLocus_subset _ _
      (F.image_subset_regularLocus i ⟨w, hw, rfl⟩)
  have hcover_piece : ∀ i : Fin F.size, F.piece i ⊆
      ⋃ x : ↥htfin.toFinset, F.piece i ∩ (F.patch i).toManifold ⁻¹' U (x : M) := by
    intro i w hw
    obtain ⟨x, hxt, hxU⟩ := Set.mem_iUnion₂.mp (htcover (hpiece_carrier i hw))
    exact Set.mem_iUnion.2 ⟨⟨x, htfin.mem_toFinset.mpr hxt⟩, hw, hxU⟩
  have step1 : ∀ i : Fin F.size,
      (∫⁻ w in F.piece i, ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w)) ≤
        ∑ x : ↥htfin.toFinset,
          ∫⁻ w in F.piece i ∩ (F.patch i).toManifold ⁻¹' U (x : M),
            ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w) := by
    intro i
    refine (lintegral_mono_set (hcover_piece i)).trans ?_
    refine (lintegral_iUnion_le _ _).trans ?_
    exact le_of_eq (tsum_fintype _)
  have step3 : ∀ x : ↥htfin.toFinset,
      (∑ i : Fin F.size, ∫⁻ w in F.piece i ∩ (F.patch i).toManifold ⁻¹' U (x : M),
        ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w)) ≤ C (x : M) := by
    intro x
    exact hCbound _ (hmem x) (restrictOpenFamily F (hUopen _ (hmem x)))
      (restrictOpenFamily_image_subset F (hUopen _ (hmem x)))
  calc (∑ i : Fin F.size, ∫⁻ w in F.piece i,
          ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w))
      ≤ ∑ i : Fin F.size, ∑ x : ↥htfin.toFinset,
          ∫⁻ w in F.piece i ∩ (F.patch i).toManifold ⁻¹' U (x : M),
            ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w) :=
        Finset.sum_le_sum fun i _ => step1 i
    _ = ∑ x : ↥htfin.toFinset, ∑ i : Fin F.size,
          ∫⁻ w in F.piece i ∩ (F.patch i).toManifold ⁻¹' U (x : M),
            ENNReal.ofReal (formPatchDensity beta.form (F.patch i) w) := Finset.sum_comm
    _ ≤ ∑ x : ↥htfin.toFinset, C (x : M) := Finset.sum_le_sum fun x _ => step3 x

/-- Conversely, global finiteness gives the local bound with `U = univ`: the
background mass is by definition the supremum of the family masses.

This records the exact strength of the local statements: taken at every point
of `V`, the local bound is EQUIVALENT to `backgroundMass_ne_top`, not weaker.
So the value of the split is not a weaker axiom but (i) the glue — the
compactness argument and the measurable subdivision of
`backgroundMass_ne_top_of_localBounds` — (ii) the fact that the remaining
obligation is literally the statement Lelong's theorem is proved in, locally
finite volume near one point, and (iii) that the obligation now covers only the
SINGULAR points, the regular ones being discharged by
`exists_localBackgroundBound_of_mem_regularLocus`. -/
theorem localBackgroundBound_univ_of_backgroundMass_ne_top
    (beta : KahlerBackground n M) (V : ClosedIrreducibleAnalyticSubvariety n M) :
    LocalBackgroundBound beta V Set.univ (backgroundMass beta V) :=
  fun F _ => le_iSup (fun F : RegularPieceFamily V (∅ : Set M) =>
    backgroundPieceMass beta F) F

/-- Lelong finiteness of the background mass, assembled from the local input. -/
theorem backgroundMass_ne_top' [CompactSpace M] (beta : KahlerBackground n M)
    (V : ClosedIrreducibleAnalyticSubvariety n M) :
    backgroundMass beta V ≠ ⊤ :=
  backgroundMass_ne_top_of_localBounds beta V fun _ hx =>
    exists_localBackgroundBound beta V hx

end

end SGPT.Foundations.Analysis.Pending.SubvarietyStokesMassInterfaces
