import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicChordBound
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicAffineCovariance
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicOrderedEndpoint
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicRooftopEndpoint
import SGPT.Foundations.Analysis.Pending.RelativeFullMass
import SGPT.Foundations.Analysis.Pending.RelativeFullMassEnergyRooftopClosure
import SGPT.Foundations.Analysis.Pending.RelativeFullMassEnergyUpwardClosure
import SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsThetaPsh

set_option autoImplicit false

/-!
# Relative classes along finite geodesics

This file records the analytic content of Xia, Proposition 4.2.1, for the
actual Perron envelope constructed in `FirstPass.FiniteGeodesics`.  The ambient
space is a connected, nonempty, positive-dimensional compact Kähler manifold,
and `theta` is required to be big relative to the supplied Kähler background.
The reference is an actual positive-mass model potential.

Two direct first-pass holes in this file separate Perron strip stability and
preservation of the finite-energy subclass. General left-endpoint recovery is
now proved from the shifted-rooftop exhaustion interface isolated in
`Pending.RelativeFullMass`; the order, finite-translation, chord, measure and
two-parameter limit steps are kernel-checked in `FirstPass`. Time reversal
proves right-endpoint recovery from the left, while affine covariance and
ordered endpoint recovery handle bounded-singularity endpoints. The endpoint
chord and a constant Perron competitor preserve their bounded singularity
type. These conclusions are consequences of the Perron construction; they are
not fields stored in a geodesic structure.

Sources: `xia-sgpt:page-0154`, `xia-sgpt:page-0155`,
`xia-sgpt:page-0156`.
-/

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

open FirstPass
open FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M] [Nonempty M]


omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  [Nonempty M] in
/-- A common theta-PSH lower barrier supplies the constant Perron competitor.
This is the direct nonemptiness mechanism available before the unresolved
strip-envelope regularization: it does not use any endpoint recovery or
moving-measure estimate. -/
theorem constantCurve_mem_finiteGeodesicCompetitors_of_common_lower
    (theta : SmoothRealForm n M 2) (u₀ u₁ w : M → EReal)
    (hw : IsThetaPshPotential theta w) (hw₀ : w ≤ u₀) (hw₁ : w ≤ u₁) :
    (fun _ : ℝ => w) ∈ finiteGeodesicCompetitors theta u₀ u₁ := by
  apply finiteGeodesicCompetitors_mono hw₀ hw₁
  exact (isSubgeodesicFrom_const hw).mem_finiteGeodesicCompetitors

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  [Nonempty M] in
/-- Any common theta-PSH lower barrier makes the Perron competitor family
nonempty.  This separates the feasibility input from the still-open passage
from the stripwise family supremum to the spatially regularized geodesic. -/
theorem finiteGeodesicCompetitors_nonempty_of_common_lower
    (theta : SmoothRealForm n M 2) (u₀ u₁ w : M → EReal)
    (hw : IsThetaPshPotential theta w) (hw₀ : w ≤ u₀) (hw₁ : w ≤ u₁) :
    (finiteGeodesicCompetitors theta u₀ u₁).Nonempty := by
  exact ⟨fun _ : ℝ => w,
    constantCurve_mem_finiteGeodesicCompetitors_of_common_lower
      theta u₀ u₁ w hw hw₀ hw₁⟩

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  [Nonempty M] in
/-- The raw Perron slice supremum retains every common theta-PSH lower
barrier.  This is the pre-regularization lower estimate needed by a future
joint strip-envelope comparison. -/
theorem common_lower_le_finiteGeodesicSliceSupremum
    (theta : SmoothRealForm n M 2) (u₀ u₁ w : M → EReal)
    (hw : IsThetaPshPotential theta w) (hw₀ : w ≤ u₀) (hw₁ : w ≤ u₁)
    (t : ℝ) :
    w ≤ finiteGeodesicSliceSupremum theta u₀ u₁ t := by
  exact competitor_slice_le_finiteGeodesicSliceSupremum
    (constantCurve_mem_finiteGeodesicCompetitors_of_common_lower
      theta u₀ u₁ w hw hw₀ hw₁) t

/-- **Feasibility of the Perron family for relative full-mass endpoints.**
Relative full mass produces a common theta-PSH lower barrier
(`exists_common_thetaPsh_lower_of_relativeFullMass`), and a constant curve at
that barrier is a genuine Perron competitor.  This is one of the two inputs of
`finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass`; the other is the
strip/slice regularization interchange, proved in
`Pending.FiniteGeodesicsJointUsc`. -/
theorem finiteGeodesicCompetitors_nonempty_of_relativeFullMass
    (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    (finiteGeodesicCompetitors theta.val u₀ u₁).Nonempty := by
  obtain ⟨w, hw, hw₀, hw₁⟩ :=
    exists_common_thetaPsh_lower_of_relativeFullMass omega theta phi u₀ u₁ hphi
      hu₀ hu₁ 0
  refine finiteGeodesicCompetitors_nonempty_of_common_lower theta.val u₀ u₁ w
    hw hw₀ (fun x => ?_)
  simpa using hw₁ x

/-- The Perron slice supremum of relative full-mass endpoints is bounded below
by a genuine theta-PSH potential at every time.  With
`finiteGeodesic_uniformlyBoundedAbove` this brackets the raw slice supremum
from both sides; only the regularization step is still missing. -/
theorem exists_thetaPsh_le_finiteGeodesicSliceSupremum_of_relativeFullMass
    (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    ∃ w : M → EReal, IsThetaPshPotential theta.val w ∧
      ∀ t : ℝ, w ≤ finiteGeodesicSliceSupremum theta.val u₀ u₁ t := by
  obtain ⟨w, hw, hw₀, hw₁⟩ :=
    exists_common_thetaPsh_lower_of_relativeFullMass omega theta phi u₀ u₁ hphi
      hu₀ hu₁ 0
  refine ⟨w, hw, fun t => common_lower_le_finiteGeodesicSliceSupremum theta.val
    u₀ u₁ w hw hw₀ (fun x => ?_) t⟩
  simpa using hw₁ x


omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- **Uniform Perron-strip upper bound.**  Compactness gives finite upper
bounds for the two theta-PSH endpoints.  The endpoint chord estimate then
bounds every genuine Perron slice by the same real constant for all times in
the open strip.  This is the boundedness input for a future strip-envelope
regularization; it does not assert that that envelope is itself PSH. -/
theorem finiteGeodesic_uniformlyBoundedAbove
    (theta : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (hu₀ : IsThetaPshPotential theta u₀) (hu₁ : IsThetaPshPotential theta u₁) :
    ∃ C : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      finiteGeodesic theta u₀ u₁ t x ≤ (C : EReal) := by
  obtain ⟨C₀, hC₀⟩ := hu₀.exists_global_upper_bound
  obtain ⟨C₁, hC₁⟩ := hu₁.exists_global_upper_bound
  refine ⟨max C₀ C₁, ?_⟩
  intro t ht x
  calc
    finiteGeodesic theta u₀ u₁ t x ≤ eRealChord (u₀ x) (u₁ x) t :=
      finiteGeodesic_le_eRealChord hu₀ hu₁ ht x
    _ ≤ eRealChord ((max C₀ C₁ : ℝ) : EReal)
        ((max C₀ C₁ : ℝ) : EReal) t :=
      eRealChord_mono
        ((hC₀ x).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)))
        ((hC₁ x).trans (EReal.coe_le_coe_iff.mpr (le_max_right _ _)))
        ht.1.le ht.2.le
    _ = ((max C₀ C₁ : ℝ) : EReal) := by
      unfold eRealChord
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- The raw slice supremum has the same strip-uniform finite upper bound as
its spatial USC regularization.  This is the exact candidate-family bound
used before the unresolved interchange between strip and slice regularization. -/
theorem finiteGeodesicSliceSupremum_uniformlyBoundedAbove
    (theta : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (hu₀ : IsThetaPshPotential theta u₀) (hu₁ : IsThetaPshPotential theta u₁) :
    ∃ C : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      finiteGeodesicSliceSupremum theta u₀ u₁ t x ≤ (C : EReal) := by
  obtain ⟨C, hC⟩ := finiteGeodesic_uniformlyBoundedAbove theta u₀ u₁ hu₀ hu₁
  refine ⟨C, ?_⟩
  intro t ht x
  exact (finiteGeodesicSliceSupremum_le theta u₀ u₁ t x).trans (hC t ht x)

omit [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M] in
/-- **Local Perron-strip boundedness.**  After fixing a chart and a smooth
local potential for `theta`, the corrected complexifications of *all* Perron
competitors have a common local real upper bound on the chart strip.  Thus the
boundedness hypothesis for a regularized-supremum argument is already
available; the remaining issue in the first direct hole is to put every
competitor into this fixed local-potential PSH family and identify its
regularized supremum with the spatially regularized `finiteGeodesic`. -/
theorem finiteGeodesicCompetitors_chart_locallyUniformlyBoundedAbove
    (theta : SmoothRealForm n M 2) (u₀ u₁ : M → EReal)
    (hu₀ : IsThetaPshPotential theta u₀) (hu₁ : IsThetaPshPotential theta u₁)
    (e : ComplexChart n M) {W : Set (ComplexModel n)}
    {rho : ComplexModel n → ℝ} (hrho : IsSmoothLocalPotential theta e W rho) :
    LocallyUniformlyBoundedAbove
      ((fun curve => subgeodesicChartFunction curve e rho) ''
        finiteGeodesicCompetitors theta u₀ u₁)
      (geodesicChartDomain W) := by
  obtain ⟨C, hC⟩ := finiteGeodesic_uniformlyBoundedAbove theta u₀ u₁ hu₀ hu₁
  intro p hp
  have hrhoc : ContinuousAt rho p.1 :=
    ((hrho.2.2.1 p.1 hp.1).contDiffAt (hrho.1.mem_nhds hp.1)).continuousAt
  have hU : {q : ComplexModel n × ℂ | rho q.1 < rho p.1 + 1} ∈ 𝓝 p := by
    exact (hrhoc.comp continuous_fst.continuousAt)
      (isOpen_Iio.mem_nhds (lt_add_one (rho p.1)))
  refine ⟨{q : ComplexModel n × ℂ | rho q.1 < rho p.1 + 1},
    mem_nhdsWithin_of_mem_nhds hU, C + rho p.1 + 1, ?_⟩
  rintro f ⟨curve, hcurve, rfl⟩ q ⟨hqU, hq⟩
  change curve q.2.re (e.val.symm q.1) + (rho q.1 : EReal) ≤ _
  calc
    curve q.2.re (e.val.symm q.1) + (rho q.1 : EReal) ≤
        (C : EReal) + (rho q.1 : EReal) :=
      add_le_add
        ((competitor_slice_le_finiteGeodesic hcurve q.2.re
          (e.val.symm q.1)).trans (hC q.2.re hq.2 (e.val.symm q.1))) le_rfl
    _ = ((C + rho q.1 : ℝ) : EReal) := by rw [EReal.coe_add]
    _ ≤ ((C + (rho p.1 + 1) : ℝ) : EReal) :=
      EReal.coe_le_coe_iff.mpr (by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hqU.le C)
    _ = ((C + rho p.1 + 1 : ℝ) : EReal) := by
      rw [add_assoc, EReal.coe_add]

/-- **The joint strip envelope is PSH.**  For relative full-mass endpoints the
joint strip USC regularization of the corrected Perron family is PSH on every
chart strip, from the fixed-local-potential PSH family
(`Pending.SubgeodesicChartPotential.plurisubharmonicOn_image_subgeodesicChartFunction`)
and the local uniform upper bound above.  Xia's Proposition 4.1.3
(`Pending.subgeodesicChartFunction_finiteGeodesic_eq_strip_envelope`) then
transfers it to the corrected `finiteGeodesic`, which is the strip half of
`finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass` below. -/
theorem plurisubharmonicOn_strip_envelope_of_relativeFullMass
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (e : ComplexChart n M) {W : Set (ComplexModel n)}
    {rho : ComplexModel n → ℝ} (hrho : IsSmoothLocalPotential theta.val e W rho) :
    PlurisubharmonicOn (uscRegularization (sSup
      ((fun curve => subgeodesicChartFunction curve e rho) ''
        finiteGeodesicCompetitors theta.val u₀ u₁))) (geodesicChartDomain W) :=
  SubgeodesicChartPotential.plurisubharmonicOn_uscRegularization_sSup_image e hrho
    (finiteGeodesicCompetitors_nonempty_of_relativeFullMass omega theta phi u₀ u₁
      hphi hu₀ hu₁)
    (finiteGeodesicCompetitors_chart_locallyUniformlyBoundedAbove theta.val u₀ u₁
      hu₀.plurisubharmonic hu₁.plurisubharmonic e hrho)

/-- **The Perron envelope of relative full-mass endpoints is a strip
subgeodesic on the open interval (Xia, Propositions 4.1.3 and 4.2.1).**  Both
halves are now proved.

*Interior slices.*  Every competitor slice is `theta`-PSH, the family is
bounded above by the endpoint chord and below by the common `theta`-PSH
barrier of a relative full-mass pair, so
`isThetaPshPotential_finiteGeodesic_of_bounded` applies.

*Strip plurisubharmonicity.*  On a chart strip the corrected `finiteGeodesic`
coincides with the *joint* upper-semicontinuous regularization of the corrected
competitor family
(`Pending.subgeodesicChartFunction_finiteGeodesic_eq_strip_envelope`), which is
PSH by `plurisubharmonicOn_strip_envelope_of_relativeFullMass` above.  That
identity is Xia's Proposition 4.1.3 (`xia-sgpt:page-0150`--`xia-sgpt:page-0152`);
it is obtained here without his almost-everywhere comparison, from joint upper
semicontinuity of `sup*` in space and time
(`Pending.upperSemicontinuousAt_finiteGeodesic_prod`).

`hn` and `hbig` are not used by this proof; they are kept because the statement
is a fixed interface of the lane. -/
theorem finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi) :
    IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁) := by
  have hlocal : HasSmoothLocalPotentials theta.val :=
    hu₀.plurisubharmonic.1.hasSmoothLocalPotentials
  have hne := finiteGeodesicCompetitors_nonempty_of_relativeFullMass omega theta
    phi u₀ u₁ hphi hu₀ hu₁
  obtain ⟨w, hw, hw₀, hw₁⟩ :=
    exists_common_thetaPsh_lower_of_relativeFullMass omega theta phi u₀ u₁ hphi
      hu₀ hu₁ 0
  have hw₁' : w ≤ u₁ := fun x => by simpa using hw₁ x
  obtain ⟨C, hC⟩ := finiteGeodesic_uniformlyBoundedAbove theta.val u₀ u₁
    hu₀.plurisubharmonic hu₁.plurisubharmonic
  refine ⟨fun t ht => isThetaPshPotential_finiteGeodesic_of_bounded hlocal hne ht
    (hC t ht) hw hw₀ hw₁', ?_⟩
  intro e z hz
  obtain ⟨W, rho, hzW, hrho⟩ := hlocal e z hz
  refine ⟨W, rho, hzW, hrho, ?_⟩
  intro p hp
  refine (plurisubharmonicOn_strip_envelope_of_relativeFullMass omega theta phi
    u₀ u₁ hphi hu₀ hu₁ e hrho p hp).congr ?_
  filter_upwards [(isOpen_geodesicChartDomain hrho.1).mem_nhds hp] with q hq
  exact (subgeodesicChartFunction_finiteGeodesic_eq_strip_envelope
    hu₀.plurisubharmonic hu₁.plurisubharmonic e hrho hq).symm

/-- The full-mass Perron envelope converges to its left endpoint in chart-local
`L¹`, assembled from the explicit shifted-rooftop exhaustion boundary and the
kernel-checked two-scale endpoint theorem. -/
theorem finiteGeodesic_tendsto_left_of_relativeFullMass
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (_hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    ManifoldL1LocallyTendsto (n := n) (finiteGeodesic theta.val u₀ u₁)
      (𝓝[>] (0 : ℝ)) u₀ := by
  let w : ℝ → M → EReal := fun C => rooftopEnvelope theta.val
    (fun x => min (u₀ x) (u₁ x + (C : EReal)))
  apply finiteGeodesic_tendsto_left_of_rooftop_exhaustion
      hu₀.plurisubharmonic hu₁.plurisubharmonic
      (w := w)
  · intro C _
    exact (relativeFullMass_rooftop_add_const hn omega theta phi u₀ u₁
      hphi hu₀ hu₁ C hprojection).1.plurisubharmonic
  · intro C _
    exact (relativeFullMass_rooftop_add_const hn omega theta phi u₀ u₁
      hphi hu₀ hu₁ C hprojection).2.1
  · intro C _
    exact (relativeFullMass_rooftop_add_const hn omega theta phi u₀ u₁
      hphi hu₀ hu₁ C hprojection).2.2
  · simpa only [w] using relativeFullMass_rooftop_add_const_tendsto
      hn omega theta phi u₀ u₁ hphi hu₀ hu₁ hprojection

/-- Time reversal transports left-endpoint recovery for swapped full-mass
endpoints to right-endpoint recovery for the original Perron geodesic. -/
theorem finiteGeodesic_tendsto_right_of_relativeFullMass
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    ManifoldL1LocallyTendsto (n := n) (finiteGeodesic theta.val u₀ u₁)
      (𝓝[<] (1 : ℝ)) u₁ := by
  have hleft := finiteGeodesic_tendsto_left_of_relativeFullMass
    hn omega theta hbig phi u₁ u₀ hphi hu₁ hu₀ hprojection
  have hreversed := hleft.comp tendsto_one_sub_nhdsLT_one
  apply ManifoldL1LocallyTendsto.congr (hu := hreversed)
  intro t
  rw [finiteGeodesic_timeReversal]
  congr 2
  ring

/-- **Xia, Proposition 4.2.1, full-mass case.** Relative full-mass endpoints
give the actual Perron envelope its prescribed `L¹` endpoints and genuine
strip-subgeodesic property.  The interior half is the theorem above; the two
endpoint limits are the chart-local `L¹` recovery theorems before it. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ :=
  ⟨hu₀.plurisubharmonic, hu₁.plurisubharmonic,
    finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass
      hn omega theta hbig phi u₀ u₁ hphi hu₀ hu₁,
    finiteGeodesic_tendsto_left_of_relativeFullMass
      hn omega theta hbig phi u₀ u₁ hphi hu₀ hu₁ hprojection,
    finiteGeodesic_tendsto_right_of_relativeFullMass
      hn omega theta hbig phi u₀ u₁ hphi hu₀ hu₁ hprojection⟩

omit [BorelSpace M] [ConnectedSpace M] [Nonempty M] in
/-- Normalized relative full-mass endpoints bound every interior Perron slice
above by the model potential.  This is the proved endpoint chord inequality
for each competitor followed by the least-USC-majorant property. -/
theorem finiteGeodesic_le_reference_of_relativeFullMass
    (_hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (_hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    finiteGeodesic theta.val u₀ u₁ t ≤ phi := by
  clear _hn _hbig omega
  refine (finiteGeodesic_le_eRealChord hu₀.plurisubharmonic
    hu₁.plurisubharmonic ht).trans ?_
  intro x
  refine (eRealChord_mono (hu₀.le_reference x) (hu₁.le_reference x)
    ht.1.le ht.2.le).trans_eq ?_
  induction hpx : phi x using EReal.rec with
  | bot =>
      simp only [eRealChord]
      rw [EReal.coe_mul_bot_of_pos (sub_pos.mpr ht.2),
        EReal.coe_mul_bot_of_pos ht.1, EReal.bot_add]
  | coe r =>
      simp only [eRealChord]
      norm_cast
      ring
  | top =>
      exact False.elim
            (hphi.plurisubharmonic.quasiPshPotential.1.ne_top x hpx)

omit [Nonempty M] in
/-- A common relative full-mass lower barrier, together with the genuine
interior Perron property, propagates relative full mass to an interior slice.
This isolates the order-theoretic part of the finite-geodesic argument from
the separate construction of the lower barrier and the Perron theorem. -/
theorem relativeFullMass_finiteGeodesic_of_interior_of_common_lower
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ w : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (hw : RelativeFullMass theta phi w hphi) (hw₀ : w ≤ u₀) (hw₁ : w ≤ u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFullMass theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi := by
  apply hw.of_between hn omega (hinterior.thetaPshPotential ht)
  · exact le_finiteGeodesic_of_le_endpoints hw.plurisubharmonic hw₀ hw₁ t
  · exact finiteGeodesic_le_reference_of_relativeFullMass
      hn omega theta hbig phi u₀ u₁ hphi hu₀ hu₁ t ht

/-- Every interior slice of the Perron geodesic between relative full-mass
endpoints remains in the same relative full-mass class. -/
theorem relativeFullMass_finiteGeodesic
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFullMass theta phi u₀ hphi)
    (hu₁ : RelativeFullMass theta phi u₁ hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFullMass theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi :=
  by
    rcases relativeFullMass_rooftop hn omega theta phi u₀ u₁ hphi hu₀ hu₁ hprojection
      with ⟨hw, hw₀, hw₁⟩
    exact relativeFullMass_finiteGeodesic_of_interior_of_common_lower
      hn omega theta hbig phi u₀ u₁
      (rooftopEnvelope theta.val (fun x => min (u₀ x) (u₁ x)))
      hphi hu₀ hu₁ hw hw₀ hw₁
      (finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass
        hn omega theta hbig phi u₀ u₁ hphi hu₀ hu₁) t ht

/-- Relative finite-energy endpoints give a genuine subgeodesic. This is the
full-mass part of Proposition 4.2.1 applied through the definition of
`RelativeFiniteEnergy`. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeFiniteEnergy
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFiniteEnergy theta phi u₀ hphi)
    (hu₁ : RelativeFiniteEnergy theta phi u₁ hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ :=
  finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass hn omega theta hbig
    phi u₀ u₁ hphi hu₀.fullMass hu₁.fullMass hprojection

/-- **Xia, Proposition 4.2.1, finite-energy case.**  The source does not
compare the moving diagonal measures directly.  It first puts the rooftop
minimum of the endpoints in the finite-energy class (Proposition 3.1.21), and
then applies upward closure to the Perron slice between that rooftop and the
model potential (Proposition 3.1.22).  Both inputs are used in the Kähler form
available here: the first is `RelativeFiniteEnergy.rooftop_of_kahler`
(contact-set concentration and contact comparison, run 0097), the second
`RelativeFiniteEnergy.of_between_of_kahler` (Guedj--Zeriahi fundamental
inequality, run 0095).  This proof therefore no longer uses the interfaces
`RelativeFiniteEnergy.rooftop` and `RelativeFiniteEnergy.of_between` of
`RelativeFiniteEnergyOrderClosure`. -/
theorem relativeFiniteEnergyIntegral_finite_finiteGeodesic
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFiniteEnergy theta phi u₀ hphi)
    (hu₁ : RelativeFiniteEnergy theta phi u₁ hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hslice : IsThetaPshPotential theta.val
      (finiteGeodesic theta.val u₀ u₁ t)) :
    relativeFiniteEnergyIntegral theta phi
      (finiteGeodesic theta.val u₀ u₁ t) hslice < ⊤ := by
  let w : M → EReal := rooftopEnvelope theta.val (fun x => min (u₀ x) (u₁ x))
  have hw : RelativeFiniteEnergy theta phi w hphi :=
    RelativeFiniteEnergy.rooftop_of_kahler hn omega theta phi u₀ u₁ hphi hu₀ hu₁ hprojection
  rcases relativeFullMass_rooftop hn omega theta phi u₀ u₁ hphi
    hu₀.fullMass hu₁.fullMass hprojection with ⟨hwfull, hw₀, hw₁⟩
  have hwle : w ≤ finiteGeodesic theta.val u₀ u₁ t := by
    exact le_finiteGeodesic_of_le_endpoints hwfull.plurisubharmonic hw₀ hw₁ t
  have hslicele : finiteGeodesic theta.val u₀ u₁ t ≤ phi :=
    finiteGeodesic_le_reference_of_relativeFullMass
      hn omega theta hbig phi u₀ u₁ hphi hu₀.fullMass hu₁.fullMass t ht
  exact ((relativeFiniteEnergy_iff theta phi
    (finiteGeodesic theta.val u₀ u₁ t) hphi hslice).1
      (RelativeFiniteEnergy.of_between_of_kahler hn omega hw hslice hwle hslicele)).2

omit [BorelSpace M] [ConnectedSpace M] [Nonempty M] in
/-- An explicitly supplied finite relative-energy integral upgrades a
full-mass interior Perron slice to the relative finite-energy class.  This
keeps the analytic integral estimate separate from the definition-level
closure step used by the finite-geodesic theorem. -/
theorem relativeFiniteEnergy_finiteGeodesic_of_fullMass_of_integral_finite
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi) (t : ℝ)
    (hfull : RelativeFullMass theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi)
    (hslice : IsThetaPshPotential theta.val (finiteGeodesic theta.val u₀ u₁ t))
    (hfinite : relativeFiniteEnergyIntegral theta phi
      (finiteGeodesic theta.val u₀ u₁ t) hslice < ⊤) :
    RelativeFiniteEnergy theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi := by
  exact (relativeFiniteEnergy_iff theta phi
    (finiteGeodesic theta.val u₀ u₁ t) hphi hslice).2 ⟨hfull, hfinite⟩

/-- A two-sided finite pointwise sandwich controls the canonical difference.
At a common pole, the upper sandwich forces the second value to be a pole as
well, so the canonical difference is zero; on the finite branch this is the
ordinary absolute-value estimate. -/
theorem canonicalERealAbsDiff_le_of_sandwich
    {a b : EReal} (ha_top : a ≠ ⊤) (R : NNReal)
    (hlower : a + ((-(R : ℝ) : ℝ) : EReal) ≤ b)
    (hupper : b ≤ a + ((R : ℝ) : EReal)) :
    canonicalERealAbsDiff a b ≤ R := by
  cases a with
  | bot =>
      have hb : b = ⊥ := by
        have : b ≤ ⊥ := by simpa using hupper
        exact le_bot_iff.mp this
      rw [hb]
      simp
  | top => exact False.elim (ha_top rfl)
  | coe a =>
      cases b with
      | bot =>
          exfalso
          rw [← EReal.coe_add] at hlower
          exact (not_le_of_gt (EReal.coe_ne_bot (a - (R : ℝ)) |>
            bot_lt_iff_ne_bot.mpr)) hlower
      | top =>
          exfalso
          rw [← EReal.coe_add] at hupper
          exact (not_le_of_gt (EReal.coe_ne_top (a + (R : ℝ)) |>
            lt_top_iff_ne_top.mpr)) hupper
      | coe b =>
          rw [← EReal.coe_add] at hlower hupper
          rw [canonicalERealAbsDiff_coe_coe, ← ENNReal.ofReal_coe_nnreal]
          apply ENNReal.ofReal_le_ofReal
          apply abs_le.mpr
          norm_cast at hlower hupper ⊢
          constructor <;> linarith

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]
  [Nonempty M] in
/-- If both theta-PSH endpoints lie pointwise between `phi - R` and `phi + R`,
the Perron finite-geodesic slice has canonical distance at most `R` from the
reference.  The lower bound is supplied by the constant theta-PSH Perron
competitor `phi - R`; the upper bound is the endpoint chord. -/
theorem canonicalERealAbsDiff_le_finiteGeodesic_of_endpoint_sandwich
    (theta : SmoothRealForm n M 2) (phi u₀ u₁ : M → EReal)
    (hphi : IsThetaPshPotential theta phi)
    (hu₀ : IsThetaPshPotential theta u₀) (hu₁ : IsThetaPshPotential theta u₁)
    (R : NNReal)
    (hlower₀ : ∀ x, phi x + ((-(R : ℝ) : ℝ) : EReal) ≤ u₀ x)
    (hupper₀ : ∀ x, u₀ x ≤ phi x + ((R : ℝ) : EReal))
    (hlower₁ : ∀ x, phi x + ((-(R : ℝ) : ℝ) : EReal) ≤ u₁ x)
    (hupper₁ : ∀ x, u₁ x ≤ phi x + ((R : ℝ) : EReal))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∀ x, canonicalERealAbsDiff (phi x) (finiteGeodesic theta u₀ u₁ t x) ≤ R := by
  intro x
  apply canonicalERealAbsDiff_le_of_sandwich
    (hphi.quasiPshPotential.1.ne_top x) R
  · exact le_finiteGeodesic_of_le_endpoints
      (hphi.add_const (-(R : ℝ))) hlower₀ hlower₁ t x
  · calc
      finiteGeodesic theta u₀ u₁ t x ≤ eRealChord (u₀ x) (u₁ x) t :=
        finiteGeodesic_le_eRealChord hu₀ hu₁ ht x
      _ ≤ eRealChord (phi x + ((R : ℝ) : EReal))
          (phi x + ((R : ℝ) : EReal)) t :=
        eRealChord_mono (hupper₀ x) (hupper₁ x) ht.1.le ht.2.le
      _ = phi x + ((R : ℝ) : EReal) := by
        induction hpx : phi x using EReal.rec with
        | bot =>
            simp only [eRealChord, EReal.bot_add]
            rw [EReal.coe_mul_bot_of_pos (sub_pos.mpr ht.2),
              EReal.coe_mul_bot_of_pos ht.1, EReal.bot_add]
        | coe r =>
            simp only [eRealChord, ← EReal.coe_add, ← EReal.coe_mul]
            norm_cast
            ring
        | top =>
            exact False.elim (hphi.quasiPshPotential.1.ne_top x hpx)

omit [ConnectedSpace M] [Nonempty M] in
/-- A bounded endpoint sandwich gives the requested finite slice integral
directly, without any comparison of moving non-pluripolar measures.  The
pointwise canonical-distance bound controls the integrand, while the actual
slice diagonal measure is finite on the compact Kähler manifold. -/
theorem relativeFiniteEnergyIntegral_finiteGeodesic_of_endpoint_sandwich
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : IsThetaPshPotential theta.val u₀) (hu₁ : IsThetaPshPotential theta.val u₁)
    (R : NNReal)
    (hlower₀ : ∀ x, phi x + ((-(R : ℝ) : ℝ) : EReal) ≤ u₀ x)
    (hupper₀ : ∀ x, u₀ x ≤ phi x + ((R : ℝ) : EReal))
    (hlower₁ : ∀ x, phi x + ((-(R : ℝ) : ℝ) : EReal) ≤ u₁ x)
    (hupper₁ : ∀ x, u₁ x ≤ phi x + ((R : ℝ) : EReal))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hslice : IsThetaPshPotential theta.val (finiteGeodesic theta.val u₀ u₁ t)) :
    relativeFiniteEnergyIntegral theta phi
      (finiteGeodesic theta.val u₀ u₁ t) hslice < ⊤ := by
  exact relativeFiniteEnergyIntegral_lt_top_of_canonicalERealAbsDiff_le
    omega theta phi (finiteGeodesic theta.val u₀ u₁ t) hslice R
    (canonicalERealAbsDiff_le_finiteGeodesic_of_endpoint_sandwich
      theta.val phi u₀ u₁ hphi.plurisubharmonic hu₀ hu₁ R
      hlower₀ hupper₀ hlower₁ hupper₁ t ht)

omit [ConnectedSpace M] [Nonempty M] in
/-- The bounded-sandwich finite-energy branch for an interior Perron slice.
Unlike the general moving-measure estimate, this theorem has no energy
hypothesis: the finite measure and the canonical-distance bound give the
integrability.  The actual slice theta-PSH and relative-full-mass conditions
are stated explicitly. -/
theorem relativeFiniteEnergy_finiteGeodesic_of_endpoint_sandwich
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : IsThetaPshPotential theta.val u₀) (hu₁ : IsThetaPshPotential theta.val u₁)
    (R : NNReal)
    (hlower₀ : ∀ x, phi x + ((-(R : ℝ) : ℝ) : EReal) ≤ u₀ x)
    (hupper₀ : ∀ x, u₀ x ≤ phi x + ((R : ℝ) : EReal))
    (hlower₁ : ∀ x, phi x + ((-(R : ℝ) : ℝ) : EReal) ≤ u₁ x)
    (hupper₁ : ∀ x, u₁ x ≤ phi x + ((R : ℝ) : EReal))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hslice : IsThetaPshPotential theta.val (finiteGeodesic theta.val u₀ u₁ t))
    (hfull : RelativeFullMass theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi) :
    RelativeFiniteEnergy theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi := by
  apply (relativeFiniteEnergy_iff theta phi
    (finiteGeodesic theta.val u₀ u₁ t) hphi hslice).2
  refine ⟨hfull, ?_⟩
  exact relativeFiniteEnergyIntegral_lt_top_of_canonicalERealAbsDiff_le
    omega theta phi (finiteGeodesic theta.val u₀ u₁ t) hslice R
    (canonicalERealAbsDiff_le_finiteGeodesic_of_endpoint_sandwich
      theta.val phi u₀ u₁ hphi.plurisubharmonic hu₀ hu₁ R
      hlower₀ hupper₀ hlower₁ hupper₁ t ht)

omit [ConnectedSpace M] [Nonempty M] in
/-- The bounded-singularity finite-energy branch for a Perron slice.  The two
comparisons in each `RelativeEInfinity` endpoint are combined into one
nonnegative radius, which supplies the two endpoint sandwiches required
above.  This requires the actual slice theta-PSH and full-mass inputs, but no
general moving-measure energy estimate. -/
theorem relativeFiniteEnergy_finiteGeodesic_of_relativeEInfinity_of_fullMass
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hslice : IsThetaPshPotential theta.val (finiteGeodesic theta.val u₀ u₁ t))
    (hfull : RelativeFullMass theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi) :
    RelativeFiniteEnergy theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi := by
  rcases hu₀.sameSingularityType.1 with ⟨C₀, hC₀⟩
  rcases hu₀.sameSingularityType.2 with ⟨D₀, hD₀⟩
  rcases hu₁.sameSingularityType.1 with ⟨C₁, hC₁⟩
  rcases hu₁.sameSingularityType.2 with ⟨D₁, hD₁⟩
  let R : NNReal := ⟨|C₀| + |C₁| + |D₀| + |D₁|, by positivity⟩
  have hC₀R : C₀ ≤ (R : ℝ) := by
    change C₀ ≤ |C₀| + |C₁| + |D₀| + |D₁|
    linarith [le_abs_self C₀, abs_nonneg C₁, abs_nonneg D₀, abs_nonneg D₁]
  have hC₁R : C₁ ≤ (R : ℝ) := by
    change C₁ ≤ |C₀| + |C₁| + |D₀| + |D₁|
    linarith [le_abs_self C₁, abs_nonneg C₀, abs_nonneg D₀, abs_nonneg D₁]
  have hD₀R : D₀ ≤ (R : ℝ) := by
    change D₀ ≤ |C₀| + |C₁| + |D₀| + |D₁|
    linarith [le_abs_self D₀, abs_nonneg C₀, abs_nonneg C₁, abs_nonneg D₁]
  have hD₁R : D₁ ≤ (R : ℝ) := by
    change D₁ ≤ |C₀| + |C₁| + |D₀| + |D₁|
    linarith [le_abs_self D₁, abs_nonneg C₀, abs_nonneg C₁, abs_nonneg D₀]
  apply relativeFiniteEnergy_finiteGeodesic_of_endpoint_sandwich
    omega theta phi u₀ u₁ hphi hu₀.plurisubharmonic hu₁.plurisubharmonic R
  · intro x
    apply (EReal.addLECancellable_coe (R : ℝ)).add_le_add_iff_right.mp
    calc
      (phi x + ((-(R : ℝ) : ℝ) : EReal)) + ((R : ℝ) : EReal) = phi x := by
        rw [add_assoc, ← EReal.coe_add]
        simp
      _ ≤ u₀ x + (D₀ : EReal) := hD₀ x (mem_univ x)
      _ ≤ u₀ x + ((R : ℝ) : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hD₀R)
  · intro x
    exact (hC₀ x (mem_univ x)).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hC₀R))
  · intro x
    apply (EReal.addLECancellable_coe (R : ℝ)).add_le_add_iff_right.mp
    calc
      (phi x + ((-(R : ℝ) : ℝ) : EReal)) + ((R : ℝ) : EReal) = phi x := by
        rw [add_assoc, ← EReal.coe_add]
        simp
      _ ≤ u₁ x + (D₁ : EReal) := hD₁ x (mem_univ x)
      _ ≤ u₁ x + ((R : ℝ) : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hD₁R)
  · intro x
    exact (hC₁ x (mem_univ x)).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hC₁R))
  · exact ht
  · exact hslice
  · exact hfull

/-- Every interior slice of the Perron geodesic between relative
finite-energy endpoints remains in the same relative finite-energy class. -/
theorem relativeFiniteEnergy_finiteGeodesic
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeFiniteEnergy theta phi u₀ hphi)
    (hu₁ : RelativeFiniteEnergy theta phi u₁ hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeFiniteEnergy theta phi (finiteGeodesic theta.val u₀ u₁ t) hphi :=
  by
    have hfull := relativeFullMass_finiteGeodesic hn omega theta hbig
      phi u₀ u₁ hphi hu₀.fullMass hu₁.fullMass hprojection t ht
    have hslice := hfull.plurisubharmonic
    exact relativeFiniteEnergy_finiteGeodesic_of_fullMass_of_integral_finite
      theta phi u₀ u₁ hphi t hfull hslice
      (relativeFiniteEnergyIntegral_finite_finiteGeodesic
        hn omega theta hbig phi u₀ u₁ hphi hu₀ hu₁ hprojection t ht hslice)

/-- Bounded-singularity endpoints give a genuine subgeodesic. This statement
is kept separate from the normalized `RelativeFullMass` predicate because
`RelativeEInfinity` records additive singularity type without imposing a
pointwise normalization. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ :=
  by
    rcases hu₀.sameSingularityType.1 with ⟨C₀, hC₀⟩
    rcases hu₀.sameSingularityType.2 with ⟨D₀, hD₀⟩
    rcases hu₁.sameSingularityType.1 with ⟨C₁, hC₁⟩
    rcases hu₁.sameSingularityType.2 with ⟨D₁, hD₁⟩
    let B : ℝ := -C₀
    let A : ℝ := C₀ - C₁
    let v₀ : M → EReal := fun x => u₀ x + (B : EReal)
    let v₁ : M → EReal := fun x => u₁ x + ((A + B : ℝ) : EReal)
    have hAB : A + B = -C₁ := by
      dsimp only [A, B]
      ring
    have hv₀psh : IsThetaPshPotential theta.val v₀ := by
      exact hu₀.plurisubharmonic.add_const B
    have hv₁psh : IsThetaPshPotential theta.val v₁ := by
      exact hu₁.plurisubharmonic.add_const (A + B)
    have hv₀phi : SameSingularityTypeOn v₀ phi univ := by
      exact (sameSingularityTypeOn_add_const u₀ univ B).trans
        hu₀.sameSingularityType
    have hv₁phi : SameSingularityTypeOn v₁ phi univ := by
      exact (sameSingularityTypeOn_add_const u₁ univ (A + B)).trans
        hu₁.sameSingularityType
    have hv₀le : v₀ ≤ phi := by
      intro x
      apply (EReal.addLECancellable_coe C₀).add_le_add_iff_right.mp
      calc
        v₀ x + (C₀ : EReal) = u₀ x := by
          dsimp only [v₀, B]
          rw [add_assoc, ← EReal.coe_add]
          simp
        _ ≤ phi x + (C₀ : EReal) := hC₀ x (mem_univ x)
    have hv₁le : v₁ ≤ phi := by
      intro x
      apply (EReal.addLECancellable_coe C₁).add_le_add_iff_right.mp
      calc
        v₁ x + (C₁ : EReal) = u₁ x := by
          dsimp only [v₁]
          rw [hAB, add_assoc, ← EReal.coe_add]
          simp
        _ ≤ phi x + (C₁ : EReal) := hC₁ x (mem_univ x)
    have hphiFull : RelativeFullMass theta phi phi hphi :=
      ⟨hphi.plurisubharmonic, le_rfl, rfl⟩
    have hv₀Full : RelativeFullMass theta phi v₀ hphi :=
      hphiFull.of_singularity_between hn omega hv₀psh hv₀phi.2
        hv₀phi.1 hv₀le
    have hv₁Full : RelativeFullMass theta phi v₁ hphi :=
      hphiFull.of_singularity_between hn omega hv₁psh hv₁phi.2
        hv₁phi.1 hv₁le
    have hinteriorShifted :=
      finiteGeodesic_isSubgeodesicInterior_of_relativeFullMass
        hn omega theta hbig phi v₀ v₁ hphi hv₀Full hv₁Full
    have hcov : finiteGeodesic theta.val v₀ v₁ =
        affineTranslatedCurve (finiteGeodesic theta.val u₀ u₁) A B := by
      funext t
      exact finiteGeodesic_affineCovariance theta.val u₀ u₁ A B t
    have hinterior := hinteriorShifted.affineTranslated (-A) (-B)
    have hcurve : affineTranslatedCurve
        (finiteGeodesic theta.val v₀ v₁) (-A) (-B) =
        finiteGeodesic theta.val u₀ u₁ := by
      rw [hcov, affineTranslatedCurve_inverse]
    rw [hcurve] at hinterior
    have hu₀le : u₀ ≤ fun x => u₁ x + ((D₁ + C₀ : ℝ) : EReal) := by
      intro x
      calc
        u₀ x ≤ phi x + (C₀ : EReal) := hC₀ x (mem_univ x)
        _ ≤ (u₁ x + (D₁ : EReal)) + (C₀ : EReal) :=
          add_le_add (hD₁ x (mem_univ x)) le_rfl
        _ = u₁ x + ((D₁ + C₀ : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]
    have hleftShifted := finiteGeodesic_tendsto_left_of_le
      hu₀.plurisubharmonic
      (hu₁.plurisubharmonic.add_const (D₁ + C₀)) hu₀le
    have hleftCorrected := hleftShifted.add_tendsto_const
      (c := fun t : ℝ => -((D₁ + C₀) * t)) (d := 0) (by
        have hcont : Continuous (fun t : ℝ => -((D₁ + C₀) * t)) := by
          fun_prop
        simpa using tendsto_nhdsWithin_of_tendsto_nhds
          (hcont.tendsto (0 : ℝ)))
    have hleft : ManifoldL1LocallyTendsto (n := n)
        (finiteGeodesic theta.val u₀ u₁) (𝓝[>] (0 : ℝ)) u₀ := by
      apply ManifoldL1LocallyTendsto.congr (hu := by
        simpa only [EReal.coe_zero, add_zero] using hleftCorrected)
      intro t
      funext x
      have hcovLeft : finiteGeodesic theta.val u₀
          (fun y => u₁ y + ((D₁ + C₀ : ℝ) : EReal)) t x =
          finiteGeodesic theta.val u₀ u₁ t x +
            (((D₁ + C₀) * t : ℝ) : EReal) := by
        have hu₀zero : (fun y => u₀ y + ((0 : ℝ) : EReal)) = u₀ := by
          funext y
          simp
        have hcov := congrFun
          (finiteGeodesic_affineCovariance theta.val u₀ u₁
            (D₁ + C₀) 0 t) x
        rw [hu₀zero] at hcov
        simpa only [add_zero] using hcov
      rw [hcovLeft]
      rw [add_assoc, ← EReal.coe_add]
      have hcancel : (D₁ + C₀) * t + -((D₁ + C₀) * t) = 0 := by ring
      rw [hcancel, EReal.coe_zero, add_zero]
    have hu₁le : u₁ ≤ fun x => u₀ x + ((D₀ + C₁ : ℝ) : EReal) := by
      intro x
      calc
        u₁ x ≤ phi x + (C₁ : EReal) := hC₁ x (mem_univ x)
        _ ≤ (u₀ x + (D₀ : EReal)) + (C₁ : EReal) :=
          add_le_add (hD₀ x (mem_univ x)) le_rfl
        _ = u₀ x + ((D₀ + C₁ : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add]
    have hrightShifted := finiteGeodesic_tendsto_left_of_le
      hu₁.plurisubharmonic
      (hu₀.plurisubharmonic.add_const (D₀ + C₁)) hu₁le
    have hrightCorrected := hrightShifted.add_tendsto_const
      (c := fun t : ℝ => -((D₀ + C₁) * t)) (d := 0) (by
        have hcont : Continuous (fun t : ℝ => -((D₀ + C₁) * t)) := by
          fun_prop
        simpa using tendsto_nhdsWithin_of_tendsto_nhds
          (hcont.tendsto (0 : ℝ)))
    have hswapped : ManifoldL1LocallyTendsto (n := n)
        (finiteGeodesic theta.val u₁ u₀) (𝓝[>] (0 : ℝ)) u₁ := by
      apply ManifoldL1LocallyTendsto.congr (hu := by
        simpa only [EReal.coe_zero, add_zero] using hrightCorrected)
      intro t
      funext x
      have hcovRight : finiteGeodesic theta.val u₁
          (fun y => u₀ y + ((D₀ + C₁ : ℝ) : EReal)) t x =
          finiteGeodesic theta.val u₁ u₀ t x +
            (((D₀ + C₁) * t : ℝ) : EReal) := by
        have hu₁zero : (fun y => u₁ y + ((0 : ℝ) : EReal)) = u₁ := by
          funext y
          simp
        have hcov := congrFun
          (finiteGeodesic_affineCovariance theta.val u₁ u₀
            (D₀ + C₁) 0 t) x
        rw [hu₁zero] at hcov
        simpa only [add_zero] using hcov
      rw [hcovRight]
      rw [add_assoc, ← EReal.coe_add]
      have hcancel : (D₀ + C₁) * t + -((D₀ + C₁) * t) = 0 := by ring
      rw [hcancel, EReal.coe_zero, add_zero]
    have hrightReversed := hswapped.comp tendsto_one_sub_nhdsLT_one
    have hright : ManifoldL1LocallyTendsto (n := n)
        (finiteGeodesic theta.val u₀ u₁) (𝓝[<] (1 : ℝ)) u₁ := by
      apply ManifoldL1LocallyTendsto.congr (hu := hrightReversed)
      intro t
      rw [finiteGeodesic_timeReversal]
      congr 2
      ring
    exact ⟨hu₀.plurisubharmonic, hu₁.plurisubharmonic, hinterior,
      hleft, hright⟩

/-- Every interior slice of the Perron geodesic between potentials of bounded
additive singularity type has the same bounded singularity type. -/
theorem relativeEInfinity_finiteGeodesic
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (hbig : BigWithRespectToViaPotentials omega theta)
    (phi u₀ u₁ : M → EReal) (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeEInfinity theta phi (finiteGeodesic theta.val u₀ u₁ t) :=
  by
    rcases hu₀.sameSingularityType.1 with ⟨C₀, hC₀⟩
    rcases hu₀.sameSingularityType.2 with ⟨D₀, hD₀⟩
    rcases hu₁.sameSingularityType.1 with ⟨C₁, hC₁⟩
    rcases hu₁.sameSingularityType.2 with ⟨D₁, hD₁⟩
    have hslicePsh :=
      (finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity
        hn omega theta hbig phi u₀ u₁ hphi hu₀ hu₁).interior.thetaPshPotential ht
    refine ⟨hslicePsh, ?_⟩
    constructor
    · let C : ℝ := max C₀ C₁
      refine ⟨C, fun x _ => ?_⟩
      have hu₀upper : u₀ x ≤ phi x + (C : EReal) := by
        exact (hC₀ x (mem_univ x)).trans
          (add_le_add le_rfl (by exact_mod_cast le_max_left C₀ C₁))
      have hu₁upper : u₁ x ≤ phi x + (C : EReal) := by
        exact (hC₁ x (mem_univ x)).trans
          (add_le_add le_rfl (by exact_mod_cast le_max_right C₀ C₁))
      refine (finiteGeodesic_le_eRealChord hu₀.plurisubharmonic
        hu₁.plurisubharmonic ht x).trans
        ((eRealChord_mono hu₀upper hu₁upper ht.1.le ht.2.le).trans_eq ?_)
      induction hpx : phi x using EReal.rec with
      | bot =>
          simp only [eRealChord, EReal.bot_add]
          rw [EReal.coe_mul_bot_of_pos (sub_pos.mpr ht.2),
            EReal.coe_mul_bot_of_pos ht.1, EReal.bot_add]
      | coe r =>
          simp only [eRealChord, ← EReal.coe_add, ← EReal.coe_mul]
          norm_cast
          ring
      | top =>
          exact False.elim
            (hphi.plurisubharmonic.quasiPshPotential.1.ne_top x hpx)
    · let D : ℝ := max D₀ D₁
      let w : M → EReal := fun x => phi x + ((-D : ℝ) : EReal)
      have hwpsh : IsThetaPshPotential theta.val w :=
        hphi.plurisubharmonic.add_const (-D)
      have hwu₀ : w ≤ u₀ := by
        intro x
        apply (EReal.addLECancellable_coe D).add_le_add_iff_right.mp
        calc
          w x + (D : EReal) = phi x := by
            dsimp only [w]
            rw [add_assoc, ← EReal.coe_add]
            simp
          _ ≤ u₀ x + (D₀ : EReal) := hD₀ x (mem_univ x)
          _ ≤ u₀ x + (D : EReal) :=
            add_le_add le_rfl (by exact_mod_cast le_max_left D₀ D₁)
      have hwu₁ : w ≤ u₁ := by
        intro x
        apply (EReal.addLECancellable_coe D).add_le_add_iff_right.mp
        calc
          w x + (D : EReal) = phi x := by
            dsimp only [w]
            rw [add_assoc, ← EReal.coe_add]
            simp
          _ ≤ u₁ x + (D₁ : EReal) := hD₁ x (mem_univ x)
          _ ≤ u₁ x + (D : EReal) :=
            add_le_add le_rfl (by exact_mod_cast le_max_right D₀ D₁)
      have hlower := le_finiteGeodesic_of_le_endpoints hwpsh hwu₀ hwu₁ t
      refine ⟨D, fun x _ => ?_⟩
      have hadd :=
        (EReal.addLECancellable_coe D).add_le_add_iff_right.mpr (hlower x)
      calc
        phi x = w x + (D : EReal) := by
          dsimp only [w]
          rw [add_assoc, ← EReal.coe_add]
          simp
        _ ≤ finiteGeodesic theta.val u₀ u₁ t x + (D : EReal) := hadd

end

end SGPT.Foundations.Analysis.Pending
