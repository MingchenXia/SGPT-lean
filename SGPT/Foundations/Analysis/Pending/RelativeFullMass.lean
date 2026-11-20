import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.Pending.GlobalNonPluripolarKahler
import SGPT.Foundations.Analysis.Pending.ManifoldPluripolar
import SGPT.Foundations.Analysis.Pending.RelativeFullMassEpsilonBarrier
import SGPT.Foundations.Analysis.Pending.RooftopFeasibility
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamond
import SGPT.Foundations.Analysis.FirstPass.Envelopes
import SGPT.Foundations.Analysis.FirstPass.ExtendedDifference
import SGPT.Foundations.Analysis.FirstPass.FiniteGeodesicRooftopEndpoint
import SGPT.Foundations.Analysis.FirstPass.PotentialL1
import SGPT.Foundations.Analysis.FirstPass.RooftopEnvelope
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicClosedRestriction
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicConvexity
import SGPT.Foundations.Analysis.FirstPass.SubgeodesicInteriorL1
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.Pending.IncreasingThetaPshChartL1
import SGPT.Foundations.Analysis.Pending.ShiftedRooftopContact
import SGPT.Foundations.Analysis.Pending.ShiftedRooftopLimit

set_option autoImplicit false

/-!
# Model potentials and relative full-mass classes

This file records the classes of Xia, Definition 3.1.3 and Definition 3.1.5,
using genuine global theta-PSH potentials and the actual diagonal global
non-pluripolar mass.  A model potential is fixed by its singularity envelope
and has strictly positive mass.  Relative full mass is equality of the two
actual diagonal masses, not an abstract mass field.

The finite-energy subclass integrates the canonical pole-modified value of
`|phi - eta|` against the actual diagonal non-pluripolar measure of `eta`.
Mathlib's `EReal.abs` preserves one-sided infinite differences as `+infinity`;
only the common negative-infinity locus is assigned the finite value zero.
No independence theorem for changing that common-pole value is asserted here.

Sources: `xia-sgpt:page-0102`, `xia-sgpt:page-0104`,
`xia-sgpt:page-0105`, `xia-sgpt:page-0108`, `xia-sgpt:page-0114`,
`xia-sgpt:page-0115`, `xia-sgpt:page-0116`, `xia-sgpt:page-0132`.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `PSH(X, theta; phi)`: genuine theta-PSH potentials normalized below the
fixed reference potential. -/
def RelativePSH (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal) : Prop :=
  IsThetaPshPotential theta.val eta ∧ eta ≤ phi

/-- `E^infinity(X, theta; phi)`: genuine theta-PSH potentials having the same
bounded additive singularity type as the fixed reference potential. -/
def RelativeEInfinity (theta : ClosedRealOneOneForm n M)
    (phi eta : M → EReal) : Prop :=
  IsThetaPshPotential theta.val eta ∧ SameSingularityTypeOn eta phi univ

theorem RelativePSH.plurisubharmonic {theta : ClosedRealOneOneForm n M}
    {phi eta : M → EReal} (h : RelativePSH theta phi eta) :
    IsThetaPshPotential theta.val eta :=
  h.1

theorem RelativePSH.le_reference {theta : ClosedRealOneOneForm n M}
    {phi eta : M → EReal} (h : RelativePSH theta phi eta) : eta ≤ phi :=
  h.2

theorem RelativeEInfinity.plurisubharmonic {theta : ClosedRealOneOneForm n M}
    {phi eta : M → EReal} (h : RelativeEInfinity theta phi eta) :
    IsThetaPshPotential theta.val eta :=
  h.1

theorem RelativeEInfinity.sameSingularityType {theta : ClosedRealOneOneForm n M}
    {phi eta : M → EReal} (h : RelativeEInfinity theta phi eta) :
    SameSingularityTypeOn eta phi univ :=
  h.2

variable [MeasurableSpace M] [CompactSpace M]

/-- A model potential in the fixed background `theta`: a genuine theta-PSH
potential fixed by `P_theta` and with strictly positive actual diagonal mass.
This is Xia's Definition 3.1.3, including its positive-mass convention. -/
structure IsModelPotential (theta : ClosedRealOneOneForm n M)
    (phi : M → EReal) : Prop where
  plurisubharmonic : IsThetaPshPotential theta.val phi
  envelope_eq : phi = singularityEnvelope theta.val phi
  positive_mass : 0 < diagonalPotentialMass theta phi plurisubharmonic

/-- `E(X, theta; phi)`: a relative theta-PSH potential whose actual diagonal
non-pluripolar mass equals that of the fixed model potential.  The existential
theta-PSH witness makes the proposition independent of a chosen proof for
`eta`; independence of the reference witness is proved below. -/
def RelativeFullMass (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (hphi : IsModelPotential theta phi) : Prop :=
  ∃ heta : IsThetaPshPotential theta.val eta,
    eta ≤ phi ∧
      diagonalPotentialMass theta eta heta =
        diagonalPotentialMass theta phi hphi.plurisubharmonic

theorem isModelPotential_iff (theta : ClosedRealOneOneForm n M)
    (phi : M → EReal) (hphi : IsThetaPshPotential theta.val phi) :
    IsModelPotential theta phi ↔
      phi = singularityEnvelope theta.val phi ∧
        0 < diagonalPotentialMass theta phi hphi := by
  constructor
  · intro h
    exact ⟨h.envelope_eq, (diagonalPotentialMass_proof_independent
      h.plurisubharmonic hphi) ▸ h.positive_mass⟩
  · rintro ⟨henvelope, hmass⟩
    exact ⟨hphi, henvelope, hmass⟩

theorem relativeFullMass_iff (theta : ClosedRealOneOneForm n M)
    (phi eta : M → EReal) (hphi : IsModelPotential theta phi)
    (heta : IsThetaPshPotential theta.val eta) :
    RelativeFullMass theta phi eta hphi ↔
      eta ≤ phi ∧
        diagonalPotentialMass theta eta heta =
          diagonalPotentialMass theta phi hphi.plurisubharmonic := by
  constructor
  · rintro ⟨heta', hle, hmass⟩
    exact ⟨hle, (diagonalPotentialMass_proof_independent heta heta').trans hmass⟩
  · rintro ⟨hle, hmass⟩
    exact ⟨heta, hle, hmass⟩

theorem relativeFullMass_reference_proof_independent
    (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (hphi kphi : IsModelPotential theta phi) :
    RelativeFullMass theta phi eta hphi ↔
      RelativeFullMass theta phi eta kphi := by
  constructor
  · rintro ⟨heta, hle, hmass⟩
    refine ⟨heta, hle, hmass.trans ?_⟩
    exact diagonalPotentialMass_proof_independent
      hphi.plurisubharmonic kphi.plurisubharmonic
  · rintro ⟨heta, hle, hmass⟩
    refine ⟨heta, hle, hmass.trans ?_⟩
    exact diagonalPotentialMass_proof_independent
      kphi.plurisubharmonic hphi.plurisubharmonic

theorem RelativeFullMass.relativePSH {theta : ClosedRealOneOneForm n M}
    {phi eta : M → EReal} {hphi : IsModelPotential theta phi}
    (h : RelativeFullMass theta phi eta hphi) : RelativePSH theta phi eta := by
  obtain ⟨heta, hle, _⟩ := h
  exact ⟨heta, hle⟩

theorem RelativeFullMass.plurisubharmonic {theta : ClosedRealOneOneForm n M}
    {phi eta : M → EReal} {hphi : IsModelPotential theta phi}
    (h : RelativeFullMass theta phi eta hphi) :
    IsThetaPshPotential theta.val eta :=
  h.relativePSH.plurisubharmonic

theorem RelativeFullMass.le_reference {theta : ClosedRealOneOneForm n M}
    {phi eta : M → EReal} {hphi : IsModelPotential theta phi}
    (h : RelativeFullMass theta phi eta hphi) : eta ≤ phi :=
  h.relativePSH.le_reference

omit [MeasurableSpace M] [CompactSpace M] in
/-- A common theta-PSH lower barrier, required only outside pluripolar sets,
already makes the shifted rooftop family nonempty.  This is the exact
feasibility condition for `rooftopCompetitors`, whose obstacle relation is
itself quasi-everywhere.  In particular, a later analytic construction need
not strengthen a naturally quasi-everywhere lower comparison to a pointwise
one merely to enter the envelope argument. -/
theorem rooftopCompetitors_nonempty_min_add_const_of_common_thetaPsh_lower_qe
    (theta : ClosedRealOneOneForm n M) (u v w : M → EReal)
    (hw : IsThetaPshPotential theta.val w)
    (hwu : QuasiEverywhere (n := n) (fun x => w x ≤ u x))
    (C : ℝ) (hwv : QuasiEverywhere (n := n) (fun x => w x ≤ v x + (C : EReal))) :
    (rooftopCompetitors theta.val
      (fun x => min (u x) (v x + (C : EReal)))).Nonempty := by
  refine ⟨w, hw, ?_⟩
  exact (quasiEverywhere_and hwu hwv).mono
    (fun _ hx => le_min hx.1 hx.2)

omit [MeasurableSpace M] in
/-- The theta-PSH conclusion for a shifted rooftop follows from the exact
quasi-everywhere common-barrier condition.  Compactness contributes only the
finite upper bound obtained from the first obstacle. -/
theorem isThetaPshPotential_rooftop_min_add_const_of_common_thetaPsh_lower_qe
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (u v w : M → EReal)
    (hu : IsThetaPshPotential theta.val u)
    (hw : IsThetaPshPotential theta.val w)
    (hwu : QuasiEverywhere (n := n) (fun x => w x ≤ u x))
    (C : ℝ) (hwv : QuasiEverywhere (n := n) (fun x => w x ≤ v x + (C : EReal))) :
    IsThetaPshPotential theta.val (rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))) := by
  apply isThetaPshPotential_rooftop_of_nonempty
  · exact rooftopCompetitors_nonempty_min_add_const_of_common_thetaPsh_lower_qe
      theta u v w hw hwu C hwv
  · exact rooftopCompetitors_min_add_const_uniformlyBoundedAbove theta u v hu C

omit [MeasurableSpace M] in
/-- If the first theta-PSH obstacle already lies below the translated second
one, it is a rooftop competitor, so the actual rooftop is theta-PSH. -/
theorem isThetaPshPotential_rooftop_min_add_const_of_le [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (u v : M → EReal)
    (hu : IsThetaPshPotential theta.val u) (C : ℝ)
    (huv : u ≤ fun x => v x + (C : EReal)) :
    IsThetaPshPotential theta.val (rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))) := by
  apply isThetaPshPotential_rooftop_of_nonempty
  · refine ⟨u, mem_rooftopCompetitors_of_le hu ?_⟩
    intro x
    exact le_min le_rfl (huv x)
  · exact rooftopCompetitors_min_add_const_uniformlyBoundedAbove theta u v hu C

omit [MeasurableSpace M] [CompactSpace M] in
/-- In the ordered case, the first obstacle is itself the shifted rooftop.
The lower bound comes from using it as a competitor; the upper bound is the
ordinary obstacle recovery inequality. -/
theorem rooftopEnvelope_min_add_const_eq_of_le [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (u v : M → EReal)
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (C : ℝ)
    (huv : u ≤ fun x => v x + (C : EReal)) :
    rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))) = u := by
  apply le_antisymm
  · exact (rooftopEnvelope_min_add_const_le_obstacles hu.1 hv.1 C).1
  · apply le_rooftopEnvelope hu
    exact quasiEverywhere_of_forall fun x => le_min le_rfl (huv x)

omit [MeasurableSpace M] [CompactSpace M] in
/-- Two potentials with the model potential's bounded additive singularity
type have an explicit common theta-PSH lower barrier.  This is the elementary
case in which a rooftop competitor can be constructed directly: if
`phi ≤ u + A` and `phi ≤ v + B`, then a sufficiently negative finite
translate of `phi` lies below both `u` and `v + C`.

The conclusion deliberately assumes `SameSingularityTypeOn`; relative full
mass alone only contains an equality of non-pluripolar masses and does not
provide either of these finite comparison constants. -/
theorem exists_common_thetaPsh_lower_of_sameSingularityType
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi)
    (hu : SameSingularityTypeOn u phi univ)
    (hv : SameSingularityTypeOn v phi univ) (C : ℝ) :
    ∃ w : M → EReal, IsThetaPshPotential theta.val w ∧
      w ≤ u ∧ w ≤ (fun x => v x + (C : EReal)) ∧
        SameSingularityTypeOn w phi univ := by
  obtain ⟨A, hA⟩ := hu.2
  obtain ⟨B, hB⟩ := hv.2
  let K : ℝ := max A (B - C)
  have hAK : A ≤ K := le_max_left _ _
  have hBCK : B ≤ C + K := by
    dsimp [K]
    linarith [le_max_right A (B - C)]
  refine ⟨fun x => phi x - (K : EReal), ?_, ?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using hphi.add_const (-K)
  · intro x
    apply (EReal.sub_le_iff_le_add (by simp) (by simp)).2
    calc
      phi x ≤ u x + (A : EReal) := hA x (mem_univ x)
      _ ≤ u x + (K : EReal) :=
        by simpa [add_comm] using
          add_le_add_right (EReal.coe_le_coe_iff.mpr hAK) (u x)
  · intro x
    apply (EReal.sub_le_iff_le_add (by simp) (by simp)).2
    calc
      phi x ≤ v x + (B : EReal) := hB x (mem_univ x)
      _ ≤ v x + ((C + K : ℝ) : EReal) :=
        by simpa [add_comm] using
          add_le_add_right (EReal.coe_le_coe_iff.mpr hBCK) (v x)
      _ = (v x + (C : EReal)) + (K : EReal) := by
        rw [EReal.coe_add, add_assoc]
  · constructor
    · refine ⟨-K, ?_⟩
      intro x _
      simp [sub_eq_add_neg]
    · refine ⟨K, ?_⟩
      intro x _
      exact (EReal.sub_le_iff_le_add (by simp) (by simp)).1 le_rfl

omit [MeasurableSpace M] [CompactSpace M] in
/-- Bounded additive equivalence with a theta-PSH reference gives a concrete
member of every shifted rooftop family.  The member is a finite negative
translate of the reference potential; spelling out this nonemptiness result
lets later envelope arguments consume precisely the analytic output they
need, without silently upgrading it to the general relative-full-mass claim. -/
theorem rooftopCompetitors_nonempty_min_add_const_of_sameSingularityType
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi)
    (husing : SameSingularityTypeOn u phi univ)
    (hvsing : SameSingularityTypeOn v phi univ) (C : ℝ) :
    (rooftopCompetitors theta.val
      (fun x => min (u x) (v x + (C : EReal)))).Nonempty := by
  obtain ⟨w, hw, hwu, hwv, _⟩ :=
    exists_common_thetaPsh_lower_of_sameSingularityType theta phi u v
      hphi husing hvsing C
  exact rooftopCompetitors_nonempty_min_add_const_of_common_thetaPsh_lower_qe
    theta u v w hw (quasiEverywhere_of_forall hwu) C
      (quasiEverywhere_of_forall hwv)

omit [MeasurableSpace M] in
/-- The preceding finite-singularity comparison gives the required rooftop
feasibility and hence a genuine theta-PSH rooftop.  This is a no-`sorry`
route for the bounded-singularity subclass; it does not claim that relative
full mass alone supplies the two comparison constants. -/
theorem isThetaPshPotential_rooftop_add_const_of_sameSingularityType [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u)
    (husing : SameSingularityTypeOn u phi univ)
    (hvsing : SameSingularityTypeOn v phi univ) (C : ℝ) :
    IsThetaPshPotential theta.val (rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))) := by
  apply isThetaPshPotential_rooftop_of_nonempty
  · exact rooftopCompetitors_nonempty_min_add_const_of_sameSingularityType
      theta phi u v hphi husing hvsing C
  · exact rooftopCompetitors_min_add_const_uniformlyBoundedAbove theta u v hu C

omit [MeasurableSpace M] [CompactSpace M] in
/-- A feasible shifted rooftop retains the common bounded additive
singularity type.  Its upper comparison comes from the first obstacle, and
its lower comparison from the explicit common barrier. -/
theorem sameSingularityTypeOn_rooftop_add_const_of_sameSingularityType [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (husing : SameSingularityTypeOn u phi univ)
    (hvsing : SameSingularityTypeOn v phi univ) (C : ℝ) :
    SameSingularityTypeOn
      (rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))))
      phi univ := by
  obtain ⟨w, hw, hwu, hwv, hwsing⟩ :=
    exists_common_thetaPsh_lower_of_sameSingularityType theta phi u v
      hphi husing hvsing C
  have hwr : w ≤ rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal))) := by
    apply le_rooftopEnvelope hw
    exact quasiEverywhere_of_forall fun x => le_min (hwu x) (hwv x)
  have hobs := rooftopEnvelope_min_add_const_le_obstacles hu.1 hv.1 C
  constructor
  · obtain ⟨A, hA⟩ := husing.1
    refine ⟨A, ?_⟩
    intro x hx
    exact (hobs.1 x).trans (hA x hx)
  · obtain ⟨A, hA⟩ := hwsing.2
    refine ⟨A, ?_⟩
    intro x hx
    exact (hA x hx).trans (add_le_add_left (hwr x) _)

omit [MeasurableSpace M] in
/-- The shifted rooftop is closed in the bounded-singularity class whenever
the common reference is theta-PSH.  This proves the analytic closure portion
of the relative `E^infinity` rooftop construction without invoking relative
full mass. -/
theorem relativeEInfinity_rooftop_add_const_of_sameSingularityType [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi)
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (husing : SameSingularityTypeOn u phi univ)
    (hvsing : SameSingularityTypeOn v phi univ) (C : ℝ) :
    RelativeEInfinity theta phi
      (rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal)))) := by
  refine ⟨isThetaPshPotential_rooftop_add_const_of_sameSingularityType
    theta phi u v hphi hu husing hvsing C, ?_⟩
  exact sameSingularityTypeOn_rooftop_add_const_of_sameSingularityType
    theta phi u v hphi hu hv husing hvsing C

/-- In particular, the shifted rooftop is theta-PSH for two normalized
`RelativeEInfinity` endpoints.  Their bounded singularity types supply the
finite comparison constants used in the preceding common-barrier argument. -/
theorem isThetaPshPotential_rooftop_add_const_of_relativeEInfinity [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu : RelativeEInfinity theta phi u)
    (hv : RelativeEInfinity theta phi v) (C : ℝ) :
    IsThetaPshPotential theta.val (rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))) :=
  isThetaPshPotential_rooftop_add_const_of_sameSingularityType theta phi u v
    hphi.plurisubharmonic hu.plurisubharmonic hu.sameSingularityType
    hv.sameSingularityType C

/-- In the relative `E^infinity` subclass, every finite shifted rooftop is
again a theta-PSH potential of the same bounded singularity type as the
model reference. -/
theorem relativeEInfinity_rooftop_add_const_of_relativeEInfinity [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu : RelativeEInfinity theta phi u)
    (hv : RelativeEInfinity theta phi v) (C : ℝ) :
    RelativeEInfinity theta phi
      (rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal)))) :=
  relativeEInfinity_rooftop_add_const_of_sameSingularityType theta phi u v
    hphi.plurisubharmonic hu.plurisubharmonic hv.plurisubharmonic
    hu.sameSingularityType hv.sameSingularityType C

omit [TopologicalSpace M] [MeasurableSpace M] [CompactSpace M] in
/-- Two potentials of the same bounded additive singularity type admit a
finite threshold after which the first is below every translate of the
second.  This only uses the two directed finite comparisons with the common
reference potential. -/
theorem exists_shifted_rooftop_order_threshold_of_sameSingularityType
    (phi u v : M → EReal)
    (husing : SameSingularityTypeOn u phi univ)
    (hvsing : SameSingularityTypeOn v phi univ) :
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → u ≤ fun x => v x + (C : EReal) := by
  obtain ⟨A, hA⟩ := husing.1
  obtain ⟨B, hB⟩ := hvsing.2
  refine ⟨A + B, ?_⟩
  intro C hC x
  calc
    u x ≤ phi x + (A : EReal) := hA x (mem_univ x)
    _ ≤ (v x + (B : EReal)) + (A : EReal) :=
      add_le_add_left (hB x (mem_univ x)) _
    _ = v x + ((A + B : ℝ) : EReal) := by
      simp [EReal.coe_add, add_comm, add_left_comm]
    _ ≤ v x + (C : EReal) :=
      add_le_add_right (EReal.coe_le_coe_iff.mpr hC) _

omit [MeasurableSpace M] [CompactSpace M] in
/-- For boundedly equivalent singularity types, the shifted rooftop is
eventually constant: after a finite threshold it is exactly the first
potential. -/
theorem exists_rooftopEnvelope_min_add_const_eq_of_sameSingularityType [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (husing : SameSingularityTypeOn u phi univ)
    (hvsing : SameSingularityTypeOn v phi univ) :
    ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))) = u := by
  obtain ⟨C₀, hC₀⟩ :=
    exists_shifted_rooftop_order_threshold_of_sameSingularityType phi u v husing hvsing
  refine ⟨C₀, ?_⟩
  intro C hC
  exact rooftopEnvelope_min_add_const_eq_of_le theta u v hu hv C (hC₀ C hC)

omit [MeasurableSpace M] [CompactSpace M] in
/-- If one obstacle is eventually below every sufficiently large translate of
the other, then the shifted rooftops are eventually equal to that first
obstacle and hence converge chart-locally in `L¹`.  This is the order-theoretic
part of rooftop exhaustion; any general full-mass proof must provide the
displayed eventual comparison by analytic means. -/
theorem manifoldL1LocallyTendsto_rooftop_add_const_of_eventual_order
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (u v : M → EReal)
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (C₀ : ℝ) (hC₀ : ∀ C : ℝ, C₀ ≤ C → u ≤ fun x => v x + (C : EReal)) :
    ManifoldL1LocallyTendsto (n := n)
      (fun (C : ℝ) x =>
        rooftopEnvelope theta.val (fun y => min (u y) (v y + (C : EReal))) x)
      atTop u := by
  refine ManifoldL1LocallyTendsto.congr' ?_
    (manifoldL1LocallyTendsto_const u
      (fun x => hu.1.quasiPlurisubharmonic.ne_top x) atTop)
  change (fun _ : ℝ => u) =ᶠ[atTop]
    (fun C x => rooftopEnvelope theta.val
      (fun y => min (u y) (v y + (C : EReal))) x)
  filter_upwards [eventually_ge_atTop C₀] with C hC
  exact (rooftopEnvelope_min_add_const_eq_of_le theta u v hu hv C
    (hC₀ C hC)).symm

omit [MeasurableSpace M] [CompactSpace M] in
/-- A finite eventual comparison threshold gives rooftop exhaustion without
requiring the two obstacles to have the same singularity type. -/
theorem manifoldL1LocallyTendsto_rooftop_add_const_of_exists_eventual_order
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (u v : M → EReal)
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (horder : ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
      u ≤ fun x => v x + (C : EReal)) :
    ManifoldL1LocallyTendsto (n := n)
      (fun (C : ℝ) x =>
        rooftopEnvelope theta.val (fun y => min (u y) (v y + (C : EReal))) x)
      atTop u := by
  obtain ⟨C₀, hC₀⟩ := horder
  exact manifoldL1LocallyTendsto_rooftop_add_const_of_eventual_order
    theta u v hu hv C₀ hC₀

omit [MeasurableSpace M] [CompactSpace M] in
/-- The shifted rooftop of two theta-PSH potentials with a common bounded
singularity type converges locally in `L¹` to the first potential as the
translation tends to `+∞`: it is eventually equal to that potential. -/
theorem manifoldL1LocallyTendsto_rooftop_add_const_of_sameSingularityType
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v)
    (husing : SameSingularityTypeOn u phi univ)
    (hvsing : SameSingularityTypeOn v phi univ) :
    ManifoldL1LocallyTendsto (n := n)
      (fun (C : ℝ) x =>
        rooftopEnvelope theta.val (fun y => min (u y) (v y + (C : EReal))) x)
      atTop u := by
  exact manifoldL1LocallyTendsto_rooftop_add_const_of_exists_eventual_order
    theta u v hu hv
    (exists_shifted_rooftop_order_threshold_of_sameSingularityType
      phi u v husing hvsing)

omit [MeasurableSpace M] [CompactSpace M] in
/-- The preceding eventual-constancy and local `L¹` result applies directly
to the `RelativeEInfinity` subclass, whose definition supplies the two
finite singularity comparisons. -/
theorem manifoldL1LocallyTendsto_rooftop_add_const_of_relativeEInfinity
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hu : RelativeEInfinity theta phi u)
    (hv : RelativeEInfinity theta phi v) :
    ManifoldL1LocallyTendsto (n := n)
      (fun (C : ℝ) x =>
        rooftopEnvelope theta.val (fun y => min (u y) (v y + (C : EReal))) x)
      atTop u :=
  manifoldL1LocallyTendsto_rooftop_add_const_of_sameSingularityType
    theta phi u v hu.plurisubharmonic hv.plurisubharmonic
    hu.sameSingularityType hv.sameSingularityType

/-- **Complete shifted-rooftop API in the bounded-singularity subclass.**
For every finite translation, the rooftop stays in `RelativeEInfinity` and
lies below both obstacles; as the translation tends to `+∞`, this family
converges locally in `L¹` to its first endpoint.  The proof is entirely the
finite-singularity route and does not use the unresolved full-mass rooftop
closure. -/
theorem relativeEInfinity_rooftop_add_const_complete [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu : RelativeEInfinity theta phi u)
    (hv : RelativeEInfinity theta phi v) :
    (∀ C : ℝ,
      RelativeEInfinity theta phi
        (rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal)))) ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))) ≤ u ∧
      rooftopEnvelope theta.val (fun x => min (u x) (v x + (C : EReal))) ≤
        (fun x => v x + (C : EReal))) ∧
    ManifoldL1LocallyTendsto (n := n)
      (fun (C : ℝ) x =>
        rooftopEnvelope theta.val (fun y => min (u y) (v y + (C : EReal))) x)
      atTop u := by
  constructor
  · intro C
    refine ⟨relativeEInfinity_rooftop_add_const_of_relativeEInfinity
      theta phi u v hphi hu hv C, ?_, ?_⟩
    · exact (rooftopEnvelope_min_add_const_le_obstacles
        hu.plurisubharmonic.1 hv.plurisubharmonic.1 C).1
    · exact (rooftopEnvelope_min_add_const_le_obstacles
        hu.plurisubharmonic.1 hv.plurisubharmonic.1 C).2
  · exact manifoldL1LocallyTendsto_rooftop_add_const_of_relativeEInfinity
      theta phi u v hu hv

/-- The complete bounded-singularity rooftop package is exactly the input of
the first-pass Perron endpoint theorem.  Thus a finite geodesic between two
`RelativeEInfinity` endpoints recovers its left endpoint in local `L¹`, with
no appeal to the unresolved general relative-full-mass rooftop closure. -/
theorem finiteGeodesic_tendsto_left_of_relativeEInfinity [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁) :
    ManifoldL1LocallyTendsto (n := n)
      (finiteGeodesic theta.val u₀ u₁) (𝓝[>] (0 : ℝ)) u₀ := by
  let w : ℝ → M → EReal := fun C => rooftopEnvelope theta.val
    (fun x => min (u₀ x) (u₁ x + (C : EReal)))
  apply finiteGeodesic_tendsto_left_of_rooftop_exhaustion
      hu₀.plurisubharmonic hu₁.plurisubharmonic (w := w)
  · intro C _
    simpa only [w] using
      (relativeEInfinity_rooftop_add_const_of_relativeEInfinity
        theta phi u₀ u₁ hphi hu₀ hu₁ C).plurisubharmonic
  · intro C _
    simpa only [w] using
      (rooftopEnvelope_min_add_const_le_obstacles
        hu₀.plurisubharmonic.1 hu₁.plurisubharmonic.1 C).1
  · intro C _
    simpa only [w] using
      (rooftopEnvelope_min_add_const_le_obstacles
        hu₀.plurisubharmonic.1 hu₁.plurisubharmonic.1 C).2
  · simpa only [w] using
      manifoldL1LocallyTendsto_rooftop_add_const_of_relativeEInfinity
        theta phi u₀ u₁ hu₀ hu₁

/-- Time reversal transfers the bounded-singularity left-endpoint recovery
to the right endpoint of the same finite geodesic. -/
theorem finiteGeodesic_tendsto_right_of_relativeEInfinity [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁) :
    ManifoldL1LocallyTendsto (n := n)
      (finiteGeodesic theta.val u₀ u₁) (𝓝[<] (1 : ℝ)) u₁ := by
  have hleft := finiteGeodesic_tendsto_left_of_relativeEInfinity
    theta phi u₁ u₀ hphi hu₁ hu₀
  have hreversed := hleft.comp tendsto_one_sub_nhdsLT_one
  apply ManifoldL1LocallyTendsto.congr (hu := hreversed)
  intro t
  rw [finiteGeodesic_timeReversal]
  congr 2
  ring

/-- The order part of the bounded-singularity finite-geodesic statement.
It requires no assertion that the Perron strip is itself PSH: two endpoint
comparisons already force every interior slice to have the same additive
singularity type as the model potential. -/
theorem sameSingularityTypeOn_finiteGeodesic_of_relativeEInfinity
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    SameSingularityTypeOn (finiteGeodesic theta.val u₀ u₁ t) phi univ := by
  rcases hu₀.sameSingularityType.1 with ⟨C₀, hC₀⟩
  rcases hu₀.sameSingularityType.2 with ⟨D₀, hD₀⟩
  rcases hu₁.sameSingularityType.1 with ⟨C₁, hC₁⟩
  rcases hu₁.sameSingularityType.2 with ⟨D₁, hD₁⟩
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

/-- Once the independent Perron-strip PSH theorem is supplied, the preceding
order calculation upgrades every interior finite-geodesic slice to the
bounded relative class.  This is intentionally conditional on the genuine
`IsSubgeodesicInterior` input and makes no claim for general full-mass
endpoints. -/
theorem relativeEInfinity_finiteGeodesic_of_interior
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    RelativeEInfinity theta phi (finiteGeodesic theta.val u₀ u₁ t) :=
  ⟨hinterior.thetaPshPotential ht,
    sameSingularityTypeOn_finiteGeodesic_of_relativeEInfinity
      theta phi u₀ u₁ hphi hu₀ hu₁ t ht⟩

/-- **Bounded finite-geodesic package with explicit interior input.**
For `RelativeEInfinity` endpoints, a supplied Perron-strip PSH proof combines
with the bounded shifted-rooftop endpoint argument to give the actual
subgeodesic-with-endpoints predicate and `RelativeEInfinity` for every
interior slice.  The separate interior hypothesis is intentional: its proof
is the remaining Perron regularity problem and is not inferred from relative
full mass here. -/
theorem finiteGeodesic_relativeEInfinity_package_of_interior [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁)) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ ∧
      ∀ t ∈ Ioo (0 : ℝ) 1,
        RelativeEInfinity theta phi (finiteGeodesic theta.val u₀ u₁ t) := by
  constructor
  · exact ⟨hu₀.plurisubharmonic, hu₁.plurisubharmonic, hinterior,
      finiteGeodesic_tendsto_left_of_relativeEInfinity theta phi u₀ u₁ hphi hu₀ hu₁,
      finiteGeodesic_tendsto_right_of_relativeEInfinity theta phi u₀ u₁ hphi hu₀ hu₁⟩
  · intro t ht
    exact relativeEInfinity_finiteGeodesic_of_interior
      theta phi u₀ u₁ hphi hu₀ hu₁ hinterior t ht

/-- **Explicit-interior replacement for the bounded finite-geodesic bridge.**
This has the same structural conclusion consumed by finite-geodesic arguments:
the Perron finite geodesic is a subgeodesic with the prescribed endpoints.
The only additional input is the actual interior strip-PSH certificate, which
is kept visible rather than being inferred from the unresolved general
relative-full-mass bridge. -/
theorem finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁)) :
    IsSubgeodesicFrom theta.val (finiteGeodesic theta.val u₀ u₁) u₀ u₁ :=
  (finiteGeodesic_relativeEInfinity_package_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior).1

/-- **Vertical-trace dichotomy for the bounded finite geodesic.**
At any fixed spatial point, the supplied interior strip certificate forces
the Perron trace either to be identically polar on `(0,1)`, or to be finite
there with convex real-valued trace.  This is the pointwise convexity
consequence used by later finite-geodesic arguments, now available under the
explicit interior hypothesis. -/
theorem finiteGeodesic_verticalTrace_convexity_dichotomy_of_relativeEInfinity_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    (x : M) :
    (∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic theta.val u₀ u₁ t x = ⊥) ∨
      ((∀ t ∈ Ioo (0 : ℝ) 1,
        finiteGeodesic theta.val u₀ u₁ t x ≠ ⊤ ∧
          finiteGeodesic theta.val u₀ u₁ t x ≠ ⊥) ∧
        ConvexOn ℝ (Ioo (0 : ℝ) 1)
          (fun t => (finiteGeodesic theta.val u₀ u₁ t x).toReal)) :=
  (finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior).verticalTrace_convexity_dichotomy x

/-- **Nonpolar bounded finite-geodesic traces are convex.**
If one interior slice at a spatial point is not a pole, the explicit strip
certificate propagates nonpolarity to every interior time and yields convexity
of the real-valued vertical trace. -/
theorem finiteGeodesic_verticalTrace_convexOn_of_nonpolar_of_relativeEInfinity_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    (x : M) {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1)
    (hc_bot : finiteGeodesic theta.val u₀ u₁ c x ≠ ⊥) :
    (∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic theta.val u₀ u₁ t x ≠ ⊥) ∧
      ConvexOn ℝ (Ioo (0 : ℝ) 1)
        (fun t => (finiteGeodesic theta.val u₀ u₁ t x).toReal) := by
  have hsub := finiteGeodesic_isSubgeodesicFrom_of_relativeEInfinity_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior
  have hnonpolar : ∀ t ∈ Ioo (0 : ℝ) 1, finiteGeodesic theta.val u₀ u₁ t x ≠ ⊥ :=
    hsub.interior.ne_bot_of_exists_ne_bot x hc hc_bot
  exact ⟨hnonpolar,
    hsub.interior.convexOn_toReal_of_forall_ne_bot x hnonpolar⟩

/-- **Interior `L¹` continuity in the bounded finite-geodesic class.**
Once the Perron-strip PSH assertion is supplied explicitly, the bounded
`RelativeEInfinity` package constructs a genuine subgeodesic with its given
endpoints.  Its standard interior continuity theorem is therefore available
without invoking the unresolved relative-full-mass endpoint statements. -/
theorem manifoldL1LocallyContinuousAt_finiteGeodesic_of_relativeEInfinity_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {c : ℝ} (hc : c ∈ Ioo (0 : ℝ) 1) :
    ManifoldL1LocallyTendsto (n := n) (finiteGeodesic theta.val u₀ u₁) (𝓝 c)
      (finiteGeodesic theta.val u₀ u₁ c) :=
  (finiteGeodesic_relativeEInfinity_package_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior).1.manifoldL1LocallyContinuousAt hc

/-- **Closed interior restriction of a bounded finite geodesic.**
On every nondegenerate closed subinterval contained in `(0,1)`, the affine
reparametrization has the two actual finite-geodesic slices as its prescribed
endpoints, and both remain in `RelativeEInfinity`.  This packages the endpoint
and `L¹` bookkeeping needed by subinterval consumers while retaining the
explicit Perron-strip hypothesis. -/
theorem finiteGeodesic_closedAffineReparametrized_relativeEInfinity_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a < b) :
    IsSubgeodesicFrom theta.val
      (affineReparametrizedCurve (finiteGeodesic theta.val u₀ u₁) a b)
      (finiteGeodesic theta.val u₀ u₁ a) (finiteGeodesic theta.val u₀ u₁ b) ∧
    RelativeEInfinity theta phi (finiteGeodesic theta.val u₀ u₁ a) ∧
      RelativeEInfinity theta phi (finiteGeodesic theta.val u₀ u₁ b) := by
  have hpackage := finiteGeodesic_relativeEInfinity_package_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior
  refine ⟨?_, hpackage.2 a ha, hpackage.2 b hb⟩
  simpa only [closedSubgeodesicSlice_eq_curve ha,
    closedSubgeodesicSlice_eq_curve hb] using
    hpackage.1.closedAffineReparametrized (le_of_lt ha.1) (le_of_lt hb.2) hab

/-- **Bounded class at every closed finite-geodesic slice.**
The endpoint convention in `closedSubgeodesicSlice` agrees with the two
given `RelativeEInfinity` endpoints; away from the boundary this is the
previous interior-slice result. -/
theorem relativeEInfinity_closedSubgeodesicSlice_finiteGeodesic_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    RelativeEInfinity theta phi
      (closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ t) := by
  by_cases ht0 : t = 0
  · subst t
    simpa using hu₀
  by_cases ht1 : t = 1
  · subst t
    simpa using hu₁
  have htI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
  rw [closedSubgeodesicSlice_eq_curve htI]
  exact relativeEInfinity_finiteGeodesic_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior t htI

/-- **Closed bounded finite-geodesic restriction, including original ends.**
For every `0 ≤ a < b ≤ 1`, the affine restriction is a certified
subgeodesic between the closed slices.  Its two endpoints are in
`RelativeEInfinity`, including when they are the original prescribed values
at time zero or one.  The Perron-strip condition remains an explicit input. -/
theorem finiteGeodesic_closedAffineReparametrized_relativeEInfinity_on_Icc_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    IsSubgeodesicFrom theta.val
      (affineReparametrizedCurve (finiteGeodesic theta.val u₀ u₁) a b)
      (closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ a)
      (closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ b) ∧
    RelativeEInfinity theta phi
      (closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ a) ∧
    RelativeEInfinity theta phi
      (closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ b) := by
  have hpackage := finiteGeodesic_relativeEInfinity_package_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior
  have haI : a ∈ Icc (0 : ℝ) 1 :=
    ⟨ha, (le_of_lt hab).trans hb⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 :=
    ⟨ha.trans (le_of_lt hab), hb⟩
  exact ⟨hpackage.1.closedAffineReparametrized ha hb hab,
    relativeEInfinity_closedSubgeodesicSlice_finiteGeodesic_of_interior
      theta phi u₀ u₁ hphi hu₀ hu₁ hinterior haI,
    relativeEInfinity_closedSubgeodesicSlice_finiteGeodesic_of_interior
      theta phi u₀ u₁ hphi hu₀ hu₁ hinterior hbI⟩

/-- **Endpoint limits for every closed bounded restriction.**
The normalized affine restriction of the finite geodesic converges in
chart-local `L¹` to its closed left and right slices.  Unlike the interior-only
version, this also applies to restrictions whose endpoint is `0` or `1`.
The supplied interior strip certificate is still explicit. -/
theorem finiteGeodesic_closedAffineReparametrized_endpoint_limits_on_Icc_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    ManifoldL1LocallyTendsto (n := n)
      (affineReparametrizedCurve (finiteGeodesic theta.val u₀ u₁) a b)
      (𝓝[>] (0 : ℝ))
      (closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ a) ∧
    ManifoldL1LocallyTendsto (n := n)
      (affineReparametrizedCurve (finiteGeodesic theta.val u₀ u₁) a b)
      (𝓝[<] (1 : ℝ))
      (closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ b) := by
  have hpackage := finiteGeodesic_closedAffineReparametrized_relativeEInfinity_on_Icc_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior ha hb hab
  exact ⟨hpackage.1.tendsto_left, hpackage.1.tendsto_right⟩

/-- **Left endpoint recovery after a bounded interior restriction.**
This is the direct endpoint-facing form of the closed-interval package: the
reparametrized curve converges in chart-local `L¹` to its actual slice at `a`.
The strip-Perron assertion remains an explicit input. -/
theorem finiteGeodesic_closedAffineReparametrized_tendsto_left_of_relativeEInfinity_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a < b) :
    ManifoldL1LocallyTendsto (n := n)
      (affineReparametrizedCurve (finiteGeodesic theta.val u₀ u₁) a b)
      (𝓝[>] (0 : ℝ)) (finiteGeodesic theta.val u₀ u₁ a) :=
  (finiteGeodesic_closedAffineReparametrized_relativeEInfinity_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior ha hb hab).1.tendsto_left

/-- **Right endpoint recovery after a bounded interior restriction.**
The same closed-interval package gives chart-local `L¹` convergence to the
actual slice at `b` as normalized time tends to one from inside. -/
theorem finiteGeodesic_closedAffineReparametrized_tendsto_right_of_relativeEInfinity_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : a < b) :
    ManifoldL1LocallyTendsto (n := n)
      (affineReparametrizedCurve (finiteGeodesic theta.val u₀ u₁) a b)
      (𝓝[<] (1 : ℝ)) (finiteGeodesic theta.val u₀ u₁ b) :=
  (finiteGeodesic_closedAffineReparametrized_relativeEInfinity_of_interior
    theta phi u₀ u₁ hphi hu₀ hu₁ hinterior ha hb hab).1.tendsto_right

/-- **Compatible adjacent bounded finite-geodesic pieces.**
For `a < b < c` in the open time interval, the restrictions to `[a,b]` and
`[b,c]` are genuine subgeodesics whose prescribed endpoint at the join is
definitionally the same finite-geodesic slice at `b`.  The last component
records that this shared endpoint remains in the bounded singularity class,
so consumers may concatenate the two certified pieces without a separate
endpoint-identification argument. -/
theorem finiteGeodesic_adjacentClosedAffineReparametrizations_of_relativeEInfinity_of_interior
    [Nonempty M] (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {a b c : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hab : a < b) (hbc : b < c) :
    IsSubgeodesicFrom theta.val
      (affineReparametrizedCurve (finiteGeodesic theta.val u₀ u₁) a b)
      (finiteGeodesic theta.val u₀ u₁ a) (finiteGeodesic theta.val u₀ u₁ b) ∧
    IsSubgeodesicFrom theta.val
      (affineReparametrizedCurve (finiteGeodesic theta.val u₀ u₁) b c)
      (finiteGeodesic theta.val u₀ u₁ b) (finiteGeodesic theta.val u₀ u₁ c) ∧
    RelativeEInfinity theta phi (finiteGeodesic theta.val u₀ u₁ b) := by
  exact ⟨(finiteGeodesic_closedAffineReparametrized_relativeEInfinity_of_interior
      theta phi u₀ u₁ hphi hu₀ hu₁ hinterior ha hb hab).1,
    (finiteGeodesic_closedAffineReparametrized_relativeEInfinity_of_interior
      theta phi u₀ u₁ hphi hu₀ hu₁ hinterior hb hc hbc).1,
    relativeEInfinity_finiteGeodesic_of_interior
      theta phi u₀ u₁ hphi hu₀ hu₁ hinterior b hb⟩

/-- **A common theta-PSH lower barrier for two relative full-mass
potentials.**  This is the relative full-mass analogue of
`exists_common_thetaPsh_lower_of_sameSingularityType`, and the input that
relative full mass alone was previously unable to supply.  It is obtained
from Xia's `epsilon`-barrier (SGPT, Corollary 2.4.3, isolated as
`RelativeFullMassEpsilonBarrier.exists_thetaPsh_epsilonBarrier`) as the
balanced convex combination of the two barriers at `epsilon = 1/2`. -/
theorem exists_common_thetaPsh_lower_of_relativeFullMass [BorelSpace M]
    [ConnectedSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    ∃ w : M → EReal, IsThetaPshPotential theta.val w ∧ w ≤ u ∧
      w ≤ fun x => v x + (C : EReal) := by
  have humass : diagonalPotentialMass theta u hu.plurisubharmonic =
      diagonalPotentialMass theta phi hphi.plurisubharmonic :=
    ((relativeFullMass_iff theta phi u hphi hu.plurisubharmonic).1 hu).2
  have hvmass : diagonalPotentialMass theta v hv.plurisubharmonic =
      diagonalPotentialMass theta phi hphi.plurisubharmonic :=
    ((relativeFullMass_iff theta phi v hphi hv.plurisubharmonic).1 hv).2
  exact RelativeFullMassEpsilonBarrier.exists_common_thetaPsh_lower_add_const
    omega theta hphi.plurisubharmonic hu.plurisubharmonic hv.plurisubharmonic
    hu.le_reference hv.le_reference (humass ▸ hphi.positive_mass)
    (hvmass ▸ hphi.positive_mass) humass hvmass C

/-- **Xia, Proposition 3.1.5, relative full-mass case; proved modulo
`RelativeFullMassEpsilonBarrier.exists_thetaPsh_epsilonBarrier`.** The actual
theta-rooftop of two relative full-mass potentials, one translated by a
finite constant, is a genuine theta-PSH potential.  The abstract envelope
theorem reduces this exactly to a nonempty rooftopCompetitors family: the
uniform upper bound already follows from u, and the common theta-PSH minorant
below both u and v + C is now supplied by
`exists_common_thetaPsh_lower_of_relativeFullMass` above, which rests on
Xia's Corollary 2.4.3 as its only unproved input. -/
theorem isThetaPshPotential_rooftop_add_const [BorelSpace M]
    [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    let w := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    IsThetaPshPotential theta.val w := by
  dsimp only
  obtain ⟨w, hw, hwu, hwv⟩ :=
    exists_common_thetaPsh_lower_of_relativeFullMass omega theta phi u v
      hphi hu hv C
  exact isThetaPshPotential_rooftop_min_add_const_of_common_thetaPsh_lower_qe
    theta u v w hu.plurisubharmonic hw
    (quasiEverywhere_of_forall fun x => hwu x) C
    (quasiEverywhere_of_forall fun x => hwv x)

/-- Rooftop obstacle recovery for relative full-mass inputs: the specialization
of `FirstPass.rooftopEnvelope_min_add_const_le_obstacles`. -/
theorem rooftop_add_const_le_obstacles [BorelSpace M]
    [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ) :
    let w := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    w ≤ u ∧ w ≤ fun x => v x + (C : EReal) :=
  rooftopEnvelope_min_add_const_le_obstacles hu.plurisubharmonic.1 hv.plurisubharmonic.1 C

/-- **Proved modulo the rooftop mass diamond
`RooftopMassDiamond.mass_add_mass_le_mass_max_add_mass_rooftop` (Xia, Theorem
3.1.3).** That inequality, together with full mass of the two inputs and
monotonicity for their maximum, gives the reference mass as a lower bound for
the actual rooftop mass. -/
theorem reference_mass_le_rooftop_add_const [BorelSpace M]
    [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ)
    (hw : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val
        (fun x => min (u x) (v x + (C : EReal)))))
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    diagonalPotentialMass theta phi hphi.plurisubharmonic ≤
      diagonalPotentialMass theta
        (rooftopEnvelope theta.val
          (fun x => min (u x) (v x + (C : EReal)))) hw := by
  set V := diagonalPotentialMass theta phi hphi.plurisubharmonic with hV
  have hv' : IsThetaPshPotential theta.val (fun x => v x + (C : EReal)) :=
    hv.plurisubharmonic.add_const C
  have hmax : IsThetaPshPotential theta.val
      (fun x => max (u x) (v x + (C : EReal))) :=
    IsThetaPshPotential.max hu.plurisubharmonic hv'
  have humass : diagonalPotentialMass theta u hu.plurisubharmonic = V :=
    ((relativeFullMass_iff theta phi u hphi hu.plurisubharmonic).1 hu).2
  have hvmass : diagonalPotentialMass theta v hv.plurisubharmonic = V :=
    ((relativeFullMass_iff theta phi v hphi hv.plurisubharmonic).1 hv).2
  have hv'mass : diagonalPotentialMass theta (fun x => v x + (C : EReal)) hv' = V := by
    rw [← hvmass]
    exact MixedMass.globalMixedMass_eq_of_sameSingularityType hn omega
      (fun _ : Fin n => hv') (fun _ => hv.plurisubharmonic)
      (fun _ => sameSingularityTypeOn_add_const v univ C)
  have hmaxle : diagonalPotentialMass theta
      (fun x => max (u x) (v x + (C : EReal))) hmax ≤ V := by
    rw [hV]
    refine MixedMass.globalMixedMass_mono hn omega (fun _ : Fin n => hmax)
      (fun _ => hphi.plurisubharmonic) (fun _ => ⟨max C 0, fun x _ => ?_⟩)
    refine max_le ?_ ?_
    · calc u x ≤ phi x := hu.le_reference x
        _ = phi x + ((0 : ℝ) : EReal) := by simp
        _ ≤ phi x + ((max C 0 : ℝ) : EReal) :=
            add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (le_max_right _ _))
    · exact add_le_add (hv.le_reference x)
        (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  have hdiamond := RooftopMassDiamond.mass_add_mass_le_mass_max_add_mass_rooftop
    omega theta hu.plurisubharmonic hv' hmax hw hprojection
  rw [humass, hv'mass] at hdiamond
  have hstep : V + V ≤ V + diagonalPotentialMass theta
      (rooftopEnvelope theta.val
        (fun x => min (u x) (v x + (C : EReal)))) hw :=
    hdiamond.trans (add_le_add hmaxle le_rfl)
  have hVtop : V ≠ ⊤ :=
    (MixedMass.globalMixedMass_lt_top omega
      (fun _ : Fin n => hphi.plurisubharmonic.1)).ne
  exact (ENNReal.add_le_add_iff_left hVtop).1 hstep

/-- Full-mass closure of the shifted rooftop, assembled from the separate PSH,
obstacle, rooftop-mass, and total-mass monotonicity inputs above. -/
theorem relativeFullMass_rooftop_add_const [BorelSpace M]
    [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    let w := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    RelativeFullMass theta phi w hphi ∧
      w ≤ u ∧ w ≤ fun x => v x + (C : EReal) := by
  dsimp only
  let w := rooftopEnvelope theta.val
    (fun x => min (u x) (v x + (C : EReal)))
  have hw : IsThetaPshPotential theta.val w := by
    simpa only [w] using isThetaPshPotential_rooftop_add_const
      hn omega theta phi u v hphi hu hv C
  have hobs : w ≤ u ∧ w ≤ fun x => v x + (C : EReal) := by
    simpa only [w] using rooftop_add_const_le_obstacles
      hn omega theta phi u v hphi hu hv C
  have hwphi : w ≤ phi := hobs.1.trans hu.le_reference
  have hlower : diagonalPotentialMass theta phi hphi.plurisubharmonic ≤
      diagonalPotentialMass theta w hw := by
    simpa only [w] using reference_mass_le_rooftop_add_const
      hn omega theta phi u v hphi hu hv C hw hprojection
  refine ⟨(relativeFullMass_iff theta phi w hphi hw).2
    ⟨hwphi, le_antisymm ?_ hlower⟩, hobs⟩
  change MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => w)
        (fun _ => hw.1) ≤
      MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => phi)
        (fun _ => hphi.plurisubharmonic.1)
  exact MixedMass.globalMixedMass_mono hn omega (fun _ => hw)
    (fun _ => hphi.plurisubharmonic)
    (fun _ => MoreSingularOn.of_le fun x _ => hwphi x)

/-- **Xia, Proposition 3.1.24** (`xia-sgpt:page-0134`, proof on
`xia-sgpt:page-0135`).  Shifted full-mass rooftops exhaust their first
obstacle in chart-local `L¹` as the translation tends to `+∞`.  This is the
single rooftop-exhaustion input used by the general Perron endpoint theorem.

Proved here on the source's route: the family is nondecreasing, its
regularized supremum `eta` is a `theta`-PSH potential below `u` carrying the
model mass (`Pending.ShiftedRooftopLimit`), Corollary 3.1.1 makes `theta^n_eta`
vanish on `{eta < u}` and the domination principle Theorem 2.4.5 upgrades this
to `eta = u` (`Pending.ShiftedRooftopContact`), and an increasing family with
regularized limit `u` converges to `u` chart-locally in `L¹`
(`Pending.IncreasingThetaPshChartL1`).  The only unproved input in that chain
is Corollary 3.1.1 itself. -/
theorem relativeFullMass_rooftop_add_const_tendsto [BorelSpace M]
    [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    ManifoldL1LocallyTendsto (n := n)
      (fun C : ℝ => rooftopEnvelope theta.val
        (fun x => min (u x) (v x + (C : EReal)))) atTop u := by
  have hu' : IsThetaPshPotential theta.val u := hu.plurisubharmonic
  have hv' : IsThetaPshPotential theta.val v := hv.plurisubharmonic
  have hphi0 : phi ≤ 0 := by
    rw [hphi.envelope_eq]
    exact singularityEnvelope_le_zero theta.val phi
  have hw : ∀ C : ℝ, IsThetaPshPotential theta.val
      (ShiftedRooftopLimit.shiftedRooftop theta u v C) := fun C =>
    isThetaPshPotential_rooftop_add_const hn omega theta phi u v hphi hu hv C
  have hle : ∀ C : ℝ,
      ShiftedRooftopLimit.shiftedRooftop theta u v C ≤ u := fun C =>
    (rooftop_add_const_le_obstacles hn omega theta phi u v hphi hu hv C).1
  have humass : diagonalPotentialMass theta u hu' =
      diagonalPotentialMass theta phi hphi.plurisubharmonic :=
    ((relativeFullMass_iff theta phi u hphi hu').1 hu).2
  have hwmass : ∀ j : ℕ, diagonalPotentialMass theta
      (ShiftedRooftopLimit.shiftedRooftop theta u v (j : ℝ)) (hw (j : ℝ)) =
        diagonalPotentialMass theta phi hphi.plurisubharmonic := by
    intro j
    have hfull := (relativeFullMass_rooftop_add_const hn omega theta phi u v
      hphi hu hv (j : ℝ) hprojection).1
    exact ((relativeFullMass_iff theta phi _ hphi (hw (j : ℝ))).1 hfull).2
  have heq : ShiftedRooftopLimit.shiftedRooftopLimit theta u v = u :=
    ShiftedRooftopContact.shiftedRooftopLimit_eq_of_mass hn omega theta
      hphi.plurisubharmonic hphi0 hphi.positive_mass hu' hu.le_reference humass
      hv' hw hwmass
  exact
    IncreasingThetaPshChartL1.manifoldL1LocallyTendsto_real_of_monotone_uscRegularization
      hw (fun C => (hle C).trans (hu.le_reference.trans hphi0))
      (ShiftedRooftopLimit.shiftedRooftop_monotone theta u v) hu' heq

/-- The unshifted rooftop specialization, including the two obstacle
inequalities needed for Perron lower bounds. -/
theorem relativeFullMass_rooftop [BorelSpace M] [ConnectedSpace M]
    [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi)
    (hprojection : RooftopMassDiamondReduction.EnvelopeLatticeMassReduction omega theta) :
    let w := rooftopEnvelope theta.val (fun x => min (u x) (v x))
    RelativeFullMass theta phi w hphi ∧ w ≤ u ∧ w ≤ v := by
  simpa using relativeFullMass_rooftop_add_const hn omega theta phi u v
    hphi hu hv 0 hprojection

/-- Full mass is closed under singularity-order interpolation between a
full-mass potential and the normalized model potential.  This is the
full-mass case of Xia, Proposition 3.1.22, obtained from mixed total-mass
monotonicity; no new analytic assumption is introduced here. -/
theorem RelativeFullMass.of_singularity_between [BorelSpace M]
    [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal}
    {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi)
    (hv : IsThetaPshPotential theta.val v)
    (huv : MoreSingularOn u v univ)
    (hvphi : MoreSingularOn v phi univ) (hvle : v ≤ phi) :
    RelativeFullMass theta phi v hphi := by
  rcases hu with ⟨hupsh, _, humass⟩
  apply (relativeFullMass_iff theta phi v hphi hv).2
  refine ⟨hvle, le_antisymm ?_ ?_⟩
  · change MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => v)
        (fun _ => hv.1) ≤
      MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => phi)
        (fun _ => hphi.plurisubharmonic.1)
    exact MixedMass.globalMixedMass_mono hn omega (fun _ => hv)
      (fun _ => hphi.plurisubharmonic)
      (fun _ => hvphi)
  · calc
      diagonalPotentialMass theta phi hphi.plurisubharmonic =
          diagonalPotentialMass theta u hupsh := humass.symm
      _ ≤ diagonalPotentialMass theta v hv := by
        change MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => u)
              (fun _ => hupsh.1) ≤
            MixedMass.globalMixedMass (fun _ : Fin n => theta) (fun _ => v)
              (fun _ => hv.1)
        exact MixedMass.globalMixedMass_mono hn omega (fun _ => hupsh)
          (fun _ => hv) (fun _ => huv)

/-- Pointwise order is the most common normalized form of the preceding
singularity-order interpolation principle. -/
theorem RelativeFullMass.of_between [BorelSpace M] [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal}
    {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi)
    (hv : IsThetaPshPotential theta.val v)
    (huv : u ≤ v) (hvphi : v ≤ phi) :
    RelativeFullMass theta phi v hphi :=
  hu.of_singularity_between hn omega hv
    (MoreSingularOn.of_le fun x _ => huv x)
    (MoreSingularOn.of_le fun x _ => hvphi x) hvphi

/-- The pointwise maximum of two normalized relative full-mass potentials is
again relative full mass.  This is the max-side input for the rooftop
mass-diamond route; it follows directly from the proved `of_between`
interpolation, independently of that diamond inequality. -/
theorem RelativeFullMass.max [BorelSpace M] [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {phi u v : M → EReal}
    {hphi : IsModelPotential theta phi}
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) :
    RelativeFullMass theta phi (fun x => max (u x) (v x)) hphi := by
  apply hu.of_between hn omega
  · exact IsThetaPshPotential.max hu.plurisubharmonic hv.plurisubharmonic
  · exact fun x => le_max_left _ _
  · exact fun x => max_le (hu.le_reference x) (hv.le_reference x)

/-- **Common-barrier rooftop closure.**  A concrete relative full-mass
potential below both shifted obstacles is itself a rooftop competitor.  It
therefore gives nonemptiness, and the existing local regularization theorem
makes the rooftop theta-PSH.  The rooftop then lies between this barrier and
the reference potential, so full mass follows from the proved
singularity-order interpolation theorem.  This isolates the remaining
unconditional rooftop issue to constructing such a common full-mass lower
barrier. -/
theorem relativeFullMass_rooftop_add_const_of_common_lower [BorelSpace M]
    [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v w : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ)
    (hw : RelativeFullMass theta phi w hphi)
    (hwu : w ≤ u) (hwv : w ≤ fun x => v x + (C : EReal)) :
    let r := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    RelativeFullMass theta phi r hphi ∧ r ≤ u ∧
      r ≤ fun x => v x + (C : EReal) := by
  dsimp only
  let r := rooftopEnvelope theta.val
    (fun x => min (u x) (v x + (C : EReal)))
  have hr : IsThetaPshPotential theta.val r := by
    apply isThetaPshPotential_rooftop_of_nonempty
    · refine ⟨w, mem_rooftopCompetitors_of_le hw.plurisubharmonic ?_⟩
      intro x
      exact le_min (hwu x) (hwv x)
    · exact rooftopCompetitors_min_add_const_uniformlyBoundedAbove theta u v
        hu.plurisubharmonic C
  have hobs : r ≤ u ∧ r ≤ fun x => v x + (C : EReal) := by
    simpa only [r] using rooftopEnvelope_min_add_const_le_obstacles
      hu.plurisubharmonic.1 hv.plurisubharmonic.1 C
  have hwr : w ≤ r := by
    apply le_rooftopEnvelope hw.plurisubharmonic
    exact quasiEverywhere_of_forall fun x => le_min (hwu x) (hwv x)
  refine ⟨hw.of_between hn omega hr hwr (hobs.1.trans hu.le_reference), hobs⟩

/-- Ordered shifted endpoints provide the common barrier by taking it to be
the first endpoint.  Hence this ordered case of the relative rooftop theorem
needs neither the general rooftop mass-diamond inequality nor the unresolved
unconditional common-barrier construction. -/
theorem relativeFullMass_rooftop_add_const_of_le [BorelSpace M]
    [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ)
    (huv : u ≤ fun x => v x + (C : EReal)) :
    let r := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    RelativeFullMass theta phi r hphi ∧ r ≤ u ∧
      r ≤ fun x => v x + (C : EReal) := by
  simpa only using relativeFullMass_rooftop_add_const_of_common_lower
    hn omega theta phi u v u hphi hu hv C hu le_rfl huv

/-- In the ordered case the shifted rooftop is exactly the first endpoint,
so its full mass and both obstacle inequalities are inherited without a
rooftop mass comparison. -/
theorem relativeFullMass_rooftop_add_const_eq_of_le [BorelSpace M]
    [ConnectedSpace M] [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ)
    (huv : u ≤ fun x => v x + (C : EReal)) :
    let r := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    r = u ∧ RelativeFullMass theta phi r hphi ∧ r ≤ u ∧
      r ≤ fun x => v x + (C : EReal) := by
  dsimp only
  have hr := rooftopEnvelope_min_add_const_eq_of_le theta u v
    hu.plurisubharmonic hv.plurisubharmonic C huv
  refine ⟨hr, ?_, ?_, ?_⟩
  · rw [hr]
    exact hu
  · rw [hr]
  · rw [hr]
    exact huv

/-- The source integral `∫_X |phi - eta| theta_eta^n`, using zero on the
common pole locus and preserving every one-sided infinite difference as
`top`.  The measure is the actual diagonal global non-pluripolar measure. -/
def relativeFiniteEnergyIntegral (theta : ClosedRealOneOneForm n M)
    (phi eta : M → EReal) (heta : IsThetaPshPotential theta.val eta) : ENNReal :=
  ∫⁻ x, canonicalERealAbsDiff (phi x) (eta x)
    ∂ diagonalPotentialMeasure theta eta heta

theorem relativeFiniteEnergyIntegral_proof_independent
    (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (heta keta : IsThetaPshPotential theta.val eta) :
    relativeFiniteEnergyIntegral theta phi eta heta =
      relativeFiniteEnergyIntegral theta phi eta keta := by
  unfold relativeFiniteEnergyIntegral
  rw [diagonalPotentialMeasure_proof_independent heta keta]

/-- `E^1(X, theta; phi)`: relative full mass together with finiteness of the
actual pole-modified absolute-difference integral. -/
def RelativeFiniteEnergy (theta : ClosedRealOneOneForm n M)
    (phi eta : M → EReal) (hphi : IsModelPotential theta phi) : Prop :=
  RelativeFullMass theta phi eta hphi ∧
    ∃ heta : IsThetaPshPotential theta.val eta,
      relativeFiniteEnergyIntegral theta phi eta heta < ⊤

/-- An already available finite-energy conclusion for the first ordered
endpoint transfers verbatim to its shifted rooftop, because the two
potentials are equal. -/
theorem relativeFiniteEnergy_rooftop_add_const_eq_of_le [BorelSpace M]
    [ConnectedSpace M] [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi u v : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu : RelativeFiniteEnergy theta phi u hphi)
    (hv : IsThetaPshPotential theta.val v) (C : ℝ)
    (huv : u ≤ fun x => v x + (C : EReal)) :
    let r := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    r = u ∧ RelativeFiniteEnergy theta phi r hphi ∧ r ≤ u ∧
      r ≤ fun x => v x + (C : EReal) := by
  dsimp only
  have hu_psh := hu.1.plurisubharmonic
  have hr := rooftopEnvelope_min_add_const_eq_of_le theta u v hu_psh hv C huv
  refine ⟨hr, ?_, ?_, ?_⟩
  · rw [hr]
    exact hu
  · rw [hr]
  · rw [hr]
    exact huv

theorem relativeFiniteEnergy_iff (theta : ClosedRealOneOneForm n M)
    (phi eta : M → EReal) (hphi : IsModelPotential theta phi)
    (heta : IsThetaPshPotential theta.val eta) :
    RelativeFiniteEnergy theta phi eta hphi ↔
      RelativeFullMass theta phi eta hphi ∧
        relativeFiniteEnergyIntegral theta phi eta heta < ⊤ := by
  constructor
  · rintro ⟨hfull, keta, hfinite⟩
    exact ⟨hfull,
      (relativeFiniteEnergyIntegral_proof_independent theta phi eta heta keta) ▸
        hfinite⟩
  · rintro ⟨hfull, hfinite⟩
    exact ⟨hfull, heta, hfinite⟩

/-- A globally bounded canonical difference has finite energy.  This is
formulated with `canonicalERealAbsDiff`, so it assigns zero at a common pole
and still prohibits a one-sided pole through the finite bound. -/
theorem relativeFiniteEnergyIntegral_lt_top_of_canonicalERealAbsDiff_le
    [BorelSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (heta : IsThetaPshPotential theta.val eta) (C : NNReal)
    (hC : ∀ x, canonicalERealAbsDiff (phi x) (eta x) ≤ C) :
    relativeFiniteEnergyIntegral theta phi eta heta < ⊤ := by
  unfold relativeFiniteEnergyIntegral
  let _ : IsFiniteMeasure (diagonalPotentialMeasure theta eta heta) :=
    GlobalNonPluripolar.globalMixedMeasure_isFiniteMeasure omega (fun _ => heta.1)
  apply IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal
  exact ⟨C, hC⟩

/-- The bounded-canonical-difference part of the relative finite-energy class.
The full-mass hypothesis supplies the genuine theta-PSH witness, and the
previous theorem supplies integrability without assuming finite energy. -/
theorem relativeFiniteEnergy_of_fullMass_of_canonicalERealAbsDiff_le
    [BorelSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hfull : RelativeFullMass theta phi eta hphi) (C : NNReal)
    (hC : ∀ x, canonicalERealAbsDiff (phi x) (eta x) ≤ C) :
    RelativeFiniteEnergy theta phi eta hphi := by
  let heta : IsThetaPshPotential theta.val eta := hfull.plurisubharmonic
  exact ⟨hfull, heta,
    relativeFiniteEnergyIntegral_lt_top_of_canonicalERealAbsDiff_le
      omega theta phi eta heta C hC⟩

/-- A finite two-sided sandwich controls the canonical difference, including
the common-pole branch.  This is kept local because the public consequences
below express it through singularity type. -/
private theorem canonicalERealAbsDiff_le_of_relative_sandwich
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

omit [MeasurableSpace M] [CompactSpace M] in
/-- Equal additive singularity type with a genuine theta-PSH reference gives
a uniform finite bound on the canonical absolute difference.  The proof keeps
the common-pole value at zero and uses the two comparison constants only on
the finite branch. -/
theorem canonicalERealAbsDiff_bounded_of_sameSingularityTypeOn
    (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi)
    (hsing : SameSingularityTypeOn eta phi univ) :
    ∃ R : NNReal, ∀ x, canonicalERealAbsDiff (phi x) (eta x) ≤ R := by
  rcases hsing.1 with ⟨C, hC⟩
  rcases hsing.2 with ⟨D, hD⟩
  let R : NNReal := ⟨|C| + |D|, by positivity⟩
  refine ⟨R, fun x => ?_⟩
  apply canonicalERealAbsDiff_le_of_relative_sandwich
    (hphi.quasiPshPotential.1.ne_top x) R
  · apply (EReal.addLECancellable_coe (R : ℝ)).add_le_add_iff_right.mp
    calc
      (phi x + ((-(R : ℝ) : ℝ) : EReal)) + ((R : ℝ) : EReal) = phi x := by
        rw [add_assoc, ← EReal.coe_add]
        simp
      _ ≤ eta x + (D : EReal) := hD x (mem_univ x)
      _ ≤ eta x + ((R : ℝ) : EReal) :=
        add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by
          change D ≤ |C| + |D|
          linarith [le_abs_self D, abs_nonneg C]))
  · exact (hC x (mem_univ x)).trans
      (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by
        change C ≤ |C| + |D|
        linarith [le_abs_self C, abs_nonneg D])))

/-- A relative full-mass potential lying above a same-singularity-type lower
barrier has the reference's additive singularity type.  This is the order
bridge used by rooftop and finite-geodesic lower-barrier arguments. -/
theorem sameSingularityTypeOn_of_relativeFullMass_of_common_lower
    (theta : ClosedRealOneOneForm n M) (phi eta w : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hfull : RelativeFullMass theta phi eta hphi)
    (hweta : w ≤ eta) (hwsing : SameSingularityTypeOn w phi univ) :
    SameSingularityTypeOn eta phi univ := by
  constructor
  · exact MoreSingularOn.of_le fun x _ => hfull.le_reference x
  · rcases hwsing.2 with ⟨D, hD⟩
    exact ⟨D, fun x hx => (hD x hx).trans (add_le_add (hweta x) le_rfl)⟩

/-- Full mass plus the reference's bounded additive singularity type gives
relative finite energy without assuming an energy integral. -/
theorem relativeFiniteEnergy_of_fullMass_of_sameSingularityType
    [BorelSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (hphi : IsModelPotential theta phi) (hfull : RelativeFullMass theta phi eta hphi)
    (hsing : SameSingularityTypeOn eta phi univ) :
    RelativeFiniteEnergy theta phi eta hphi := by
  rcases canonicalERealAbsDiff_bounded_of_sameSingularityTypeOn theta phi eta
    hphi.plurisubharmonic hsing with ⟨R, hR⟩
  exact relativeFiniteEnergy_of_fullMass_of_canonicalERealAbsDiff_le
    omega theta phi eta hphi hfull R hR

/-- A same-singularity-type common lower barrier upgrades a relative full-mass
potential to relative finite energy.  Thus a full-mass rooftop or Perron slice
can use any already-constructed common lower barrier without invoking the
unresolved general rooftop mass or moving-measure energy estimates. -/
theorem relativeFiniteEnergy_of_fullMass_of_common_lower_of_sameSingularityType
    [BorelSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi eta w : M → EReal)
    (hphi : IsModelPotential theta phi) (hfull : RelativeFullMass theta phi eta hphi)
    (hweta : w ≤ eta) (hwsing : SameSingularityTypeOn w phi univ) :
    RelativeFiniteEnergy theta phi eta hphi := by
  exact relativeFiniteEnergy_of_fullMass_of_sameSingularityType
    omega theta phi eta hphi hfull
    (sameSingularityTypeOn_of_relativeFullMass_of_common_lower
      theta phi eta w hphi hfull hweta hwsing)

/-- A shifted rooftop above a common relative full-mass lower barrier has
finite relative energy when the barrier has the model singularity type.  The
obstacle inequalities are retained for later Perron applications.  This is a
conditional closure theorem: it does not use the unresolved general rooftop
mass-diamond inequality or construct the common barrier. -/
theorem relativeFiniteEnergy_rooftop_add_const_of_common_lower_of_sameSingularityType
    [BorelSpace M] [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v w : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ)
    (hw : RelativeFullMass theta phi w hphi)
    (hwu : w ≤ u) (hwv : w ≤ fun x => v x + (C : EReal))
    (hwsing : SameSingularityTypeOn w phi univ) :
    let r := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    RelativeFiniteEnergy theta phi r hphi ∧ r ≤ u ∧
      r ≤ fun x => v x + (C : EReal) := by
  dsimp only
  let r := rooftopEnvelope theta.val
    (fun x => min (u x) (v x + (C : EReal)))
  rcases relativeFullMass_rooftop_add_const_of_common_lower
    hn omega theta phi u v w hphi hu hv C hw hwu hwv with ⟨hr, hru, hrv⟩
  have hwr : w ≤ r := by
    apply le_rooftopEnvelope hw.plurisubharmonic
    exact quasiEverywhere_of_forall fun x => le_min (hwu x) (hwv x)
  have hrsing : SameSingularityTypeOn r phi univ :=
    sameSingularityTypeOn_of_relativeFullMass_of_common_lower
      theta phi r w hphi hr hwr hwsing
  exact ⟨relativeFiniteEnergy_of_fullMass_of_sameSingularityType
    omega theta phi r hphi hr hrsing, hru, hrv⟩

/-- In the ordered shifted case the first endpoint is the common barrier, so
its model singularity type gives finite energy for the rooftop without a
separate barrier witness. -/
theorem relativeFiniteEnergy_rooftop_add_const_of_le_of_sameSingularityType
    [BorelSpace M] [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M)
    (phi u v : M → EReal) (hphi : IsModelPotential theta phi)
    (hu : RelativeFullMass theta phi u hphi)
    (hv : RelativeFullMass theta phi v hphi) (C : ℝ)
    (huv : u ≤ fun x => v x + (C : EReal))
    (husing : SameSingularityTypeOn u phi univ) :
    let r := rooftopEnvelope theta.val
      (fun x => min (u x) (v x + (C : EReal)))
    RelativeFiniteEnergy theta phi r hphi ∧ r ≤ u ∧
      r ≤ fun x => v x + (C : EReal) := by
  simpa only using
    relativeFiniteEnergy_rooftop_add_const_of_common_lower_of_sameSingularityType
      hn omega theta phi u v u hphi hu hv C hu le_rfl huv husing

/-- A potential of bounded additive singularity type admits a finite downward
normalization in the relative full-mass class.  The translate is required:
`RelativeEInfinity` alone does not impose the normalization `eta ≤ phi` on
the original potential. -/
theorem exists_relativeFullMass_sub_const_of_relativeEInfinity
    [BorelSpace M] [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (hphi : IsModelPotential theta phi) (heta : RelativeEInfinity theta phi eta) :
    ∃ C : ℝ, RelativeFullMass theta phi
      (fun x => eta x - (C : EReal)) hphi ∧
      SameSingularityTypeOn (fun x => eta x - (C : EReal)) phi univ := by
  rcases heta.sameSingularityType.1 with ⟨C, hC⟩
  let etaC : M → EReal := fun x => eta x - (C : EReal)
  have hetaC : IsThetaPshPotential theta.val etaC := by
    exact heta.plurisubharmonic.sub_const C
  have hetaCphi : etaC ≤ phi := by
    intro x
    apply (EReal.addLECancellable_coe C).add_le_add_iff_right.mp
    calc
      (etaC x + (C : EReal)) = eta x := by
        dsimp only [etaC]
        rw [sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add]
        simp
      _ ≤ phi x + (C : EReal) := hC x (mem_univ x)
  have hetaCeta : SameSingularityTypeOn etaC eta univ := by
    simpa only [etaC, sub_eq_add_neg, EReal.coe_neg] using
      (sameSingularityTypeOn_add_const eta univ (-C))
  have hetaCsing : SameSingularityTypeOn etaC phi univ :=
    hetaCeta.trans heta.sameSingularityType
  have hphiFull : RelativeFullMass theta phi phi hphi :=
    ⟨hphi.plurisubharmonic, le_rfl, rfl⟩
  have hfull : RelativeFullMass theta phi etaC hphi :=
    hphiFull.of_singularity_between hn omega hetaC hetaCsing.2 hetaCsing.1 hetaCphi
  exact ⟨C, hfull, hetaCsing⟩

/-- The normalized translate supplied by bounded additive singularity type
belongs to the relative finite-energy class.  No claim is made for the
untranslated potential, whose pointwise normalization may fail. -/
theorem exists_relativeFiniteEnergy_sub_const_of_relativeEInfinity
    [BorelSpace M] [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (hphi : IsModelPotential theta phi) (heta : RelativeEInfinity theta phi eta) :
    ∃ C : ℝ, RelativeFiniteEnergy theta phi
      (fun x => eta x - (C : EReal)) hphi := by
  rcases exists_relativeFullMass_sub_const_of_relativeEInfinity
    hn omega theta phi eta hphi heta with ⟨C, hfull, hsing⟩
  exact ⟨C, relativeFiniteEnergy_of_fullMass_of_sameSingularityType
    omega theta phi (fun x => eta x - (C : EReal)) hphi hfull hsing⟩

/-- **Normalized full mass for every closed bounded finite-geodesic slice.**
The bounded-slice package supplies a common singularity type at every time in
`[0,1]`; a finite downward translation then places that closed slice in the
normalized relative full-mass class.  This does not assert the unshifted slice
is normalized. -/
theorem exists_relativeFullMass_sub_const_closedSubgeodesicSlice_finiteGeodesic_of_interior
    [BorelSpace M] [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ C : ℝ, RelativeFullMass theta phi
      (fun x => closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ t x -
        (C : EReal)) hphi ∧
      SameSingularityTypeOn
        (fun x => closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ t x -
          (C : EReal)) phi univ :=
  exists_relativeFullMass_sub_const_of_relativeEInfinity
    hn omega theta phi
    (closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ t) hphi
    (relativeEInfinity_closedSubgeodesicSlice_finiteGeodesic_of_interior
      theta phi u₀ u₁ hphi hu₀ hu₁ hinterior ht)

/-- **Normalized finite energy for every closed bounded finite-geodesic slice.**
This is the finite-energy consumer of the explicit-interior bounded package:
each closed slice admits some finite downward normalization in the relative
finite-energy class. -/
theorem exists_relativeFiniteEnergy_sub_const_closedSubgeodesicSlice_finiteGeodesic_of_interior
    [BorelSpace M] [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ C : ℝ, RelativeFiniteEnergy theta phi
      (fun x => closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ t x -
        (C : EReal)) hphi :=
  exists_relativeFiniteEnergy_sub_const_of_relativeEInfinity
    hn omega theta phi
    (closedSubgeodesicSlice (finiteGeodesic theta.val u₀ u₁) u₀ u₁ t) hphi
    (relativeEInfinity_closedSubgeodesicSlice_finiteGeodesic_of_interior
      theta phi u₀ u₁ hphi hu₀ hu₁ hinterior ht)

/-- **Normalized full mass for an actual interior bounded finite-geodesic slice.**
This is the interior-slice spelling of the closed-slice normalization package,
for consumers formulated directly in terms of `finiteGeodesic`. -/
theorem exists_relativeFullMass_sub_const_finiteGeodesic_of_interior
    [BorelSpace M] [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, RelativeFullMass theta phi
      (fun x => finiteGeodesic theta.val u₀ u₁ t x - (C : EReal)) hphi ∧
      SameSingularityTypeOn
        (fun x => finiteGeodesic theta.val u₀ u₁ t x - (C : EReal)) phi univ := by
  simpa only [closedSubgeodesicSlice_eq_curve ht] using
    (exists_relativeFullMass_sub_const_closedSubgeodesicSlice_finiteGeodesic_of_interior
      hn omega theta phi u₀ u₁ hphi hu₀ hu₁ hinterior
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

/-- **Normalized finite energy for an actual interior bounded finite-geodesic slice.**
This is the direct finite-energy form used by arguments whose input is the
Perron slice itself rather than its closed-endpoint extension. -/
theorem exists_relativeFiniteEnergy_sub_const_finiteGeodesic_of_interior
    [BorelSpace M] [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, RelativeFiniteEnergy theta phi
      (fun x => finiteGeodesic theta.val u₀ u₁ t x - (C : EReal)) hphi := by
  simpa only [closedSubgeodesicSlice_eq_curve ht] using
    (exists_relativeFiniteEnergy_sub_const_closedSubgeodesicSlice_finiteGeodesic_of_interior
      hn omega theta phi u₀ u₁ hphi hu₀ hu₁ hinterior
      ⟨le_of_lt ht.1, le_of_lt ht.2⟩)

/-- **Joint normalized finite-energy bridge for an interior bounded
finite-geodesic slice.**  The one translation constant is retained together
with its full-mass and additive-singularity witnesses, so a consumer can use
the normalized slice without silently replacing it by the unshifted Perron
slice.  In particular, this does not instantiate finite-geodesic results whose
input is an unshifted normalized curve. -/
theorem exists_relativeFiniteEnergy_with_fullMass_sub_const_finiteGeodesic_of_interior
    [BorelSpace M] [ConnectedSpace M] [Nonempty M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) (phi u₀ u₁ : M → EReal)
    (hphi : IsModelPotential theta phi)
    (hu₀ : RelativeEInfinity theta phi u₀)
    (hu₁ : RelativeEInfinity theta phi u₁)
    (hinterior : IsSubgeodesicInterior theta.val (finiteGeodesic theta.val u₀ u₁))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ,
      RelativeFiniteEnergy theta phi
        (fun x => finiteGeodesic theta.val u₀ u₁ t x - (C : EReal)) hphi ∧
      RelativeFullMass theta phi
        (fun x => finiteGeodesic theta.val u₀ u₁ t x - (C : EReal)) hphi ∧
      SameSingularityTypeOn
        (fun x => finiteGeodesic theta.val u₀ u₁ t x - (C : EReal)) phi univ := by
  rcases exists_relativeFullMass_sub_const_finiteGeodesic_of_interior
    hn omega theta phi u₀ u₁ hphi hu₀ hu₁ hinterior ht with ⟨C, hfull, hsing⟩
  exact ⟨C,
    relativeFiniteEnergy_of_fullMass_of_sameSingularityType
      omega theta phi
      (fun x => finiteGeodesic theta.val u₀ u₁ t x - (C : EReal)) hphi hfull hsing,
    hfull, hsing⟩

theorem RelativeFiniteEnergy.fullMass {theta : ClosedRealOneOneForm n M}
    {phi eta : M → EReal} {hphi : IsModelPotential theta phi}
    (h : RelativeFiniteEnergy theta phi eta hphi) :
    RelativeFullMass theta phi eta hphi :=
  h.1

theorem RelativeFiniteEnergy.relativePSH {theta : ClosedRealOneOneForm n M}
    {phi eta : M → EReal} {hphi : IsModelPotential theta phi}
    (h : RelativeFiniteEnergy theta phi eta hphi) :
    RelativePSH theta phi eta :=
  h.fullMass.relativePSH

theorem relativeFiniteEnergy_reference_proof_independent
    (theta : ClosedRealOneOneForm n M) (phi eta : M → EReal)
    (hphi kphi : IsModelPotential theta phi) :
    RelativeFiniteEnergy theta phi eta hphi ↔
      RelativeFiniteEnergy theta phi eta kphi := by
  exact and_congr
    (relativeFullMass_reference_proof_independent theta phi eta hphi kphi)
    Iff.rfl

end

end SGPT.Foundations.Analysis.Pending
