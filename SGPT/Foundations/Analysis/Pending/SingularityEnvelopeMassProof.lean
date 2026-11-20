import SGPT.Foundations.Analysis.Pending.IGoodMassReduction
import SGPT.Foundations.Analysis.Pending.IncreasingLimitMass

set_option autoImplicit false

/-!
# Mass of the P-envelope

Toward `SingularityEnvelopeMassPreserving` (Xia, Proposition 3.1.3,
`xia-sgpt:page-0100`).  The source proof has two inputs:

1. the truncated envelopes `(φ + C) ∧ V_θ` have the singularity type of `φ`,
   hence the mass of `φ` by the monotonicity theorem (Theorem 2.4.3);
2. total non-pluripolar mass is continuous along increasing sequences with
   regularized limit (Corollary 2.4.1, from DDNL, Theorem 2.6).

Input 1 is proved below from `globalMixedMass_mono` on a compact Kähler
manifold in positive dimension, together with `mass φ ≤ mass P_θ[φ]`.  Input 2,
in the one inequality that (3.6) uses, is the statement `IncreasingLimitMassLe`,
proved in `Pending.IncreasingLimitMass` from the local semicontinuity theorem
`IncreasingTruncationLimit.truncationLimitMeasure_le_liminf_of_monotone` (DDNL,
Theorem 2.6, local form), itself proved from the Bedford--Taylor convergence theorem
for increasing sequences (`Pending.BedfordTaylorIncreasing`).
-/

open Set

namespace SGPT.Foundations.Analysis.Pending

noncomputable section

open FirstPass
open FirstPass.PositiveClasses
open DiagonalMass MixedMass

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

omit [Nonempty M] in
/-- Diagonal mass is monotone in the singularity order, in every dimension. -/
theorem diagonalPotentialMass_mono_of_kahler (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (huv : MoreSingularOn u v univ) :
    diagonalPotentialMass theta u hu ≤ diagonalPotentialMass theta v hv :=
  MassFromBoundedDifference.globalMixedMeasure_univ_le_of_moreSingular
    (θ := fun _ => theta) (fun _ => hu) (fun _ => hv) (fun _ => huv)
    fun _ _ ha hb _ ht hab hba =>
      (MixedMassBoundedDifference.globalMixedMeasure_univ_eq_of_le_add omega ha hb ht hab
        hba).le

omit [Nonempty M] in
/-- Diagonal mass is monotone in the singularity order. -/
theorem diagonalPotentialMass_mono (_hn : 0 < n) (omega : KahlerBackground n M)
    {theta : ClosedRealOneOneForm n M} {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (huv : MoreSingularOn u v univ) :
    diagonalPotentialMass theta u hu ≤ diagonalPotentialMass theta v hv :=
  diagonalPotentialMass_mono_of_kahler omega hu hv huv

omit [MeasurableSpace M] [BorelSpace M] in
/-- A genuine theta-PSH potential is more singular than its P-envelope. -/
theorem moreSingularOn_singularityEnvelope {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (hφ : IsThetaPshPotential θ φ) :
    MoreSingularOn φ (singularityEnvelope θ φ) univ := by
  obtain ⟨C, hC⟩ := hφ.exists_normalized_singularityCompetitor
  have hle := le_singularityEnvelope hC.1.1 hC.1.2 hC.2
  refine ⟨C, fun x _ => ?_⟩
  calc φ x = (φ x - (C : EReal)) + (C : EReal) := by
        rw [EReal.sub_add_cancel]
    _ ≤ singularityEnvelope θ φ x + (C : EReal) := add_le_add_left (hle x) _

/-- The easy half of Xia, Proposition 3.1.3: `∫ θ_φ^n ≤ ∫ θ_{P_θ[φ]}^n`. -/
theorem diagonalPotentialMass_le_singularityEnvelope (_hn : 0 < n)
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    {phi : M → EReal} (hphi : IsThetaPshPotential theta.val phi)
    (hP : IsThetaPshPotential theta.val (singularityEnvelope theta.val phi)) :
    diagonalPotentialMass theta phi hphi ≤
      diagonalPotentialMass theta (singularityEnvelope theta.val phi) hP :=
  diagonalPotentialMass_mono_of_kahler omega hphi hP (moreSingularOn_singularityEnvelope hphi)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- If `φ - C` is normalized, every truncated envelope at a level `≥ -C` has a
competitor, namely `φ - C`. -/
theorem sub_const_mem_truncatedSingularityCompetitors {θ : SmoothRealForm n M 2}
    {φ : M → EReal} {C a : ℝ} (hC : (fun x => φ x - (C : EReal)) ∈ thetaPshCompetitors θ)
    (ha : -C ≤ a) :
    (fun x => φ x - (C : EReal)) ∈ truncatedSingularityCompetitors θ φ a := by
  refine ⟨hC, fun x => ?_⟩
  show φ x - (C : EReal) ≤ _
  rw [sub_eq_add_neg, ← EReal.coe_neg]
  exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ha)

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- For a level `a ≥ -C`, the truncated envelope `(φ + a) ∧ V_θ` has the
singularity type of `φ`. -/
theorem sameSingularityTypeOn_truncatedSingularityEnvelope {θ : SmoothRealForm n M 2}
    {φ : M → EReal} (hφ : IsThetaPshPotential θ φ) {C a : ℝ}
    (hC : (fun x => φ x - (C : EReal)) ∈ thetaPshCompetitors θ) (ha : -C ≤ a) :
    SameSingularityTypeOn φ (truncatedSingularityEnvelope θ φ a) univ := by
  have hle := le_truncatedSingularityEnvelope hC.1 hC.2
    (sub_const_mem_truncatedSingularityCompetitors hC ha).2
  refine ⟨⟨C, fun x _ => ?_⟩, ⟨a, fun x _ =>
    truncatedSingularityEnvelope_le_add hφ.1.quasiPlurisubharmonic θ a x⟩⟩
  calc φ x = (φ x - (C : EReal)) + (C : EReal) := by
        rw [EReal.sub_add_cancel]
    _ ≤ truncatedSingularityEnvelope θ φ a x + (C : EReal) := add_le_add_left (hle x) _

/-- Xia, Corollary 2.4.1, in the one inequality used for (3.6), diagonal total
mass, sequences: the regularized limit of an increasing sequence of normalized
potentials carries no more mass than the sequence.  Proved as
`increasingLimitMassLe` below. -/
def IncreasingLimitMassLe (theta : ClosedRealOneOneForm n M) : Prop :=
  ∀ (u : ℕ → M → EReal) (hu : ∀ j, IsThetaPshPotential theta.val (u j)),
    Monotone u → (∀ j, u j ≤ 0) →
    ∀ hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, u j)),
      diagonalPotentialMass theta (uscRegularization (⨆ j, u j)) hU ≤
        ⨆ j, diagonalPotentialMass theta (u j) (hu j)

/-- Xia, Proposition 3.1.3 (diagonal case) on a compact Kähler manifold, in every
dimension, from the increasing-limit mass inequality. -/
theorem singularityEnvelopeMassPreserving_of_increasingLimitMassLe_of_kahler
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hinc : IncreasingLimitMassLe theta) :
    SingularityEnvelopeMassPreserving theta := by
  intro phi hphi hP
  refine le_antisymm ?_ (diagonalPotentialMass_mono_of_kahler omega hphi hP
    (moreSingularOn_singularityEnvelope hphi))
  obtain ⟨C, hC⟩ := hphi.exists_normalized_sub_const
  have hlocal := hphi.1.hasSmoothLocalPotentials
  have hlevel : ∀ j : ℕ, -C ≤ -C + j := fun j => le_add_of_nonneg_right j.cast_nonneg
  let u : ℕ → M → EReal := fun j => truncatedSingularityEnvelope theta.val phi (-C + j)
  have hu : ∀ j, IsThetaPshPotential theta.val (u j) := fun j =>
    truncatedSingularityEnvelope_isThetaPshPotential hlocal
      ⟨_, sub_const_mem_truncatedSingularityCompetitors hC (hlevel j)⟩
  have hmono : Monotone u := fun i j hij =>
    truncatedSingularityEnvelope_mono _ _ (by simpa using hij)
  have heq := singularityEnvelope_eq_uscRegularization_iSup_truncated theta.val phi (-C)
  have hU : IsThetaPshPotential theta.val (uscRegularization (⨆ j, u j)) := heq ▸ hP
  calc diagonalPotentialMass theta (singularityEnvelope theta.val phi) hP
      = diagonalPotentialMass theta (uscRegularization (⨆ j, u j)) hU :=
        diagonalPotentialMass_congr heq hP hU
    _ ≤ ⨆ j, diagonalPotentialMass theta (u j) (hu j) :=
        hinc u hu hmono (fun j => truncatedSingularityEnvelope_le_zero _ _ _) hU
    _ ≤ diagonalPotentialMass theta phi hphi := iSup_le fun j =>
        diagonalPotentialMass_mono_of_kahler omega (hu j) hphi
          (sameSingularityTypeOn_truncatedSingularityEnvelope hphi hC (hlevel j)).2

/-- Xia, Proposition 3.1.3 (diagonal case) on a compact Kähler manifold in
positive dimension, from the increasing-limit mass inequality. -/
theorem singularityEnvelopeMassPreserving_of_increasingLimitMassLe (_hn : 0 < n)
    (omega : KahlerBackground n M) {theta : ClosedRealOneOneForm n M}
    (hinc : IncreasingLimitMassLe theta) :
    SingularityEnvelopeMassPreserving theta :=
  singularityEnvelopeMassPreserving_of_increasingLimitMassLe_of_kahler omega hinc

omit [Nonempty M] in
/-- `IncreasingLimitMassLe` holds in every background, from the local
semicontinuity theorem of `Pending.IncreasingTruncationLimit`. -/
theorem increasingLimitMassLe (theta : ClosedRealOneOneForm n M) :
    IncreasingLimitMassLe theta :=
  fun u hu hmono _ hU =>
    IncreasingLimitMass.diagonalPotentialMass_le_iSup_of_monotone u hu hmono hU

/-- Xia, Proposition 3.1.3 (diagonal case) on a compact Kähler manifold. -/
theorem singularityEnvelopeMassPreserving (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) : SingularityEnvelopeMassPreserving theta :=
  singularityEnvelopeMassPreserving_of_increasingLimitMassLe_of_kahler omega
    (increasingLimitMassLe theta)

end

end SGPT.Foundations.Analysis.Pending
