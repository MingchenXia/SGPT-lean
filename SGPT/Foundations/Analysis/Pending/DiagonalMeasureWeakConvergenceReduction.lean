import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondLimit
import SGPT.Foundations.Analysis.Pending.DecreasingRooftopTailEnvelope

/-!
# Reductions for the weak diagonal-measure step in Xia's Corollary 2.4.2

This module contains the parts of the sequential argument in Xia's Corollary
2.4.2 that do not use its missing global weak-convergence theorem.  For a
nonpositive theta-PSH sequence `u`, its regularized tail upper envelope
`psi_k = (sup_{j >= k} u_j)^*` is constructed in
`DecreasingRooftopTailEnvelope`.  Here we prove:

* contact mass can only increase when `u_k` is replaced by `psi_k`;
* a measure carried by the zero-contact locus has total mass equal to contact
  mass; and
* any typed weighted-diagonal-measure convergence conclusion gives the desired
  contact-mass limsup bound by pure order-limit bookkeeping.

The last hypothesis is intentionally the exact output expected from the
unformalized weak convergence of the diagonal measures.  No weak convergence
principle, source interface, or new axiom is introduced here.

Source: Xia, *Singularities in Global Pluripotential Theory*, Corollary 2.4.2
(`xia-sgpt:page-0077`--`xia-sgpt:page-0078`).
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.DiagonalMeasureWeakConvergenceReduction

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
open SGPT.Foundations.Analysis.Pending.RooftopMassDiamondLimit
open SGPT.Foundations.Analysis.Pending.DecreasingRooftopTailEnvelope

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- A tail envelope remains below any upper-semicontinuous common upper bound
of its original sequence. -/
theorem tailEnvelope_le_of_forall_le
    {u : ℕ → M → EReal} {v : M → EReal}
    (huv : ∀ j, u j ≤ v) (hv : UpperSemicontinuous v) (k : ℕ) :
    tailEnvelope u k ≤ v := by
  apply uscRegularization_le hv
  exact sSup_le fun w hw => by
    obtain ⟨j, _hj, rfl⟩ := hw
    exact huv j

/-- Contact mass is monotone under an ordered replacement of nonpositive
theta-PSH potentials.  The sole analytic input is Xia's already-proved
contact-measure comparison. -/
theorem contactMass_le_contactMass_of_le_of_nonpositive
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    (hv0 : ∀ x, v x ≤ 0) (huv : u ≤ v) :
    contactMass theta u hu ≤ contactMass theta v hv := by
  let E : Set M := {x | u x = 0}
  let F : Set M := {x | v x = 0}
  have hEmeas : MeasurableSet E := by
    exact measurableSet_eq_fun
      hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable measurable_const
  have hcontact : E ∩ {x | u x = v x} = E := by
    ext x
    constructor
    · exact fun hx => hx.1
    · intro hx
      refine ⟨hx, le_antisymm (huv x) ?_⟩
      change u x = 0 at hx
      rw [hx]
      exact hv0 x
  have hsub : E ⊆ F := by
    intro x hx
    change u x = 0 at hx
    change v x = 0
    exact le_antisymm (hv0 x) (by simpa [hx] using huv x)
  have hle := contact_measure_le omega hu hv huv hEmeas
  change diagonalPotentialMeasure theta u hu E ≤ diagonalPotentialMeasure theta v hv F
  calc
    diagonalPotentialMeasure theta u hu E =
        diagonalPotentialMeasure theta u hu (E ∩ {x | u x = v x}) := by rw [hcontact]
    _ ≤ diagonalPotentialMeasure theta v hv (E ∩ {x | u x = v x}) := hle
    _ = diagonalPotentialMeasure theta v hv E := by rw [hcontact]
    _ ≤ diagonalPotentialMeasure theta v hv F := measure_mono hsub

/-- Replacing a nonpositive sequence by its regularized tail envelopes can
only increase each contact mass. -/
theorem contactMass_le_contactMass_tailEnvelope
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (u : ℕ → M → EReal) (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hu0 : ∀ j x, u j x ≤ 0) (k : ℕ) :
    contactMass theta (u k) (hu k) ≤
      contactMass theta (tailEnvelope u k)
        (isThetaPshPotential_tailEnvelope
          (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k) := by
  apply contactMass_le_contactMass_of_le_of_nonpositive omega theta (hu k)
    (isThetaPshPotential_tailEnvelope
      (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k)
  · intro x
    exact tailEnvelope_le_of_forall_le (fun j => fun y => hu0 j y)
      upperSemicontinuous_const k x
  · exact le_tailEnvelope_self u k

/-- The limsup contact mass of the original sequence is bounded by that of its
tail envelopes.  This is Xia's tail replacement before any weak convergence
is used. -/
theorem limsup_contactMass_le_limsup_contactMass_tailEnvelope
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (u : ℕ → M → EReal) (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hu0 : ∀ j x, u j x ≤ 0) :
    limsup (fun k => contactMass theta (u k) (hu k)) atTop ≤
      limsup (fun k => contactMass theta (tailEnvelope u k)
        (isThetaPshPotential_tailEnvelope
          (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k)) atTop := by
  exact Filter.limsup_le_limsup
    (Filter.Eventually.of_forall fun k =>
      contactMass_le_contactMass_tailEnvelope omega theta u hu hu0 k)
    (by isBoundedDefault) (by isBoundedDefault)

/-- If the diagonal measure gives no mass to the strict negativity locus of a
nonpositive potential, its total diagonal mass is exactly its contact mass. -/
theorem contactMass_eq_diagonalPotentialMass_of_measure_lt_zero_eq_zero
    (theta : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hu0 : ∀ x, u x ≤ 0)
    (hneg : diagonalPotentialMeasure theta u hu {x | u x < 0} = 0) :
    contactMass theta u hu = diagonalPotentialMass theta u hu := by
  let E : Set M := {x | u x = 0}
  let N : Set M := {x | u x < 0}
  have hEmeas : MeasurableSet E := by
    exact measurableSet_eq_fun
      hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable measurable_const
  have hNmeas : MeasurableSet N := by
    exact measurableSet_lt hu.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
      measurable_const
  have hdisj : Disjoint E N := by
    refine Set.disjoint_left.mpr fun x hxE hxN => ?_
    change u x = 0 at hxE
    change u x < 0 at hxN
    exact (ne_of_lt hxN) hxE
  have hunion : E ∪ N = univ := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    exact eq_or_lt_of_le (hu0 x)
  change diagonalPotentialMeasure theta u hu E = diagonalPotentialMeasure theta u hu univ
  calc
    diagonalPotentialMeasure theta u hu E = diagonalPotentialMeasure theta u hu E +
        diagonalPotentialMeasure theta u hu N := by
          rw [hneg]
          exact (add_zero _).symm
    _ = diagonalPotentialMeasure theta u hu (E ∪ N) :=
      (measure_union hdisj hNmeas).symm
    _ = diagonalPotentialMeasure theta u hu univ := by rw [hunion]

omit [BorelSpace M] in
/-- For an antitone theta-PSH sequence the tail envelope is termwise equal to
the original sequence, hence has the same total diagonal mass. -/
theorem diagonalPotentialMass_tailEnvelope_eq_of_antitone
    (theta : ClosedRealOneOneForm n M) (u : ℕ → M → EReal)
    (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hu0 : ∀ j x, u j x ≤ 0) (hanti : Antitone u) (k : ℕ) :
    diagonalPotentialMass theta (tailEnvelope u k)
        (isThetaPshPotential_tailEnvelope
          (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k) =
      diagonalPotentialMass theta (u k) (hu k) := by
  let htail : IsThetaPshPotential theta.val (tailEnvelope u k) :=
    isThetaPshPotential_tailEnvelope
      (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k
  have heq : tailEnvelope u k = u k := tailEnvelope_eq_of_antitone
    (fun j => (hu j).1.quasiPlurisubharmonic.upperSemicontinuous) hanti k
  have htail' : IsThetaPshPotential theta.val (u k) := by
    simpa only [heq] using htail
  calc
    diagonalPotentialMass theta (tailEnvelope u k)
        (isThetaPshPotential_tailEnvelope
          (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k) =
        diagonalPotentialMass theta (tailEnvelope u k) htail := by rfl
    _ = diagonalPotentialMass theta (u k) htail' := by
      unfold diagonalPotentialMass
      exact congrArg (fun mu : Measure M => mu univ)
        (diagonalPotentialMeasure_congr htail htail' heq)
    _ = diagonalPotentialMass theta (u k) (hu k) :=
      diagonalPotentialMass_proof_independent htail' (hu k)

/-- A scalar sequence bounded pointwise by a convergent sequence has its
limsup bounded by that limit.  This is the order-theoretic end of a weak
measure convergence argument. -/
theorem limsup_le_of_forall_le_of_tendsto
    {a w : ℕ → ℝ≥0∞} {L : ℝ≥0∞}
    (hle : ∀ k, a k ≤ w k) (hlim : Tendsto w atTop (𝓝 L)) :
    limsup a atTop ≤ L := by
  calc
    limsup a atTop ≤ limsup w atTop :=
      Filter.limsup_le_limsup (Filter.Eventually.of_forall hle)
    _ = L := hlim.limsup_eq

omit [BorelSpace M] in
/-- A typed weak-convergence output for weighted diagonal measures implies the
contact-mass limsup bound.  A future global weak-convergence theorem need only
provide `hweighted`; all tail/contact/limit bookkeeping is proved here. -/
theorem contactMass_limsup_le_of_tendsto_weightedDiagonalMeasure
    (theta : ClosedRealOneOneForm n M) (u : ℕ → M → EReal)
    (hu : ∀ k, IsThetaPshPotential theta.val (u k))
    (v : M → EReal) (hv : IsThetaPshPotential theta.val v)
    (weight : ℕ → M → ℝ≥0∞) (L : ℝ≥0∞)
    (hcontrol : ∀ k, contactMass theta (u k) (hu k) ≤
      ∫⁻ x, weight k x ∂(diagonalPotentialMeasure theta (u k) (hu k)))
    (hweighted : Tendsto (fun k => ∫⁻ x, weight k x ∂
      (diagonalPotentialMeasure theta (u k) (hu k))) atTop (𝓝 L))
    (hlimit : L ≤ contactMass theta v hv) :
    limsup (fun k => contactMass theta (u k) (hu k)) atTop ≤
      contactMass theta v hv := by
  exact (limsup_le_of_forall_le_of_tendsto hcontrol hweighted).trans hlimit

/-- The full sequential reduction in the form needed by Xia's Corollary
2.4.2.  The three hypotheses labelled `hcontrol`, `hweighted`, and `hlimit`
are precisely the residual weak-diagonal-measure statement; all other steps
are internal. -/
theorem contactMass_limsup_le_of_tail_weightedDiagonalMeasure
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (u : ℕ → M → EReal) (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hu0 : ∀ j x, u j x ≤ 0)
    (v : M → EReal) (hv : IsThetaPshPotential theta.val v)
    (weight : ℕ → M → ℝ≥0∞) (L : ℝ≥0∞)
    (hcontrol : ∀ k,
      contactMass theta (tailEnvelope u k)
        (isThetaPshPotential_tailEnvelope
          (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k) ≤
      ∫⁻ x, weight k x ∂(diagonalPotentialMeasure theta (tailEnvelope u k)
        (isThetaPshPotential_tailEnvelope
          (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k)))
    (hweighted : Tendsto (fun k => ∫⁻ x, weight k x ∂
      (diagonalPotentialMeasure theta (tailEnvelope u k)
        (isThetaPshPotential_tailEnvelope
          (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k)))
      atTop (𝓝 L))
    (hlimit : L ≤ contactMass theta v hv) :
    limsup (fun k => contactMass theta (u k) (hu k)) atTop ≤
      contactMass theta v hv := by
  calc
    limsup (fun k => contactMass theta (u k) (hu k)) atTop ≤
        limsup (fun k => contactMass theta (tailEnvelope u k)
          (isThetaPshPotential_tailEnvelope
            (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k)) atTop :=
      limsup_contactMass_le_limsup_contactMass_tailEnvelope omega theta u hu hu0
    _ ≤ contactMass theta v hv :=
      contactMass_limsup_le_of_tendsto_weightedDiagonalMeasure theta
        (tailEnvelope u)
        (fun k => isThetaPshPotential_tailEnvelope
          (hu 0).1.hasSmoothLocalPotentials hu (fun j => fun x => hu0 j x) k)
        v hv weight L hcontrol hweighted hlimit

end

end SGPT.Foundations.Analysis.Pending.DiagonalMeasureWeakConvergenceReduction
