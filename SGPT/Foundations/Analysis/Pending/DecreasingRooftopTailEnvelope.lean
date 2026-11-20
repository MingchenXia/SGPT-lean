import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes
import SGPT.Foundations.Analysis.Pending.DecreasingThetaPshChartL1
import SGPT.Foundations.Analysis.Pending.RooftopMassDiamondTruncationBridge

/-!
# Decreasing tail envelopes for the rooftop limit

For a sequence of normalized theta-PSH potentials `u_j`, Xia's decreasing
argument replaces the sequence by the regularized tail upper envelopes

`psi_k = (sup_{j >= k} u_j)^*`.

This file proves the elementary envelope layer.  In particular, when the
input sequence is already antitone, the tail envelope at level `k` is exactly
`u_k`.  Thus for the finite rooftop truncations all PSH, order, and local L1
facts required by the argument are internal consequences of the existing
rooftop and decreasing-family APIs.  The remaining analytic issue is the
weak convergence of the associated diagonal measures, which is deliberately
not asserted here.

Source for the tail construction: Xia, *Singularities in Global
Pluripotential Theory*, Corollary 2.4.2 (`xia-sgpt:page-0077`).
-/

set_option autoImplicit false

open Filter Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.DecreasingRooftopTailEnvelope

open FirstPass
open SGPT.Foundations.Analysis.Pending.DecreasingThetaPshChartL1
open SGPT.Foundations.Analysis.Pending.RooftopMassDiamondTruncationBridge

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The part of a sequence starting at `k`. -/
def tailFamily (u : ℕ → M → EReal) (k : ℕ) : Set (M → EReal) :=
  {w | ∃ j : ℕ, k ≤ j ∧ w = u j}

/-- Xia's upper-semicontinuous tail upper envelope. -/
def tailEnvelope (u : ℕ → M → EReal) (k : ℕ) : M → EReal :=
  uscRegularization (sSup (tailFamily u k))

omit [TopologicalSpace M] in
theorem mem_tailFamily_self (u : ℕ → M → EReal) (k : ℕ) :
    u k ∈ tailFamily u k := ⟨k, le_rfl, rfl⟩

omit [TopologicalSpace M] in
theorem tailFamily_nonempty (u : ℕ → M → EReal) (k : ℕ) :
    (tailFamily u k).Nonempty :=
  ⟨u k, mem_tailFamily_self u k⟩

omit [TopologicalSpace M] in
theorem tailFamily_mono {u : ℕ → M → EReal} {k l : ℕ} (hkl : k ≤ l) :
    tailFamily u l ⊆ tailFamily u k := by
  rintro w ⟨j, hlj, rfl⟩
  exact ⟨j, hkl.trans hlj, rfl⟩

/-- The tail upper envelopes decrease as the tail is shortened. -/
theorem tailEnvelope_antitone (u : ℕ → M → EReal) :
    Antitone (tailEnvelope u) := by
  intro k l hkl
  apply uscRegularization_mono
  exact sSup_le_sSup (tailFamily_mono hkl)

/-- The `k`-th original term is a lower bound for its tail envelope. -/
theorem le_tailEnvelope_self (u : ℕ → M → EReal) (k : ℕ) :
    u k ≤ tailEnvelope u k := by
  exact (le_sSup (mem_tailFamily_self u k)).trans (le_uscRegularization _)

omit [TopologicalSpace M] in
theorem tailFamily_le_self_of_antitone {u : ℕ → M → EReal}
    (hanti : Antitone u) (k : ℕ) {w : M → EReal} (hw : w ∈ tailFamily u k) :
    w ≤ u k := by
  obtain ⟨j, hkj, rfl⟩ := hw
  exact hanti hkj

/-- For an antitone upper-semicontinuous sequence, regularizing the `k`-tail
does not alter its first term. -/
theorem tailEnvelope_eq_of_antitone {u : ℕ → M → EReal}
    (husc : ∀ k, UpperSemicontinuous (u k)) (hanti : Antitone u) (k : ℕ) :
    tailEnvelope u k = u k := by
  apply le_antisymm
  · apply uscRegularization_le (husc k)
    exact sSup_le fun w hw => tailFamily_le_self_of_antitone hanti k hw
  · exact le_tailEnvelope_self u k

/-- A normalized theta-PSH tail family has a normalized theta-PSH upper
envelope. -/
theorem isThetaPshPotential_tailEnvelope
    {theta : SmoothRealForm n M 2} {u : ℕ → M → EReal}
    (hlocal : HasSmoothLocalPotentials theta) (hu : ∀ j, IsThetaPshPotential theta (u j))
    (hu0 : ∀ j, u j ≤ 0) (k : ℕ) :
    IsThetaPshPotential theta (tailEnvelope u k) := by
  refine ⟨?_, ?_⟩
  · exact thetaPlurisubharmonic_uscRegularization_sSup hlocal
      (tailFamily_nonempty u k) (fun w hw => by
        obtain ⟨j, _hj, rfl⟩ := hw
        exact hu j) (fun w hw => by
          obtain ⟨j, _hj, rfl⟩ := hw
          exact hu0 j)
  · exact (hu k).2.mono (le_tailEnvelope_self u k)

/-- The tail sequence has the same chart-local `L¹` limit as an antitone
theta-PSH sequence, because its terms agree pointwise with the original
sequence. -/
theorem manifoldL1LocallyTendsto_tailEnvelope_of_antitone_iInf
    {theta : ClosedRealOneOneForm n M} {u : ℕ → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential theta.val (u j))
    (hanti : Antitone u) (hv : IsThetaPshPotential theta.val v)
    (hinf : (⨅ j : ℕ, u j) = v) :
    ManifoldL1LocallyTendsto (n := n) (tailEnvelope u) atTop v := by
  apply ManifoldL1LocallyTendsto.congr (fun k => ?_)
    (manifoldL1LocallyTendsto_of_antitone_iInf hu hanti hv hinf)
  exact (tailEnvelope_eq_of_antitone
    (fun k => (hu k).1.quasiPlurisubharmonic.upperSemicontinuous) hanti k).symm

/-- For the finite rooftop truncations, Xia's tail upper envelope is exactly
the already decreasing truncation sequence. -/
theorem tailEnvelope_modelTruncationRooftopData_eq
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (phi psi : M → EReal)
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x))) :
    tailEnvelope (modelTruncationRooftopData theta phi psi) =
      modelTruncationRooftopData theta phi psi := by
  funext k
  apply tailEnvelope_eq_of_antitone
  · intro j
    have hj : IsThetaPshPotential theta.val
        (modelTruncationRooftopData theta phi psi j) :=
      model_truncation_rooftop_isThetaPshPotential theta hphi hpsi hmax j
    exact hj.1.quasiPlurisubharmonic.upperSemicontinuous
  · exact modelTruncationRooftopData_antitone theta phi psi

/-- Each finite rooftop tail envelope remains a normalized theta-PSH
potential.  This is a direct envelope construction, independent of any
measure-convergence statement. -/
theorem isThetaPshPotential_tailEnvelope_modelTruncationRooftopData
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hphimodel : phi = singularityEnvelope theta.val phi)
    (hpsimodel : psi = singularityEnvelope theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (k : ℕ) :
    IsThetaPshPotential theta.val
      (tailEnvelope (modelTruncationRooftopData theta phi psi) k) := by
  have hzero : IsThetaPshPotential theta.val
      (modelTruncationRooftopData theta phi psi 0) :=
    model_truncation_rooftop_isThetaPshPotential theta hphi hpsi hmax 0
  have hlocal : HasSmoothLocalPotentials theta.val :=
    hzero.1.hasSmoothLocalPotentials
  apply isThetaPshPotential_tailEnvelope hlocal
  · exact model_truncation_rooftop_isThetaPshPotential theta hphi hpsi hmax
  · intro j x
    exact
      model_truncation_rooftop_le_zero theta hphi hpsi hphimodel hpsimodel hmax j x

/-- The tail envelope of the model truncations has the same checked local
`L¹` limit as the truncations themselves. -/
theorem manifoldL1LocallyTendsto_tailEnvelope_modelTruncationRooftopData
    [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi)
    (hphimodel : phi = singularityEnvelope theta.val phi)
    (hpsimodel : psi = singularityEnvelope theta.val psi)
    (hmax : IsThetaPshPotential theta.val (fun x => max (phi x) (psi x)))
    (hroof : IsThetaPshPotential theta.val
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x)))) :
    ManifoldL1LocallyTendsto (n := n)
      (tailEnvelope (modelTruncationRooftopData theta phi psi)) atTop
      (rooftopEnvelope theta.val (fun x => min (phi x) (psi x))) := by
  apply manifoldL1LocallyTendsto_tailEnvelope_of_antitone_iInf
  · exact model_truncation_rooftop_isThetaPshPotential theta hphi hpsi hmax
  · exact modelTruncationRooftopData_antitone theta phi psi
  · exact hroof
  · exact iInf_modelTruncationRooftopData_eq_rooftop theta hphi hpsi
      hphimodel hpsimodel hmax hroof

end

end SGPT.Foundations.Analysis.Pending.DecreasingRooftopTailEnvelope
