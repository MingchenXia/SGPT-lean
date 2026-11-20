import SGPT.Foundations.Analysis.FirstPass.RooftopEnvelope
import SGPT.Foundations.Analysis.FirstPass.ThetaPshEnvelopes
import SGPT.Foundations.Analysis.FirstPass.ThetaPshComparison
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

set_option autoImplicit false

/-!
# Feasibility of a rooftop family

Two facts about `rooftopEnvelope` that depend on nothing beyond `FirstPass`:

* a nonempty rooftop family with one common finite upper bound has a genuine
  `theta`-PSH envelope (`isThetaPshPotential_rooftop_of_nonempty`), which
  separates the local regularization argument from the analytic nonemptiness
  question for a particular pair of obstacles;
* for the obstacle `min (u, v + C)` with `u` a `theta`-PSH potential, such a
  bound always exists on a compact manifold
  (`rooftopCompetitors_min_add_const_uniformlyBoundedAbove`), because every
  competitor lies below `u` quasi-everywhere and hence everywhere.

Both were proved as preliminaries inside `Pending.RelativeFullMass`; they are
relocated here, with their statements and names unchanged, so that the modules
BELOW `RelativeFullMass` -- in particular `Pending.ShiftedRooftopContact` --
can use them.  `Pending.RelativeFullMass` imports this file, so nothing that
referred to them has to change.
-/

open Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending

open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A nonempty rooftop family with a common finite upper bound has a genuine
theta-PSH upper envelope.  This separates the local regularization argument
from the analytic nonemptiness question for a particular pair of obstacles. -/
theorem isThetaPshPotential_rooftop_of_nonempty
    {theta : SmoothRealForm n M 2} {f : M → EReal}
    (hne : (rooftopCompetitors theta f).Nonempty)
    (hbound : ∃ B : ℝ, ∀ g ∈ rooftopCompetitors theta f, ∀ x,
      g x ≤ (B : EReal)) :
    IsThetaPshPotential theta (rooftopEnvelope theta f) := by
  obtain ⟨q, hq⟩ := hne
  have hne : (rooftopCompetitors theta f).Nonempty := ⟨q, hq⟩
  obtain ⟨B, hB⟩ := hbound
  have hlocal : HasSmoothLocalPotentials theta :=
    hq.1.1.hasSmoothLocalPotentials
  constructor
  · intro e z hz
    obtain ⟨W, rho, hzW, hrho⟩ := hlocal e z hz
    refine ⟨W, rho, hzW, hrho, ?_⟩
    let G := chartCorrectedFamily (rooftopCompetitors theta f) e rho
    have hGne : G.Nonempty :=
      chartCorrectedFamily_nonempty hne e rho
    have hGpsh : ∀ g ∈ G, PlurisubharmonicOn g W :=
      chartCorrectedFamily_plurisubharmonicOn (fun _ hu ↦ hu.1) e hrho
    have hGbound : LocallyUniformlyBoundedAbove G W := by
      intro x hx
      have hrhoc : ContinuousAt rho x :=
        ((hrho.2.2.1 x hx).contDiffAt (hrho.1.mem_nhds hx)).continuousAt
      have hU : {y | rho y < rho x + 1} ∈ 𝓝 x :=
        hrhoc (isOpen_Iio.mem_nhds (lt_add_one (rho x)))
      refine ⟨{y | rho y < rho x + 1},
        mem_nhdsWithin_of_mem_nhds hU, B + rho x + 1, ?_⟩
      rintro g ⟨p, hp, rfl⟩ y ⟨hy, _⟩
      change p (e.val.symm y) + (rho y : EReal) ≤ _
      calc
        p (e.val.symm y) + (rho y : EReal) ≤
            (B : EReal) + (rho y : EReal) :=
          add_le_add (hB p hp (e.val.symm y)) le_rfl
        _ = ((B + rho y : ℝ) : EReal) := by rw [EReal.coe_add]
        _ ≤ ((B + (rho x + 1) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hy.le B)
        _ = ((B + rho x + 1 : ℝ) : EReal) := by
          rw [add_assoc, EReal.coe_add]
    have hp := plurisubharmonicOn_uscRegularization_sSup hrho.1 hGne hGpsh hGbound
    intro x hx
    apply (hp x hx).congr
    filter_upwards [hrho.1.mem_nhds hx] with y hy
    change uscRegularization
      (sSup (chartCorrectedFamily (rooftopCompetitors theta f) e rho)) y = _
    rw [show sSup (chartCorrectedFamily (rooftopCompetitors theta f) e rho) =
        (fun t ↦ chartFunction (sSup (rooftopCompetitors theta f)) e t +
          (rho t : EReal)) by
      funext t
      exact sSup_chartCorrectedFamily_apply (rooftopCompetitors theta f) e rho t]
    rw [uscRegularization_add_coe_continuousAt_apply _
      (((hrho.2.2.1 y hy).contDiffAt (hrho.1.mem_nhds hy)).continuousAt)]
    rw [uscRegularization_chartFunction_apply _ e (hrho.2.1 hy)]
    rfl
  · exact rooftopEnvelope_locallyNondegenerate hne

variable [CompactSpace M]

/-- Rooftop competitors below the first theta-PSH obstacle have one finite
global upper bound on a compact manifold. -/
theorem rooftopCompetitors_min_add_const_uniformlyBoundedAbove [Nonempty M]
    (theta : ClosedRealOneOneForm n M) (u v : M → EReal)
    (hu : IsThetaPshPotential theta.val u) (C : ℝ) :
    ∃ B : ℝ, ∀ g ∈ rooftopCompetitors theta.val
      (fun x => min (u x) (v x + (C : EReal))), ∀ x, g x ≤ (B : EReal) := by
  obtain ⟨B, hB⟩ := hu.exists_global_upper_bound
  refine ⟨B, ?_⟩
  intro g hg x
  have hgu : g ≤ u := hg.1.1.le_of_quasiEverywhere_le hu.1
    (hg.2.mono fun y hy => hy.trans (min_le_left _ _))
  exact (hgu x).trans (hB x)

end

end SGPT.Foundations.Analysis.Pending
