import SGPT.Foundations.Analysis.Pending.RooftopObstacleQuasiEverywhere
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

set_option autoImplicit false

/-!
# Envelopes of a decreasing family of obstacles, with (2.20) only quasi-everywhere (C6 of I-0510)

`Pending.RooftopUscObstacleApproximation.rooftopEnvelope_eq_iInf_of_antitone` identifies the
envelope of the limit of a decreasing family of obstacles with the limit of the envelopes,
assuming Xia's (2.20) `P_θ(g_k) ≤ g_k` **everywhere** for the members.  For obstacles that are not
upper semicontinuous (Xia's Step 2 family, the reference truncations of the affine obstacle of
Theorem 2.4.5) (2.20) holds only quasi-everywhere, and the identification survives as soon as a
countable union of pluripolar sets is pluripolar (`CountablyStablePluripolar`, proved on compact
connected Kähler manifolds in `Pending.PluripolarOuterCapacity`):

  `P_θ(⨅ F_k) = ⨅ P_θ(F_k)`  (`rooftopEnvelope_eq_iInf_of_antitone_qe`).

The infimum of the envelopes is `θ`-PSH (decreasing limit), lies above every competitor of the
limit obstacle, and lies below every `F_k` quasi-everywhere, hence below `⨅ F_k`
quasi-everywhere: it is itself a competitor.  Obstacles are arbitrary extended-real functions.
-/

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopDecreasingLimitQE

open FirstPass
open SGPT.Foundations.Analysis.Pending.RooftopObstacleQuasiEverywhere

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {theta : SmoothRealForm n M 2}

/-- **The rooftop envelope commutes with a decreasing limit of obstacles**, given (2.20)
quasi-everywhere for the members and countable stability of pluripolarity. -/
theorem rooftopEnvelope_eq_iInf_of_antitone_qe (hcount : CountablyStablePluripolar n M)
    {f : M → EReal} {F : ℕ → M → EReal}
    (hgf : ∀ x, (⨅ k, F k x) = f x) (hanti : ∀ x, Antitone fun k => F k x)
    (hpsh : ∀ k, ThetaPlurisubharmonic theta (rooftopEnvelope theta (F k)))
    (hple : ∀ k, QuasiEverywhere (n := n) (fun x => rooftopEnvelope theta (F k) x ≤ F k x))
    (hne : (rooftopCompetitors theta f).Nonempty) (x : M) :
    rooftopEnvelope theta f x = ⨅ k, rooftopEnvelope theta (F k) x := by
  set I : M → EReal := fun y => ⨅ k, rooftopEnvelope theta (F k) y with hIdef
  have hFanti : ∀ y, Antitone fun k => rooftopEnvelope theta (F k) y := fun y j k hjk =>
    rooftopEnvelope_mono (θ := theta) (fun z => hanti z hjk) y
  have hfF : ∀ k y, f y ≤ F k y := fun k y => (hgf y) ▸ iInf_le (fun j => F j y) k
  obtain ⟨v, hv⟩ := hne
  have hvI : v ≤ I := fun y =>
    le_iInf fun k => le_rooftopEnvelope hv.1 (hv.2.mono fun z hz => hz.trans (hfF k z)) y
  have hpot : IsThetaPshPotential theta I :=
    ⟨ThetaPshDecreasingLimit.thetaPlurisubharmonic_iInf_of_antitone hpsh hFanti,
      hv.1.2.mono hvI⟩
  have hlef : QuasiEverywhere (n := n) (fun y => I y ≤ f y) := by
    refine (quasiEverywhere_forall hcount hple).mono fun y hy => ?_
    rw [← hgf y]
    exact le_iInf fun k => (iInf_le _ k).trans (hy k)
  refine le_antisymm ?_ (le_rooftopEnvelope hpot hlef x)
  exact le_iInf fun k => rooftopEnvelope_mono (θ := theta) (fun y => hfF k y) x

/-- **Pointwise convergence of the envelopes along a decreasing family of obstacles.** -/
theorem tendsto_rooftopEnvelope_of_antitone_qe (hcount : CountablyStablePluripolar n M)
    {f : M → EReal} {F : ℕ → M → EReal}
    (hgf : ∀ x, (⨅ k, F k x) = f x) (hanti : ∀ x, Antitone fun k => F k x)
    (hpsh : ∀ k, ThetaPlurisubharmonic theta (rooftopEnvelope theta (F k)))
    (hple : ∀ k, QuasiEverywhere (n := n) (fun x => rooftopEnvelope theta (F k) x ≤ F k x))
    (hne : (rooftopCompetitors theta f).Nonempty) (x : M) :
    Tendsto (fun k => rooftopEnvelope theta (F k) x) atTop
      (𝓝 (rooftopEnvelope theta f x)) := by
  rw [rooftopEnvelope_eq_iInf_of_antitone_qe hcount hgf hanti hpsh hple hne x]
  exact tendsto_atTop_iInf fun j k hjk =>
    rooftopEnvelope_mono (θ := theta) (fun z => hanti z hjk) x

end SGPT.Foundations.Analysis.Pending.RooftopDecreasingLimitQE
