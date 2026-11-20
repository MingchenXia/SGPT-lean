import SGPT.Foundations.Analysis.Pending.RooftopUscEnvelopeConcentration
import SGPT.Foundations.Analysis.Pending.NonBigPotentialMass

set_option autoImplicit false

/-!
# Xia's Theorem 2.4.4 on an arbitrary pseudo-effective class

`Pending.RooftopUscEnvelopeConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_upperSemicontinuous`
proves Xia's Theorem 2.4.4 (`xia-sgpt:page-0079`, equation (2.23)) for an upper
semicontinuous obstacle bounded below by a real translate of `V_theta`, on a
**big** class, and with quasi-continuity of the obstacle as the one remaining
source-level hypothesis.  This module removes *both* of the hypotheses that are
about `theta` rather than about the obstacle:

* `hbig`.  Bigness enters only through Xia's Lemma 2.4.1, which makes `V_theta`
  locally bounded off `nK({theta})`.  For a class containing no Kähler current
  there is nothing to prove instead: **every** `theta`-PSH potential then has
  total non-pluripolar mass `0`
  (`Pending.NonBigPotentialMass.diagonalPotentialMeasure_eq_zero_of_not_isBigClass`,
  proved there from Boucksom's transcendental Grauert--Riemenschneider criterion
  by monotonicity in the singularity order), so every set is null.

* `hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val)`.  The
  envelope hypothesis `hw` already exhibits one `theta`-PSH potential, which is
  all `FirstPass.thetaPshSupremum_isThetaPshPotential` needs.

What is left is a statement whose hypotheses concern only the obstacle, in
exactly the shape the Section 3.1 consumers carry — `Pending.RooftopContactConcentration`
and `Pending.DominationPrincipleContactChain` assume pseudo-effectivity of
`{theta}` and nothing more.  So the bigness mismatch recorded in I-0430 /
I-0444 / I-0463(e) is resolved without changing any existing statement: what
those consumers still owe is the passage of the measures to the limit along the
truncations (Xia's Step 1.2, `xia-sgpt:page-0080`--`page-0081`) and
quasi-continuity of the truncated obstacle, not a decision about `hbig`.

`M` empty and `n = 0` are covered rather than excluded: in an empty space every
set is empty, and in dimension `0` no class is non-big
(`Pending.NonBigPotentialMass.isBigClass_of_dim_zero`), which is why `0 < n` is
still carried — the big half genuinely needs it.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopUscConcentrationPseudoeffective

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaCapacity
open SGPT.Foundations.Analysis.Pending.NonBigPotentialMass
open SGPT.Foundations.Analysis.Pending.PatchLocalBoundedMeasure

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Xia, SGPT, Theorem 2.4.4 (`xia-sgpt:page-0079`, equation (2.23)) on an
arbitrary pseudo-effective class, for an upper semicontinuous obstacle bounded
relative to the reference.**  `theta^n_{P_theta(f)}` gives no mass to
`{P_theta(f) < f}`.

No bigness hypothesis, no nonemptiness hypothesis and no separate hypothesis
that `V_theta` is a genuine potential: the first is split off by the trichotomy
of `Pending.NonBigPotentialMass`, the second is the degenerate case, and the
third follows from `hw`.  `M` is connected (human decision I-0902 on I-0825):
the non-big branch rests on Boucksom's volume criterion, which is about connected
compact Kähler manifolds.

The hypotheses that remain are about the obstacle alone: upper semicontinuity,
`f <= 0`, the relative lower bound `V_theta + c <= f`, quasi-continuity `hfqc`
of `f` against `Cap_theta(-, V_theta)` on compact subsets of an open set where
`V_theta` is bounded, and that `P_theta(f)` is a genuine potential. -/
theorem diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_upperSemicontinuous_of_pseudoeffective
    [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {f : M → EReal}
    (hf : UpperSemicontinuous f) {c : ℝ}
    (hfc : ∀ x, thetaPshSupremum theta.val x + (c : EReal) ≤ f x)
    (hf0 : ∀ x, f x ≤ 0)
    (hfqc : ∀ Omega : Set M, IsOpen Omega →
      IsBoundedPotentialOn (thetaPshSupremum theta.val) Omega →
      ∀ K : Set M, IsCompact K → K ⊆ Omega → ∀ eps : ℝ, 0 < eps →
      ∃ G : Set M, IsOpen G ∧
        thetaCapacity theta (thetaPshSupremum theta.val) G < ENNReal.ofReal eps ∧
        ContinuousOn (fun y => (f y).toReal) (K \ G))
    (hw : IsThetaPshPotential theta.val (rooftopEnvelope theta.val f)) :
    diagonalPotentialMeasure theta (rooftopEnvelope theta.val f) hw
      {x : M | rooftopEnvelope theta.val f x < f x} = 0 := by
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Set.eq_empty_of_isEmpty {x : M | rooftopEnvelope theta.val f x < f x}]
    exact measure_empty
  by_cases hbig : IsBigClass (RealBottChern.ofRepresentative theta)
  · have hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val) :=
      SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential theta.val
        theta.2.1 theta.2.2 hw.1.hasSmoothLocalPotentials ⟨_, hw⟩
    exact RooftopUscEnvelopeConcentration.diagonalPotentialMeasure_rooftopEnvelope_lt_eq_zero_of_upperSemicontinuous
      hn hbig hV hf hfc hf0 hfqc hw
  · exact diagonalPotentialMeasure_eq_zero_of_not_isBigClass omega theta hw hbig _

end

end SGPT.Foundations.Analysis.Pending.RooftopUscConcentrationPseudoeffective
