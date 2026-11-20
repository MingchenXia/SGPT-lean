import SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact
import SGPT.Foundations.Analysis.Pending.BoucksomNonBigSupremumMass
import SGPT.Foundations.Analysis.Pending.LocalPotentials

set_option autoImplicit false

/-!
# Xia's Corollary 2.4.4 for an arbitrary pseudo-effective class

`Pending.BigClassEnvelopeContact.diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_isBigClass`
is Xia's Corollary 2.4.4 (`xia-sgpt:page-0094`, the "in particular" clause) for
a **big** class: `theta^n_{V_theta}` gives no mass to `{V_theta < 0}`.  Bigness
enters through Xia's Lemma 2.4.1, which produces the normalized reference that
makes `V_theta` locally bounded off `nK({theta})`; for a merely pseudo-effective
class there is no such reference.

This module removes the hypothesis, by the trichotomy

* `n = 0`: then every real two-form is semipositive, so `0` is a
  `theta`-PSH potential, `V_theta = 0`, and `{V_theta < 0}` is empty.  Nothing
  analytic is used.
* `n > 0` and `{theta}` big: the proved statement above.
* `n > 0` and `{theta}` not big: then the *total* mass `int theta^n_{V_theta}`
  vanishes, so every set is null.  That vanishing is the one classical input
  recorded here as `diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass`.

Why the third bullet is a theorem of the literature and not a restatement of its
consumer.  Boucksom's volume of a pseudo-effective class `alpha` is
`v(alpha) = sup_T int_X T_ac^n` over closed positive currents `T` in `alpha`
(`bou02-volume:1.3`), and `bou02-volume:4.8` (Theorem 4.7 of the published
version) is the transcendental Grauert--Riemenschneider criterion

  `alpha` is big   iff   `v(alpha) > 0`,

"big" meaning exactly, as here, that `alpha` contains a Kähler current.  The
non-pluripolar mass of any `theta`-PSH potential is at most `v({theta})`
(`begz-big-classes:thm:comp` and the surrounding discussion of `<T^n> <= T_ac^n`),
so a non-big class has `int theta^n_{V_theta} = 0`.  The statement recorded
below is therefore about the *total* mass, makes no reference to the sublevel
set `{V_theta < 0}`, and cannot be recovered from its consumer by
instantiation.

Two hypotheses of the interface are not decoration.

* `omega : KahlerBackground n M`.  The source statement is the
  Grauert--Riemenschneider criterion **in the Kähler case**
  (`bou02-volume`, `locators.tsv` anchor 4.8: "pseudoeffective (1,1)-class on
  the compact Kähler manifold X").  Dropping it would make the statement false:
  `IsBigClass` is `Nonempty (KahlerCurrent alpha)` and a `KahlerCurrent` carries
  a `KahlerBackground`, so on a compact complex manifold with no Kähler form
  *no* class is big, `hnb` is free, and the conclusion would force every class
  on, say, a non-projective Moishezon manifold to have zero mass -- false for a
  big line bundle there.  The hypothesis is also free downstream: the consumer
  `SingularityEnvelopeContact.diagonalPotentialMeasure_thetaPshSupremum_lt_zero`
  already carries `omega`.
* `0 < n` is kept to match the big-class half, which needs it; the `n = 0`
  branch of the theorem below is proved outright instead, and is in any case
  degenerate (in dimension `0` strict positivity is vacuous, so every class is
  big and `hnb` is unsatisfiable).
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonBigSupremumMass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.BigClassEnvelopeContact

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- In dimension `0` every smooth real two-form is semipositive: the tangent
model is a subsingleton, so the two arguments of the alternating coefficient
coincide and it vanishes. -/
theorem isSemipositive_of_dim_zero (hn : n = 0) (a : SmoothRealForm n M 2) :
    a.IsSemipositive := by
  subst hn
  intro e z _ v
  have hv : v = Complex.I • v := Subsingleton.elim _ _
  have hzero : a.coeff e z ![v, Complex.I • v] = 0 := by
    refine (a.coeff e z).map_eq_zero_of_eq ![v, Complex.I • v]
      (i := 0) (j := 1) ?_ (by decide)
    simpa using hv
  rw [hzero]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- In dimension `0` the canonical reference is identically zero. -/
theorem thetaPshSupremum_eq_zero_of_dim_zero (hn : n = 0)
    (theta : ClosedRealOneOneForm n M) :
    thetaPshSupremum theta.val = 0 := by
  refine le_antisymm (thetaPshSupremum_le_zero theta.val) ?_
  have h0 : IsThetaPshPotential theta.val (fun _ : M => (0 : EReal)) :=
    (SGPT.Foundations.Analysis.Pending.LocalPotentials.isThetaPshPotential_zero_iff
      theta).mpr (isSemipositive_of_dim_zero hn theta.val)
  exact le_thetaPshSupremum h0 le_rfl

/-- The source-anchored Boucksom input is isolated in
`Pending.BoucksomNonBigSupremumMass`; this wrapper preserves the public theorem
used by the Corollary 2.4.4 trichotomy. -/
theorem diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val))
    (hnb : ¬ IsBigClass (RealBottChern.ofRepresentative theta)) :
    diagonalPotentialMass theta (thetaPshSupremum theta.val) hV = 0 := by
  exact
    SGPT.Foundations.Analysis.Pending.BoucksomNonBigSupremumMass.diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass
      hn omega theta hV hnb

/-- **Xia, SGPT, Corollary 2.4.4 (`xia-sgpt:page-0094`), with no bigness
hypothesis.**  The non-pluripolar Monge--Ampère measure of the canonical
reference gives no mass to `{V_theta < 0}`. -/
theorem diagonalPotentialMeasure_thetaPshSupremum_lt_zero [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    (hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val)) :
    diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV
      {x | thetaPshSupremum theta.val x < 0} = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hzero := thetaPshSupremum_eq_zero_of_dim_zero hn theta
    have hempty : {x : M | thetaPshSupremum theta.val x < 0} = ∅ := by
      ext x
      simp [congrFun hzero x]
    rw [hempty]
    simp
  · by_cases hb : IsBigClass (RealBottChern.ofRepresentative theta)
    · exact diagonalPotentialMeasure_thetaPshSupremum_lt_zero_of_isBigClass hn theta hb hV
    · refine nonpos_iff_eq_zero.mp ?_
      calc diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV
              {x | thetaPshSupremum theta.val x < 0}
          ≤ diagonalPotentialMeasure theta (thetaPshSupremum theta.val) hV univ :=
            measure_mono (subset_univ _)
        _ = 0 :=
            diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass hn omega theta hV hb

end

end SGPT.Foundations.Analysis.Pending.NonBigSupremumMass
