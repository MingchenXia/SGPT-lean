import SGPT.Foundations.Analysis.Pending.NonBigSupremumMass
import SGPT.Foundations.Analysis.Pending.SingularityEnvelopeMassProof

set_option autoImplicit false

/-!
# A non-big class has no non-pluripolar mass at all

`Pending.NonBigSupremumMass.diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass`
is the named classical input of that module: for a pseudo-effective class
containing no Kähler current, the total non-pluripolar mass of the **canonical
reference** `V_theta` vanishes (Boucksom's transcendental
Grauert--Riemenschneider criterion, `bou02-volume:4.8`, together with the bound
of the non-pluripolar mass by the volume of the class).

This module is the two-line consequence for an **arbitrary** `theta`-PSH
potential, which is the form every consumer wants:

  `{theta}` not big  `==>`  `int_X theta^n_u = 0`   for every `u in PSH(X, theta)`,

and hence `theta^n_u E = 0` for every set `E` whatsoever.  The proof is
monotonicity of the mass in the singularity order,
`Pending.diagonalPotentialMass_mono_of_kahler`, applied to
`FirstPass.thetaPshSupremum_minimalSingularities`: every `theta`-PSH potential
is more singular than `V_theta`, because it has a real upper bound `C` and
`u - C <= 0` makes `u - C` a competitor of `V_theta`.  No new analytic input is
introduced.

Also recorded here, for the same trichotomies: in dimension `0` **every** class
is big, so a non-bigness hypothesis is unsatisfiable there.  The witness is the
zero potential: by
`Pending.NonBigSupremumMass.isSemipositive_of_dim_zero` every smooth real
two-form on a `0`-dimensional manifold is semipositive, in particular
`theta - omega`, so `theta + dd^c 0 >= omega` exhibits a Kähler current in
`{theta}`.  This is what makes the `0 < n` of the classical input free in a
trichotomy that already has a Kähler background at hand.

The degenerate cases are covered rather than excluded: `M` empty (every set is
`empty`, so every measure of it is `0`) and `n = 0` (no non-big class exists).
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonBigPotentialMass

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.NonBigSupremumMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
/-- **In dimension `0` every class with a Kähler background is big.**  The zero
function is a potential of a Kähler current, because on a `0`-dimensional
manifold every smooth real two-form -- in particular `theta - omega` -- is
semipositive.  Consequently a `¬ IsBigClass` hypothesis is unsatisfiable in
dimension `0`, which is what frees the `0 < n` of
`Pending.NonBigSupremumMass.diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass`
inside a trichotomy. -/
theorem isBigClass_of_dim_zero (hn : n = 0) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) :
    IsBigClass (RealBottChern.ofRepresentative theta) :=
  ⟨{ representative := theta
     represents := rfl
     potential := fun _ => 0
     lowerBound := omega
     strictlyPsh :=
       (SGPT.Foundations.Analysis.Pending.LocalPotentials.isThetaPshPotential_zero_iff
           (theta - omega.form)).mpr
         (isSemipositive_of_dim_zero hn (theta - omega.form).val) }⟩

/-- **A non-big class carries no non-pluripolar mass.**  Every `theta`-PSH
potential has total non-pluripolar mass `0` as soon as `{theta}` contains no
Kähler current.

This is the classical input of `Pending.NonBigSupremumMass` transported along
the singularity order: `u` is more singular than `V_theta`
(`FirstPass.thetaPshSupremum_minimalSingularities`) and the mass is monotone in
that order (`Pending.diagonalPotentialMass_mono_of_kahler`). -/
theorem diagonalPotentialMass_eq_zero_of_not_isBigClass [Nonempty M] [ConnectedSpace M]
    (hn : 0 < n) (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hnb : ¬ IsBigClass (RealBottChern.ofRepresentative theta)) :
    diagonalPotentialMass theta u hu = 0 := by
  have hne : ∃ v, IsThetaPshPotential theta.val v := ⟨u, hu⟩
  have hV : IsThetaPshPotential theta.val (thetaPshSupremum theta.val) :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_isThetaPshPotential theta.val
      theta.2.1 theta.2.2 hu.1.hasSmoothLocalPotentials hne
  have hmore : MoreSingularOn u (thetaPshSupremum theta.val) univ :=
    SGPT.Foundations.Analysis.Pending.thetaPshSupremum_minimalSingularities theta.val
      theta.2.1 theta.2.2 hu.1.hasSmoothLocalPotentials hne u hu
  have hmono := diagonalPotentialMass_mono_of_kahler omega hu hV hmore
  rw [diagonalPotentialMass_thetaPshSupremum_eq_zero_of_not_isBigClass hn omega theta hV hnb]
    at hmono
  exact le_antisymm hmono zero_le

/-- **A non-big class charges no set at all.**  The measure form of
`diagonalPotentialMass_eq_zero_of_not_isBigClass`, with the two degenerate
cases absorbed: `M` empty makes every set empty, and `n = 0` makes the
hypothesis `hnb` unsatisfiable by `isBigClass_of_dim_zero`.  No dimension or
nonemptiness hypothesis is left, which is what lets a consumer split on
bigness alone. -/
theorem diagonalPotentialMeasure_eq_zero_of_not_isBigClass [ConnectedSpace M]
    (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {u : M → EReal}
    (hu : IsThetaPshPotential theta.val u)
    (hnb : ¬ IsBigClass (RealBottChern.ofRepresentative theta)) (E : Set M) :
    diagonalPotentialMeasure theta u hu E = 0 := by
  rcases isEmpty_or_nonempty M with hM | hM
  · rw [Set.eq_empty_of_isEmpty E]
    exact measure_empty
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact absurd (isBigClass_of_dim_zero hn omega theta) hnb
  refine le_antisymm ?_ zero_le
  calc diagonalPotentialMeasure theta u hu E
      ≤ diagonalPotentialMass theta u hu := measure_mono (subset_univ E)
    _ = 0 := diagonalPotentialMass_eq_zero_of_not_isBigClass hn omega theta hu hnb

end

end SGPT.Foundations.Analysis.Pending.NonBigPotentialMass
