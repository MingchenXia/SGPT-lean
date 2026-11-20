import SGPT.Foundations.Analysis.Pending.DiagonalMass
import SGPT.Foundations.Analysis.Pending.GlobalDiagonalConvexScaling
import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

set_option autoImplicit false

/-!
# The convex-combination lower bound for the non-pluripolar product

For `t ∈ (0,1)` and `u, v ∈ PSH(X, theta)` whose convex combination
`w = t u + (1 - t) v` is again a genuine `theta`-PSH potential, the currents
satisfy `theta_w = t theta_u + (1 - t) theta_v`, so multilinearity of the
non-pluripolar product (BEGZ, Proposition 1.4 and the discussion of
`equ:nonpp`) expands `theta_w^n` into the binomial sum of the mixed products
`<theta_u^k ∧ theta_v^{n-k}>`, each of which is a positive measure.  Dropping
all but the extreme term gives

  `t^n theta_u^n ≤ theta_w^n`    as measures.       (*)

This is the only consequence of multilinearity used by the measure chain on
`xia-sgpt:page-0088` (Xia's step `1_{D_a} a^{-n} theta_{eta_a}^n ≤
1_{D_a} theta_{gamma_a}^n`), so it is isolated here as a single named
interface rather than as the full binomial expansion.

**Proof.**  `Pending.GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le`
already proves exactly this inequality for `globalMixedMeasure` of the constant
tuples, by replacing one slot at a time through one-slot positive linearity
(`Pending.GlobalSlotLinear.globalMixedMeasure_update_add_smul`, itself the
manifold form of Bedford--Taylor slot additivity and homogeneity,
`Pending.BedfordTaylor.IsBTLimit.add_slot` and `IsBTLimit.const_mul_slot`) and
dropping the `v`-summand.  Since `diagonalPotentialMeasure` is by definition the
constant-tuple `globalMixedMeasure`, the statement here is that theorem read
through `DiagonalMass`.  No binomial expansion is needed, and none is used.

The hypothesis `hw` is redundant —
`ThetaPshConvexCombination.isThetaPshPotential_convexComb` proves it from
`hu`, `hv`, `ht0`, `ht1` — but it is kept as an argument so that a caller who
already has that proof term (every caller so far does) can pass it rather than
rebuild it; `diagonalPotentialMeasure` is proof-independent, so nothing depends
on which one is used.

**Degenerate cases.**  In dimension `n = 0` the factor is `t^0 = 1` and both
sides are the same measure: `Pending.MixedNonPluripolar` shows
(`mixedTruncationLimitMeasure_zero_dim`) that in dimension zero the mixed
truncation limit does not depend on the potentials at all.  When the
potentials are `-infinity` on a pluripolar set the statement is unaffected,
because both sides are non-pluripolar measures; and `IsThetaPshPotential`
already excludes the locally-identically-`-infinity` inputs.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.NonPluripolarConvexCombLower

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- **Multilinearity of the non-pluripolar product (BEGZ), in the single form
used by Xia's step on `xia-sgpt:page-0088`.**  The diagonal non-pluripolar
measure of a convex combination dominates the scaled measure of either
constituent, on every set. -/
theorem ofReal_pow_smul_diagonalPotentialMeasure_le_convexComb
    (theta : ClosedRealOneOneForm n M) {u v : M → EReal}
    (hu : IsThetaPshPotential theta.val u) (hv : IsThetaPshPotential theta.val v)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hw : IsThetaPshPotential theta.val (convexComb t u v)) (E : Set M) :
    ENNReal.ofReal (t ^ n) * diagonalPotentialMeasure theta u hu E ≤
      diagonalPotentialMeasure theta (convexComb t u v) hw E :=
  GlobalDiagonalConvexScaling.globalMixedMeasure_diagonal_convexComb_le hu hv ht0 ht1 E

end

end SGPT.Foundations.Analysis.Pending.NonPluripolarConvexCombLower
