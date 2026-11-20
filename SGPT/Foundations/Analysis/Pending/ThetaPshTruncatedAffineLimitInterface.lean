import SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeBarrierInterface
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierTruncatedLimit
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple
import SGPT.Foundations.Analysis.Pending.ThetaPshTruncatedAffineLimitMassChain

set_option autoImplicit false

/-!
# Step 1.3 of Xia's Lemma 2.4.4

**This module is no longer a source boundary.**  Step 1.3 is PROVED, for a
connected `M`, in `Pending.ThetaPshTruncatedAffineLimitMassChain`, by the
source's own contradiction argument; `hasNondegenerateTruncatedAffineLimit`
below packages that proof in the predicate form the Step-1 assembly consumes,
and it is what
`Pending.RooftopConvexCombBarrierStepOneAssembly.exists_thetaPsh_convexCombBarrier_of_interfaces`
now calls.  The two statements that proof rests on are Xia's Theorem 2.4.4 for
the affine obstacle (already open in this workspace before it, and used
identically on `xia-sgpt:page-0088`) and the compactness of `PSH(X, θ)`
(`Pending.ThetaPshAntitoneSupNondegenerate`).

`xiaLemma244_step13_hasNondegenerateTruncatedAffineLimit`, the original named
interface (the same assertion without `[ConnectedSpace M]`), had no consumer
once the proof above supplied the assembly, and was retired by the human's
decision I-0661.

The rest of this docstring is the original account of the construction and of
what the argument needs, written while Step 1.3 was still a named interface;
"this interface" there means the predicate `HasNondegenerateTruncatedAffineLimit`,
which is now proved (`hasNondegenerateTruncatedAffineLimit`).

`Pending.RooftopConvexCombBarrierTruncatedLimit` builds Xia's
`φ_k = φ ∨ (ϕ - k)`, `η_k = P_θ(a φ_k + (1-a) ϕ)` and `η = inf_k η_k`, and proves
everything about them that Step 1 needs *except* the one point Xia's Step 1.3
(`xia-sgpt:page-0085`--`xia-sgpt:page-0086`) is devoted to: `η ≢ -∞`.

That point is the predicate `HasNondegenerateTruncatedAffineLimit` below.

## What Xia's proof of it uses, and why it is not available here

Assuming `sup_X η_k → -∞`, Xia derives (2.35),
`θ_{η_k}^n ≤ aⁿ 1_{D_k} θ_{φ_k}^n` with `D_k = {a⁻¹ η_k + (1-a⁻¹) ϕ = φ_k}`,
from three inputs: his Lemma 2.4.2 on contact sets, positivity and
multilinearity of the non-pluripolar product, and **Theorem 2.4.4 for the affine
obstacle**, i.e.
`Pending.DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero`,
which is itself an open named interface in this workspace.  He then combines
(2.35) with the mass identity (2.36) and with (2.34) — the latter proved in
`Pending.RooftopConvexCombBarrierStepOne.le_add_const_of_le_of_singularityEnvelope_eq`
— and the contradiction is with the admissible interval (2.28).

So this interface is *not* an irreducible assumption: it is reachable from
`xiaTheorem244_affineObstacle_noncontact_eq_zero` plus Lemma 2.4.2 and
multilinearity.  It is recorded as a named interface because that chain is not
formalized yet.

**It is NOT strictly smaller than the statement it replaces, and must not be
described as such.**  It is *interderivable* with
`Pending.RooftopConvexCombBarrierModelReduction.ModelReferenceStepOne`: the
forward direction is
`Pending.RooftopConvexCombBarrierStepOneAssembly.modelReferenceStepOne_of_hasNondegenerateTruncatedAffineLimit`,
and the converse is elementary — a competitor `η` of the untruncated problem
satisfies `a⁻¹η + (1-a⁻¹)v ≤ u ≤ u ∨ (v-k)`, so by
`ConvexCombObstacleAlgebra.convexCombValue_le_iff` it is a rooftop competitor of
every truncated obstacle, hence `η ≤ η_k` for all `k`, hence `η ≤ η` and the
limit inherits nondegeneracy.  What this interface buys is therefore not a
weaker hypothesis but a *concrete* one: the residual target is pinned to one
explicitly constructed function, which is the object Xia's Step 1.3 actually
argues about.  The genuinely smaller half of the split is
`Pending.ThetaPshModelReference` (Step 1.2), not this one — and that half is
now proved, so this interface is the whole residue of Step 1.

## Hypotheses, and why each is kept

`v ≤ 0` and `P_θ[v] = v` are what (2.34) consumes; `0 < ∫θ_u^n` and the
admissibility of `a` are what the final contradiction violates.  None of them is
decorative: without the interval (2.28) the conclusion is false in general, since
`aⁿ(∫θ_v^n - ∫θ_u^n) ≥ ∫θ_v^n` is exactly the inequality Xia derives from
`η ≡ -∞`.  In dimension `0` the interval reduces to `0 < ∫θ_u^n`, and the same
contradiction `m ≤ m - ∫θ_u^n` applies, so nothing degenerates.  `IsThetaPshPotential`
already forbids `u ≡ -∞` locally.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ThetaPshTruncatedAffineLimit

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierTruncatedLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-- **Xia's Step 1.3, in the source's own words.**  For a normalized `P`-fixed
reference `v`, a partner `u ≤ v` of positive mass and an admissible weight `a`,
the decreasing limit `η = inf_k P_θ(a (u ∨ (v-k)) + (1-a) v)` is not identically
`-∞`.

The conclusion is `∃ x, η x ≠ ⊥`, which is literally
`xia-sgpt:page-0085`'s "it remains to show that `η ≢ -∞`", and NOT the stronger
`LocallyNondegenerate η`.  The two are equivalent here, but only because the
identity principle is available: `η` is `θ`-PSH
(`RooftopConvexCombBarrierTruncatedLimit.thetaPlurisubharmonic_truncatedAffineLimit`)
and `M` is connected, so
`ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot` upgrades one
finite value to local nondegeneracy.  Asking the interface for the upgraded form
would be asking for more than the source proves, so the upgrade is done here
instead (`locallyNondegenerate_truncatedAffineLimit`). -/
def HasNondegenerateTruncatedAffineLimit (theta : ClosedRealOneOneForm n M) (a : ℝ) : Prop :=
  ∀ (u v : M → EReal) (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v), u ≤ v → v ≤ 0 →
    singularityEnvelope theta.val v = v →
    0 < diagonalPotentialMass theta u hu →
    ConvexCombEnvelopeMass.IsAdmissibleWeight n (diagonalPotentialMass theta u hu)
      (diagonalPotentialMass theta v hv) a →
    ∃ x : M, truncatedAffineLimit theta.val a u v x ≠ ⊥

omit [MeasurableSpace M] [BorelSpace M] in
/-- **The identity principle closes the gap between Xia's `η ≢ -∞` and the local
nondegeneracy the potential predicate needs.**  Proved, not assumed. -/
theorem locallyNondegenerate_truncatedAffineLimit [ConnectedSpace M]
    {theta : ClosedRealOneOneForm n M} {a : ℝ} (ha : 1 < a)
    {u v : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (hle : u ≤ v)
    (hne : ∃ x : M, truncatedAffineLimit theta.val a u v x ≠ ⊥) :
    LocallyNondegenerate (truncatedAffineLimit theta.val a u v) :=
  ThetaPshIdentityPrinciple.locallyNondegenerate_of_exists_ne_bot
    (thetaPlurisubharmonic_truncatedAffineLimit hle hu hv ha) hne

/-- **Xia, SGPT, Lemma 2.4.4, Step 1.3, in the predicate form the Step-1
assembly consumes** (`xia-sgpt:page-0085`--`xia-sgpt:page-0086`).  Proved, for a
connected `M`, in `Pending.ThetaPshTruncatedAffineLimitMassChain`; see that
module for the chain and for the two source-anchored inputs it rests on.

Xia's normalization `ϕ ≤ 0` is part of this predicate but is not used by the
proof, so it is discarded here. -/
theorem hasNondegenerateTruncatedAffineLimit [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M) (a : ℝ) :
    HasNondegenerateTruncatedAffineLimit (n := n) theta a :=
  fun _u _v hu hv hle _hv0 hfix hpos hadm =>
    ThetaPshTruncatedAffineLimitMassChain.exists_ne_bot_truncatedAffineLimit
      omega theta hu hv hle hfix hpos hadm

end

end SGPT.Foundations.Analysis.Pending.ThetaPshTruncatedAffineLimit
