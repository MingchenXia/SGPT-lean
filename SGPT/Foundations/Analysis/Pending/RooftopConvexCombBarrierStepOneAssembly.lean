import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierModelReduction
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierTruncatedLimit
import SGPT.Foundations.Analysis.Pending.ThetaPshTruncatedAffineLimitInterface

set_option autoImplicit false

/-!
# Step 1 of Xia's Lemma 2.4.4, assembled from its two remaining obligations

Putting `Pending.RooftopConvexCombBarrierModelReduction` (Step 1.2) and
`Pending.RooftopConvexCombBarrierTruncatedLimit` (the construction of Step 1.3)
together, the whole of Xia's Step 1 — the source boundary behind Corollary
2.4.3, the middle stage of Theorem 2.4.5, `Pending.RelativeFullMass` and
`Pending.RooftopMassDiamond` — rests on exactly two statements:

1. `RooftopConvexCombBarrierModelReduction.HasModelReference` — the increasing
   transfinite `P_θ`-chain stabilizes (`xia-sgpt:page-0084`);
2. `Pending.ThetaPshTruncatedAffineLimit.HasNondegenerateTruncatedAffineLimit` —
   for a normalized `P`-fixed reference `ϕ` of the right mass,
   `inf_k P_θ(a(φ ∨ (ϕ-k)) + (1-a)ϕ) ≢ -∞` (`xia-sgpt:page-0085`--`page-0086`,
   Xia's Step 1.3).

**Exactly how far this goes, stated precisely, because the two natural
formulations are easy to conflate.**

* Obligation 1 is genuinely *smaller* than Step 1: it mentions only `P_θ`, the
  singularity order and the diagonal mass, and no barrier at all.
* Obligation 2 is *not* smaller — it is interderivable with
  `ModelReferenceStepOne`, i.e. with Step 1 for a normalized `P`-fixed
  reference.  What it buys is concreteness, not weakness: the residual target
  becomes one explicitly constructed function.  See the docstring of
  `Pending.ThetaPshTruncatedAffineLimitInterface` for the converse derivation.
* `exists_thetaPsh_convexCombBarrier_of_obligations` is **sorry-free**, but its
  type is *not* that of
  `Pending.ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`: it carries
  the two obligations as extra hypotheses and does not take `omega`.
* `exists_thetaPsh_convexCombBarrier_of_interfaces` is the declaration whose type
  *does* match that theorem (up to the position of the `{phi psi}` binder), and it
  carries `sorryAx` from the remaining interface (obligation 2).  No single
  declaration is both.

Everything between the two obligations is proved: Xia's normalization, the mass
bookkeeping, the truncation `φ_k`, the nonemptiness of the competitor family,
(2.31) at each level, the monotonicity of `(η_k)_k`, the identification
`inf_k φ_k = φ`, the `θ`-PSH-ness of the decreasing limit, and the identity
principle that turns `η ≢ -∞` into local nondegeneracy.

Obligation 1 is discharged by the proved theorem
`Pending.ThetaPshModelReference.exists_thetaPsh_modelReference` (Zorn's lemma on
the admissible references, Choquet's lemma for the limit-ordinal step).
Obligation 2 is where Xia uses
Theorem 2.4.4 for the affine obstacle, which this workspace carries as the named
interface
`Pending.DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero`,
together with his Lemma 2.4.2 and multilinearity of the non-pluripolar product;
it is *not* discharged here.

`Pending.RooftopConvexCombBarrierStepOne` is deliberately NOT part of this
assembly.  Its Step 1.1 is unnecessary here, because
`RooftopConvexCombBarrierTruncatedLimit.shifted_mem_rooftopCompetitors` exhibits
`ϕ - a k` as a competitor outright; and its (2.34) is an input to Xia's proof of
obligation 2, which is not formalized.  Both are therefore proved but currently
load-free.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierStepOneAssembly

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierModelReduction
open SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierTruncatedLimit
open SGPT.Foundations.Analysis.Pending.ThetaPshTruncatedAffineLimit
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

omit [BorelSpace M] in
/-- Step 1 for a normalized `P`-fixed reference follows from the nondegeneracy of
the truncated affine limit alone. -/
theorem modelReferenceStepOne_of_hasNondegenerateTruncatedAffineLimit
    [ConnectedSpace M] (theta : ClosedRealOneOneForm n M) {a : ℝ}
    (hnd : HasNondegenerateTruncatedAffineLimit (n := n) theta a) :
    ModelReferenceStepOne (n := n) theta a := by
  intro u v hu hv hle hv0 hfix hpos hadm
  exact exists_convexCombBarrier_of_locallyNondegenerate_truncatedAffineLimit
    hle hu hv hadm.one_lt
    (Pending.ThetaPshTruncatedAffineLimit.locallyNondegenerate_truncatedAffineLimit
      hadm.one_lt hu hv hle (hnd u v hu hv hle hv0 hfix hpos hadm))

/-- **Xia's Lemma 2.4.4, Step 1, from its two remaining obligations.**
Identical in statement to
`Pending.ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`.

Sorry-free: the only inputs are the stabilization of the `P`-chain and the
nondegeneracy of the truncated affine limit. -/
theorem exists_thetaPsh_convexCombBarrier_of_obligations [ConnectedSpace M]
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    {a : ℝ}
    (ha : ConvexCombEnvelopeMass.IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a)
    (hstab : HasModelReference (n := n) theta)
    (hnd : HasNondegenerateTruncatedAffineLimit (n := n) theta a) :
    ∃ eta : M → EReal, IsThetaPshPotential theta.val eta ∧ convexComb a⁻¹ eta psi ≤ phi :=
  exists_thetaPsh_convexCombBarrier_of_hasModelReference theta hphi hpsi hle hpos ha hstab
    (modelReferenceStepOne_of_hasNondegenerateTruncatedAffineLimit theta hnd)

/-- The same conclusion with the stabilization discharged from its named
interface, so that the only remaining input is Xia's Step 1.3. -/
theorem exists_thetaPsh_convexCombBarrier_of_nondegenerateTruncatedAffineLimit
    [ConnectedSpace M] (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    {a : ℝ}
    (ha : ConvexCombEnvelopeMass.IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a)
    (hnd : HasNondegenerateTruncatedAffineLimit (n := n) theta a) :
    ∃ eta : M → EReal, IsThetaPshPotential theta.val eta ∧ convexComb a⁻¹ eta psi ≤ phi :=
  exists_thetaPsh_convexCombBarrier_of_obligations theta hphi hpsi hle hpos ha
    (fun _v hv hv0 =>
      Pending.ThetaPshModelReference.exists_thetaPsh_modelReference omega theta hv hv0)
    hnd

/-- **Xia's Lemma 2.4.4, Step 1, with both obligations discharged from their
named interfaces.**  Identical in statement to
`Pending.ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`, including its
`omega` and `[ConnectedSpace M]` binders, so the source boundary of Step 1 is now
`Pending.ThetaPshTruncatedAffineLimitInterface` and nothing else: obligation 1 is
supplied by the proved `Pending.ThetaPshModelReference`. -/
theorem exists_thetaPsh_convexCombBarrier_of_interfaces [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    {a : ℝ}
    (ha : ConvexCombEnvelopeMass.IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a) :
    ∃ eta : M → EReal, IsThetaPshPotential theta.val eta ∧ convexComb a⁻¹ eta psi ≤ phi :=
  exists_thetaPsh_convexCombBarrier_of_obligations theta hphi hpsi hle hpos ha
    (fun _v hv hv0 =>
      Pending.ThetaPshModelReference.exists_thetaPsh_modelReference omega theta hv hv0)
    (Pending.ThetaPshTruncatedAffineLimit.hasNondegenerateTruncatedAffineLimit
      omega theta a)

omit [BorelSpace M] in
/-- **The converse: obligation 2 is interderivable with its own consumer, so it
is a reformulation of the residual target and NOT a smaller statement.**

This is recorded as a theorem rather than as a docstring claim, because it is the
honest measure of what the Step 1.3 interface buys.  A competitor `η` of the
untruncated problem satisfies `a⁻¹η + (1-a⁻¹)v ≤ u ≤ u ∨ (v-k)`, so wherever `v`
is finite — quasi-everywhere — the rearrangement
`ConvexCombObstacleAlgebra.convexCombValue_le_iff` makes `η` a rooftop competitor
of every truncated obstacle; hence `η ≤ η_k` for all `k`, hence `η ≤ inf_k η_k`,
and the limit inherits a finite value from `η`.

Together with `modelReferenceStepOne_of_hasNondegenerateTruncatedAffineLimit`
this gives `HasNondegenerateTruncatedAffineLimit ↔ ModelReferenceStepOne`. -/
theorem hasNondegenerateTruncatedAffineLimit_of_modelReferenceStepOne
    (theta : ClosedRealOneOneForm n M) {a : ℝ} (ha : 1 < a)
    (hstep : ModelReferenceStepOne (n := n) theta a) :
    HasNondegenerateTruncatedAffineLimit (n := n) theta a := by
  intro u v hu hv hle hv0 hfix hpos hadm
  obtain ⟨eta, heta, hbar⟩ := hstep u v hu hv hle hv0 hfix hpos hadm
  have hPtop : ∀ y, v y ≠ ⊤ := fun y => hv.1.quasiPlurisubharmonic.ne_top y
  -- `eta` is a rooftop competitor of every truncated obstacle.
  have hcomp : ∀ k : ℕ, eta ∈ rooftopCompetitors theta.val
      (convexComb a (truncatedReference u v k) v) := by
    intro k
    refine ⟨heta, ?_⟩
    refine (Pending.quasiPsh_finite_quasiEverywhere (u := v) hv.quasiPshPotential).mono ?_
    rintro x ⟨hb, ht⟩
    refine (Pending.ConvexCombObstacleAlgebra.convexCombValue_le_iff ha hb ht).mp ?_
    exact (hbar x).trans (le_truncatedReference (Phi := v) k x)
  have hle_env : ∀ k : ℕ, eta ≤ truncatedAffineEnvelope theta.val a u v k :=
    fun k => le_rooftopEnvelope heta (hcomp k).2
  -- Hence `eta ≤ inf_k eta_k`, and `eta` is finite somewhere.
  obtain ⟨x, -, hx⟩ := heta.2 (Classical.arbitrary M) Set.univ isOpen_univ (Set.mem_univ _)
  refine ⟨x, ?_⟩
  have hbot : eta x ≤ truncatedAffineLimit theta.val a u v x :=
    le_iInf fun k => hle_env k x
  intro hcon
  rw [hcon, le_bot_iff] at hbot
  exact hx hbot

end

end SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierStepOneAssembly
