import SGPT.Foundations.Analysis.Pending.ConvexCombEnvelopeBarrierInterface
import SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierStepOne
import SGPT.Foundations.Analysis.Pending.ThetaPshModelReference

set_option autoImplicit false

/-!
# Step 1.2 of Xia's Lemma 2.4.4: the reference may be taken normalized and `P`-fixed

Xia's Step 1.2 (`xia-sgpt:page-0084`) reduces Lemma 2.4.4 to the case where the
less singular potential `ψ` is replaced by the limit `φ_∞` of the increasing
transfinite sequence `ψ_0 = ψ`, `ψ_{α+1} = P_θ[ψ_α]`.  What the rest of the
proof uses about `φ_∞` is only:

* `ψ ≤ φ_∞ ≤ 0`;
* `∫ θ_{φ_∞}^n = ∫ θ_ψ^n`, so the admissible interval (2.28) is unchanged;
* `P_θ[φ_∞] = φ_∞`, which is what (2.34) needs.

This module performs that reduction, taking the stabilization itself from
`Pending.ThetaPshModelReference.exists_thetaPsh_modelReference`, which is now
**proved** there (Zorn's lemma on the admissible references, with Choquet's
lemma supplying the limit-ordinal step).  What is proved here is everything
else: Xia's normalization `φ ≤ ψ ≤ 0` is discharged
rather than assumed (the statement is invariant under a common real shift, and a
compact `θ`-PSH potential has a finite global upper bound), the mass
bookkeeping that keeps the admissible interval (2.28) unchanged, and the
monotone transfer of (2.29) from `ϕ` back to `ψ`.

The positive-mass idempotence `P_θ[P_θ[ψ]] = P_θ[ψ]` would give the fixed point
in one step and is **deliberately not used**: its `sorryAx` is Step 1 of Lemma
2.4.4 itself, through `Pending.DominationPrincipleMiddleStage`, so it would turn
the reduction into a round trip through a corollary of its own target.  See the
docstring of `Pending.ThetaPshModelReference`.

## What this gives

`exists_thetaPsh_convexCombBarrier_of_modelReference` has **exactly** the
conclusion of Xia's Step 1, i.e. of
`Pending.ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`, and derives
it from two strictly smaller inputs, the first of which is now discharged:

* `Pending.ThetaPshModelReference.exists_thetaPsh_modelReference` — the
  transfinite stabilization, which mentions only `P_θ`, the singularity order
  and the mass; **proved**, so it is no longer a boundary;
* `ModelReferenceStepOne` — Step 1 restricted to references that are already
  normalized and `P`-fixed.

The residue inside `ModelReferenceStepOne` is therefore Steps 1.1 and 1.3 for a
model reference; Step 1.1 is proved in
`Pending.RooftopConvexCombBarrierStepOne`, and Step 1.3 is the only piece that
consumes Xia's Theorem 2.4.4 for the affine obstacle.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierModelReduction

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.DiagonalMeasureRegularity
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-! ### A common real shift -/

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M] [Nonempty M] in
/-- Shifting both entries of a convex combination by the same real constant
shifts the combination by it.  The weights sum to `1`, which is the only thing
used. -/
theorem convexComb_add_coe {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (u v : M → EReal) (c : ℝ) (x : M) :
    convexComb t (fun y => u y + (c : EReal)) (fun y => v y + (c : EReal)) x =
      convexComb t u v x + (c : EReal) := by
  have ht1' : (0 : ℝ) < 1 - t := by linarith
  have hsum : ((t * c : ℝ) : EReal) + (((1 - t) * c : ℝ) : EReal) = (c : EReal) := by
    rw [← EReal.coe_add]
    congr 1
    ring
  simp only [convexComb_apply]
  rw [coe_mul_add_coe ht0, coe_mul_add_coe ht1']
  calc (t : EReal) * u x + ((t * c : ℝ) : EReal) +
        (((1 - t : ℝ) : EReal) * v x + (((1 - t) * c : ℝ) : EReal))
      = (t : EReal) * u x + ((1 - t : ℝ) : EReal) * v x +
          (((t * c : ℝ) : EReal) + (((1 - t) * c : ℝ) : EReal)) := by
        abel
    _ = (t : EReal) * u x + ((1 - t : ℝ) : EReal) * v x + (c : EReal) := by
        rw [hsum]

omit [Nonempty M] in
/-- The diagonal mass is invariant under adding a real constant to the
potential. -/
theorem diagonalPotentialMass_add_const (theta : ClosedRealOneOneForm n M)
    {v : M → EReal} (hv : IsThetaPshPotential theta.val v) (C : ℝ)
    (hvC : IsThetaPshPotential theta.val (fun x => v x + (C : EReal))) :
    diagonalPotentialMass theta (fun x => v x + (C : EReal)) hvC =
      diagonalPotentialMass theta v hv := by
  unfold diagonalPotentialMass
  rw [diagonalPotentialMeasure_add_const theta hv C hvC]

/-! ### Step 1 for a normalized `P`-fixed reference -/

/-- The conclusion of Xia's Step 1.2 stabilization, as a predicate on the
background alone: every normalized `θ`-PSH potential is dominated by a
`P`-fixed normalized potential of the same diagonal mass.

Keeping it as a named predicate is what makes the reduction below *checkably*
independent of Step 1: the version of the reduction that takes this predicate as
a hypothesis is sorry-free, so the only external input of the interface version
is `Pending.ThetaPshModelReference.exists_thetaPsh_modelReference`. -/
def HasModelReference (theta : ClosedRealOneOneForm n M) : Prop :=
  ∀ (psi : M → EReal) (hpsi : IsThetaPshPotential theta.val psi), psi ≤ 0 →
    ∃ (Phi : M → EReal) (hPhi : IsThetaPshPotential theta.val Phi),
      psi ≤ Phi ∧ Phi ≤ 0 ∧ singularityEnvelope theta.val Phi = Phi ∧
        diagonalPotentialMass theta Phi hPhi = diagonalPotentialMass theta psi hpsi

/-- **Step 1 of Xia's Lemma 2.4.4, restricted to a model reference.**  The
reference `v` is asked to be normalized (`v ≤ 0`) and a fixed point of the
`P`-envelope (`P_θ[v] = v`), which is exactly the situation Xia's Step 1.2
arranges before running Steps 1.1 and 1.3.

This is a *hypothesis* of the reduction below, not a new source boundary: the
reduction proves the unrestricted Step 1 from it. -/
def ModelReferenceStepOne (theta : ClosedRealOneOneForm n M) (a : ℝ) : Prop :=
  ∀ (u v : M → EReal) (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v), u ≤ v → v ≤ 0 →
    singularityEnvelope theta.val v = v →
    0 < diagonalPotentialMass theta u hu →
    ConvexCombEnvelopeMass.IsAdmissibleWeight n (diagonalPotentialMass theta u hu)
      (diagonalPotentialMass theta v hv) a →
    ∃ eta : M → EReal, IsThetaPshPotential theta.val eta ∧ convexComb a⁻¹ eta v ≤ u

/-- **Xia's Step 1.2** (`xia-sgpt:page-0084`).  Step 1 of Lemma 2.4.4 in
general follows from Step 1 for a normalized `P`-fixed reference.

The conclusion is byte-identical to that of
`Pending.ConvexCombEnvelopeMass.exists_thetaPsh_convexCombBarrier`, so this is a
reduction of that source boundary and not a restatement of it.  The stabilization
of the transfinite `P_θ`-chain is the hypothesis `hstab`; everything else is
proved here — Xia's normalization `φ ≤ ψ ≤ 0` by the shift invariance above, and
the mass bookkeeping that keeps the admissible interval (2.28) unchanged by
`diagonalPotentialMass_add_const`.  This version is deliberately stated with
`hstab` as a predicate rather than with the interface discharged, so that
`#print axioms` on it exhibits the reduction as sorry-free.

The positive-mass idempotence of `P_θ` (Xia's Theorem 3.1.2) is **not** used to
discharge `hstab`; see the module docstring for why that would be circular. -/
theorem exists_thetaPsh_convexCombBarrier_of_hasModelReference
    (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    {a : ℝ}
    (ha : ConvexCombEnvelopeMass.IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a)
    (hstab : HasModelReference (n := n) theta)
    (hmodel : ModelReferenceStepOne (n := n) theta a) :
    ∃ eta : M → EReal, IsThetaPshPotential theta.val eta ∧ convexComb a⁻¹ eta psi ≤ phi := by
  classical
  have ha1 : 1 < a := ha.one_lt
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha1
  have hinv0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have hinv1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha1
  -- Xia's normalization: shift both potentials below zero.
  obtain ⟨B, hB⟩ := hpsi.exists_global_upper_bound
  set phi' : M → EReal := fun x => phi x + ((-B : ℝ) : EReal) with hphi'def
  set psi' : M → EReal := fun x => psi x + ((-B : ℝ) : EReal) with hpsi'def
  have hphi' : IsThetaPshPotential theta.val phi' := hphi.add_const (-B)
  have hpsi' : IsThetaPshPotential theta.val psi' := hpsi.add_const (-B)
  have hle' : phi' ≤ psi' := fun x => add_le_add (hle x) le_rfl
  have hpsi'0 : psi' ≤ 0 := by
    intro x
    have h := hB x
    calc psi x + ((-B : ℝ) : EReal) ≤ (B : EReal) + ((-B : ℝ) : EReal) :=
          add_le_add h le_rfl
      _ = 0 := by rw [← EReal.coe_add]; norm_num
  have hmphi' : diagonalPotentialMass theta phi' hphi' = diagonalPotentialMass theta phi hphi :=
    diagonalPotentialMass_add_const theta hphi (-B) hphi'
  have hmpsi' : diagonalPotentialMass theta psi' hpsi' = diagonalPotentialMass theta psi hpsi :=
    diagonalPotentialMass_add_const theta hpsi (-B) hpsi'
  -- Xia's transfinite stabilization supplies the model reference.
  obtain ⟨Phi, hPhi, hpsiPhi, hPhi0, hfix, hmPhi⟩ := hstab psi' hpsi' hpsi'0
  have hlePhi : phi' ≤ Phi := fun x => (hle' x).trans (hpsiPhi x)
  have hposphi' : 0 < diagonalPotentialMass theta phi' hphi' := by rwa [hmphi']
  have hadm : ConvexCombEnvelopeMass.IsAdmissibleWeight n
      (diagonalPotentialMass theta phi' hphi') (diagonalPotentialMass theta Phi hPhi) a := by
    rw [hmphi', hmPhi, hmpsi']
    exact ha
  obtain ⟨eta', heta', hbar'⟩ :=
    hmodel phi' Phi hphi' hPhi hlePhi hPhi0 hfix hposphi' hadm
  -- Undo the shift.
  refine ⟨fun x => eta' x + (B : EReal), heta'.add_const B, fun x => ?_⟩
  have hshift : convexComb a⁻¹ (fun y => eta' y + (B : EReal)) psi x +
      ((-B : ℝ) : EReal) = convexComb a⁻¹ eta' psi' x := by
    have h := convexComb_add_coe (t := a⁻¹) hinv0 hinv1
      (fun y => eta' y + (B : EReal)) psi (-B) x
    have hcancel : (fun y => (eta' y + (B : EReal)) + ((-B : ℝ) : EReal)) = eta' := by
      funext y
      rw [add_assoc, ← EReal.coe_add]
      norm_num
    rw [hcancel] at h
    exact h.symm
  have hchain : convexComb a⁻¹ eta' psi' x ≤ phi' x :=
    (convexComb_mono hinv0.le hinv1.le (le_refl eta') hpsiPhi x).trans (hbar' x)
  have hkey : convexComb a⁻¹ (fun y => eta' y + (B : EReal)) psi x +
      ((-B : ℝ) : EReal) ≤ phi x + ((-B : ℝ) : EReal) := by
    rw [hshift]
    exact hchain
  -- Cancel the finite shift.
  have := add_le_add hkey (le_refl ((B : ℝ) : EReal))
  calc convexComb a⁻¹ (fun y => eta' y + (B : EReal)) psi x
      = convexComb a⁻¹ (fun y => eta' y + (B : EReal)) psi x + ((-B : ℝ) : EReal) +
          ((B : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]
        norm_num
    _ ≤ phi x + ((-B : ℝ) : EReal) + ((B : ℝ) : EReal) := this
    _ = phi x := by rw [add_assoc, ← EReal.coe_add]; norm_num

/-- **Xia's Step 1.2, with the stabilization taken from its named interface.**
Identical in statement to
`exists_thetaPsh_convexCombBarrier_of_hasModelReference` with `hstab`
discharged by `Pending.ThetaPshModelReference.exists_thetaPsh_modelReference`. -/
theorem exists_thetaPsh_convexCombBarrier_of_modelReference [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {phi psi : M → EReal}
    (hphi : IsThetaPshPotential theta.val phi)
    (hpsi : IsThetaPshPotential theta.val psi) (hle : phi ≤ psi)
    (hpos : 0 < diagonalPotentialMass theta phi hphi)
    {a : ℝ}
    (ha : ConvexCombEnvelopeMass.IsAdmissibleWeight n (diagonalPotentialMass theta phi hphi)
      (diagonalPotentialMass theta psi hpsi) a)
    (hmodel : ModelReferenceStepOne (n := n) theta a) :
    ∃ eta : M → EReal, IsThetaPshPotential theta.val eta ∧ convexComb a⁻¹ eta psi ≤ phi :=
  exists_thetaPsh_convexCombBarrier_of_hasModelReference theta hphi hpsi hle hpos ha
    (fun _v hv hv0 =>
      Pending.ThetaPshModelReference.exists_thetaPsh_modelReference omega theta hv hv0)
    hmodel

end

end SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierModelReduction
