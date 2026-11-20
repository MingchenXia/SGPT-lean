import SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
import SGPT.Foundations.Analysis.Pending.IEnvelopeStrongOpenness
import SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
import SGPT.Foundations.Analysis.Pending.RooftopFeasibility
import SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

set_option autoImplicit false

/-!
# Step 1.3 of Xia's Lemma 2.4.4: the construction, and what is left to prove

Xia's Step 1.3 (`xia-sgpt:page-0085`--`xia-sgpt:page-0086`) finishes Step 1 of
Lemma 2.4.4 for a reference `ϕ` fixed by the `P`-envelope.  For each `k > 0` he
sets

  `φ_k = φ ∨ (ϕ - k)`,   `η_k = P_θ(a φ_k + (1-a) ϕ)`,   `η = inf_k η_k`,

observes that `η` satisfies (2.33) automatically, and then spends the whole of
Step 1.3 on the single remaining point: **`η ≢ -∞`**.

This module builds `φ_k`, `η_k`, `η` and proves everything except that point:

* `truncatedReference_isThetaPshPotential`, `truncatedReference_le_reference`,
  `reference_sub_le_truncatedReference` — `ϕ - k ≤ φ_k ≤ ϕ`, so `φ_k ∼ ϕ`;
* `shifted_mem_rooftopCompetitors` — `ϕ - a k` is already a competitor of the
  obstacle `a φ_k + (1-a) ϕ`, so the family is nonempty *without* Step 1.1;
* `truncatedAffineEnvelope_isThetaPshPotential` — hence `η_k ∈ PSH(X, θ)`;
* `convexComb_truncatedAffineEnvelope_le` — Xia's (2.31) at level `k`:
  `a⁻¹ η_k + (1-a⁻¹) ϕ ≤ φ_k`;
* `truncatedAffineEnvelope_antitone` — `(η_k)_k` is decreasing;
* `iInf_truncatedReference` — `inf_k φ_k = φ`, which is where the truncation
  disappears;
* `thetaPlurisubharmonic_truncatedAffineLimit` — `η` is `θ`-PSH as a decreasing
  limit, with **no** nondegeneracy claimed;
* `exists_convexCombBarrier_of_locallyNondegenerate_truncatedAffineLimit` — the
  reduction: once `η` is locally nondegenerate, Xia's (2.33) holds.

So the entire analytic content of Step 1, for a `P`-fixed reference, is
`LocallyNondegenerate (truncatedAffineLimit θ a φ ϕ)`.  Xia proves it by
contradiction from (2.35), which uses his Theorem 2.4.4 for the affine obstacle
(`Pending.DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero`),
Lemma 2.4.2, and multilinearity of the non-pluripolar product; the named form of
that residue is `Pending.ThetaPshTruncatedAffineLimitInterface`.

Note that nothing in this module uses `P_θ[ϕ] = ϕ`, positivity of the mass, or a
measure: the fixed-point hypothesis enters only in Step 1.3's contradiction,
through (2.34).
-/

open Set MeasureTheory Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierTruncatedLimit

open FirstPass
open SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
open SGPT.Foundations.Analysis.Pending.RooftopEnvelopeAeObstacle
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.ThetaPshDecreasingLimit

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### The truncated reference `φ_k = φ ∨ (ϕ - k)` -/

/-- Xia's `φ_k = φ ∨ (ϕ - k)` (`xia-sgpt:page-0085`). -/
def truncatedReference (phi Phi : M → EReal) (k : ℕ) : M → EReal :=
  fun x => Max.max (phi x) (Phi x + ((-(k : ℝ) : ℝ) : EReal))

/-- Xia's `η_k = P_θ(a φ_k + (1-a) ϕ)`. -/
def truncatedAffineEnvelope (theta : SmoothRealForm n M 2) (a : ℝ)
    (phi Phi : M → EReal) (k : ℕ) : M → EReal :=
  rooftopEnvelope theta (convexComb a (truncatedReference phi Phi k) Phi)

/-- Xia's `η = inf_k η_k`. -/
def truncatedAffineLimit (theta : SmoothRealForm n M 2) (a : ℝ)
    (phi Phi : M → EReal) : M → EReal :=
  fun x => ⨅ k, truncatedAffineEnvelope theta a phi Phi k x

variable {theta : SmoothRealForm n M 2} {phi Phi : M → EReal}

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- `ϕ - k ≤ φ_k`. -/
theorem reference_sub_le_truncatedReference (k : ℕ) (x : M) :
    Phi x + ((-(k : ℝ) : ℝ) : EReal) ≤ truncatedReference phi Phi k x :=
  le_max_right _ _

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- `φ ≤ φ_k`. -/
theorem le_truncatedReference (k : ℕ) (x : M) :
    phi x ≤ truncatedReference phi Phi k x :=
  le_max_left _ _

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- A non-`⊤` extended real is a real coercion once it is not `⊥`. -/
theorem exists_coe_of_ne {A : EReal} (hAtop : A ≠ ⊤) (hAbot : A ≠ ⊥) :
    ∃ r : ℝ, A = (r : EReal) :=
  ⟨A.toReal, (EReal.coe_toReal hAtop hAbot).symm⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- `φ_k ≤ ϕ`, because `φ ≤ ϕ` and `ϕ` is not `⊤`. -/
theorem truncatedReference_le_reference (hle : phi ≤ Phi)
    (hPtop : ∀ x, Phi x ≠ ⊤) (k : ℕ) : truncatedReference phi Phi k ≤ Phi := by
  intro x
  refine max_le (hle x) ?_
  rcases eq_or_ne (Phi x) ⊥ with hb | hb
  · rw [hb, EReal.bot_add]
  · obtain ⟨p, hp⟩ := exists_coe_of_ne (hPtop x) hb
    rw [hp, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (by simp)

/-- `φ_k` is a genuine `θ`-PSH potential. -/
theorem truncatedReference_isThetaPshPotential
    (hphi : IsThetaPshPotential theta phi) (hPhi : IsThetaPshPotential theta Phi)
    (k : ℕ) : IsThetaPshPotential theta (truncatedReference phi Phi k) :=
  Pending.IsThetaPshPotential.max hphi (hPhi.add_const (-(k : ℝ)))

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- `(φ_k)_k` is decreasing. -/
theorem truncatedReference_antitone (hPtop : ∀ x, Phi x ≠ ⊤) (x : M) :
    Antitone fun k : ℕ => truncatedReference phi Phi k x := by
  intro j k hjk
  refine max_le_max le_rfl ?_
  rcases eq_or_ne (Phi x) ⊥ with hb | hb
  · rw [hb, EReal.bot_add, EReal.bot_add]
  · obtain ⟨p, hp⟩ := exists_coe_of_ne (hPtop x) hb
    rw [hp, ← EReal.coe_add, ← EReal.coe_add]
    refine EReal.coe_le_coe_iff.mpr ?_
    have : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
    linarith

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- **`inf_k φ_k = φ`.**  Where `ϕ` is finite the truncation is inactive for
large `k`; at a pole of `ϕ` the shift does nothing and `φ` is a pole too. -/
theorem iInf_truncatedReference (hle : phi ≤ Phi) (hPtop : ∀ x, Phi x ≠ ⊤) (x : M) :
    (⨅ k : ℕ, truncatedReference phi Phi k x) = phi x := by
  refine le_antisymm ?_ (le_iInf fun k => le_truncatedReference (phi := phi) k x)
  rcases eq_or_ne (Phi x) ⊥ with hb | hb
  · have hphibot : phi x = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [← hb]
      exact hle x
    refine (iInf_le _ 0).trans (le_of_eq ?_)
    show Max.max (phi x) (Phi x + ((-((0 : ℕ) : ℝ) : ℝ) : EReal)) = phi x
    rw [hb, EReal.bot_add, hphibot, max_self]
  · obtain ⟨p, hp⟩ := exists_coe_of_ne (hPtop x) hb
    rcases eq_or_ne (phi x) ⊥ with hq | hq
    · -- The truncated values are `p - k`, whose infimum is `⊥`.
      rw [hq, le_bot_iff, iInf_eq_bot]
      intro b hbpos
      obtain ⟨r, hr⟩ : ∃ r : ℝ, (r : EReal) ≤ b := by
        induction b with
        | bot => exact absurd hbpos (lt_irrefl ⊥)
        | top => exact ⟨0, le_top⟩
        | coe r => exact ⟨r, le_rfl⟩
      obtain ⟨k, hk⟩ := exists_nat_gt (p - r)
      refine ⟨k, lt_of_lt_of_le ?_ hr⟩
      have hterm : truncatedReference phi Phi k x = ((p + -(k : ℝ) : ℝ) : EReal) := by
        show Max.max (phi x) (Phi x + ((-((k : ℕ) : ℝ) : ℝ) : EReal)) = _
        rw [hq, hp, ← EReal.coe_add]
        exact max_eq_right bot_le
      rw [hterm]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
    · -- `φ x` is finite; the truncation is inactive once `k` is large.
      have hqtop : phi x ≠ ⊤ := by
        intro h
        have := hle x
        rw [h, hp] at this
        exact absurd (top_le_iff.mp this) (EReal.coe_ne_top _)
      obtain ⟨q, hqe⟩ := exists_coe_of_ne hqtop hq
      obtain ⟨k, hk⟩ := exists_nat_gt (p - q)
      refine (iInf_le _ k).trans (le_of_eq ?_)
      show Max.max (phi x) (Phi x + ((-((k : ℕ) : ℝ) : ℝ) : EReal)) = phi x
      rw [hqe, hp, ← EReal.coe_add]
      exact max_eq_left (EReal.coe_le_coe_iff.mpr (by linarith))

/-! ### The truncated affine envelope `η_k` -/

/-- **The shifted reference is already a competitor.**  `ϕ - a k` satisfies the
barrier inequality for `φ_k` by the very definition of the truncation, so the
competitor family of `a φ_k + (1-a) ϕ` is nonempty without Step 1.1. -/
theorem shifted_mem_rooftopCompetitors
    (hPhi : IsThetaPshPotential theta Phi) {a : ℝ} (ha : 1 < a) (k : ℕ) :
    (fun x => Phi x + ((-(a * k) : ℝ) : EReal)) ∈
      rooftopCompetitors theta (convexComb a (truncatedReference phi Phi k) Phi) := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  refine mem_rooftopCompetitors_of_le (hPhi.add_const _) fun x => ?_
  have hPtop : Phi x ≠ ⊤ := hPhi.1.quasiPlurisubharmonic.ne_top x
  simp only [convexComb_apply]
  rcases eq_or_ne (Phi x) ⊥ with hb | hb
  · rw [hb, EReal.bot_add]
    exact bot_le
  · obtain ⟨p, hp⟩ := exists_coe_of_ne hPtop hb
    have hAle : ((p + -(k : ℝ) : ℝ) : EReal) ≤ truncatedReference phi Phi k x := by
      have h := reference_sub_le_truncatedReference (phi := phi) (Phi := Phi) k x
      rwa [hp, ← EReal.coe_add] at h
    rw [hp]
    calc (p : EReal) + ((-(a * k) : ℝ) : EReal)
        = (a : EReal) * ((p + -(k : ℝ) : ℝ) : EReal) +
            ((1 - a : ℝ) : EReal) * (p : EReal) := by
          rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add]
          exact EReal.coe_eq_coe_iff.mpr (by ring)
      _ ≤ (a : EReal) * truncatedReference phi Phi k x +
            ((1 - a : ℝ) : EReal) * (p : EReal) :=
          add_le_add (mul_le_mul_of_nonneg_left hAle (EReal.coe_nonneg.mpr ha0.le)) le_rfl

variable [CompactSpace M] [Nonempty M]

/-- The competitor family of the truncated obstacle is uniformly bounded above,
because every competitor lies below `φ_k ≤ ϕ`. -/
theorem rooftopCompetitors_truncated_bddAbove (hle : phi ≤ Phi)
    (hphi : IsThetaPshPotential theta phi) (hPhi : IsThetaPshPotential theta Phi)
    {a : ℝ} (ha : 1 < a) (k : ℕ) :
    ∃ B : ℝ, ∀ g ∈ rooftopCompetitors theta (convexComb a (truncatedReference phi Phi k) Phi),
      ∀ x, g x ≤ (B : EReal) := by
  obtain ⟨B, hB⟩ := hPhi.exists_global_upper_bound
  have hPtop : ∀ x, Phi x ≠ ⊤ := fun x => hPhi.1.quasiPlurisubharmonic.ne_top x
  have htrunc := truncatedReference_le_reference (phi := phi) (Phi := Phi) hle hPtop k
  refine ⟨B, fun g hg x => ?_⟩
  have hgle : g ≤ truncatedReference phi Phi k :=
    hg.1.1.le_of_quasiEverywhere_le
      (truncatedReference_isThetaPshPotential hphi hPhi k).1
      (hg.2.mono fun y hy => hy.trans
        (convexCombValue_le_left ha (htrunc y) (hPtop y)))
  exact (hgle x).trans ((htrunc x).trans (hB x))

/-- `η_k` is a genuine `θ`-PSH potential. -/
theorem truncatedAffineEnvelope_isThetaPshPotential (hle : phi ≤ Phi)
    (hphi : IsThetaPshPotential theta phi) (hPhi : IsThetaPshPotential theta Phi)
    {a : ℝ} (ha : 1 < a) (k : ℕ) :
    IsThetaPshPotential theta (truncatedAffineEnvelope theta a phi Phi k) :=
  isThetaPshPotential_rooftop_of_nonempty
    ⟨_, shifted_mem_rooftopCompetitors hPhi ha k⟩
    (rooftopCompetitors_truncated_bddAbove hle hphi hPhi ha k)

omit [CompactSpace M] [Nonempty M] in
/-- `ϕ - a k ≤ η_k`: the explicit competitor lies below the envelope. -/
theorem reference_sub_le_truncatedAffineEnvelope
    (hPhi : IsThetaPshPotential theta Phi) {a : ℝ} (ha : 1 < a) (k : ℕ) :
    (fun x => Phi x + ((-(a * k) : ℝ) : EReal)) ≤
      truncatedAffineEnvelope theta a phi Phi k :=
  le_rooftopEnvelope (hPhi.add_const _) (shifted_mem_rooftopCompetitors hPhi ha k).2

omit [CompactSpace M] [Nonempty M] in
/-- `(η_k)_k` is decreasing, because the obstacle is. -/
theorem truncatedAffineEnvelope_antitone (hPtop : ∀ x, Phi x ≠ ⊤) {a : ℝ} (ha0 : 0 < a)
    (x : M) : Antitone fun k : ℕ => truncatedAffineEnvelope theta a phi Phi k x := by
  intro j k hjk
  refine rooftopEnvelope_mono (fun y => ?_) x
  simp only [convexComb_apply]
  exact add_le_add (mul_le_mul_of_nonneg_left
    (truncatedReference_antitone (phi := phi) hPtop y hjk)
    (EReal.coe_nonneg.mpr ha0.le)) le_rfl

/-! ### The decreasing limit `η = inf_k η_k` -/

/-- **`η` is `θ`-PSH**, as a decreasing limit of `θ`-PSH functions.  No
nondegeneracy is claimed: the infimum may still be identically `-∞`, which is
exactly what Xia's Step 1.3 rules out. -/
theorem thetaPlurisubharmonic_truncatedAffineLimit (hle : phi ≤ Phi)
    (hphi : IsThetaPshPotential theta phi) (hPhi : IsThetaPshPotential theta Phi)
    {a : ℝ} (ha : 1 < a) :
    ThetaPlurisubharmonic theta (truncatedAffineLimit theta a phi Phi) :=
  thetaPlurisubharmonic_iInf_of_antitone
    (fun k => (truncatedAffineEnvelope_isThetaPshPotential hle hphi hPhi ha k).1)
    (fun x => truncatedAffineEnvelope_antitone (phi := phi)
      (fun y => hPhi.1.quasiPlurisubharmonic.ne_top y) (lt_trans zero_lt_one ha) x)

/-- **Xia's (2.31) at level `k`** (`xia-sgpt:page-0083`, applied on
`xia-sgpt:page-0085` to the truncated pair): `a⁻¹ η_k + (1-a⁻¹) ϕ ≤ φ_k`.

The envelope lies below its obstacle Lebesgue-almost-everywhere in every chart,
`ϕ` is finite quasi-everywhere, and there the obstacle form and the barrier form
of the inequality agree; both sides being genuine potentials, the comparison
propagates to all of `M`. -/
theorem convexComb_truncatedAffineEnvelope_le {Theta : ClosedRealOneOneForm n M}
    (hle : phi ≤ Phi) (hphi : IsThetaPshPotential Theta.val phi)
    (hPhi : IsThetaPshPotential Theta.val Phi) {a : ℝ} (ha : 1 < a) (k : ℕ) :
    convexComb a⁻¹ (truncatedAffineEnvelope Theta.val a phi Phi k) Phi ≤
      truncatedReference phi Phi k := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have hinv0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have hinv1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hE := truncatedAffineEnvelope_isThetaPshPotential hle hphi hPhi ha k
  have hW : IsThetaPshPotential Theta.val
      (convexComb a⁻¹ (truncatedAffineEnvelope Theta.val a phi Phi k) Phi) :=
    isThetaPshPotential_convexComb hE hPhi hinv0 hinv1
  have htr := truncatedReference_isThetaPshPotential hphi hPhi k
  refine ThetaPlurisubharmonic.le_of_ae_in_charts_le hW.1 htr.1 ?_
  intro e
  have hne : (rooftopCompetitors Theta.val
      (convexComb a (truncatedReference phi Phi k) Phi)).Nonempty :=
    ⟨_, shifted_mem_rooftopCompetitors hPhi ha k⟩
  have hbound := rooftopCompetitors_truncated_bddAbove hle hphi hPhi ha k
  have hae1 := ae_rooftopEnvelope_le_obstacle Theta hne hbound e
  have hae2 := (Pending.quasiPsh_finite_quasiEverywhere
    (u := Phi) hPhi.quasiPshPotential).ae_in_chart e volume
  filter_upwards [hae1, hae2] with z h1 h2
  exact (convexCombValue_le_iff ha h2.1 h2.2).mpr h1

/-- **Xia's Step 1.3, reduced to its one remaining point.**  For `φ ≤ ϕ` in
`PSH(X, θ)` and `a > 1`, once the decreasing limit
`η = inf_k P_θ(a (φ ∨ (ϕ - k)) + (1-a) ϕ)` is locally nondegenerate, it is a
genuine `θ`-PSH potential satisfying Xia's (2.33),
`a⁻¹ η + (1-a⁻¹) ϕ ≤ φ`.

Everything here is proved: the limit is `θ`-PSH as a decreasing limit, it lies
below each `η_k`, hence below each `φ_k` after the affine change, and
`inf_k φ_k = φ`.  The fixed-point hypothesis `P_θ[ϕ] = ϕ`, the positive mass and
the admissible interval are *not* used — they are what Xia needs for the
nondegeneracy itself. -/
theorem exists_convexCombBarrier_of_locallyNondegenerate_truncatedAffineLimit
    {Theta : ClosedRealOneOneForm n M}
    (hle : phi ≤ Phi) (hphi : IsThetaPshPotential Theta.val phi)
    (hPhi : IsThetaPshPotential Theta.val Phi) {a : ℝ} (ha : 1 < a)
    (hnd : LocallyNondegenerate (truncatedAffineLimit Theta.val a phi Phi)) :
    ∃ eta : M → EReal, IsThetaPshPotential Theta.val eta ∧
      convexComb a⁻¹ eta Phi ≤ phi := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have hinv0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have hPtop : ∀ y, Phi y ≠ ⊤ := fun y => hPhi.1.quasiPlurisubharmonic.ne_top y
  refine ⟨truncatedAffineLimit Theta.val a phi Phi,
    ⟨thetaPlurisubharmonic_truncatedAffineLimit hle hphi hPhi ha, hnd⟩, fun x => ?_⟩
  have key : ∀ k : ℕ,
      convexComb a⁻¹ (truncatedAffineLimit Theta.val a phi Phi) Phi x ≤
        truncatedReference phi Phi k x := by
    intro k
    refine le_trans ?_ (convexComb_truncatedAffineEnvelope_le hle hphi hPhi ha k x)
    simp only [convexComb_apply]
    exact add_le_add (mul_le_mul_of_nonneg_left
      (iInf_le (fun j => truncatedAffineEnvelope Theta.val a phi Phi j x) k)
      (EReal.coe_nonneg.mpr hinv0.le)) le_rfl
  calc convexComb a⁻¹ (truncatedAffineLimit Theta.val a phi Phi) Phi x
      ≤ ⨅ k : ℕ, truncatedReference phi Phi k x := le_iInf key
    _ = phi x := iInf_truncatedReference hle hPtop x

end

end SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierTruncatedLimit
