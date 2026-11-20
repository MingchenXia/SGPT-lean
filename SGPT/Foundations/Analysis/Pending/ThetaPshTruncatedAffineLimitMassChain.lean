import SGPT.Foundations.Analysis.Pending.DominationPrincipleAffineContactInterface
import SGPT.Foundations.Analysis.Pending.DominationPrincipleContactChainCore
import SGPT.Foundations.Analysis.Pending.MaxMassDecomposition
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierModelReduction
import SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierTruncatedLimit
import SGPT.Foundations.Analysis.Pending.ThetaPshAntitoneSupNondegenerate

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Step 1.3 of Xia's Lemma 2.4.4: the mass chain of `xia-sgpt:page-0086`

`Pending.RooftopConvexCombBarrierTruncatedLimit` builds Xia's truncated family

  `φ_j = φ ∨ (ϕ - j)`,  `η_j = P_θ(a φ_j + (1-a) ϕ)`,  `η = inf_j η_j`,

and proves everything about it that Step 1 needs except the single point Step 1.3
is devoted to: `η ≢ -∞`.  This module proves that point, by carrying out the
source's own contradiction argument (`xia-sgpt:page-0085`--`page-0086`).

## The argument

Suppose `η ≡ -∞`.  Then, `η_j` being antitone, the suprema `sup_X η_j` must tend
to `-∞`; that step is the classical compactness property of `PSH(X, θ)` and is
the one named input taken from outside
(`Pending.ThetaPshAntitoneSupNondegenerate`).  Fix `k`.  For `j` large,
`sup_X η_j ≤ -a k`, so Xia's (2.34)
(`RooftopConvexCombBarrierStepOne.le_add_const_of_le_of_singularityEnvelope_eq`,
proved) upgrades that to `η_j ≤ ϕ - a k` *everywhere* — this is the source's
`{η_j ≤ ϕ - a k} = X`.  Now run the source chain, with `B = X`:

* `a^{-n} θ^n_{η_j} ≤ 1_{D_j} θ^n_{φ_j}`, `D_j = {a^{-1}η_j + (1-a^{-1})ϕ = φ_j}`
  — Xia's (2.35), proved in `Pending.DominationPrincipleContactChainCore` from
  multilinearity and Lemma 2.4.2, with the envelope-concentration hypothesis
  supplied by the affine instance of Theorem 2.4.4
  (`Pending.DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero`).
* On `D_j` one has `η_j = a φ_j + (1-a) ϕ`, so `η_j ≤ ϕ - a k` forces
  `φ_j ≤ ϕ - k`, hence `φ ≤ ϕ - k`: `D_j ⊆ (S_k)ᶜ` for `S_k = {φ > ϕ - k}`.
* `θ^n_{φ_j}((S_k)ᶜ) = ∫θ^n_ϕ - θ^n_{φ_j}(S_k) ≤ ∫θ^n_ϕ - θ^n_φ(S_k)`, which is
  Xia's (2.36): the total masses of `φ_j` and of `ϕ` agree because
  `ϕ - j ≤ φ_j ≤ ϕ`, and `θ^n_φ(S_k) ≤ θ^n_{φ_j}(S_k)` is Lemma 2.4.2 on the
  contact set, since `φ = φ_j` on `S_k` once `j ≥ k`.

Multiplying by `a^n` gives `∫θ^n_ϕ ≤ a^n (∫θ^n_ϕ - θ^n_φ(S_k))` for every `k`.
The `S_k` increase to the finiteness locus of `φ`, which carries all of
`θ^n_φ` (its complement is the pole set, which the non-pluripolar measure does
not charge), so `θ^n_φ(S_k) ↑ ∫θ^n_φ` and the limit contradicts the admissible
interval (2.28) for `a`.

## What is assumed and what is proved

Two named inputs, both source-anchored and neither derivable from this module's
own conclusion by instantiation:

1. `DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero`
   — Xia's Theorem 2.4.4 for the affine obstacle, already open in this workspace
   before this module and used identically on `xia-sgpt:page-0088`;
2. `ThetaPshAntitoneSupNondegenerate.exists_ne_bot_iInf_of_forall_exists_le`
   — compactness of `PSH(X, θ)`, a statement about arbitrary antitone families
   with no envelope, mass or contact set in it.

Everything between them — (2.34) at the truncated level, the (2.35) instance,
the contact inclusion, (2.36), the exhaustion and the `ℝ≥0∞` endgame — is proved
here.

## Degenerate cases

In dimension `0` the admissible interval reduces to `0 < ∫θ^n_φ` and the final
contradiction reads `m ≤ m - ∫θ^n_φ`, so nothing degenerates.  `φ` and `ϕ` may
be `-∞` on a pluripolar set: the pole set of `ϕ` is handled explicitly in the
contact inclusion (there `φ_j` is `-∞` too, so the point lies in `(S_k)ᶜ`
outright), and the pole set of `φ` is exactly what the exhaustion discards.
-/

open Set MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis.Pending.ThetaPshTruncatedAffineLimitMassChain

open FirstPass FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending.DiagonalMass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination
open SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
open SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierTruncatedLimit
open SGPT.Foundations.Analysis.Pending.RooftopContactConcentration

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [Nonempty M]

/-! ### Pointwise algebra -/

/-- The barrier form of "`η ≤ ϕ - a k` implies `φ_j ≤ ϕ - k` on the contact
set".  For a finite `B` and `a > 1`, `E ≤ B - a k` gives
`a⁻¹ E + (1 - a⁻¹) B ≤ B - k`; this is the exact rearrangement Xia performs
between the second and third lines of the display on `xia-sgpt:page-0086`. -/
theorem convexCombValue_le_sub_of_le_sub {a : ℝ} (ha : 1 < a) {B E : EReal}
    (hBbot : B ≠ ⊥) (hBtop : B ≠ ⊤) {k : ℝ}
    (h : E ≤ B + ((-(a * k) : ℝ) : EReal)) :
    ((a⁻¹ : ℝ) : EReal) * E + ((1 - a⁻¹ : ℝ) : EReal) * B ≤
      B + ((-k : ℝ) : EReal) := by
  refine (convexCombValue_le_iff ha hBbot hBtop).mpr ?_
  lift B to ℝ using ⟨hBtop, hBbot⟩ with b
  refine h.trans (le_of_eq ?_)
  rw [← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul,
    ← EReal.coe_add]
  exact EReal.coe_eq_coe_iff.mpr (by ring)

/-! ### The truncated family lies below the reference -/

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
/-- `η_j ≤ ϕ`.  The obstacle `a φ_j + (1-a) ϕ` lies below `φ_j`, hence below
`ϕ`, so every quasi-everywhere competitor does; and a quasi-everywhere
comparison of `θ`-PSH functions is pointwise. -/
theorem truncatedAffineEnvelope_le_reference {theta : ClosedRealOneOneForm n M}
    {u v : M → EReal}
    (hv : IsThetaPshPotential theta.val v) (huv : u ≤ v) {a : ℝ} (ha : 1 < a)
    (j : ℕ) : truncatedAffineEnvelope theta.val a u v j ≤ v := by
  have hvtop : ∀ x, v x ≠ ⊤ := fun x => hv.1.quasiPlurisubharmonic.ne_top x
  have hpv := truncatedReference_le_reference huv hvtop j
  have hobs : convexComb a (truncatedReference u v j) v ≤ v := by
    intro x
    simp only [convexComb_apply]
    exact (convexCombValue_le_left ha (hpv x) (hvtop x)).trans (hpv x)
  refine (rooftopEnvelope_le_iff
    hv.1.quasiPlurisubharmonic.upperSemicontinuous).mpr ?_
  intro w hw hqe
  exact ThetaPlurisubharmonic.le_of_quasiEverywhere_le hw.1 hv.1
    (hqe.mono fun x hx => hx.trans (hobs x))

/-! ### Equal masses -/

omit [Nonempty M] in
/-- If `w` is sandwiched between `v - C` and `v`, it has the same diagonal
non-pluripolar mass as `v`.  This is Theorem 2.4.3 applied twice, together with
the translation invariance of the mass. -/
theorem diagonalPotentialMass_eq_of_sandwich (omega : KahlerBackground n M)
    (theta : ClosedRealOneOneForm n M) {v w : M → EReal}
    (hv : IsThetaPshPotential theta.val v)
    (hw : IsThetaPshPotential theta.val w) (hwv : w ≤ v) {C : ℝ}
    (hvw : ∀ x, v x + ((-C : ℝ) : EReal) ≤ w x) :
    diagonalPotentialMass theta w hw = diagonalPotentialMass theta v hv := by
  refine le_antisymm (diagonalPotentialMass_mono_of_kahler omega hw hv
    (MoreSingularOn.of_le fun x _ => hwv x)) ?_
  have hshift : IsThetaPshPotential theta.val (fun x => v x + ((-C : ℝ) : EReal)) :=
    hv.add_const (-C)
  calc diagonalPotentialMass theta v hv
      = diagonalPotentialMass theta (fun x => v x + ((-C : ℝ) : EReal)) hshift :=
        (RooftopConvexCombBarrierModelReduction.diagonalPotentialMass_add_const
          theta hv (-C) hshift).symm
    _ ≤ diagonalPotentialMass theta w hw :=
        diagonalPotentialMass_mono_of_kahler omega hshift hw
          (MoreSingularOn.of_le fun x _ => hvw x)

/-! ### Shifting the reference by an integer -/

omit [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  [Nonempty M] in
/-- `ϕ - m ≤ ϕ - l` for `l ≤ m`, with the pole of `ϕ` handled explicitly. -/
theorem reference_sub_le_reference_sub {v : M → EReal} (hvtop : ∀ x, v x ≠ ⊤)
    (x : M) {l m : ℕ} (hlm : l ≤ m) :
    v x + ((-(m : ℝ) : ℝ) : EReal) ≤ v x + ((-(l : ℝ) : ℝ) : EReal) := by
  rcases eq_or_ne (v x) ⊥ with hb | hb
  · rw [hb, EReal.bot_add, EReal.bot_add]
  · obtain ⟨r, hr⟩ := exists_coe_of_ne (hvtop x) hb
    rw [hr, ← EReal.coe_add, ← EReal.coe_add]
    refine EReal.coe_le_coe_iff.mpr ?_
    have : (l : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hlm
    linarith

/-! ### The concentration hypothesis of (2.35) at the truncated level -/

/-- The affine instance of Xia's Theorem 2.4.4, read at the truncated data
`φ_j = φ ∨ (ϕ - j)` and `ϕ`.  Its hypotheses are available because
`ϕ - j ≤ φ_j ≤ ϕ` makes `φ_j` of the same mass as `ϕ`. -/
theorem noncontact_eq_zero_truncated [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (huv : u ≤ v)
    (hposv : 0 < diagonalPotentialMass theta v hv) {a : ℝ} (ha : 1 < a) (j : ℕ) :
    diagonalPotentialMeasure theta (truncatedAffineEnvelope theta.val a u v j)
        (truncatedAffineEnvelope_isThetaPshPotential huv hu hv ha j)
      {x : M | truncatedAffineEnvelope theta.val a u v j x <
        convexComb a (truncatedReference u v j) v x} = 0 := by
  have hvtop : ∀ x, v x ≠ ⊤ := fun x => hv.1.quasiPlurisubharmonic.ne_top x
  have hp : IsThetaPshPotential theta.val (truncatedReference u v j) :=
    truncatedReference_isThetaPshPotential hu hv j
  have hmass : diagonalPotentialMass theta (truncatedReference u v j) hp =
      diagonalPotentialMass theta v hv :=
    diagonalPotentialMass_eq_of_sandwich omega theta hv hp
      (truncatedReference_le_reference huv hvtop j)
      (fun x => reference_sub_le_truncatedReference (phi := u) j x)
  exact DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero
    omega theta hp hv (truncatedReference_le_reference huv hvtop j)
    (by rw [hmass]; exact hposv) hmass ha _

/-! ### Step 1.3 -/

/-- **Step 1.3 from the concentration of the truncated affine envelopes** (the source's
contradiction argument, `xia-sgpt:page-0085`--`page-0086`), with Xia's Theorem 2.4.4 at the
truncated affine obstacles taken as the hypothesis `hnc`.  `exists_ne_bot_truncatedAffineLimit`
supplies `hnc` in general (`noncontact_eq_zero_truncated`),
`exists_ne_bot_truncatedAffineLimit_of_isBigClass` for a big class without Boucksom 4.8. -/
theorem exists_ne_bot_truncatedAffineLimit_of_noncontact [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (huv : u ≤ v)
    (hfix : singularityEnvelope theta.val v = v)
    (hpos : 0 < diagonalPotentialMass theta u hu) {a : ℝ}
    (hadm : ConvexCombEnvelopeMass.IsAdmissibleWeight n
      (diagonalPotentialMass theta u hu) (diagonalPotentialMass theta v hv) a)
    (hnc : ∀ (ha : 1 < a) (j : ℕ),
      diagonalPotentialMeasure theta (truncatedAffineEnvelope theta.val a u v j)
          (truncatedAffineEnvelope_isThetaPshPotential huv hu hv ha j)
        {x : M | truncatedAffineEnvelope theta.val a u v j x <
          convexComb a (truncatedReference u v j) v x} = 0) :
    ∃ x : M, truncatedAffineLimit theta.val a u v x ≠ ⊥ := by
  classical
  by_contra hcontra
  have hcon : ∀ x : M,
      (⨅ j : ℕ, truncatedAffineEnvelope theta.val a u v j x) = ⊥ :=
    fun x => not_not.mp fun h => hcontra ⟨x, h⟩
  have ha : 1 < a := hadm.one_lt
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have hvtop : ∀ x, v x ≠ ⊤ := fun x => hv.1.quasiPlurisubharmonic.ne_top x
  have hutop : ∀ x, u x ≠ ⊤ := fun x => hu.1.quasiPlurisubharmonic.ne_top x
  have hp : ∀ j : ℕ, IsThetaPshPotential theta.val (truncatedReference u v j) :=
    fun j => truncatedReference_isThetaPshPotential hu hv j
  have hE : ∀ j : ℕ,
      IsThetaPshPotential theta.val (truncatedAffineEnvelope theta.val a u v j) :=
    fun j => truncatedAffineEnvelope_isThetaPshPotential huv hu hv ha j
  have hpv : ∀ j : ℕ, truncatedReference u v j ≤ v :=
    fun j => truncatedReference_le_reference huv hvtop j
  have hEv : ∀ j : ℕ, truncatedAffineEnvelope theta.val a u v j ≤ v :=
    fun j => truncatedAffineEnvelope_le_reference hv huv ha j
  have hmassp : ∀ j : ℕ,
      diagonalPotentialMass theta (truncatedReference u v j) (hp j) =
        diagonalPotentialMass theta v hv :=
    fun j => diagonalPotentialMass_eq_of_sandwich omega theta hv (hp j) (hpv j)
      (fun x => reference_sub_le_truncatedReference (phi := u) j x)
  have hmassE : ∀ j : ℕ,
      diagonalPotentialMass theta (truncatedAffineEnvelope theta.val a u v j) (hE j) =
        diagonalPotentialMass theta v hv :=
    fun j => diagonalPotentialMass_eq_of_sandwich omega theta hv (hE j) (hEv j)
      (fun x => reference_sub_le_truncatedAffineEnvelope (phi := u) hv ha j x)
  have hmuv : diagonalPotentialMass theta u hu ≤ diagonalPotentialMass theta v hv :=
    diagonalPotentialMass_mono_of_kahler omega hu hv
      (MoreSingularOn.of_le fun x _ => huv x)
  have hmvtop : diagonalPotentialMass theta v hv ≠ ⊤ :=
    (DiagonalMeasureRegularity.diagonalPotentialMeasure_lt_top omega theta hv
      Set.univ).ne
  have hmutop : diagonalPotentialMass theta u hu ≠ ⊤ :=
    (DiagonalMeasureRegularity.diagonalPotentialMeasure_lt_top omega theta hu
      Set.univ).ne
  -- Xia's `S_k = {φ > ϕ - k}`
  set S : ℕ → Set M :=
    fun k => {x : M | v x + ((-(k : ℝ) : ℝ) : EReal) < u x} with hSdef
  have hSmeas : ∀ k : ℕ, MeasurableSet (S k) := fun k =>
    MaxMassDecomposition.measurableSet_potential_lt hu (hv.add_const (-(k : ℝ)))
  have hSmono : Monotone S := fun l m hlm x hx =>
    lt_of_le_of_lt (reference_sub_le_reference_sub hvtop x hlm) hx
  -- the one external input: the suprema must tend to `-∞`
  have hdecay : ∀ C : ℝ, ∃ j : ℕ, ∀ x : M,
      truncatedAffineEnvelope theta.val a u v j x ≤ ((-C : ℝ) : EReal) :=
    fun C => ThetaPshAntitoneSupNondegenerate.exists_forall_le_of_forall_iInf_eq_bot
      hE (fun x => truncatedAffineEnvelope_antitone (phi := u) hvtop ha0 x) hcon C
  -- the source's estimate at each truncation level
  have key : ∀ k : ℕ, diagonalPotentialMass theta v hv ≤
      ENNReal.ofReal (a ^ n) *
        (diagonalPotentialMass theta v hv -
          diagonalPotentialMeasure theta u hu (S k)) := by
    intro k
    obtain ⟨j0, hj0⟩ := hdecay (a * k)
    have hjk : k ≤ max j0 k := le_max_right j0 k
    set j : ℕ := max j0 k with hjdef
    have hbound : ∀ x : M,
        truncatedAffineEnvelope theta.val a u v j x ≤ ((-(a * k) : ℝ) : EReal) :=
      fun x => (truncatedAffineEnvelope_antitone (phi := u) hvtop ha0 x
        (le_max_left j0 k)).trans (hj0 x)
    -- (2.34): `{η_j ≤ ϕ - a k} = X`
    have hsmall : ∀ x : M, truncatedAffineEnvelope theta.val a u v j x ≤
        v x + ((-(a * k) : ℝ) : EReal) := fun x =>
      RooftopConvexCombBarrierStepOne.le_add_const_of_le_of_singularityEnvelope_eq
        (hE j) hfix (hEv j) hbound x
    -- the contact set of (2.35) misses `S_k`
    have hD : {x : M |
        convexComb a⁻¹ (truncatedAffineEnvelope theta.val a u v j) v x =
          truncatedReference u v j x} ⊆ (S k)ᶜ := by
      intro x hx
      simp only [hSdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
      refine le_trans (le_truncatedReference (Phi := v) j x) ?_
      rcases eq_or_ne (v x) ⊥ with hb | hb
      · have hle := hpv j x
        rw [hb, EReal.bot_add]
        rwa [hb] at hle
      · rw [← hx]
        simpa only [convexComb_apply] using
          convexCombValue_le_sub_of_le_sub ha hb (hvtop x) (hsmall x)
    -- (2.35) with `B = X`
    have h235 := DominationPrincipleContactChain.ofReal_pow_smul_measure_le_contact
      omega theta (hp j) hv (hE j) ha (hpv j)
      (convexComb_truncatedAffineEnvelope_le huv hu hv ha j)
      (hnc ha j) Set.univ
    -- (2.36): the contact comparison of Lemma 2.4.2 on `S_k`
    have hcontactS : S k ⊆ {x : M | u x = truncatedReference u v j x} := by
      intro x hx
      exact (max_eq_left
        (lt_of_le_of_lt (reference_sub_le_reference_sub hvtop x hjk) hx).le).symm
    have h236 : diagonalPotentialMeasure theta u hu (S k) ≤
        diagonalPotentialMeasure theta (truncatedReference u v j) (hp j) (S k) :=
      measure_le_of_subset_contact omega theta hu (hp j)
        (fun x => le_truncatedReference (Phi := v) j x) (S k) hcontactS
    have hcompl :
        diagonalPotentialMeasure theta (truncatedReference u v j) (hp j) ((S k)ᶜ) =
          diagonalPotentialMass theta v hv -
            diagonalPotentialMeasure theta (truncatedReference u v j) (hp j) (S k) := by
      have hpu : diagonalPotentialMeasure theta (truncatedReference u v j) (hp j)
          Set.univ = diagonalPotentialMass theta v hv := hmassp j
      rw [measure_compl (hSmeas k)
        (DiagonalMeasureRegularity.diagonalPotentialMeasure_lt_top omega theta
          (hp j) (S k)).ne, hpu]
    have hchain : ENNReal.ofReal (a⁻¹ ^ n) * diagonalPotentialMass theta v hv ≤
        diagonalPotentialMass theta v hv -
          diagonalPotentialMeasure theta u hu (S k) := by
      have h1 : ENNReal.ofReal (a⁻¹ ^ n) * diagonalPotentialMass theta v hv ≤
          diagonalPotentialMeasure theta (truncatedReference u v j) (hp j)
            (Set.univ ∩ {x : M |
              convexComb a⁻¹ (truncatedAffineEnvelope theta.val a u v j) v x =
                truncatedReference u v j x}) := by
        rw [← hmassE j]; exact h235
      refine h1.trans ?_
      refine le_trans (measure_mono (fun x hx => hD hx.2)) ?_
      rw [hcompl]
      exact tsub_le_tsub_left h236 _
    have hcoe : ENNReal.ofReal (a ^ n) * ENNReal.ofReal (a⁻¹ ^ n) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← mul_pow,
        mul_inv_cancel₀ (ne_of_gt ha0), one_pow, ENNReal.ofReal_one]
    calc diagonalPotentialMass theta v hv
        = ENNReal.ofReal (a ^ n) *
            (ENNReal.ofReal (a⁻¹ ^ n) * diagonalPotentialMass theta v hv) := by
          rw [← mul_assoc, hcoe, one_mul]
      _ ≤ ENNReal.ofReal (a ^ n) *
            (diagonalPotentialMass theta v hv -
              diagonalPotentialMeasure theta u hu (S k)) := by
          gcongr
  -- the `S_k` carry all of `θ^n_φ` in the limit
  have hpole : diagonalPotentialMeasure theta u hu {x : M | u x = ⊥} = 0 :=
    GlobalDiagonalScaling.globalMixedMeasure_pole_null_of_nondegenerate
      (fun _ : Fin n => hu.1) hu
  have hcover : (Set.univ : Set M) ⊆ {x : M | u x = ⊥} ∪ ⋃ k : ℕ, S k := by
    intro x _
    rcases eq_or_ne (u x) ⊥ with hb | hb
    · exact Or.inl hb
    · refine Or.inr ?_
      have hvb : v x ≠ ⊥ := fun h => hb (le_bot_iff.mp (h ▸ huv x))
      obtain ⟨r, hr⟩ := exists_coe_of_ne (hvtop x) hvb
      obtain ⟨s, hs⟩ := exists_coe_of_ne (hutop x) hb
      obtain ⟨k, hk⟩ := exists_nat_gt (r - s)
      refine Set.mem_iUnion.mpr ⟨k, ?_⟩
      show v x + ((-(k : ℝ) : ℝ) : EReal) < u x
      rw [hr, hs, ← EReal.coe_add]
      exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have hsup : diagonalPotentialMass theta u hu ≤
      ⨆ k : ℕ, diagonalPotentialMeasure theta u hu (S k) := by
    have h1 : diagonalPotentialMass theta u hu ≤
        diagonalPotentialMeasure theta u hu ({x : M | u x = ⊥} ∪ ⋃ k : ℕ, S k) :=
      measure_mono hcover
    refine h1.trans ?_
    refine (measure_union_le _ _).trans ?_
    rw [hpole, zero_add]
    exact le_of_eq hSmono.measure_iUnion
  -- the `ℝ≥0∞` endgame against the admissible interval (2.28)
  obtain ⟨-, hlt⟩ := hadm
  have hctop : ENNReal.ofReal (a ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc0 : ENNReal.ofReal (a ^ n) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hdelta : 0 < diagonalPotentialMass theta v hv -
      ENNReal.ofReal (a ^ n) *
        (diagonalPotentialMass theta v hv - diagonalPotentialMass theta u hu) :=
    tsub_pos_of_lt hlt
  have hstep : ∀ k : ℕ,
      diagonalPotentialMass theta v hv -
          ENNReal.ofReal (a ^ n) * (diagonalPotentialMass theta v hv -
            diagonalPotentialMass theta u hu) ≤
        ENNReal.ofReal (a ^ n) * (diagonalPotentialMass theta u hu -
          diagonalPotentialMeasure theta u hu (S k)) := by
    intro k
    have hnu : diagonalPotentialMeasure theta u hu (S k) ≤
        diagonalPotentialMass theta u hu := measure_mono (Set.subset_univ _)
    have hsplit : (diagonalPotentialMass theta v hv -
          diagonalPotentialMass theta u hu) +
          (diagonalPotentialMass theta u hu -
            diagonalPotentialMeasure theta u hu (S k)) =
        diagonalPotentialMass theta v hv -
          diagonalPotentialMeasure theta u hu (S k) :=
      tsub_add_tsub_cancel hmuv hnu
    have hk := key k
    rw [← hsplit, mul_add] at hk
    exact tsub_le_iff_right.mpr (by rw [add_comm]; exact hk)
  have hbound : ∀ k : ℕ,
      (diagonalPotentialMass theta v hv -
        ENNReal.ofReal (a ^ n) * (diagonalPotentialMass theta v hv -
          diagonalPotentialMass theta u hu)) / ENNReal.ofReal (a ^ n) ≤
      diagonalPotentialMass theta u hu -
        diagonalPotentialMeasure theta u hu (S k) := fun k =>
    (ENNReal.div_le_iff_le_mul (Or.inl hc0) (Or.inl hctop)).mpr
      (by
        rw [mul_comm (diagonalPotentialMass theta u hu -
          diagonalPotentialMeasure theta u hu (S k)) (ENNReal.ofReal (a ^ n))]
        exact hstep k)
  have heps0 : 0 < (diagonalPotentialMass theta v hv -
      ENNReal.ofReal (a ^ n) * (diagonalPotentialMass theta v hv -
        diagonalPotentialMass theta u hu)) / ENNReal.ofReal (a ^ n) :=
    ENNReal.div_pos hdelta.ne' hctop
  have hle : ∀ k : ℕ, diagonalPotentialMeasure theta u hu (S k) ≤
      diagonalPotentialMass theta u hu -
        (diagonalPotentialMass theta v hv -
          ENNReal.ofReal (a ^ n) * (diagonalPotentialMass theta v hv -
            diagonalPotentialMass theta u hu)) / ENNReal.ofReal (a ^ n) := by
    intro k
    have hnu : diagonalPotentialMeasure theta u hu (S k) ≤
        diagonalPotentialMass theta u hu := measure_mono (Set.subset_univ _)
    refine ENNReal.le_sub_of_add_le_left
      (ENNReal.div_lt_top (ne_top_of_le_ne_top hmvtop tsub_le_self) hc0).ne ?_
    calc (diagonalPotentialMass theta v hv -
            ENNReal.ofReal (a ^ n) * (diagonalPotentialMass theta v hv -
              diagonalPotentialMass theta u hu)) / ENNReal.ofReal (a ^ n) +
          diagonalPotentialMeasure theta u hu (S k)
        ≤ (diagonalPotentialMass theta u hu -
            diagonalPotentialMeasure theta u hu (S k)) +
            diagonalPotentialMeasure theta u hu (S k) := by
          gcongr
          exact hbound k
      _ = diagonalPotentialMass theta u hu := tsub_add_cancel_of_le hnu
  exact absurd (hsup.trans (iSup_le hle))
    (not_le.mpr (ENNReal.sub_lt_self hmutop hpos.ne' heps0.ne'))


/-- **Xia, SGPT, Lemma 2.4.4, Step 1.3** (`xia-sgpt:page-0085`--`page-0086`):
the decreasing limit `η = inf_j P_θ(a (φ ∨ (ϕ - j)) + (1-a) ϕ)` is not
identically `-∞`.

The proof is the source's contradiction argument; see the module docstring for
the chain and for the two named inputs it rests on.  Xia's normalisation `ϕ ≤ 0`
is not needed here and is therefore not assumed. -/
theorem exists_ne_bot_truncatedAffineLimit [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (huv : u ≤ v)
    (hfix : singularityEnvelope theta.val v = v)
    (hpos : 0 < diagonalPotentialMass theta u hu) {a : ℝ}
    (hadm : ConvexCombEnvelopeMass.IsAdmissibleWeight n
      (diagonalPotentialMass theta u hu) (diagonalPotentialMass theta v hv) a) :
    ∃ x : M, truncatedAffineLimit theta.val a u v x ≠ ⊥ :=
  exists_ne_bot_truncatedAffineLimit_of_noncontact omega theta hu hv huv hfix hpos hadm
    fun ha j => noncontact_eq_zero_truncated omega theta hu hv huv
      (lt_of_lt_of_le hpos (diagonalPotentialMass_mono_of_kahler omega hu hv
        (MoreSingularOn.of_le fun x _ => huv x))) ha j

/-- The affine instance of Xia's Theorem 2.4.4 at the truncated data, **for a big class**: no
positivity of mass is needed, and the big-class form of the affine theorem
(`DominationPrincipleAffineContactProof.xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le_of_isBigClass`)
does not pass through Boucksom 4.8. -/
theorem noncontact_eq_zero_truncated_of_isBigClass [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (huv : u ≤ v)
    (hbig : NonKahlerLocus.IsBigClass (RealBottChern.ofRepresentative theta)) {a : ℝ}
    (ha : 1 < a) (j : ℕ) :
    diagonalPotentialMeasure theta (truncatedAffineEnvelope theta.val a u v j)
        (truncatedAffineEnvelope_isThetaPshPotential huv hu hv ha j)
      {x : M | truncatedAffineEnvelope theta.val a u v j x <
        convexComb a (truncatedReference u v j) v x} = 0 := by
  have hvtop : ∀ x, v x ≠ ⊤ := fun x => hv.1.quasiPlurisubharmonic.ne_top x
  exact DominationPrincipleAffineContactProof.xiaTheorem244_affineObstacle_noncontact_eq_zero_of_le_of_isBigClass
    omega theta (truncatedReference_isThetaPshPotential hu hv j) hv
    (truncatedReference_le_reference huv hvtop j) hbig ha _

/-- **Xia's Lemma 2.4.4, Step 1.3, for a big class**, without Boucksom 4.8. -/
theorem exists_ne_bot_truncatedAffineLimit_of_isBigClass [ConnectedSpace M]
    (omega : KahlerBackground n M) (theta : ClosedRealOneOneForm n M)
    {u v : M → EReal} (hu : IsThetaPshPotential theta.val u)
    (hv : IsThetaPshPotential theta.val v) (huv : u ≤ v)
    (hfix : singularityEnvelope theta.val v = v)
    (hbig : NonKahlerLocus.IsBigClass (RealBottChern.ofRepresentative theta))
    (hpos : 0 < diagonalPotentialMass theta u hu) {a : ℝ}
    (hadm : ConvexCombEnvelopeMass.IsAdmissibleWeight n
      (diagonalPotentialMass theta u hu) (diagonalPotentialMass theta v hv) a) :
    ∃ x : M, truncatedAffineLimit theta.val a u v x ≠ ⊥ :=
  exists_ne_bot_truncatedAffineLimit_of_noncontact omega theta hu hv huv hfix hpos hadm
    fun ha j => noncontact_eq_zero_truncated_of_isBigClass omega theta hu hv huv hbig ha j

end

end SGPT.Foundations.Analysis.Pending.ThetaPshTruncatedAffineLimitMassChain
