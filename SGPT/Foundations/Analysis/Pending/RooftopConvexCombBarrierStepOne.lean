import SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
import SGPT.Foundations.Analysis.FirstPass.Envelopes
import SGPT.Foundations.Analysis.FirstPass.FiniteTranslation
import SGPT.Foundations.Analysis.FirstPass.ThetaPshCompactBounds

set_option autoImplicit false

/-!
# Step 1 of Xia's Lemma 2.4.4: the parts that do not need envelope concentration

Xia, SGPT, Lemma 2.4.4 (`xia-sgpt:page-0083`, proof body
`xia-sgpt:page-0084`--`xia-sgpt:page-0086`) asks, for `φ ≤ ψ` of positive mass
and an admissible weight `a`, for one `η ∈ PSH(X, θ)` with

  `a⁻¹ η + (1 - a⁻¹) ψ ≤ φ`.   (2.29)

Its **Step 1** splits into three pieces on `xia-sgpt:page-0084`--`page-0086`:

* **Step 1.1** — the case `ψ ∼ φ`, where `η = φ - C` works;
* **Step 1.2** — a reduction replacing `ψ` by the `P`-envelope fixed point
  `φ_∞ = P_θ[ψ]`, together with the observation (2.34);
* **Step 1.3** — the contradiction argument, which is the only piece that uses
  Xia's Theorem 2.4.4 (envelope concentration) for the affine obstacle.

This module proves Steps 1.1 and the (2.34) half of Step 1.2, in the form the
rest of the argument consumes.  Nothing here needs a measure, a Kähler
background, or a mass: both are order statements about `θ`-PSH potentials and
about `P_θ[·]`.

## What is proved

* `convexCombValue_le_of_le_add_coe` — the pointwise inequality behind Step 1.1;
* `exists_convexCombBarrier_of_moreSingular` — **Step 1.1**: if `ψ` is at least
  as singular as `φ` (one global additive constant `ψ ≤ φ + C`, which is Xia's
  `ψ ∼ φ` in the direction that matters), then (2.29) holds with
  `η = φ - (a-1)C`;
* `le_add_const_of_le_of_singularityEnvelope_eq` — **Xia's (2.34)**, in the form
  that avoids a supremum over `X`: if `P_θ[Φ] = Φ` and `τ ≤ Φ` is `θ`-PSH with
  `τ ≤ B` for a real `B`, then `τ ≤ Φ + B` *everywhere*.  Xia states this as
  `sup_{Φ ≠ -∞}(τ - Φ) = sup_X τ`; the inequality above is the direction Step 1.3
  uses (`{η_j ≤ Φ - ak} = X` once `sup_X η_j ≤ -ak`), and it needs no
  subtraction of infinities.

Step 1.3 itself is not here: it consumes envelope concentration for the affine
obstacle, `Pending.DominationPrincipleContactChain.xiaTheorem244_affineObstacle_noncontact_eq_zero`.

**Neither theorem currently carries load, and that is deliberate.**  Step 1.1 is
not needed by
`Pending.RooftopConvexCombBarrierStepOneAssembly`, because
`RooftopConvexCombBarrierTruncatedLimit.shifted_mem_rooftopCompetitors` exhibits
`ϕ - a k` as a competitor of the truncated obstacle outright, which is a shorter
route to the same nonemptiness.  And (2.34) is an input to Xia's *proof* of the
Step 1.3 nondegeneracy, which is still an open interface, so nothing consumes it
yet either.  Both are kept because they are exactly what that proof needs.
-/

open Set
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierStepOne

open FirstPass
open SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-! ### The pointwise inequality behind Step 1.1 -/

/-- **Step 1.1, pointwise.**  Let `a > 1` and let `A` be an extended real that
is not `⊤`.  If `B ≤ A + C` for a real `C`, then the barrier value of (2.29)
built from the *shifted* potential `A - (a-1)C` lies below `A`.

The shift is exactly the one Xia writes as `η = φ - C` for large `C`: the
weight `1 - a⁻¹` in front of `B` costs `(1 - a⁻¹)C`, and `a⁻¹` of the shift
repays it. -/
theorem convexCombValue_le_of_le_add_coe {a : ℝ} (ha : 1 < a) {A B : EReal} {C : ℝ}
    (hAtop : A ≠ ⊤) (hB : B ≤ A + (C : EReal)) :
    ((a⁻¹ : ℝ) : EReal) * (A + ((-((a - 1) * C) : ℝ) : EReal)) +
        ((1 - a⁻¹ : ℝ) : EReal) * B ≤ A := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have hinv0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  have hinv1 : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
  have hrest0 : (0 : ℝ) < 1 - a⁻¹ := by linarith
  rcases eq_or_ne A ⊥ with hA | hA
  · -- A pole of `A` is a pole of `B`, and the whole expression is `⊥`.
    subst hA
    have hBbot : B = ⊥ := by
      simpa [EReal.bot_add] using hB
    subst hBbot
    rw [EReal.coe_mul_bot_of_pos hrest0, EReal.add_bot]
  · lift A to ℝ using ⟨hAtop, hA⟩ with α
    have hBtop : B ≠ ⊤ := by
      intro h
      rw [h] at hB
      rw [← EReal.coe_add] at hB
      exact absurd (top_le_iff.mp hB) (EReal.coe_ne_top _)
    rcases eq_or_ne B ⊥ with hBbot | hBbot
    · subst hBbot
      rw [EReal.coe_mul_bot_of_pos hrest0, EReal.add_bot]
      exact bot_le
    · lift B to ℝ using ⟨hBtop, hBbot⟩ with b
      have hb : b ≤ α + C := by
        rw [← EReal.coe_add] at hB
        exact EReal.coe_le_coe_iff.mp hB
      rw [← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      refine EReal.coe_le_coe_iff.mpr ?_
      have hid : a⁻¹ * (α + -((a - 1) * C)) = a⁻¹ * α - (1 - a⁻¹) * C := by
        field_simp
        ring
      rw [hid]
      nlinarith

/-! ### Step 1.1 -/

/-- **Xia's Step 1.1** (`xia-sgpt:page-0084`).  If `ψ` is **at least as
singular** as `φ` — one global additive constant `ψ ≤ φ + C`, i.e.
`MoreSingularOn ψ φ`, which is the half of `ψ ∼ φ` the argument uses (the other
half, `φ ≤ ψ`, is not needed) — then Xia's (2.29) holds outright, with the
explicit competitor `η = φ - (a-1)C`.

No mass, measure, or Kähler background is involved, and no envelope is formed:
this is the base case that makes the family of Step 1.2 nonempty. -/
theorem exists_convexCombBarrier_of_moreSingular {theta : SmoothRealForm n M 2}
    {phi psi : M → EReal} (hphi : IsThetaPshPotential theta phi)
    (hms : MoreSingularOn psi phi univ) {a : ℝ} (ha : 1 < a) :
    ∃ eta : M → EReal, IsThetaPshPotential theta eta ∧ convexComb a⁻¹ eta psi ≤ phi := by
  obtain ⟨C, hC⟩ := hms
  refine ⟨fun x => phi x + ((-((a - 1) * C) : ℝ) : EReal),
    hphi.add_const _, fun x => ?_⟩
  exact convexCombValue_le_of_le_add_coe ha
    (hphi.1.quasiPlurisubharmonic.ne_top x) (hC x (mem_univ x))

/-! ### Xia's (2.34) -/

/-- **Xia's (2.34)** (`xia-sgpt:page-0084`--`page-0085`), in the inequality form
Step 1.3 consumes.  Let `Φ` be a fixed point of the `P`-envelope,
`P_θ[Φ] = Φ`, and let `τ` be a `θ`-PSH potential with `τ ≤ Φ` and a global real
upper bound `B`.  Then `τ ≤ Φ + B` everywhere.

Xia phrases this as `sup_{Φ ≠ -∞}(τ - Φ) = sup_X τ`.  The form here avoids
subtracting `-∞` from `-∞`: it says precisely that the normalization
`τ - sup_X τ` still lies below `Φ`, which is how the identity is used — once
`sup_X η_j ≤ -a k`, the set `{η_j ≤ Φ - a k}` is all of `X`.

Only `P_θ[Φ] = Φ` is used, not the transfinite construction that produces it;
the hypothesis `τ ≤ Φ` enters only through the additive comparison. -/
theorem le_add_const_of_le_of_singularityEnvelope_eq {theta : SmoothRealForm n M 2}
    {Phi tau : M → EReal} (htau : IsThetaPshPotential theta tau)
    (hfix : singularityEnvelope theta Phi = Phi) (hle : tau ≤ Phi)
    {B : ℝ} (hB : ∀ x, tau x ≤ (B : EReal)) (x : M) :
    tau x ≤ Phi x + (B : EReal) := by
  have hshift : IsThetaPshPotential theta (fun y => tau y + ((-B : ℝ) : EReal)) :=
    htau.add_const (-B)
  have hle0 : (fun y => tau y + ((-B : ℝ) : EReal)) ≤ 0 := by
    intro y
    have h := hB y
    calc tau y + ((-B : ℝ) : EReal) ≤ (B : EReal) + ((-B : ℝ) : EReal) :=
          add_le_add h le_rfl
      _ = 0 := by
          rw [← EReal.coe_add]
          norm_num
  have hms : MoreSingularOn (fun y => tau y + ((-B : ℝ) : EReal)) Phi univ :=
    ⟨-B, fun y _ => add_le_add (hle y) le_rfl⟩
  have hkey := le_singularityEnvelope hshift hle0 hms
  rw [hfix] at hkey
  have h := hkey x
  -- `tau x + (-B) ≤ Phi x` gives `tau x ≤ Phi x + B`.
  have h' := add_le_add h (le_refl ((B : ℝ) : EReal))
  calc tau x = tau x + ((-B : ℝ) : EReal) + ((B : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]
        norm_num
    _ ≤ Phi x + ((B : ℝ) : EReal) := h'

end

end SGPT.Foundations.Analysis.Pending.RooftopConvexCombBarrierStepOne
