import SGPT.Foundations.Analysis.Pending.ThetaPshConvexCombination

set_option autoImplicit false

/-!
# The extended-real algebra of Xia's affine obstacle

Xia's Lemma 2.4.4 (`xia-sgpt:page-0083`) works with two readings of one
relation between three extended reals: the *barrier* form
`a⁻¹ E + (1 - a⁻¹) B ≤ A` of (2.29) and the *obstacle* form
`E ≤ a A + (1 - a) B` of (2.30).  For `a > 1` and a finite `B` they are the
same statement, and the whole pointwise family is collected here, with no
manifold and no measure in sight, so that both the envelope construction
(`Pending.ConvexCombEnvelopeMass`) and its consumers can use it without
importing one another.

These four lemmas were proved in `Pending.RooftopConvexCombBarrier`; that
module now `export`s them from here, so their fully qualified names and their
statements are unchanged.
-/

namespace SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra

noncomputable section

/-- For `a > 1` the value `a·A + (1-a)·B` of the affine combination lies below
`A` whenever `A ≤ B` and `B` is not `⊤`.  This is the pointwise reason why the
obstacle of Xia's envelope is dominated by the smaller potential. -/
theorem convexCombValue_le_left {a : ℝ} (ha : 1 < a) {A B : EReal}
    (hAB : A ≤ B) (hBtop : B ≠ ⊤) :
    (a : EReal) * A + ((1 - a : ℝ) : EReal) * B ≤ A := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have hneg : (1 - a : ℝ) < 0 := by linarith
  rcases eq_or_ne B ⊥ with hBbot | hBbot
  · subst hBbot
    have hA : A = ⊥ := le_bot_iff.mp hAB
    subst hA
    rw [EReal.coe_mul_bot_of_pos ha0, EReal.coe_mul_bot_of_neg hneg,
      EReal.bot_add]
  · lift B to ℝ using ⟨hBtop, hBbot⟩ with b
    rcases eq_or_ne A ⊥ with hAbot | hAbot
    · subst hAbot
      rw [EReal.coe_mul_bot_of_pos ha0, EReal.bot_add]
    · have hAtop : A ≠ ⊤ := fun h => by
        rw [h] at hAB; exact hBtop (top_le_iff.mp hAB)
      lift A to ℝ using ⟨hAtop, hAbot⟩ with α
      have hab : α ≤ b := EReal.coe_le_coe_iff.mp hAB
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      refine EReal.coe_le_coe_iff.mpr ?_
      nlinarith

/-- **The rearrangement behind Xia's (2.28)--(2.29).**  For `a > 1` and a
finite `B`, the `ε = a⁻¹` barrier inequality and the envelope inequality are
the same statement. -/
theorem convexCombValue_le_iff {a : ℝ} (ha : 1 < a) {A B E : EReal}
    (hBbot : B ≠ ⊥) (hBtop : B ≠ ⊤) :
    ((a⁻¹ : ℝ) : EReal) * E + ((1 - a⁻¹ : ℝ) : EReal) * B ≤ A ↔
      E ≤ (a : EReal) * A + ((1 - a : ℝ) : EReal) * B := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have hane : a ≠ 0 := ne_of_gt ha0
  have heps0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  lift B to ℝ using ⟨hBtop, hBbot⟩ with b
  rw [← EReal.coe_mul (1 - a⁻¹ : ℝ) b, ← EReal.coe_mul (1 - a : ℝ) b]
  induction E with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos heps0, EReal.bot_add]
    simp
  | top =>
    rw [EReal.coe_mul_top_of_pos heps0, EReal.top_add_coe]
    constructor
    · intro h
      have hA : A = ⊤ := top_le_iff.mp h
      subst hA
      rw [EReal.coe_mul_top_of_pos ha0, EReal.top_add_coe]
    · intro h
      induction A with
      | bot =>
        rw [EReal.coe_mul_bot_of_pos ha0, EReal.bot_add] at h
        exact absurd (le_bot_iff.mp h) (by simp)
      | top => exact le_rfl
      | coe alpha =>
        rw [← EReal.coe_mul a alpha, ← EReal.coe_add] at h
        exact absurd (top_le_iff.mp h) (EReal.coe_ne_top _)
  | coe e =>
    rw [← EReal.coe_mul (a⁻¹ : ℝ) e, ← EReal.coe_add]
    induction A with
    | bot =>
      rw [EReal.coe_mul_bot_of_pos ha0, EReal.bot_add]
      exact iff_of_false (fun h => EReal.coe_ne_bot _ (le_bot_iff.mp h))
        (fun h => EReal.coe_ne_bot _ (le_bot_iff.mp h))
    | top =>
      rw [EReal.coe_mul_top_of_pos ha0, EReal.top_add_coe]
      simp
    | coe alpha =>
      rw [← EReal.coe_mul a alpha, ← EReal.coe_add, EReal.coe_le_coe_iff,
        EReal.coe_le_coe_iff]
      constructor
      · intro h
        have h' := mul_le_mul_of_nonneg_left h ha0.le
        have hid : a * (a⁻¹ * e + (1 - a⁻¹) * b) = e + (a - 1) * b := by
          field_simp
        rw [hid] at h'
        nlinarith
      · intro h
        have h' := mul_le_mul_of_nonneg_left h heps0.le
        have hid : a⁻¹ * (a * alpha + (1 - a) * b) = alpha - (1 - a⁻¹) * b := by
          field_simp
          ring
        rw [hid] at h'
        nlinarith

/-- **The reverse rearrangement behind Xia's contact set.**  For `a > 1` and
`B` not `⊤`, if the obstacle value `a A + (1 - a) B` already lies below `E`,
then `A` lies below the barrier value `a⁻¹ E + (1 - a⁻¹) B`.  This is the
implication `{eta_a ≥ obstacle} ⊆ {phi ≤ gamma_a}` used to identify the
contact set. -/
theorem le_convexCombValue_of_convexCombValue_le {a : ℝ} (ha : 1 < a)
    {A B E : EReal} (hAB : A ≤ B) (hBtop : B ≠ ⊤) (hEtop : E ≠ ⊤)
    (h : (a : EReal) * A + ((1 - a : ℝ) : EReal) * B ≤ E) :
    A ≤ ((a⁻¹ : ℝ) : EReal) * E + ((1 - a⁻¹ : ℝ) : EReal) * B := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have heps0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  rcases eq_or_ne B ⊥ with hB | hB
  · subst hB
    rw [le_bot_iff.mp hAB]
    exact bot_le
  · lift B to ℝ using ⟨hBtop, hB⟩ with b
    rcases eq_or_ne A ⊥ with hA | hA
    · rw [hA]; exact bot_le
    · have hAtop : A ≠ ⊤ := fun hA' => hBtop (top_le_iff.mp (hA' ▸ hAB))
      lift A to ℝ using ⟨hAtop, hA⟩ with α
      rw [← EReal.coe_mul a α, ← EReal.coe_mul (1 - a : ℝ) b, ← EReal.coe_add] at h
      have hEbot : E ≠ ⊥ := fun hE => by
        rw [hE, le_bot_iff] at h
        exact EReal.coe_ne_bot _ h
      lift E to ℝ using ⟨hEtop, hEbot⟩ with e
      rw [EReal.coe_le_coe_iff] at h
      rw [← EReal.coe_mul (a⁻¹ : ℝ) e, ← EReal.coe_mul (1 - a⁻¹ : ℝ) b,
        ← EReal.coe_add, EReal.coe_le_coe_iff]
      have hid : a⁻¹ * (a * α + (1 - a) * b) = α - (1 - a⁻¹) * b := by
        field_simp
        ring
      have h' := mul_le_mul_of_nonneg_left h heps0.le
      rw [hid] at h'
      linarith

/-- **The cancellation behind `D_a ∩ {phi = psi} ⊆ {eta_a = phi}`.**  If the
barrier value built from `E` and `A` already equals `A`, and `E ≤ A` with `A`
not `⊤`, then `E = A`.  At a pole of `A` this is the inequality alone; off it
the finite affine relation cancels. -/
theorem eq_of_convexCombValue_eq {a : ℝ} (ha : 1 < a) {A E : EReal}
    (hEA : E ≤ A) (hAtop : A ≠ ⊤)
    (h : ((a⁻¹ : ℝ) : EReal) * E + ((1 - a⁻¹ : ℝ) : EReal) * A = A) :
    E = A := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have heps0 : (0 : ℝ) < a⁻¹ := inv_pos.mpr ha0
  rcases eq_or_ne A ⊥ with hA | hA
  · rw [hA] at hEA ⊢
    exact le_bot_iff.mp hEA
  · lift A to ℝ using ⟨hAtop, hA⟩ with α
    rw [← EReal.coe_mul (1 - a⁻¹ : ℝ) α] at h
    have hEtop : E ≠ ⊤ := fun hE => by
      rw [hE] at hEA
      exact hAtop (top_le_iff.mp hEA)
    have hEbot : E ≠ ⊥ := by
      intro hE
      rw [hE, EReal.coe_mul_bot_of_pos heps0, EReal.bot_add] at h
      exact EReal.coe_ne_bot _ h.symm
    lift E to ℝ using ⟨hEtop, hEbot⟩ with ε
    rw [← EReal.coe_mul (a⁻¹ : ℝ) ε, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    refine EReal.coe_eq_coe_iff.mpr ?_
    have hid : a⁻¹ * ε = a⁻¹ * α := by linarith
    exact mul_left_cancel₀ (ne_of_gt heps0) hid

/-- **Xia's (2.37), pointwise.**  Let `1 < a < a'` and put `c = a / a'`.  At a
point where the two potentials `A ≤ B` are finite, if `E` lies below the
`a'`-obstacle `a' A + (1 - a') B`, then the convex combination `c E + (1 - c) A`
lies below the `a`-obstacle `a A + (1 - a) B`.  This is the reason the
`a'`-competitors, pushed towards `A`, are `a`-competitors. -/
theorem convexCombValue_chain {a a' : ℝ} (ha : 1 < a) (haa : a < a')
    {A B E : EReal} (hAB : A ≤ B) (hAbot : A ≠ ⊥) (hAtop : A ≠ ⊤)
    (hBbot : B ≠ ⊥) (hBtop : B ≠ ⊤)
    (h : E ≤ (a' : EReal) * A + ((1 - a' : ℝ) : EReal) * B) :
    ((a / a' : ℝ) : EReal) * E + ((1 - a / a' : ℝ) : EReal) * A ≤
      (a : EReal) * A + ((1 - a : ℝ) : EReal) * B := by
  have ha0 : (0 : ℝ) < a := lt_trans zero_lt_one ha
  have ha'0 : (0 : ℝ) < a' := lt_trans ha0 haa
  have hc0 : (0 : ℝ) < a / a' := div_pos ha0 ha'0
  have hc1 : a / a' < 1 := (div_lt_one ha'0).mpr haa
  lift A to ℝ using ⟨hAtop, hAbot⟩ with α
  lift B to ℝ using ⟨hBtop, hBbot⟩ with b
  have hab : α ≤ b := EReal.coe_le_coe_iff.mp hAB
  rw [← EReal.coe_mul a' α, ← EReal.coe_mul (1 - a' : ℝ) b, ← EReal.coe_add] at h
  rw [← EReal.coe_mul (1 - a / a' : ℝ) α, ← EReal.coe_mul a α,
    ← EReal.coe_mul (1 - a : ℝ) b, ← EReal.coe_add]
  induction E with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hc0, EReal.bot_add]
    exact bot_le
  | top => exact absurd (top_le_iff.mp h) (EReal.coe_ne_top _)
  | coe e =>
    rw [← EReal.coe_mul (a / a' : ℝ) e, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have he : e ≤ a' * α + (1 - a') * b := EReal.coe_le_coe_iff.mp h
    have hstep : (a / a') * e ≤ (a / a') * (a' * α + (1 - a') * b) :=
      mul_le_mul_of_nonneg_left he hc0.le
    have hid : (a / a') * (a' * α + (1 - a') * b) = a * α + (a / a' - a) * b := by
      field_simp
    rw [hid] at hstep
    nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hc1)) (sub_nonneg.mpr hab)]

end

end SGPT.Foundations.Analysis.Pending.ConvexCombObstacleAlgebra
