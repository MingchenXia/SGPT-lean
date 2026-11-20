import SGPT.NAPotential.TwoNodeRepair
import SGPT.NAPotential.TwoNodeRayGeneral

/-!
Exact scalar lower-convex-envelope results for the negative of the repaired
two-node curve, including finite first-node values and minus-infinity poles.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.TwoNodeRepair

open Set

/-- The corrected two-node scalar curve when both original values are real. -/
def realTailHull (a b s : ℝ) : EReal :=
  if 0 < s then ⊥
  else if s ≤ -1 then (max a b : ℝ)
  else (((1 + s) * a + (-s) * max a b : ℝ) : EReal)

/-- Exact real-height epigraph of the negative corrected scalar curve. -/
theorem epigraph_neg_realTailHull (a b : ℝ) :
    SGPT.Convex.epigraph (fun s => -realTailHull a b s) =
      {p : ℝ × ℝ | p.1 ≤ 0 ∧ -max a b ≤ p.2 ∧
        -a + p.1 * (max a b - a) ≤ p.2} := by
  ext p
  have hm : 0 ≤ max a b - a := sub_nonneg.mpr (le_max_left a b)
  by_cases hp : 0 < p.1
  · simp only [SGPT.Convex.epigraph, realTailHull, hp, if_true, EReal.neg_bot,
      not_le.mpr (EReal.coe_lt_top p.2), Set.mem_ofPred_eq, not_le.mpr hp, false_and]
  by_cases ht : p.1 ≤ -1
  · have hline : -a + p.1 * (max a b - a) ≤ -max a b := by
      have h := mul_nonneg (show 0 ≤ -1 - p.1 by linarith) hm
      nlinarith
    simp only [SGPT.Convex.epigraph, realTailHull, hp, if_false, ht, if_true,
      ← EReal.coe_neg, EReal.coe_le_coe_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨not_lt.mp hp, h, hline.trans h⟩
    · exact fun h => h.2.1
  · have hline : -max a b ≤ -a + p.1 * (max a b - a) := by
      have h := mul_nonneg (show 0 ≤ p.1 + 1 by linarith) hm
      nlinarith
    have hv : -(((1 + p.1) * a + (-p.1) * max a b : ℝ) : EReal) =
        ((-a + p.1 * (max a b - a) : ℝ) : EReal) := by
      rw [← EReal.coe_neg]
      congr 1
      ring
    simp only [SGPT.Convex.epigraph, realTailHull, hp, if_false, ht, hv,
      EReal.coe_le_coe_iff, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨not_lt.mp hp, hline.trans h, h⟩
    · exact fun h => h.2.2

/-- Corrected scalar curve is concave, using the literal epigraph convention. -/
theorem isConvex_neg_realTailHull (a b : ℝ) :
    SGPT.Convex.IsConvex (fun s => -realTailHull a b s) := by
  rw [SGPT.Convex.IsConvex, epigraph_neg_realTailHull]
  intro p hp q hq α β hα hβ hsum
  rcases hp with ⟨hp₀, hp₁, hp₂⟩
  rcases hq with ⟨hq₀, hq₁, hq₂⟩
  refine ⟨?_, ?_, ?_⟩
  · change α * p.1 + β * q.1 ≤ 0
    have h := add_nonpos (mul_nonpos_of_nonneg_of_nonpos hα hp₀)
      (mul_nonpos_of_nonneg_of_nonpos hβ hq₀)
    exact h
  · change -max a b ≤ α * p.2 + β * q.2
    have h := add_le_add (mul_le_mul_of_nonneg_left hp₁ hα)
      (mul_le_mul_of_nonneg_left hq₁ hβ)
    have he : α * (-max a b) + β * (-max a b) = -max a b := by
      rw [← add_mul, hsum, one_mul]
    rwa [he] at h
  · change -a + (α * p.1 + β * q.1) * (max a b - a) ≤ α * p.2 + β * q.2
    have h := add_le_add (mul_le_mul_of_nonneg_left hp₂ hα)
      (mul_le_mul_of_nonneg_left hq₂ hβ)
    have he : α * (-a + p.1 * (max a b - a)) +
        β * (-a + q.1 * (max a b - a)) =
          -a + (α * p.1 + β * q.1) * (max a b - a) := by
      calc
        _ = -(α + β) * a + (α * p.1 + β * q.1) * (max a b - a) := by ring
        _ = _ := by rw [hsum]; ring
    rwa [he] at h

/-- The original scalar two-node piecewise-linear curve. -/
def realTwoNodeInput (a b s : ℝ) : EReal :=
  if 0 < s then ⊥
  else if s ≤ -1 then (b : EReal)
  else (((1 + s) * a + (-s) * b : ℝ) : EReal)

/-- The max-tail replacement dominates the original source trace. -/
theorem realTwoNodeInput_le_realTailHull (a b s : ℝ) :
    realTwoNodeInput a b s ≤ realTailHull a b s := by
  by_cases hp : 0 < s
  · simp only [realTwoNodeInput, realTailHull, hp, if_true, le_refl]
  by_cases ht : s ≤ -1
  · simp only [realTwoNodeInput, realTailHull, hp, if_false, ht, if_true,
      EReal.coe_le_coe_iff]
    exact le_max_right a b
  · simp only [realTwoNodeInput, realTailHull, hp, if_false, ht,
      EReal.coe_le_coe_iff]
    have h := mul_nonneg (show 0 ≤ -s by linarith [not_lt.mp hp])
      (sub_nonneg.mpr (le_max_right a b))
    nlinarith

/-- Every convex minorant of the negative source trace lies below the
negative repaired curve; the hypotheses are actual endpoint/ray bounds. -/
theorem convex_minorant_le_neg_realTailHull (a b : ℝ) {f : ℝ → EReal}
    (hf : SGPT.Convex.IsConvex f) (hzero : f 0 ≤ ((-a : ℝ) : EReal))
    (hray : ∀ t : ℝ, t ≤ -1 → f t ≤ ((-b : ℝ) : EReal)) :
    f ≤ fun s => -realTailHull a b s := by
  intro s
  by_cases hp : 0 < s
  · simp only [realTailHull, hp, if_true, EReal.neg_bot, le_top]
  have hminusA : f (-1) ≤ ((-a : ℝ) : EReal) :=
    convex_le_on_left_of_bounded_ray hf (-a) (-b) hzero hray (by norm_num)
  have hminusB : f (-1) ≤ ((-b : ℝ) : EReal) := hray (-1) le_rfl
  have hminus : f (-1) ≤ ((-max a b : ℝ) : EReal) := by
    rcases le_total a b with hab | hba
    · simpa only [max_eq_right hab] using hminusB
    · simpa only [max_eq_left hba] using hminusA
  by_cases ht : s ≤ -1
  · have ha := convex_le_on_left_of_bounded_ray hf (-a) (-b) hzero hray ht
    have hb := hray s ht
    have hm : f s ≤ ((-max a b : ℝ) : EReal) := by
      rcases le_total a b with hab | hba
      · simpa only [max_eq_right hab] using hb
      · simpa only [max_eq_left hba] using ha
    simpa only [realTailHull, hp, if_false, ht, if_true, ← EReal.coe_neg] using hm
  · have hs₁ : -1 ≤ s := (not_le.mp ht).le
    have hs₀ : s ≤ 0 := not_lt.mp hp
    have hmid := convex_le_on_unit_segment hf (-a) (-max a b) hzero hminus hs₁ hs₀
    have he : ((1 + s) * (-a) + (-s) * (-max a b) : ℝ) =
        -((1 + s) * a + (-s) * max a b) := by ring
    rw [he] at hmid
    simpa only [realTailHull, hp, if_false, ht, ← EReal.coe_neg] using hmid

/-- Exact scalar least-concave-majorant identity for two finite node values. -/
theorem literal_real_envelope_eq_tail_repair (a b s : ℝ) :
    -SGPT.Convex.lowerConvexEnvelope (fun t => -realTwoNodeInput a b t) s =
      realTailHull a b s := by
  let f : ℝ → EReal := fun t => -realTwoNodeInput a b t
  have hminor : (fun t => -realTailHull a b t) ≤ f := by
    intro t
    exact EReal.neg_le_neg_iff.mpr (realTwoNodeInput_le_realTailHull a b t)
  have hlo := SGPT.Convex.le_lowerConvexEnvelope (isConvex_neg_realTailHull a b) hminor
  have hzero : SGPT.Convex.lowerConvexEnvelope f 0 ≤ ((-a : ℝ) : EReal) := by
    have h := SGPT.Convex.lowerConvexEnvelope_le f 0
    have hone : realTwoNodeInput a b 0 = (a : EReal) := by
      norm_num [realTwoNodeInput]
    simpa only [f, hone, ← EReal.coe_neg] using h
  have hray : ∀ t : ℝ, t ≤ -1 → SGPT.Convex.lowerConvexEnvelope f t ≤
      ((-b : ℝ) : EReal) := by
    intro t ht
    have h := SGPT.Convex.lowerConvexEnvelope_le f t
    have hp : ¬ 0 < t := by linarith
    simpa [f, realTwoNodeInput, hp, ht] using h
  have hhi : SGPT.Convex.lowerConvexEnvelope f ≤ fun t => -realTailHull a b t :=
    convex_minorant_le_neg_realTailHull a b (SGPT.Convex.isConvex_lowerConvexEnvelope f)
      hzero hray
  have heq := le_antisymm hhi hlo
  have hv := congrFun heq s
  have hn := congrArg (fun z : EReal => -z) hv
  simpa only [f, neg_neg] using hn

/-- The scalar source trace when the first node is minus infinity and the
last node is finite. -/
def botFirstTailHull (b s : ℝ) : EReal :=
  if s ≤ -1 then (b : EReal) else ⊥

/-- In the pole case the real-height epigraph is one half-strip. -/
theorem epigraph_neg_botFirstTailHull (b : ℝ) :
    SGPT.Convex.epigraph (fun s => -botFirstTailHull b s) =
      {p : ℝ × ℝ | p.1 ≤ -1 ∧ -b ≤ p.2} := by
  ext p
  by_cases hp : p.1 ≤ -1
  · simp only [SGPT.Convex.epigraph, botFirstTailHull, hp, if_true,
      ← EReal.coe_neg, EReal.coe_le_coe_iff, Set.mem_ofPred_eq, true_and]
  · simp only [SGPT.Convex.epigraph, botFirstTailHull, hp, if_false, EReal.neg_bot,
      not_le.mpr (EReal.coe_lt_top p.2), Set.mem_ofPred_eq, false_and]

/-- No finiteness of the first node is hidden in the repaired concavity
argument: its minus-infinity case is directly epigraph-convex. -/
theorem isConvex_neg_botFirstTailHull (b : ℝ) :
    SGPT.Convex.IsConvex (fun s => -botFirstTailHull b s) := by
  rw [SGPT.Convex.IsConvex, epigraph_neg_botFirstTailHull]
  intro p hp q hq α β hα hβ hsum
  rcases hp with ⟨hp₀, hp₁⟩
  rcases hq with ⟨hq₀, hq₁⟩
  constructor
  · change α * p.1 + β * q.1 ≤ -1
    have h := add_le_add (mul_le_mul_of_nonneg_left hp₀ hα)
      (mul_le_mul_of_nonneg_left hq₀ hβ)
    have he : α * (-1 : ℝ) + β * (-1 : ℝ) = -1 := by nlinarith [hsum]
    rwa [he] at h
  · change -b ≤ α * p.2 + β * q.2
    have h := add_le_add (mul_le_mul_of_nonneg_left hp₁ hα)
      (mul_le_mul_of_nonneg_left hq₁ hβ)
    have he : α * (-b) + β * (-b) = -b := by rw [← add_mul, hsum, one_mul]
    rwa [he] at h

/-- Exact literal envelope in the first-node pole case: the original
trace is already concave in the real-height epigraph convention. -/
theorem literal_botFirst_envelope_eq_tail_repair (b s : ℝ) :
    -SGPT.Convex.lowerConvexEnvelope (fun t => -botFirstTailHull b t) s =
      botFirstTailHull b s := by
  rw [SGPT.Convex.lowerConvexEnvelope_eq_self (isConvex_neg_botFirstTailHull b)]
  exact neg_neg _

end SGPT.NAPotential.TwoNodeRepair
