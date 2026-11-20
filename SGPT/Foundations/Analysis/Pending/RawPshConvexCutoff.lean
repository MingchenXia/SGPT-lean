import SGPT.Foundations.Analysis.Pending.RegularizedMaxPsh
import SGPT.Foundations.Analysis.Pending.PshRadialRegularization

set_option autoImplicit false

/-! A genuine finite convex cutoff of arbitrary extended-real PSH input.
The bounded PSH field and sharp original truncation/superlevel identities
are internally proved. Poles, identically bottom, empty domains and n=0
are retained; no measure comparison or convergence certificate is supplied. -/

noncomputable section
open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.RawPshConvexCutoff
open FirstPass FirstPass.MongeAmpere SmoothMax RegularizedMaxEReal ScaledSmoothMax

variable {n : ℕ}

/-- The explicit convex cutoff is locally bounded PSH, even for a raw pole. -/
theorem isLocallyBoundedPshOn_convexCutoff
    (U : TopologicalSpace.Opens (ComplexModel n)) {u : ComplexModel n → EReal}
    (hu : PlurisubharmonicOn u U) (b : ℝ) :
    IsLocallyBoundedPshOn U
      (fun z => b + SmoothMax.posPart ((max (u z) ((b - 2 : ℝ) : EReal)).toReal - b)) := by
  let v : ComplexModel n → ℝ := fun z => (max (u z) ((b - 2 : ℝ) : EReal)).toReal
  have hv : IsLocallyBoundedPshOn U v :=
    PshRadialRegularization.isLocallyBoundedPshOn_truncation U.isOpen hu (b - 2)
  have hreg := RegularizedMaxPsh.plurisubharmonicOn_eregularizedMax
    (δ := 1) (by norm_num) hv.1
    ((RegularizedMaxPsh.discPshOn_const b (U : Set (ComplexModel n))).plurisubharmonicOn U.isOpen)
  have heq (y : ComplexModel n) :
      eregularizedMax 1 (v y : EReal) (b : EReal) =
        ((b + SmoothMax.posPart (v y - b) : ℝ) : EReal) := by
    rw [eregularizedMax_eq_coe_formula (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
      (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp
  refine ⟨?_, ?_⟩
  · intro z hz
    refine (hreg z hz).congr (Eventually.of_forall fun y => ?_)
    exact heq y
  · intro z hz
    obtain ⟨V, hzV, hVU, C, hC⟩ := hv.2 z hz
    refine ⟨V, hzV, hVU, |C| + |b| + 1, fun y hy => ?_⟩
    have hlo : max (v y) b ≤ b + SmoothMax.posPart (v y - b) := by
      simpa [scaledSmoothMax_apply] using
        max_le_scaledSmoothMax (by norm_num : (0 : ℝ) < 1)
          (fun _ : Unit => v y) (fun _ : Unit => b) ()
    have hhi : b + SmoothMax.posPart (v y - b) ≤ max (v y) b + 1 := by
      simpa [scaledSmoothMax_apply] using
        scaledSmoothMax_le_max_add (by norm_num : (0 : ℝ) < 1)
          (fun _ : Unit => v y) (fun _ : Unit => b) ()
    have hvy : v y ≤ |C| := (le_abs_self _).trans ((hC y hy).trans (le_abs_self C))
    have hm : max (v y) b ≤ |C| + |b| :=
      max_le (by linarith [abs_nonneg b]) (by linarith [le_abs_self b, abs_nonneg C])
    have hbq := (le_max_right (v y) b).trans hlo
    exact abs_le.mpr ⟨by change -(|C| + |b| + 1) ≤ b + SmoothMax.posPart (v y - b)
                         linarith [neg_abs_le b, abs_nonneg C],
                       by change b + SmoothMax.posPart (v y - b) ≤ |C| + |b| + 1
                          linarith⟩

/-- The cutoff preserves the exact sharp maximum and original superlevel,
including at negative infinity. Every finite threshold is natural input. -/
theorem convexCutoff_sharp_properties {u : EReal} (hu : u ≠ ⊤) (b : ℝ) :
    let q : ℝ := b + SmoothMax.posPart ((max u ((b - 2 : ℝ) : EReal)).toReal - b)
    (((b + 1 : ℝ) : EReal) ≤ u → (q : EReal) = u) ∧
    (u ≤ ((b + 1 : ℝ) : EReal) → q ≤ b + 1) ∧
    max (q : EReal) ((b + 1 : ℝ) : EReal) = max u ((b + 1 : ℝ) : EReal) ∧
    (((b + 1 : ℝ) : EReal) < (q : EReal) ↔ ((b + 1 : ℝ) : EReal) < u) := by
  let t : ℝ := (max u ((b - 2 : ℝ) : EReal)).toReal
  let q : ℝ := b + SmoothMax.posPart (t - b)
  have hbot : max u ((b - 2 : ℝ) : EReal) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)
  have htop : max u ((b - 2 : ℝ) : EReal) ≠ ⊤ :=
    (max_lt (lt_top_iff_ne_top.mpr hu) (EReal.coe_lt_top _)).ne
  have htc : (t : EReal) = max u ((b - 2 : ℝ) : EReal) := EReal.coe_toReal htop hbot
  have hfloor : ((b - 2 : ℝ) : EReal) ≤ ((b + 1 : ℝ) : EReal) := by
    exact_mod_cast (by linarith : b - 2 ≤ b + 1)
  have hhigh : ((b + 1 : ℝ) : EReal) ≤ u → (q : EReal) = u := by
    intro h
    have hu0 : u ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h
    have huc : (u.toReal : EReal) = u := EReal.coe_toReal hu hu0
    have ht : t = u.toReal := congrArg EReal.toReal (max_eq_left (hfloor.trans h))
    have hb : b + 1 ≤ u.toReal := by
      have hh := h
      rw [← huc] at hh
      exact_mod_cast hh
    have hq : q = u.toReal := by
      dsimp only [q]
      rw [ht, SmoothMax.posPart_eq_self (by linarith)]
      ring
    rw [hq, huc]
  have hlow : u ≤ ((b + 1 : ℝ) : EReal) → q ≤ b + 1 := by
    intro h
    have htE : (t : EReal) ≤ ((b + 1 : ℝ) : EReal) := by
      rw [htc]
      exact max_le h hfloor
    have ht : t ≤ b + 1 := by exact_mod_cast htE
    have hp := SmoothMax.posPart_monotone (show t - b ≤ 1 by linarith)
    rw [SmoothMax.posPart_eq_self (by norm_num : (1 : ℝ) ≤ 1)] at hp
    dsimp only [q]
    linarith
  have hmax : max (q : EReal) ((b + 1 : ℝ) : EReal) = max u ((b + 1 : ℝ) : EReal) := by
    by_cases h : ((b + 1 : ℝ) : EReal) ≤ u
    · rw [hhigh h]
    · have hl : u ≤ ((b + 1 : ℝ) : EReal) := (lt_of_not_ge h).le
      have hq : (q : EReal) ≤ ((b + 1 : ℝ) : EReal) := by exact_mod_cast hlow hl
      rw [max_eq_right hq, max_eq_right hl]
  refine ⟨hhigh, hlow, hmax, ?_⟩
  have hh := congrArg (fun r : EReal => ((b + 1 : ℝ) : EReal) < r) hmax
  have he : (((b + 1 : ℝ) : EReal) < (q : EReal)) =
      (((b + 1 : ℝ) : EReal) < u) := by
    simpa only [lt_max_iff, lt_self_iff_false, or_false] using hh
  exact ⟨fun h => he ▸ h, fun h => he.symm ▸ h⟩

end SGPT.Foundations.Analysis.Pending.RawPshConvexCutoff
