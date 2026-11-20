import SGPT.Foundations.Analysis.FirstPass.PshRealConvexity

/-!
# Quantitative interior continuity on invariant PSH lines

The real trace of an imaginary-translation-invariant plurisubharmonic
function satisfies the usual local convex-function Lipschitz estimate whenever
the four values under consideration are finite.  This quantitative form is
suited to dominated-convergence arguments for chartwise `L¹` continuity.
-/

open Set

namespace SGPT.Foundations.Analysis

/-- Four finite values on an invariant PSH line satisfy the standard
three-point local Lipschitz estimate. -/
theorem PlurisubharmonicOn.comp_re_toReal_abs_sub_le
    {v : ℝ → EReal} {I : Set ℝ}
    (hu : PlurisubharmonicOn (fun z : ℂ => v z.re) (Complex.re ⁻¹' I))
    {a c b t : ℝ} (hac : a < c) (hcb : c < b)
    (hat : a < t) (htb : t < b) (habI : Icc a b ⊆ I)
    (ha_top : v a ≠ ⊤) (ha_bot : v a ≠ ⊥)
    (hc_top : v c ≠ ⊤) (hc_bot : v c ≠ ⊥)
    (hb_top : v b ≠ ⊤) (hb_bot : v b ≠ ⊥)
    (ht_top : v t ≠ ⊤) (ht_bot : v t ≠ ⊥) :
    |(v t).toReal - (v c).toReal| ≤ |t - c| *
      (|(v a).toReal - (v c).toReal| / (c - a) +
        |(v b).toReal - (v c).toReal| / (b - c)) := by
  let A : ℝ := (v a).toReal
  let C : ℝ := (v c).toReal
  let B : ℝ := (v b).toReal
  let T : ℝ := (v t).toReal
  have hca : 0 < c - a := sub_pos.mpr hac
  have hbc : 0 < b - c := sub_pos.mpr hcb
  rcases lt_trichotomy t c with htc | rfl | hct
  · have hupper := hu.comp_re_toReal_le_affine_chord hat htc
      (fun x hx => habI ⟨hx.1, hx.2.trans hcb.le⟩)
      ha_top ha_bot ht_top ht_bot hc_top hc_bot
    have hlower := hu.comp_re_toReal_le_affine_chord htc hcb
      (fun x hx => habI ⟨hat.le.trans hx.1, hx.2⟩)
      ht_top ht_bot hc_top hc_bot hb_top hb_bot
    change T ≤ A + (t - a) * (C - A) / (c - a) at hupper
    change C ≤ T + (c - t) * (B - T) / (b - t) at hlower
    have hbt : 0 < b - t := sub_pos.mpr (htc.trans hcb)
    have hupper' : (T - C) * (c - a) ≤ (c - t) * (A - C) := by
      have hform : A + (t - a) * (C - A) / (c - a) =
          ((c - t) * A + (t - a) * C) / (c - a) := by
        field_simp [hca.ne']
        ring
      rw [hform] at hupper
      have h := (le_div_iff₀ hca).mp hupper
      nlinarith
    have hlower' : (b - c) * (C - T) ≤ (c - t) * (B - C) := by
      have hform : T + (c - t) * (B - T) / (b - t) =
          ((b - c) * T + (c - t) * B) / (b - t) := by
        field_simp [hbt.ne']
        ring
      rw [hform] at hlower
      have h := (le_div_iff₀ hbt).mp hlower
      nlinarith
    have hu' : T - C ≤ (c - t) * |A - C| / (c - a) := by
      apply (le_div_iff₀ hca).2
      nlinarith [le_abs_self (A - C)]
    have hl' : -(c - t) * |B - C| / (b - c) ≤ T - C := by
      apply (div_le_iff₀ hbc).2
      nlinarith [le_abs_self (B - C)]
    change |T - C| ≤ |t - c| *
      (|A - C| / (c - a) + |B - C| / (b - c))
    have habs : |t - c| = c - t := by
      rw [abs_of_neg (sub_neg.mpr htc)]
      ring
    rw [habs]
    have hX : 0 ≤ |A - C| / (c - a) :=
      div_nonneg (abs_nonneg (A - C)) hca.le
    have hY : 0 ≤ |B - C| / (b - c) :=
      div_nonneg (abs_nonneg (B - C)) hbc.le
    have hct0 : 0 ≤ c - t := sub_nonneg.mpr htc.le
    have hl'' : -(c - t) * (|B - C| / (b - c)) ≤ T - C := by
      simpa [div_eq_mul_inv, mul_assoc] using hl'
    have hu'' : T - C ≤ (c - t) * (|A - C| / (c - a)) := by
      simpa [div_eq_mul_inv, mul_assoc] using hu'
    apply abs_le.mpr
    constructor
    · calc
        -((c - t) * (|A - C| / (c - a) + |B - C| / (b - c))) ≤
            -(c - t) * (|B - C| / (b - c)) := by
              nlinarith [mul_nonneg hct0 hX]
        _ ≤ T - C := hl''
    · calc
        T - C ≤ (c - t) * (|A - C| / (c - a)) := hu''
        _ ≤ (c - t) * (|A - C| / (c - a) + |B - C| / (b - c)) := by
          nlinarith [mul_nonneg hct0 hY]
  · simp
  · have hupper := hu.comp_re_toReal_le_affine_chord hct htb
      (fun x hx => habI ⟨hac.le.trans hx.1, hx.2⟩)
      hc_top hc_bot ht_top ht_bot hb_top hb_bot
    have hlower := hu.comp_re_toReal_le_affine_chord hac hct
      (fun x hx => habI ⟨hx.1, hx.2.trans htb.le⟩)
      ha_top ha_bot hc_top hc_bot ht_top ht_bot
    change T ≤ C + (t - c) * (B - C) / (b - c) at hupper
    change C ≤ A + (c - a) * (T - A) / (t - a) at hlower
    have hta : 0 < t - a := sub_pos.mpr (hac.trans hct)
    have hupper' : (T - C) * (b - c) ≤ (t - c) * (B - C) := by
      nlinarith [((le_div_iff₀ hbc).mp (show
        T - C ≤ (t - c) * (B - C) / (b - c) by linarith))]
    have hlower' : (c - a) * (C - T) ≤ (t - c) * (A - C) := by
      have hform : A + (c - a) * (T - A) / (t - a) =
          ((t - c) * A + (c - a) * T) / (t - a) := by
        field_simp [hta.ne']
        ring
      rw [hform] at hlower
      have h := (le_div_iff₀ hta).mp hlower
      nlinarith
    have hu' : T - C ≤ (t - c) * |B - C| / (b - c) := by
      apply (le_div_iff₀ hbc).2
      nlinarith [le_abs_self (B - C)]
    have hl' : -(t - c) * |A - C| / (c - a) ≤ T - C := by
      apply (div_le_iff₀ hca).2
      nlinarith [le_abs_self (A - C)]
    change |T - C| ≤ |t - c| *
      (|A - C| / (c - a) + |B - C| / (b - c))
    rw [abs_of_pos (sub_pos.mpr hct)]
    have hX : 0 ≤ |A - C| / (c - a) :=
      div_nonneg (abs_nonneg (A - C)) hca.le
    have hY : 0 ≤ |B - C| / (b - c) :=
      div_nonneg (abs_nonneg (B - C)) hbc.le
    have htc0 : 0 ≤ t - c := sub_nonneg.mpr hct.le
    have hl'' : -(t - c) * (|A - C| / (c - a)) ≤ T - C := by
      simpa [div_eq_mul_inv, mul_assoc] using hl'
    have hu'' : T - C ≤ (t - c) * (|B - C| / (b - c)) := by
      simpa [div_eq_mul_inv, mul_assoc] using hu'
    apply abs_le.mpr
    constructor
    · calc
        -((t - c) * (|A - C| / (c - a) + |B - C| / (b - c))) ≤
            -(t - c) * (|A - C| / (c - a)) := by
              nlinarith [mul_nonneg htc0 hY]
        _ ≤ T - C := hl''
    · calc
        T - C ≤ (t - c) * (|B - C| / (b - c)) := hu''
        _ ≤ (t - c) * (|A - C| / (c - a) + |B - C| / (b - c)) := by
          nlinarith [mul_nonneg htc0 hX]

end SGPT.Foundations.Analysis
