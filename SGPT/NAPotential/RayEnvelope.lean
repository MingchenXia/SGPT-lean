import SGPT.Convex.Epigraph
import Mathlib.Data.EReal.Operations

/-!
The hypotheses are statements about a concrete EReal function, not
certificates of the desired envelope value. The argument
uses the project's real-height epigraph definition of convexity.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.PointwiseRayEnvelope

/-- A convex function bounded above on a left ray and at 0 is ≤ 0 at -1.
No closedness, continuity, or prohibition of either infinite value is assumed. -/
theorem convex_le_zero_at_neg_one {f : ℝ → EReal} (hf : SGPT.Convex.IsConvex f)
    (hzero : f 0 ≤ 0) (c : ℝ) (hray : ∀ t : ℝ, t ≤ -1 → f t ≤ (c : EReal)) :
    f (-1) ≤ 0 := by
  by_contra hn
  obtain ⟨r, hr0', hrf⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hr0 : 0 < r := EReal.coe_lt_coe_iff.mp (by simpa using hr0')
  let k : ℝ := 2 + |c| / r
  have hk : 1 < k := by
    dsimp [k]
    have h := div_nonneg (abs_nonneg c) hr0.le
    linarith
  have hk0 : 0 < k := by linarith
  have hkr : r * (|c| / r) = |c| := by field_simp [ne_of_gt hr0]
  have hsmall : c / k < r := by
    rw [div_lt_iff₀ hk0]
    dsimp [k]
    have hca := le_abs_self c
    nlinarith
  have ha : 0 ≤ k⁻¹ := inv_nonneg.mpr hk0.le
  have hb : 0 ≤ 1 - k⁻¹ := by
    have hi : k⁻¹ < 1 := (inv_lt_one₀ hk0).mpr hk
    linarith
  have ht : -k ≤ -1 := by linarith
  have hconv := hf (x := (-k, c)) (y := (0, 0)) (hray (-k) ht)
    (by change f 0 ≤ ((0 : ℝ) : EReal); simpa using hzero) ha hb (by ring)
  change f (k⁻¹ • (-k) + (1 - k⁻¹) • (0 : ℝ)) ≤
    ((k⁻¹ * c + (1 - k⁻¹) * 0 : ℝ) : EReal) at hconv
  have hx : k⁻¹ • (-k) + (1 - k⁻¹) • (0 : ℝ) = -1 := by
    simp [smul_eq_mul, ne_of_gt hk0]
  have hy : k⁻¹ * c + (1 - k⁻¹) * 0 = c / k := by
    simp [div_eq_mul_inv, mul_comm]
  rw [hx, hy] at hconv
  exact (not_lt_of_ge hconv) ((EReal.coe_lt_coe hsmall).trans hrf)

/-- If the original curve is nonpositive, is zero at 0, and has a finite
constant left tail, its literal pointwise upper concave envelope is 0 at -1. -/
theorem upper_envelope_neg_one_eq_zero {a : ℝ → EReal}
    (hnonpos : ∀ t, a t ≤ 0) (hzero : a 0 = 0)
    (c : ℝ) (hray : ∀ t : ℝ, t ≤ -1 → a t = (c : EReal)) :
    -SGPT.Convex.lowerConvexEnvelope (fun t => -a t) (-1) = 0 := by
  let f : ℝ → EReal := fun t => -a t
  let g := SGPT.Convex.lowerConvexEnvelope f
  have hg0 : g 0 ≤ 0 := by
    have h := SGPT.Convex.lowerConvexEnvelope_le f 0
    simpa [f, hzero] using h
  have hgr : ∀ t : ℝ, t ≤ -1 → g t ≤ ((-c : ℝ) : EReal) := by
    intro t ht
    have h := SGPT.Convex.lowerConvexEnvelope_le f t
    simpa [f, hray t ht] using h
  have hle : g (-1) ≤ 0 :=
    convex_le_zero_at_neg_one (SGPT.Convex.isConvex_lowerConvexEnvelope f) hg0 (-c) hgr
  have hge : 0 ≤ g (-1) := by
    have hm : (fun _ : ℝ => (0 : EReal)) ≤ f := by
      intro t
      have h := EReal.neg_le_neg_iff.mpr (hnonpos t)
      simpa [f] using h
    have h := SGPT.Convex.le_lowerConvexEnvelope (SGPT.Convex.isConvex_const 0) hm (-1)
    simpa [g] using h
  have heq : g (-1) = 0 := le_antisymm hle hge
  simpa [g, f] using congrArg (fun v : EReal => -v) heq

end SGPT.NAPotential.PointwiseRayEnvelope
