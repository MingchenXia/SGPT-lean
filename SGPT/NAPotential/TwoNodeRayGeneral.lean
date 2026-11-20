import SGPT.NAPotential.RayEnvelope

/-!
Generalized left-ray convexity bounds under finite vertical translations.
The proof uses real-height epigraphs and does not assume the convex function
finite, proper, or closed.
-/
set_option autoImplicit false
noncomputable section

namespace SGPT.NAPotential.TwoNodeRepair

/-- Scaling the parameter by any real constant and translating values by a
finite real preserves convexity in the exact extended-real epigraph sense. -/
theorem isConvex_scale_sub_real {f : ℝ → EReal} (hf : SGPT.Convex.IsConvex f)
    (q a : ℝ) : SGPT.Convex.IsConvex (fun t : ℝ => f (q * t) - (a : EReal)) := by
  intro p hp r hr α β hα hβ hsum
  change f (q * p.1) - (a : EReal) ≤ (p.2 : EReal) at hp
  change f (q * r.1) - (a : EReal) ≤ (r.2 : EReal) at hr
  have hp' : f (q * p.1) ≤ ((p.2 + a : ℝ) : EReal) := by
    have h := (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))).mp hp
    simpa only [← EReal.coe_add] using h
  have hr' : f (q * r.1) ≤ ((r.2 + a : ℝ) : EReal) := by
    have h := (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))).mp hr
    simpa only [← EReal.coe_add] using h
  have hm := hf (x := (q * p.1, p.2 + a)) (y := (q * r.1, r.2 + a))
    hp' hr' hα hβ hsum
  change f (q * (α • p.1 + β • r.1)) - (a : EReal) ≤
    ((α * p.2 + β * r.2 : ℝ) : EReal)
  apply (EReal.sub_le_iff_le_add
    (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))).mpr
  have harg : α • (q * p.1) + β • (q * r.1) =
      q * (α • p.1 + β • r.1) := by simp only [smul_eq_mul]; ring
  have hheight : α * (p.2 + a) + β * (r.2 + a) =
      (α * p.2 + β * r.2) + a := by
    calc
      _ = (α * p.2 + β * r.2) + (α + β) * a := by ring
      _ = _ := by rw [hsum, one_mul]
  change f (α • (q * p.1) + β • (q * r.1)) ≤
    ((α * (p.2 + a) + β * (r.2 + a) : ℝ) : EReal) at hm
  rw [harg, hheight] at hm
  simpa only [← EReal.coe_add] using hm

/-- A convex extended-real function bounded above on the whole left ray
lies below its finite right-end bound throughout that ray. -/
theorem convex_le_on_left_of_bounded_ray {f : ℝ → EReal}
    (hf : SGPT.Convex.IsConvex f) (a c : ℝ) (hzero : f 0 ≤ (a : EReal))
    (hray : ∀ t : ℝ, t ≤ -1 → f t ≤ (c : EReal))
    {s : ℝ} (hs : s ≤ -1) : f s ≤ (a : EReal) := by
  let q : ℝ := -s
  have hq : 1 ≤ q := by dsimp [q]; linarith
  let g : ℝ → EReal := fun t => f (q * t) - (a : EReal)
  have hg : SGPT.Convex.IsConvex g := isConvex_scale_sub_real hf q a
  have hgzero : g 0 ≤ 0 := by
    change f (q * 0) - (a : EReal) ≤ 0
    apply (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))).mpr
    simpa using hzero
  have hgray : ∀ t : ℝ, t ≤ -1 → g t ≤ ((c - a : ℝ) : EReal) := by
    intro t ht
    have hqt : q * t ≤ -1 := by
      have hm := mul_nonneg (sub_nonneg.mpr hq) (show 0 ≤ -t by linarith)
      nlinarith
    change f (q * t) - (a : EReal) ≤ ((c - a : ℝ) : EReal)
    apply (EReal.sub_le_iff_le_add
      (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))).mpr
    have h := hray (q * t) hqt
    simpa only [← EReal.coe_add, sub_add_cancel] using h
  have h := SGPT.NAPotential.PointwiseRayEnvelope.convex_le_zero_at_neg_one
    hg hgzero (c - a) hgray
  change f (q * -1) - (a : EReal) ≤ 0 at h
  have h' := (EReal.sub_le_iff_le_add
    (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))).mp h
  simpa [q] using h'

/-- Exact finite-height epigraph interpolation on the original two-node
segment, without assuming the convex function is finite at either endpoint. -/
theorem convex_le_on_unit_segment {f : ℝ → EReal} (hf : SGPT.Convex.IsConvex f)
    (a m : ℝ) (hzero : f 0 ≤ (a : EReal)) (hminus : f (-1) ≤ (m : EReal))
    {s : ℝ} (hs₁ : -1 ≤ s) (hs₀ : s ≤ 0) :
    f s ≤ (((1 + s) * a + (-s) * m : ℝ) : EReal) := by
  have h := hf (x := (0, a)) (y := (-1, m)) hzero hminus
    (show 0 ≤ 1 + s by linarith) (show 0 ≤ -s by linarith) (by ring)
  change f ((1 + s) • (0 : ℝ) + (-s) • (-1 : ℝ)) ≤
    (((1 + s) * a + (-s) * m : ℝ) : EReal) at h
  have hpoint : (1 + s) • (0 : ℝ) + (-s) • (-1 : ℝ) = s := by
    simp only [smul_eq_mul]
    ring
  rwa [hpoint] at h

end SGPT.NAPotential.TwoNodeRepair
