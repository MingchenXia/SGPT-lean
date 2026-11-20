import SGPT.Okounkov.TranscendentalWNLegendreSmoothFamily

/-!
# Convex functions with linear growth (package WN-LEG)

Blueprint `claude-tok-wn-leg`, node `tok-wn-leg:chord`.  Let `f : ℝ → ℝ` be differentiable with
continuous strictly increasing derivative and `-K₁ + max(ay, by) ≤ f(y) ≤ K₂ + max(ay, by)`,
`a < b`.  Then

* `f'(y) ≥ b - (K₁ + K₂)/L` for `y ≥ L > 0` and `f'(y) ≤ a + (K₁ + K₂)/L` for `y ≤ -L`
  (`chord_lower`, `chord_upper`: the slope bounds behind the tightness estimate
  `tok-wn-leg:tight`);
* `a < f' < b` and `f'` maps `ℝ` onto `(a, b)` (`deriv_mem_Ioo_of_bounds`,
  `exists_deriv_eq_of_bounds`).

Consequently a smooth strictly convex `F(z, y)` with such bounds for every `z ∈ D` satisfies the
hypotheses of the smooth case (`IsSmoothLegendreData.of_bounds`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
  SGPT.Foundations.Analysis.FirstPass.MongeAmpere

section OneVariable

variable {f f' : ℝ → ℝ} {a b K₁ K₂ : ℝ}

theorem sub_le_of_deriv_le_on (hf : ∀ y, HasDerivAt f (f' y) y) (hmono : Monotone f')
    {x y : ℝ} (hxy : x ≤ y) : f y - f x ≤ f' y * (y - x) := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  refine (convex_Icc x y).image_sub_le_mul_sub_of_deriv_le hcont.continuousOn
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt) ?_ x (left_mem_Icc.mpr hxy) y
    (right_mem_Icc.mpr hxy) hxy
  intro t ht
  rw [interior_Icc] at ht
  rw [(hf t).deriv]
  exact hmono ht.2.le

theorem le_sub_of_le_deriv_on (hf : ∀ y, HasDerivAt f (f' y) y) (hmono : Monotone f')
    {x y : ℝ} (hxy : x ≤ y) : f' x * (y - x) ≤ f y - f x := by
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  refine (convex_Icc x y).mul_sub_le_image_sub_of_le_deriv hcont.continuousOn
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt) ?_ x (left_mem_Icc.mpr hxy) y
    (right_mem_Icc.mpr hxy) hxy
  intro t ht
  rw [interior_Icc] at ht
  rw [(hf t).deriv]
  exact hmono ht.1.le

variable (hf : ∀ y, HasDerivAt f (f' y) y) (hmono : Monotone f') (hab : a ≤ b)
  (hlo : ∀ y, -K₁ + max (a * y) (b * y) ≤ f y) (hhi : ∀ y, f y ≤ K₂ + max (a * y) (b * y))
include hf hmono hab hlo hhi

omit hab in
/-- **The slope bound at `+∞`**: `f'(y) ≥ b - (K₁ + K₂)/L` for `y ≥ L > 0`. -/
theorem chord_lower {L : ℝ} (hL : 0 < L) {y : ℝ} (hy : L ≤ y) :
    b - (K₁ + K₂) / L ≤ f' y := by
  have h1 := sub_le_of_deriv_le_on hf hmono hL.le
  have h2 := hlo L
  have h3 := hhi 0
  have hmax : b * L ≤ max (a * L) (b * L) := le_max_right _ _
  simp only [mul_zero, max_self, add_zero, sub_zero] at h3 h1
  have hfL : b * L - K₁ - K₂ ≤ f' L * L := by linarith
  have hdiv : b - f' L ≤ (K₁ + K₂) / L := by
    rw [le_div_iff₀ hL]
    nlinarith
  linarith [hmono hy]

omit hab in
/-- **The slope bound at `-∞`**: `f'(y) ≤ a + (K₁ + K₂)/L` for `y ≤ -L < 0`. -/
theorem chord_upper {L : ℝ} (hL : 0 < L) {y : ℝ} (hy : y ≤ -L) :
    f' y ≤ a + (K₁ + K₂) / L := by
  have h1 := le_sub_of_le_deriv_on hf hmono (show -L ≤ 0 by linarith)
  have h2 := hlo (-L)
  have h3 := hhi 0
  have hmax : a * -L ≤ max (a * -L) (b * -L) := le_max_left _ _
  simp only [mul_zero, max_self, add_zero, sub_neg_eq_add] at h3 h1
  have hfL : f' (-L) * L ≤ K₁ + K₂ + a * L := by nlinarith
  have : f' (-L) ≤ a + (K₁ + K₂) / L := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hL]
    linarith
  exact (hmono hy).trans this

omit hf hmono hab in
theorem bounds_nonneg : 0 ≤ K₁ + K₂ := by
  have h2 := hlo 0
  have h3 := hhi 0
  simp only [mul_zero, max_self, add_zero] at h2 h3
  linarith

omit hlo in
/-- **The derivative stays strictly below `b`** when it is strictly increasing. -/
theorem deriv_lt_of_bounds (hsm : StrictMono f') (y₀ : ℝ) : f' y₀ < b := by
  by_contra hcon
  push Not at hcon
  set y₁ := max y₀ 0 + 1 with hy₁
  have hy₀₁ : y₀ < y₁ := by rw [hy₁]; linarith [le_max_left y₀ 0]
  have hy₁0 : 0 ≤ y₁ := by rw [hy₁]; linarith [le_max_right y₀ 0]
  have hη : b < f' y₁ := hcon.trans_lt (hsm hy₀₁)
  set η := f' y₁ - b with hη_def
  have hηpos : 0 < η := by linarith
  set A := K₂ + b * y₁ - f y₁ with hA
  set t := y₁ + A / η + 1 with ht
  have hA0 : 0 ≤ A := by
    have := hhi y₁
    have hm : max (a * y₁) (b * y₁) ≤ b * y₁ := by
      rw [max_le_iff]; exact ⟨by nlinarith, le_rfl⟩
    linarith
  have hfrac : 0 ≤ A / η := div_nonneg hA0 hηpos.le
  have hty : y₁ ≤ t := by rw [ht]; linarith
  have ht0 : 0 ≤ t := hy₁0.trans hty
  have h1 := le_sub_of_le_deriv_on hf hmono hty
  have h2 := hhi t
  have hm : max (a * t) (b * t) ≤ b * t := by
    rw [max_le_iff]; exact ⟨by nlinarith, le_rfl⟩
  have hsplit : f' y₁ * (t - y₁) = b * (t - y₁) + η * (t - y₁) := by rw [hη_def]; ring
  have key : η * (t - y₁) ≤ A := by rw [hA]; nlinarith
  have hid : η * (t - y₁) = A + η := by
    rw [ht]; field_simp; ring
  linarith

/-- **The derivative stays strictly above `a`** (reflect `y ↦ -y`). -/
theorem lt_deriv_of_bounds (hsm : StrictMono f') (y₀ : ℝ) : a < f' y₀ := by
  have hg : ∀ y, HasDerivAt (fun y => f (-y)) (-f' (-y)) y := by
    intro y
    have := (hf (-y)).comp y (hasDerivAt_neg y)
    exact this.congr_deriv (by ring)
  have hgm : Monotone fun y => -f' (-y) := fun x y hxy => by
    simp only [neg_le_neg_iff]; exact hmono (neg_le_neg hxy)
  have hgs : StrictMono fun y => -f' (-y) := fun x y hxy => by
    simp only [neg_lt_neg_iff]; exact hsm (neg_lt_neg hxy)
  have hlo' : ∀ y, -K₁ + max (-b * y) (-a * y) ≤ f (-y) := by
    intro y
    have := hlo (-y)
    rw [max_comm] at this
    simpa [neg_mul, mul_neg] using this
  have hhi' : ∀ y, f (-y) ≤ K₂ + max (-b * y) (-a * y) := by
    intro y
    have := hhi (-y)
    rw [max_comm] at this
    simpa [neg_mul, mul_neg] using this
  have := deriv_lt_of_bounds hg hgm (neg_le_neg hab) hhi' hgs (-y₀)
  simp only [neg_neg, neg_lt_neg_iff] at this
  exact this

omit hab in
/-- **`f'` is onto `(a, b)`**, if it is continuous and strictly increasing. -/
theorem exists_deriv_eq_of_bounds (hc : Continuous f') {lam : ℝ} (hlam : lam ∈ Ioo a b) :
    ∃ y, f' y = lam := by
  have hK := bounds_nonneg hlo hhi
  set L₁ := (K₁ + K₂) / (b - lam) + 1 with hL₁
  set L₂ := (K₁ + K₂) / (lam - a) + 1 with hL₂
  have hb : 0 < b - lam := sub_pos.mpr hlam.2
  have ha : 0 < lam - a := sub_pos.mpr hlam.1
  have hL₁pos : 0 < L₁ := by rw [hL₁]; positivity
  have hL₂pos : 0 < L₂ := by rw [hL₂]; positivity
  have h1 : lam ≤ f' L₁ := by
    have := chord_lower hf hmono hlo hhi hL₁pos le_rfl
    have hlt : (K₁ + K₂) / L₁ ≤ b - lam := by
      rw [div_le_iff₀ hL₁pos, hL₁]
      have : (K₁ + K₂) / (b - lam) * (b - lam) = K₁ + K₂ := div_mul_cancel₀ _ hb.ne'
      nlinarith
    linarith
  have h2 : f' (-L₂) ≤ lam := by
    have := chord_upper hf hmono hlo hhi hL₂pos le_rfl
    have hlt : (K₁ + K₂) / L₂ ≤ lam - a := by
      rw [div_le_iff₀ hL₂pos, hL₂]
      have : (K₁ + K₂) / (lam - a) * (lam - a) = K₁ + K₂ := div_mul_cancel₀ _ ha.ne'
      nlinarith
    linarith
  have hle : -L₂ ≤ L₁ := by linarith
  obtain ⟨y, -, hy⟩ := intermediate_value_Icc hle hc.continuousOn ⟨h2, h1⟩
  exact ⟨y, hy⟩

end OneVariable

namespace IsSmoothLegendreData

variable {N : ℕ}

/-- **The hypotheses of the smooth case from linear growth** (`tok-wn-leg:chord`): `F` smooth on
`D × ℝ`, strictly convex in `y`, with `-K₁(z) + max(ay, by) ≤ F(z, y) ≤ K₂(z) + max(ay, by)`. -/
theorem of_bounds {D : Set (ComplexModel N)} {F : ComplexModel N × ℝ → ℝ} {a b : ℝ}
    (hD : IsOpen D) (hF : ContDiffOn ℝ ∞ F (D ×ˢ univ)) (hab : a < b)
    (hpos : ∀ z ∈ D, ∀ y : ℝ, 0 < partialYY F (z, y))
    (hbd : ∀ z ∈ D, ∃ K₁ K₂ : ℝ, ∀ y : ℝ,
      -K₁ + max (a * y) (b * y) ≤ F (z, y) ∧ F (z, y) ≤ K₂ + max (a * y) (b * y)) :
    IsSmoothLegendreData D F a b := by
  have hc2 : ∀ z ∈ D, ∀ y, ContDiffAt ℝ 2 F (z, y) := fun z hz y =>
    (hF.contDiffAt ((hD.prod isOpen_univ).mem_nhds ⟨hz, mem_univ y⟩)).of_le two_le_infty
  have hslice : ∀ z ∈ D, (∀ y, HasDerivAt (fun t => F (z, t)) (partialY F (z, y)) y) ∧
      StrictMono (fun y => partialY F (z, y)) ∧ Continuous fun y => partialY F (z, y) := by
    intro z hz
    refine ⟨fun y => hasDerivAt_slice (hc2 z hz y),
      strictMono_of_hasDerivAt_pos (fun y => hasDerivAt_partialY_slice (hc2 z hz y)) (hpos z hz),
      continuous_iff_continuousAt.mpr fun y =>
        (hasDerivAt_partialY_slice (hc2 z hz y)).continuousAt⟩
  refine ⟨hD, hF, hpos, fun z hz y => ?_, fun z hz lam hlam => ?_⟩
  · obtain ⟨K₁, K₂, hK⟩ := hbd z hz
    obtain ⟨hd, hsm, -⟩ := hslice z hz
    exact ⟨lt_deriv_of_bounds hd hsm.monotone hab.le (fun y => (hK y).1) (fun y => (hK y).2) hsm y,
      deriv_lt_of_bounds hd hsm.monotone hab.le (fun y => (hK y).2) hsm y⟩
  · obtain ⟨K₁, K₂, hK⟩ := hbd z hz
    obtain ⟨hd, hsm, hcont⟩ := hslice z hz
    exact exists_deriv_eq_of_bounds hd hsm.monotone (fun y => (hK y).1)
      (fun y => (hK y).2) hcont hlam

end IsSmoothLegendreData

end SGPT.Okounkov.TranscendentalWN
