import SGPT.Foundations.Analysis.Pending.BedfordTaylorTimeSlot

set_option autoImplicit false

/-!
# Functions with vanishing weak second derivative are affine

* `exists_affine_of_integral_mul_iteratedDeriv_two` — **the one-dimensional Weyl lemma**: a function
  `f` continuous on `(a, b)` with `∫ f χ'' = 0` for every smooth `χ` with compact support in `(a, b)`
  is affine on `(a, b)`.
* `exists_affine_of_integral_timeLaplacian` — **the strip form**: if `f` is continuous on `(a, b)` and
  `∫_ℂ f(Re τ) (Δψ/4)(τ) dλ(τ) = 0` for every smooth `ψ` with compact support in the strip
  `{a < Re τ < b}`, then `f` is affine on `(a, b)`. This is how "the energy is harmonic in `τ`"
  becomes "the energy is affine in `t`" at the end of Xia's Step 1 (`xia-sgpt:page-0171`).

## The proof of the Weyl lemma
1. If `χ` is smooth with compact support in `(c, d)`, `∫ χ = 0` and `∫ s χ(s) ds = 0`, then
   `η(x) = ∫_c^x (x - s) χ(s) ds` is smooth with compact support in `[c, d]` and `η'' = χ`
   (`exists_iteratedDeriv_two_eq`), so `∫ f χ = 0`.
2. For a normalized bump `ρ` and points `p < q`, `x`, the combination
   `ρ(· - x) - α ρ(· - p) - β ρ(· - q)` with `α + β = 1`, `α p + β q = x` has vanishing moments of
   order `0` and `1`, so the averages `A(y) = ∫ f(t) ρ(t - y) dt` satisfy `A(x) = α A(p) + β A(q)`.
3. As the bump shrinks, `A(y) → f(y)` by continuity, so `f(x) = α f(p) + β f(q)`.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.AffineOfWeakSecondDerivative

open BedfordTaylorTimeSlot

noncomputable section

/-! ### Primitives -/

/-- `∫_c^x χ`. -/
def prim (χ : ℝ → ℝ) (c x : ℝ) : ℝ := ∫ s in c..x, χ s

theorem hasDerivAt_prim {χ : ℝ → ℝ} (hχ : Continuous χ) (c x : ℝ) :
    HasDerivAt (prim χ c) (χ x) x :=
  (hχ.integral_hasStrictDerivAt c x).hasDerivAt

theorem deriv_prim {χ : ℝ → ℝ} (hχ : Continuous χ) (c : ℝ) : deriv (prim χ c) = χ :=
  funext fun x => (hasDerivAt_prim hχ c x).deriv

theorem contDiff_prim {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (c : ℝ) : ContDiff ℝ ∞ (prim χ c) := by
  rw [contDiff_infty_iff_deriv, deriv_prim hχ.continuous]
  exact ⟨fun x => (hasDerivAt_prim hχ.continuous c x).differentiableAt, hχ⟩

theorem prim_eq_zero_of_le {χ : ℝ → ℝ} {c x : ℝ} (hχ : ∀ s, s ≤ c → χ s = 0) (hx : x ≤ c) :
    prim χ c x = 0 := by
  unfold prim
  have h : ∀ s ∈ uIcc c x, χ s = (fun _ => (0 : ℝ)) s := fun s hs => by
    rw [uIcc_of_ge hx] at hs
    exact hχ s hs.2
  rw [intervalIntegral.integral_congr h]
  simp

theorem prim_eq_integral_of_ge {χ : ℝ → ℝ} {c d x : ℝ}
    (hχ : ∀ s, s ∉ Ioo c d → χ s = 0) (hcd : c ≤ d) (hx : d ≤ x) :
    prim χ c x = ∫ s, χ s := by
  unfold prim
  rw [intervalIntegral.integral_of_le (hcd.trans hx)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => hχ s fun h => hs ?_
  exact ⟨h.1, h.2.le.trans hx⟩

/-- **A double primitive.** If `χ` is smooth, vanishes off `(c, d)` and has vanishing moments
`∫ χ = 0 = ∫ s χ(s) ds`, then `η(x) = x ∫_c^x χ - ∫_c^x s χ(s) ds` is smooth, vanishes off `(c, d)`
and `η'' = χ`. -/
theorem exists_iteratedDeriv_two_eq {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {c d : ℝ} (hcd : c ≤ d)
    (hχcd : ∀ s, s ∉ Ioo c d → χ s = 0) (h0 : ∫ s, χ s = 0) (h1 : ∫ s, s * χ s = 0) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ (∀ x, x ∉ Ioo c d → η x = 0) ∧ iteratedDeriv 2 η = χ := by
  have hsχ : ContDiff ℝ ∞ fun s => s * χ s := contDiff_id.mul hχ
  have hsχcd : ∀ s, s ∉ Ioo c d → s * χ s = 0 := fun s hs => by rw [hχcd s hs, mul_zero]
  refine ⟨fun x => x * prim χ c x - prim (fun s => s * χ s) c x,
    (contDiff_id.mul (contDiff_prim hχ c)).sub (contDiff_prim hsχ c), ?_, ?_⟩
  · intro x hx
    rcases le_or_gt x c with hxc | hcx
    · have hle : ∀ s, s ≤ c → χ s = 0 := fun s hs => hχcd s fun h => absurd h.1 (not_lt.2 hs)
      have hle' : ∀ s, s ≤ c → s * χ s = 0 := fun s hs => by rw [hle s hs, mul_zero]
      simp only [prim_eq_zero_of_le hle hxc, prim_eq_zero_of_le hle' hxc, mul_zero, sub_zero]
    · have hdx : d ≤ x := by
        by_contra h
        exact hx ⟨hcx, lt_of_not_ge h⟩
      simp only [prim_eq_integral_of_ge hχcd hcd hdx, prim_eq_integral_of_ge hsχcd hcd hdx, h0, h1,
        mul_zero, sub_zero]
  · have hd1 : deriv (fun x => x * prim χ c x - prim (fun s => s * χ s) c x) = prim χ c := by
      funext x
      have h : HasDerivAt (fun y => y * prim χ c y - prim (fun s => s * χ s) c y)
          (1 * prim χ c x + x * χ x - x * χ x) x :=
        ((hasDerivAt_id' x).mul (hasDerivAt_prim hχ.continuous c x)).sub
          (hasDerivAt_prim hsχ.continuous c x)
      rw [h.deriv]
      simp
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd1, deriv_prim hχ.continuous]

/-- A compact subset of `(a, b)` lies in some `(c, d)` with `a < c ≤ d < b`. -/
theorem exists_Ioo_of_isCompact {a b : ℝ} {K : Set ℝ} (hK : IsCompact K) (hKab : K ⊆ Ioo a b)
    (hab : a < b) : ∃ c d, a < c ∧ c ≤ d ∧ d < b ∧ K ⊆ Ioo c d := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨(2 * a + b) / 3, (2 * a + b) / 3, by linarith, le_rfl, by linarith, empty_subset _⟩
  · have hm := hKab (hK.sInf_mem hne)
    have hM := hKab (hK.sSup_mem hne)
    refine ⟨(a + sInf K) / 2, (sSup K + b) / 2, by linarith [hm.1], ?_, by linarith [hM.2], ?_⟩
    · linarith [csInf_le hK.bddBelow (hK.sSup_mem hne), hm.1, hM.2]
    · intro k hk
      constructor
      · linarith [csInf_le hK.bddBelow hk, hm.1]
      · linarith [le_csSup hK.bddAbove hk, hM.2]

/-- **Test functions with vanishing moments.** Under the hypothesis of the Weyl lemma, `∫ f χ = 0`
for every smooth `χ` with compact support in `(a, b)` and `∫ χ = 0 = ∫ s χ(s) ds`. -/
theorem integral_mul_eq_zero_of_moments {a b : ℝ} {f : ℝ → ℝ}
    (h : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo a b →
      ∫ x, f x * iteratedDeriv 2 χ x = 0)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχab : tsupport χ ⊆ Ioo a b)
    (h0 : ∫ s, χ s = 0) (h1 : ∫ s, s * χ s = 0) : ∫ x, f x * χ x = 0 := by
  rcases le_or_gt b a with hba | hab
  · have : tsupport χ = ∅ := subset_eq_empty hχab (Ioo_eq_empty (not_lt.2 hba))
    have hz : ∀ x, χ x = 0 := fun x => image_eq_zero_of_notMem_tsupport (by simp [this])
    simp [hz]
  obtain ⟨c, d, hac, hcd, hdb, hK⟩ := exists_Ioo_of_isCompact hχc hχab hab
  have hχcd : ∀ s, s ∉ Ioo c d → χ s = 0 := fun s hs =>
    image_eq_zero_of_notMem_tsupport fun h => hs (hK h)
  obtain ⟨η, hη, hηcd, hη2⟩ := exists_iteratedDeriv_two_eq hχ hcd hχcd h0 h1
  have hηsupp : tsupport η ⊆ Icc c d :=
    closure_minimal (fun x hx => by
      by_contra h'
      exact hx (hηcd x fun h'' => h' (Ioo_subset_Icc_self h''))) isClosed_Icc
  have hηc : HasCompactSupport η := isCompact_Icc.of_isClosed_subset (isClosed_tsupport η) hηsupp
  have := h η hη hηc (hηsupp.trans (Icc_subset_Ioo hac hdb))
  rwa [hη2] at this

/-! ### Averages against translated bumps -/

/-- The bump of radii `r/2 < r` at `0`. -/
def bumpOfRadius (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) where
  rIn := r / 2
  rOut := r
  rIn_pos := half_pos hr
  rIn_lt_rOut := half_lt_self hr

/-- The translate `t ↦ ρ(t - y)` of the normalized bump. -/
def shiftedBump (φ : ContDiffBump (0 : ℝ)) (y t : ℝ) : ℝ := φ.normed volume (t - y)

theorem contDiff_shiftedBump (φ : ContDiffBump (0 : ℝ)) (y : ℝ) :
    ContDiff ℝ ∞ (shiftedBump φ y) :=
  φ.contDiff_normed.comp (contDiff_id.sub contDiff_const)

theorem shiftedBump_nonneg (φ : ContDiffBump (0 : ℝ)) (y t : ℝ) : 0 ≤ shiftedBump φ y t :=
  φ.nonneg_normed _

theorem shiftedBump_eq_zero (φ : ContDiffBump (0 : ℝ)) {y t : ℝ} (ht : φ.rOut ≤ |t - y|) :
    shiftedBump φ y t = 0 := by
  unfold shiftedBump
  by_contra h
  have : t - y ∈ Function.support (φ.normed volume) := h
  rw [φ.support_normed_eq, Real.ball_eq_Ioo] at this
  have h2 : |t - y| < φ.rOut := abs_lt.2 ⟨by linarith [this.1], by linarith [this.2]⟩
  linarith

theorem tsupport_shiftedBump (φ : ContDiffBump (0 : ℝ)) (y : ℝ) :
    tsupport (shiftedBump φ y) ⊆ closedBall y φ.rOut :=
  closure_minimal (fun t ht => by
    by_contra h
    rw [mem_closedBall, Real.dist_eq, not_le] at h
    exact ht (shiftedBump_eq_zero φ h.le)) isClosed_closedBall

theorem hasCompactSupport_shiftedBump (φ : ContDiffBump (0 : ℝ)) (y : ℝ) :
    HasCompactSupport (shiftedBump φ y) :=
  (isCompact_closedBall y φ.rOut).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_shiftedBump φ y)

theorem integral_shiftedBump (φ : ContDiffBump (0 : ℝ)) (y : ℝ) : ∫ t, shiftedBump φ y t = 1 := by
  unfold shiftedBump
  rw [integral_sub_right_eq_self (fun t => φ.normed volume t) y]
  exact φ.integral_normed

theorem integral_mul_shiftedBump (φ : ContDiffBump (0 : ℝ)) (y : ℝ) :
    ∫ t, t * shiftedBump φ y t = y + ∫ s, s * φ.normed volume s := by
  have h := integral_add_right_eq_self (μ := volume) (fun t => t * shiftedBump φ y t) y
  simp only [shiftedBump, add_sub_cancel_right] at h
  unfold shiftedBump
  rw [← h]
  have hi1 : Integrable fun s => s * φ.normed volume s :=
    (continuous_id.mul φ.continuous_normed).integrable_of_hasCompactSupport
      φ.hasCompactSupport_normed.mul_left
  have hi2 : Integrable fun s => y * φ.normed volume s := φ.integrable_normed.const_mul y
  have : (fun s => (s + y) * φ.normed volume s) =
      fun s => s * φ.normed volume s + y * φ.normed volume s := by
    funext s; ring
  rw [this, integral_add hi1 hi2, integral_const_mul, φ.integral_normed]
  ring

theorem integrable_mul_shiftedBump {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo a b))
    (φ : ContDiffBump (0 : ℝ)) {y : ℝ} (hy : closedBall y φ.rOut ⊆ Ioo a b) :
    Integrable fun t => f t * shiftedBump φ y t := by
  have hcont : Continuous fun t => f t * shiftedBump φ y t :=
    BedfordTaylor.continuous_of_continuousOn_of_eq_zero isOpen_Ioo isClosed_closedBall hy
      (hf.mul (contDiff_shiftedBump φ y).continuous.continuousOn) fun t ht => by
        rw [image_eq_zero_of_notMem_tsupport fun h => ht (tsupport_shiftedBump φ y h), mul_zero]
  exact hcont.integrable_of_hasCompactSupport (hasCompactSupport_shiftedBump φ y).mul_left

/-- `A(y) = ∫ f(t) ρ(t - y) dt`. -/
def bumpAverage (φ : ContDiffBump (0 : ℝ)) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ t, f t * shiftedBump φ y t

/-- **Three-point identity for the averages.** -/
theorem bumpAverage_eq_combination {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo a b))
    (h : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo a b →
      ∫ x, f x * iteratedDeriv 2 χ x = 0)
    (φ : ContDiffBump (0 : ℝ)) {p q x : ℝ} (hpq : p < q)
    (hp : closedBall p φ.rOut ⊆ Ioo a b) (hq : closedBall q φ.rOut ⊆ Ioo a b)
    (hx : closedBall x φ.rOut ⊆ Ioo a b) :
    bumpAverage φ f x =
      (q - x) / (q - p) * bumpAverage φ f p + (x - p) / (q - p) * bumpAverage φ f q := by
  set α := (q - x) / (q - p)
  set β := (x - p) / (q - p)
  have hqp : q - p ≠ 0 := sub_ne_zero.2 hpq.ne'
  have hαβ : α + β = 1 := by simp only [α, β]; field_simp; ring
  have hαβx : α * p + β * q = x := by simp only [α, β]; field_simp; ring
  set χ : ℝ → ℝ := fun t => shiftedBump φ x t - α * shiftedBump φ p t - β * shiftedBump φ q t
  have hχ : ContDiff ℝ ∞ χ :=
    ((contDiff_shiftedBump φ x).sub (contDiff_const.mul (contDiff_shiftedBump φ p))).sub
      (contDiff_const.mul (contDiff_shiftedBump φ q))
  have hsupp : tsupport χ ⊆ closedBall x φ.rOut ∪ closedBall p φ.rOut ∪ closedBall q φ.rOut := by
    refine closure_minimal (fun t ht => ?_)
      ((isClosed_closedBall.union isClosed_closedBall).union isClosed_closedBall)
    by_contra hn
    simp only [mem_union, not_or, mem_closedBall, Real.dist_eq, not_le] at hn
    exact ht (by simp only [χ, shiftedBump_eq_zero φ hn.1.1.le, shiftedBump_eq_zero φ hn.1.2.le,
      shiftedBump_eq_zero φ hn.2.le, mul_zero, sub_zero])
  have hχc : HasCompactSupport χ :=
    (((isCompact_closedBall _ _).union (isCompact_closedBall _ _)).union
      (isCompact_closedBall _ _)).of_isClosed_subset (isClosed_tsupport _) hsupp
  have hχab : tsupport χ ⊆ Ioo a b := hsupp.trans (union_subset (union_subset hx hp) hq)
  have hI (y : ℝ) : Integrable (shiftedBump φ y) :=
    (contDiff_shiftedBump φ y).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_shiftedBump φ y)
  have hJ (y : ℝ) : Integrable fun t => t * shiftedBump φ y t :=
    (continuous_id.mul (contDiff_shiftedBump φ y).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_shiftedBump φ y).mul_left
  have hA : Integrable fun t => shiftedBump φ x t - α * shiftedBump φ p t :=
    (hI x).sub ((hI p).const_mul α)
  have h0 : ∫ s, χ s = 0 := by
    simp only [χ]
    rw [integral_sub hA ((hI q).const_mul β),
      integral_sub (hI x) ((hI p).const_mul α), integral_const_mul, integral_const_mul,
      integral_shiftedBump, integral_shiftedBump, integral_shiftedBump]
    linarith
  have h1 : ∫ s, s * χ s = 0 := by
    have hfun : (fun s => s * χ s) = fun s =>
        s * shiftedBump φ x s - α * (s * shiftedBump φ p s) - β * (s * shiftedBump φ q s) := by
      funext s; simp only [χ]; ring
    have hB : Integrable fun s => s * shiftedBump φ x s - α * (s * shiftedBump φ p s) :=
      (hJ x).sub ((hJ p).const_mul α)
    rw [hfun, integral_sub hB ((hJ q).const_mul β),
      integral_sub (hJ x) ((hJ p).const_mul α), integral_const_mul, integral_const_mul,
      integral_mul_shiftedBump, integral_mul_shiftedBump, integral_mul_shiftedBump]
    linear_combination (-(∫ s, s * φ.normed volume s)) * hαβ - hαβx
  have hzero := integral_mul_eq_zero_of_moments h hχ hχc hχab h0 h1
  have hfun : (fun t => f t * χ t) = fun t =>
      f t * shiftedBump φ x t - α * (f t * shiftedBump φ p t) - β * (f t * shiftedBump φ q t) := by
    funext t; simp only [χ]; ring
  have hC : Integrable fun t => f t * shiftedBump φ x t - α * (f t * shiftedBump φ p t) :=
    (integrable_mul_shiftedBump hf φ hx).sub ((integrable_mul_shiftedBump hf φ hp).const_mul α)
  rw [hfun, integral_sub hC ((integrable_mul_shiftedBump hf φ hq).const_mul β),
    integral_sub (integrable_mul_shiftedBump hf φ hx)
      ((integrable_mul_shiftedBump hf φ hp).const_mul α),
    integral_const_mul, integral_const_mul] at hzero
  unfold bumpAverage
  linarith

/-- **The averages converge** as the bump shrinks. -/
theorem tendsto_bumpAverage {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo a b)) {y : ℝ}
    (hy : y ∈ Ioo a b) :
    Tendsto (fun k : ℕ => bumpAverage (bumpOfRadius (1 / (k + 1)) Nat.one_div_pos_of_nat) f y)
      atTop (𝓝 (f y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 (hf.continuousAt (isOpen_Ioo.mem_nhds hy))
    (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min hδ (lt_min (sub_pos.2 hy.1) (sub_pos.2 hy.2)))
  refine ⟨N, fun k hk => ?_⟩
  set φ := bumpOfRadius (1 / (k + 1)) Nat.one_div_pos_of_nat
  have hr : φ.rOut < min δ (min (y - a) (b - y)) := by
    have : (1 : ℝ) / (k + 1) ≤ 1 / (N + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hk)
    exact lt_of_le_of_lt this hN
  have hball : closedBall y φ.rOut ⊆ Ioo a b := by
    rw [Real.closedBall_eq_Icc]
    intro t ht
    constructor
    · linarith [ht.1, min_le_right δ (min (y - a) (b - y)), min_le_left (y - a) (b - y)]
    · linarith [ht.2, min_le_right δ (min (y - a) (b - y)), min_le_right (y - a) (b - y)]
  have hint := integrable_mul_shiftedBump hf φ hball
  have hI : Integrable (shiftedBump φ y) :=
    (contDiff_shiftedBump φ y).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_shiftedBump φ y)
  have hdiff : bumpAverage φ f y - f y = ∫ t, (f t - f y) * shiftedBump φ y t := by
    have : (fun t => (f t - f y) * shiftedBump φ y t) =
        fun t => f t * shiftedBump φ y t - f y * shiftedBump φ y t := by
      funext t; ring
    rw [this, integral_sub hint (hI.const_mul _), integral_const_mul, integral_shiftedBump,
      mul_one]
    rfl
  rw [Real.dist_eq, hdiff]
  have hbound : ∀ t, ‖(f t - f y) * shiftedBump φ y t‖ ≤ ε / 2 * shiftedBump φ y t := by
    intro t
    rw [norm_mul, Real.norm_of_nonneg (shiftedBump_nonneg φ y t), Real.norm_eq_abs]
    by_cases ht : |t - y| < φ.rOut
    · refine mul_le_mul_of_nonneg_right ?_ (shiftedBump_nonneg φ y t)
      have := hδf (show dist t y < δ by
        rw [Real.dist_eq]; exact ht.trans (hr.trans_le (min_le_left _ _)))
      rw [Real.dist_eq] at this
      exact this.le
    · rw [shiftedBump_eq_zero φ (not_lt.1 ht)]
      simp
  calc |∫ t, (f t - f y) * shiftedBump φ y t|
      ≤ ∫ t, ε / 2 * shiftedBump φ y t :=
        norm_integral_le_of_norm_le (hI.const_mul _) (Eventually.of_forall hbound)
    _ = ε / 2 := by rw [integral_const_mul, integral_shiftedBump, mul_one]
    _ < ε := half_lt_self hε

/-- **The one-dimensional Weyl lemma.** A function continuous on `(a, b)` whose weak second
derivative vanishes is affine on `(a, b)`. -/
theorem exists_affine_of_integral_mul_iteratedDeriv_two {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (h : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Ioo a b →
      ∫ x, f x * iteratedDeriv 2 χ x = 0) :
    ∃ c₀ c₁ : ℝ, ∀ x ∈ Ioo a b, f x = c₀ + c₁ * x := by
  rcases le_or_gt b a with hba | hab
  · exact ⟨0, 0, fun x hx => absurd (hx.1.trans hx.2) (not_lt.2 hba)⟩
  set p := (2 * a + b) / 3
  set q := (a + 2 * b) / 3
  have hp : p ∈ Ioo a b := ⟨by simp only [p]; linarith, by simp only [p]; linarith⟩
  have hq : q ∈ Ioo a b := ⟨by simp only [q]; linarith, by simp only [q]; linarith⟩
  have hpq : p < q := by simp only [p, q]; linarith
  have hqp : q - p ≠ 0 := sub_ne_zero.2 hpq.ne'
  have hev (y : ℝ) (hy : y ∈ Ioo a b) : ∀ᶠ k : ℕ in atTop,
      closedBall y (bumpOfRadius (1 / (k + 1)) Nat.one_div_pos_of_nat).rOut ⊆ Ioo a b := by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt (lt_min (sub_pos.2 hy.1) (sub_pos.2 hy.2))
    refine eventually_atTop.2 ⟨N, fun k hk => ?_⟩
    have hr : (1 : ℝ) / (k + 1) < min (y - a) (b - y) :=
      lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.succ_le_succ hk)) hN
    show closedBall y (1 / (k + 1)) ⊆ Ioo a b
    rw [Real.closedBall_eq_Icc]
    intro t ht
    exact ⟨by linarith [ht.1, min_le_left (y - a) (b - y)],
      by linarith [ht.2, min_le_right (y - a) (b - y)]⟩
  refine ⟨f p - (f q - f p) / (q - p) * p, (f q - f p) / (q - p), fun x hx => ?_⟩
  have hcomb : f x = (q - x) / (q - p) * f p + (x - p) / (q - p) * f q := by
    have hlim := ((tendsto_bumpAverage hf hp).const_mul ((q - x) / (q - p))).add
      ((tendsto_bumpAverage hf hq).const_mul ((x - p) / (q - p)))
    refine tendsto_nhds_unique (tendsto_bumpAverage hf hx) (hlim.congr' ?_)
    filter_upwards [hev p hp, hev q hq, hev x hx] with k hkp hkq hkx
    exact (bumpAverage_eq_combination hf h _ hpq hkp hkq hkx).symm
  rw [hcomb]
  field_simp
  ring

/-! ### The strip form -/

theorem iteratedDeriv_eq_zero_of_notMem_tsupport {χ : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport χ)
    (k : ℕ) : iteratedDeriv k χ x = 0 := by
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have : iteratedFDeriv ℝ k χ x = 0 := by
    by_contra h
    exact hx (support_iteratedFDeriv_subset k h)
  simp [this]

theorem tsupport_iteratedDeriv_subset (χ : ℝ → ℝ) (k : ℕ) :
    tsupport (iteratedDeriv k χ) ⊆ tsupport χ :=
  closure_minimal (fun x hx => by
    by_contra h
    exact hx (iteratedDeriv_eq_zero_of_notMem_tsupport h k)) (isClosed_tsupport χ)

/-- A second directional derivative is the second derivative along the real line. -/
theorem realHessian_eq_iteratedDeriv {u : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (τ v : ℂ) :
    realHessian u τ v v = iteratedDeriv 2 (fun s : ℝ => u (τ + (s : ℂ) * v)) 0 := by
  set A : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have h := realHessian_comp_affine hu A τ 0 1 1
  have hA (s : ℝ) : A s = (s : ℂ) * v := by simp [A, Complex.real_smul]
  simp only [hA, Complex.ofReal_zero, zero_mul, add_zero, Complex.ofReal_one, one_mul] at h
  rw [← h, iteratedDeriv_eq_iteratedFDeriv]
  unfold realHessian
  congr 1
  funext i
  fin_cases i <;> rfl

theorem timeLaplacian_re_mul_im {χ β : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hβ : ContDiff ℝ ∞ β)
    (τ : ℂ) :
    timeLaplacian (fun z : ℂ => χ z.re * β z.im) τ =
      (iteratedDeriv 2 χ τ.re * β τ.im + χ τ.re * iteratedDeriv 2 β τ.im) / 4 := by
  have hψ : ContDiff ℝ 2 fun z : ℂ => χ z.re * β z.im :=
    ((hχ.comp Complex.reCLM.contDiff).mul (hβ.comp Complex.imCLM.contDiff)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  unfold timeLaplacian
  rw [realHessian_eq_iteratedDeriv hψ, realHessian_eq_iteratedDeriv hψ]
  have h1 : (fun s : ℝ => χ (τ + (s : ℂ) * 1).re * β (τ + (s : ℂ) * 1).im) =
      fun s => χ (τ.re + s) * β τ.im := by
    funext s; simp
  have h2 : (fun s : ℝ => χ (τ + (s : ℂ) * Complex.I).re * β (τ + (s : ℂ) * Complex.I).im) =
      fun s => χ τ.re * β (τ.im + s) := by
    funext s; simp
  rw [h1, h2, iteratedDeriv_mul_const_field (fun s => χ (τ.re + s)),
    iteratedDeriv_const_mul_field _ (fun s => β (τ.im + s)),
    iteratedDeriv_comp_const_add, iteratedDeriv_comp_const_add]
  simp

theorem integrable_mul_of_tsupport {a b : ℝ} {f g : ℝ → ℝ} (hf : ContinuousOn f (Ioo a b))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgab : tsupport g ⊆ Ioo a b) :
    Integrable fun x => f x * g x := by
  have hcont : Continuous fun x => f x * g x :=
    BedfordTaylor.continuous_of_continuousOn_of_eq_zero isOpen_Ioo (isClosed_tsupport g) hgab
      (hf.mul hg.continuousOn) fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  exact hcont.integrable_of_hasCompactSupport hgc.mul_left

/-- **The strip form.** If `∫_ℂ f(Re τ) (Δψ/4)(τ) dλ(τ) = 0` for every smooth `ψ` with compact
support in the strip `{a < Re τ < b}`, then `f` is affine on `(a, b)`. -/
theorem exists_affine_of_integral_timeLaplacian {a b : ℝ} {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b))
    (h : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ {τ : ℂ | τ.re ∈ Ioo a b} → ∫ τ, f τ.re * timeLaplacian ψ τ = 0) :
    ∃ c₀ c₁ : ℝ, ∀ x ∈ Ioo a b, f x = c₀ + c₁ * x := by
  refine exists_affine_of_integral_mul_iteratedDeriv_two hf fun χ hχ hχc hχab => ?_
  set φ := bumpOfRadius 1 one_pos
  set β : ℝ → ℝ := φ.normed volume
  have hβ : ContDiff ℝ ∞ β := φ.contDiff_normed
  have hβc : HasCompactSupport β := φ.hasCompactSupport_normed
  set ψ : ℂ → ℝ := fun z => χ z.re * β z.im
  have hψ : ContDiff ℝ ∞ ψ := (hχ.comp Complex.reCLM.contDiff).mul (hβ.comp Complex.imCLM.contDiff)
  set e := Complex.equivRealProdCLM
  set S : Set ℂ := e ⁻¹' (tsupport χ ×ˢ tsupport β)
  have hSc : IsCompact S := e.toHomeomorph.isCompact_preimage.2 (hχc.prod hβc)
  have hSclosed : IsClosed S :=
    ((isClosed_tsupport χ).prod (isClosed_tsupport β)).preimage e.continuous
  have hψS : tsupport ψ ⊆ S := closure_minimal (fun z hz => by
    have h1 : χ z.re ≠ 0 := fun h0 => hz (by simp [ψ, h0])
    have h2 : β z.im ≠ 0 := fun h0 => hz (by simp [ψ, h0])
    exact ⟨subset_tsupport χ h1, subset_tsupport β h2⟩) hSclosed
  have hψc : HasCompactSupport ψ := hSc.of_isClosed_subset (isClosed_tsupport ψ) hψS
  have hψab : tsupport ψ ⊆ {τ : ℂ | τ.re ∈ Ioo a b} := fun z hz => hχab (hψS hz).1
  have hzero := h ψ hψ hψc hψab
  -- the integral over `ℂ = ℝ × ℝ`
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  rw [← hmp.integral_comp Complex.measurableEquivRealProd.symm.measurableEmbedding] at hzero
  have hTL (z : ℂ) : timeLaplacian ψ z =
      (iteratedDeriv 2 χ z.re * β z.im + χ z.re * iteratedDeriv 2 β z.im) / 4 :=
    timeLaplacian_re_mul_im hχ hβ z
  simp only [Complex.measurableEquivRealProd_symm_apply, hTL] at hzero
  have hfun : (fun p : ℝ × ℝ => f p.1 * ((iteratedDeriv 2 χ p.1 * β p.2 +
        χ p.1 * iteratedDeriv 2 β p.2) / 4)) =
      fun p => (f p.1 * iteratedDeriv 2 χ p.1 / 4) * β p.2 +
        (f p.1 * χ p.1 / 4) * iteratedDeriv 2 β p.2 := by
    funext p; ring
  have hχ2 : Continuous (iteratedDeriv 2 χ) := hχ.continuous_iteratedDeriv 2 (WithTop.coe_le_coe.mpr le_top)
  have hI1 : Integrable fun x => f x * iteratedDeriv 2 χ x / 4 := by
    have := integrable_mul_of_tsupport hf hχ2
      (hχc.mono' ((subset_tsupport _).trans (tsupport_iteratedDeriv_subset χ 2)))
      ((tsupport_iteratedDeriv_subset χ 2).trans hχab)
    exact this.div_const 4
  have hI2 : Integrable fun x => f x * χ x / 4 :=
    (integrable_mul_of_tsupport hf hχ.continuous hχc hχab).div_const 4
  have hβi : Integrable β := φ.integrable_normed
  have hβ1 : Continuous (deriv β) := hβ.continuous_deriv (by simp)
  have hβ2 : Continuous (iteratedDeriv 2 β) := hβ.continuous_iteratedDeriv 2 (WithTop.coe_le_coe.mpr le_top)
  have hβ2i : Integrable (iteratedDeriv 2 β) :=
    hβ2.integrable_of_hasCompactSupport
      (hβc.mono' ((subset_tsupport _).trans (tsupport_iteratedDeriv_subset β 2)))
  have hβ1i : Integrable (deriv β) := by
    have h1 : deriv β = iteratedDeriv 1 β := iteratedDeriv_one.symm
    rw [h1] at hβ1 ⊢
    exact hβ1.integrable_of_hasCompactSupport
      (hβc.mono' ((subset_tsupport _).trans (tsupport_iteratedDeriv_subset β 1)))
  have hβ2zero : ∫ y, iteratedDeriv 2 β y = 0 := by
    refine integral_eq_zero_of_hasDerivAt_of_integrable (f := deriv β) (fun y => ?_) hβ2i hβ1i
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (((contDiff_infty_iff_deriv.1 hβ).2.differentiable (by simp)) y).hasDerivAt
  have e1 := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x => f x * iteratedDeriv 2 χ x / 4) β
  have e2 := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x => f x * χ x / 4) (iteratedDeriv 2 β)
  rw [hfun, Measure.volume_eq_prod, integral_add (hI1.mul_prod hβi) (hI2.mul_prod hβ2i),
    e1, e2, φ.integral_normed, hβ2zero, mul_one, mul_zero, add_zero] at hzero
  rw [integral_div] at hzero
  linarith

end

end SGPT.Foundations.Analysis.Pending.AffineOfWeakSecondDerivative
