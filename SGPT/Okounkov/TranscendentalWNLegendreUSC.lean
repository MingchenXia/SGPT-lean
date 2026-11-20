import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Order.Filter.Finite

/-!
# Upper semicontinuity of suprema of concave families (WN21 Lemma 3.2)

Blueprint node `tok-wn:legendre-usc` (chapter `claude-tok-wn`); source D. Witt Nyström,
arXiv:2103.03660 (WN21), Lemma 3.2 (`references/wn21-restricted-volume`, `\label{usc}`).

*If `v_λ`, `λ ∈ [a, b]`, is a concave family of upper semicontinuous functions such that `v_λ`
is locally bounded for `λ ∈ [a', b']`, `a' < b'`, then `sup_{λ ∈ [a, b]} v_λ` is upper
semicontinuous.*  (WN21's proof uses `v_{a'}`, `v_{(a'+b')/2}`, `v_{b'}`, so
`[a', b'] ⊆ [a, b]` is implicit in the statement.)

Functions take values in `EReal`, never `⊤` (the usual `[-∞, ∞)` convention for upper
semicontinuous functions in pluripotential theory); the value `⊥` is allowed.  Concavity of a
family at a point `y` is the `EReal` chord inequality
`t v_{λ₁}(y) + (1 - t) v_{λ₂}(y) ≤ v_{t λ₁ + (1 - t) λ₂}(y)` for `λ₁, λ₂ ∈ [a, b]`, `t ∈ [0, 1]`
(`IsConcaveFamilyAt`).

The proof is WN21's: near `x`, bounds on `v_{a'}`, `v_m`, `v_{b'}` (`m = (a' + b') / 2`) and
concavity give one-sided slope bounds `v_λ ≤ v_μ + K |λ - μ|` (for `m ≤ μ ≤ λ`, resp.
`λ ≤ μ ≤ m`, `concave_right_slope_bound`), so the supremum over `[a, b]` is within `K h` of a
maximum over a finite grid of mesh `h` containing `m`, and each grid function is upper
semicontinuous.

## Main results

* `upperSemicontinuousAt_iSup_concave` — the pointwise statement at `x`;
* `upperSemicontinuousOn_iSup_concave`, `upperSemicontinuous_iSup_concave` — the lemma on an
  open set, resp. globally (the form of WN21 Lemma 3.2).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.TranscendentalWN

open Set Filter
open scoped Topology

variable {X : Type*}

/-- A family `v_λ`, `λ ∈ I`, is **concave at `y`**: the `EReal` chord inequality holds for all
`λ₁, λ₂ ∈ I` and `t ∈ [0, 1]`. -/
def IsConcaveFamilyAt (v : ℝ → X → EReal) (I : Set ℝ) (y : X) : Prop :=
  ∀ lam₁ ∈ I, ∀ lam₂ ∈ I, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (t : EReal) * v lam₁ y + ((1 - t : ℝ) : EReal) * v lam₂ y ≤
      v (t * lam₁ + (1 - t) * lam₂) y

/-! ### The slope bound -/

/-- The real core of the slope bound: two chord inequalities from `a'` give
`(m - a') (v_λ - v_μ) ≤ (λ - μ) (v_m - v_{a'})` for `a' < m ≤ μ ≤ λ`. -/
theorem slope_core {a' m μ lam p q r s : ℝ} (ham : a' < m) (hmμ : m ≤ μ) (hμl : μ ≤ lam)
    (h1 : (μ - a') * s + (lam - μ) * p ≤ (lam - a') * r)
    (h2 : (m - a') * r + (μ - m) * p ≤ (μ - a') * q) :
    (m - a') * (s - r) ≤ (lam - μ) * (q - p) := by
  have hμa : 0 < μ - a' := by linarith
  have hA : (μ - a') * (s - r) ≤ (lam - μ) * (r - p) := by nlinarith
  have hB : (m - a') * (r - p) ≤ (μ - a') * (q - p) := by nlinarith
  have hlμ : 0 ≤ lam - μ := by linarith
  have hma : 0 < m - a' := by linarith
  have hC : (μ - a') * ((m - a') * (s - r)) ≤ (μ - a') * ((lam - μ) * (q - p)) := by
    have := mul_le_mul_of_nonneg_left hA hma.le
    have := mul_le_mul_of_nonneg_left hB hlμ
    nlinarith
  exact le_of_mul_le_mul_left hC hμa

/-- The chord inequality between a real `p` at the left point and the values at the right
point, multiplied out: for `0 < t ≤ 1` the `EReal` chord inequality `t z + (1 - t) p ≤ w` with
finite `z`, `w` reads `t z + (1 - t) p ≤ w` in `ℝ`. -/
theorem chord_real_of_ereal {t p z w : ℝ}
    (h : (t : EReal) * (z : EReal) + ((1 - t : ℝ) : EReal) * (p : EReal) ≤ (w : EReal)) :
    t * z + (1 - t) * p ≤ w := by
  have : ((t * z + (1 - t) * p : ℝ) : EReal) ≤ (w : EReal) := by
    simpa only [EReal.coe_add, EReal.coe_mul] using h
  exact EReal.coe_le_coe_iff.mp this

/-- A chord inequality with a pole at the inner point forces a pole at the outer point. -/
theorem eq_bot_of_chord_bot {t p : ℝ} {z : EReal} (hz : z ≠ ⊤)
    (h : (t : EReal) * z + ((1 - t : ℝ) : EReal) * (p : EReal) ≤ ⊥) : z = ⊥ := by
  by_contra hzb
  have hz' : z = ((z.toReal : ℝ) : EReal) := (EReal.coe_toReal hz hzb).symm
  rw [hz', ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add] at h
  exact EReal.coe_ne_bot _ (le_bot_iff.mp h)

/-- **The one-sided slope bound** (WN21, proof of Lemma 3.2): for a family concave at `y` on
`I ⊇ [a', λ]`, with `v_{a'}(y) = p` and `v_m(y) = q` finite, `a' < m ≤ μ ≤ λ`,
`(m - a') v_λ(y) ≤ (m - a') v_μ(y) + (λ - μ)(q - p)`, i.e.
`v_λ(y) ≤ v_μ(y) + (λ - μ) (q - p) / (m - a')`. -/
theorem concave_right_slope_bound {v : ℝ → X → EReal} {I : Set ℝ} {y : X}
    (hconc : IsConcaveFamilyAt v I y) (hne : ∀ lam ∈ I, v lam y ≠ ⊤)
    {a' m μ lam p q : ℝ} (ham : a' < m) (hmμ : m ≤ μ) (hμl : μ ≤ lam)
    (ha'I : a' ∈ I) (hμI : μ ∈ I) (hlI : lam ∈ I)
    (hp : v a' y = (p : EReal)) (hq : v m y = (q : EReal)) :
    v lam y ≤ v μ y + (((lam - μ) * (q - p) / (m - a') : ℝ) : EReal) := by
  rcases eq_or_lt_of_le hμl with hμl' | hμl'
  · subst hμl'
    simp
  have hla : 0 < lam - a' := by linarith
  have hμa : 0 < μ - a' := by linarith
  have hma : 0 < m - a' := by linarith
  -- the chord at `μ` between `λ` and `a'`
  set t₁ : ℝ := (μ - a') / (lam - a') with ht₁
  have ht₁pos : 0 < t₁ := div_pos hμa hla
  have ht₁le : t₁ ≤ 1 := (div_le_one hla).mpr (by linarith)
  have hμeq : t₁ * lam + (1 - t₁) * a' = μ := by
    rw [ht₁]; field_simp; ring
  have c1 := hconc lam hlI a' ha'I t₁ ht₁pos.le ht₁le
  rw [hμeq, hp] at c1
  -- the chord at `m` between `μ` and `a'`
  set t₂ : ℝ := (m - a') / (μ - a') with ht₂
  have ht₂pos : 0 < t₂ := div_pos hma hμa
  have ht₂le : t₂ ≤ 1 := (div_le_one hμa).mpr (by linarith)
  have hmeq : t₂ * μ + (1 - t₂) * a' = m := by
    rw [ht₂]; field_simp; ring
  have c2 := hconc μ hμI a' ha'I t₂ ht₂pos.le ht₂le
  rw [hmeq, hp, hq] at c2
  by_cases hlb : v lam y = ⊥
  · rw [hlb]; exact bot_le
  by_cases hμb : v μ y = ⊥
  · rw [hμb] at c1
    exact absurd (eq_bot_of_chord_bot (hne lam hlI) c1) hlb
  set s : ℝ := (v lam y).toReal
  set r : ℝ := (v μ y).toReal
  have hs : v lam y = (s : EReal) := (EReal.coe_toReal (hne lam hlI) hlb).symm
  have hr : v μ y = (r : EReal) := (EReal.coe_toReal (hne μ hμI) hμb).symm
  rw [hs, hr] at c1
  rw [hr] at c2
  have r1 := chord_real_of_ereal c1
  have r2 := chord_real_of_ereal c2
  -- clear denominators
  have h1 : (μ - a') * s + (lam - μ) * p ≤ (lam - a') * r := by
    have e1 : t₁ * s + (1 - t₁) * p = ((μ - a') * s + (lam - μ) * p) / (lam - a') := by
      rw [ht₁]; field_simp; ring
    rw [e1, div_le_iff₀ hla] at r1
    linarith
  have h2 : (m - a') * r + (μ - m) * p ≤ (μ - a') * q := by
    have e2 : t₂ * r + (1 - t₂) * p = ((m - a') * r + (μ - m) * p) / (μ - a') := by
      rw [ht₂]; field_simp; ring
    rw [e2, div_le_iff₀ hμa] at r2
    linarith
  have key := slope_core ham hmμ hμl'.le h1 h2
  rw [hs, hr, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have : s - r ≤ (lam - μ) * (q - p) / (m - a') := by
    rw [le_div_iff₀ hma]; linarith
  linarith

/-- Concavity is preserved by the reflection `λ ↦ -λ`. -/
theorem IsConcaveFamilyAt.neg {v : ℝ → X → EReal} {I : Set ℝ} {y : X}
    (h : IsConcaveFamilyAt v I y) :
    IsConcaveFamilyAt (fun lam => v (-lam)) (-I) y := by
  intro l₁ hl₁ l₂ hl₂ t ht0 ht1
  have := h (-l₁) hl₁ (-l₂) hl₂ t ht0 ht1
  have he : -(t * l₁ + (1 - t) * l₂) = t * -l₁ + (1 - t) * -l₂ := by ring
  simpa only [he] using this

/-- **The left slope bound**, by reflection: for `λ ≤ μ ≤ m < b'`, with `v_{b'}(y) = p` and
`v_m(y) = q` finite, `v_λ(y) ≤ v_μ(y) + (μ - λ) (q - p) / (b' - m)`. -/
theorem concave_left_slope_bound {v : ℝ → X → EReal} {I : Set ℝ} {y : X}
    (hconc : IsConcaveFamilyAt v I y) (hne : ∀ lam ∈ I, v lam y ≠ ⊤)
    {b' m μ lam p q : ℝ} (hmb : m < b') (hμm : μ ≤ m) (hlμ : lam ≤ μ)
    (hb'I : b' ∈ I) (hμI : μ ∈ I) (hlI : lam ∈ I)
    (hp : v b' y = (p : EReal)) (hq : v m y = (q : EReal)) :
    v lam y ≤ v μ y + (((μ - lam) * (q - p) / (b' - m) : ℝ) : EReal) := by
  have h := concave_right_slope_bound (v := fun l => v (-l)) (I := -I) hconc.neg
    (fun l hl => hne (-l) hl) (a' := -b') (m := -m) (μ := -μ) (lam := -lam)
    (by linarith) (by linarith) (by linarith)
    (by simpa using hb'I) (by simpa using hμI) (by simpa using hlI)
    (by simpa using hp) (by simpa using hq)
  have e1 : (-lam - -μ) * (q - p) / (-m - -b') = (μ - lam) * (q - p) / (b' - m) := by ring
  simpa only [neg_neg, e1] using h

/-! ### Grids -/

/-- Every point of `[m, b]` lies within `h` above a grid point `m + k h`, `k ≤ ⌊(b - m)/h⌋`. -/
theorem exists_grid_right {m b h lam : ℝ} (hh : 0 < h) (hl : lam ∈ Icc m b) :
    ∃ k ∈ Finset.range (⌊(b - m) / h⌋₊ + 1),
      m + k * h ≤ lam ∧ lam - (m + k * h) < h := by
  have hx : 0 ≤ (lam - m) / h := div_nonneg (by linarith [hl.1]) hh.le
  refine ⟨⌊(lam - m) / h⌋₊, ?_, ?_, ?_⟩
  · rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_mono (div_le_div_of_nonneg_right (by linarith [hl.2]) hh.le)
  · have := Nat.floor_le hx
    have : (⌊(lam - m) / h⌋₊ : ℝ) * h ≤ lam - m := by
      rwa [le_div_iff₀ hh] at this
    linarith
  · have := Nat.lt_floor_add_one ((lam - m) / h)
    have : lam - m < ((⌊(lam - m) / h⌋₊ : ℝ) + 1) * h := by
      rwa [div_lt_iff₀ hh] at this
    nlinarith

/-- Every point of `[a, m]` lies within `h` below a grid point `m - k h`, `k ≤ ⌊(m - a)/h⌋`. -/
theorem exists_grid_left {m a h lam : ℝ} (hh : 0 < h) (hl : lam ∈ Icc a m) :
    ∃ k ∈ Finset.range (⌊(m - a) / h⌋₊ + 1),
      lam ≤ m - k * h ∧ (m - k * h) - lam < h := by
  obtain ⟨k, hk, h1, h2⟩ := exists_grid_right (m := -m) (b := -a) (lam := -lam) hh
    ⟨by linarith [hl.2], by linarith [hl.1]⟩
  refine ⟨k, by simpa [show -a - -m = m - a by ring] using hk, by linarith, by linarith⟩

/-- Grid points stay in the interval. -/
theorem grid_right_mem {m b h : ℝ} (hh : 0 < h) (hmb : m ≤ b) {k : ℕ}
    (hk : k ∈ Finset.range (⌊(b - m) / h⌋₊ + 1)) : m + k * h ∈ Icc m b := by
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hk' : (k : ℝ) ≤ (b - m) / h :=
    (Nat.cast_le.mpr hk).trans (Nat.floor_le (div_nonneg (by linarith) hh.le))
  rw [le_div_iff₀ hh] at hk'
  exact ⟨by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)], by linarith⟩

theorem grid_left_mem {m a h : ℝ} (hh : 0 < h) (ham : a ≤ m) {k : ℕ}
    (hk : k ∈ Finset.range (⌊(m - a) / h⌋₊ + 1)) : m - k * h ∈ Icc a m := by
  have := grid_right_mem (m := -m) (b := -a) hh (by linarith)
    (by simpa [show -a - -m = m - a by ring] using hk)
  exact ⟨by linarith [this.2], by linarith [this.1]⟩

/-! ### The lemma -/

variable [TopologicalSpace X]

/-- **WN21 Lemma 3.2 at a point.**  Let `v_λ`, `λ ∈ [a, b]`, be a family, concave near `x`,
with values `≠ ⊤` near `x`, each `v_λ` upper semicontinuous at `x`, and `v_{a'}`, `v_{b'}`,
`v_{(a'+b')/2}` bounded near `x`, `a ≤ a' < b' ≤ b` (it suffices that every `v_λ`,
`λ ∈ [a', b']`, be locally bounded near `x`).  Then `y ↦ sup_{λ ∈ [a, b]} v_λ(y)` is upper
semicontinuous at `x`. -/
theorem upperSemicontinuousAt_iSup_concave {v : ℝ → X → EReal} {a b a' b' : ℝ} {x : X}
    (haa : a ≤ a') (hab' : a' < b') (hbb : b' ≤ b)
    (hconc : ∀ᶠ y in 𝓝 x, IsConcaveFamilyAt v (Icc a b) y)
    (hne : ∀ᶠ y in 𝓝 x, ∀ lam ∈ Icc a b, v lam y ≠ ⊤)
    (husc : ∀ lam ∈ Icc a b, UpperSemicontinuousAt (v lam) x)
    (hbdd : ∀ lam ∈ Icc a' b', ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      ((-C : ℝ) : EReal) ≤ v lam y ∧ v lam y ≤ (C : EReal)) :
    UpperSemicontinuousAt (fun y => ⨆ lam ∈ Icc a b, v lam y) x := by
  set I := Icc a b
  set m : ℝ := (a' + b') / 2 with hm
  have ham : a' < m := by rw [hm]; linarith
  have hmb : m < b' := by rw [hm]; linarith
  have ha'I : a' ∈ I := ⟨haa, by linarith⟩
  have hb'I : b' ∈ I := ⟨by linarith, hbb⟩
  have hmI : m ∈ I := ⟨by linarith, by linarith⟩
  obtain ⟨C₁, hC₁⟩ := hbdd a' ⟨le_rfl, hab'.le⟩
  obtain ⟨C₂, hC₂⟩ := hbdd m ⟨ham.le, hmb.le⟩
  obtain ⟨C₃, hC₃⟩ := hbdd b' ⟨hab'.le, le_rfl⟩
  set C : ℝ := max (max |C₁| |C₂|) |C₃| with hC
  have hC₁C : |C₁| ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hC₂C : |C₂| ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hC₃C : |C₃| ≤ C := le_max_right _ _
  -- the slope constant
  set K : ℝ := 2 * C / (m - a') + 2 * C / (b' - m) + 1 with hK
  have hma : 0 < m - a' := by linarith
  have hbm : 0 < b' - m := by linarith
  have hC0 : 0 ≤ C := (abs_nonneg C₁).trans hC₁C
  have hKpos : 0 < K := by
    have : 0 ≤ 2 * C / (m - a') := div_nonneg (by linarith) hma.le
    have : 0 ≤ 2 * C / (b' - m) := div_nonneg (by linarith) hbm.le
    linarith
  -- finite values of the three bounded members near `x`
  have hfin : ∀ᶠ y in 𝓝 x, IsConcaveFamilyAt v I y ∧ (∀ lam ∈ I, v lam y ≠ ⊤) ∧
      (∃ p q r : ℝ, v a' y = p ∧ v m y = q ∧ v b' y = r ∧
        q - p ≤ 2 * C ∧ q - r ≤ 2 * C) := by
    filter_upwards [hconc, hne, hC₁, hC₂, hC₃] with y hcy hny h1 h2 h3
    refine ⟨hcy, hny, ?_⟩
    have fin : ∀ (z : EReal) (D : ℝ), ((-D : ℝ) : EReal) ≤ z → z ≤ (D : EReal) →
        ∃ w : ℝ, z = w ∧ -D ≤ w ∧ w ≤ D := by
      intro z D hl hu
      have hzb : z ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hl
      have hzt : z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hu
      refine ⟨z.toReal, (EReal.coe_toReal hzt hzb).symm, ?_, ?_⟩
      · rw [← EReal.coe_toReal hzt hzb] at hl; exact EReal.coe_le_coe_iff.mp hl
      · rw [← EReal.coe_toReal hzt hzb] at hu; exact EReal.coe_le_coe_iff.mp hu
    obtain ⟨p, hp, hp1, hp2⟩ := fin _ _ h1.1 h1.2
    obtain ⟨q, hq, hq1, hq2⟩ := fin _ _ h2.1 h2.2
    obtain ⟨r, hr, hr1, hr2⟩ := fin _ _ h3.1 h3.2
    refine ⟨p, q, r, hp, hq, hr, ?_, ?_⟩
    · have := le_abs_self C₂; have := le_abs_self C₁; linarith
    · have := le_abs_self C₂; have := le_abs_self C₃; linarith
  -- the uniform one-sided bounds
  have hslope : ∀ᶠ y in 𝓝 x, ∀ μ ∈ I, ∀ lam ∈ I,
      ((m ≤ μ ∧ μ ≤ lam) ∨ (lam ≤ μ ∧ μ ≤ m)) →
        v lam y ≤ v μ y + ((K * |lam - μ| : ℝ) : EReal) := by
    filter_upwards [hfin] with y ⟨hcy, hny, p, q, r, hp, hq, hr, hqp, hqr⟩
    intro μ hμ lam hl hcase
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hb := concave_right_slope_bound hcy hny ham h1 h2 ha'I hμ hl hp hq
      refine hb.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_))
      rw [abs_of_nonneg (by linarith : 0 ≤ lam - μ)]
      have e : (lam - μ) * (q - p) / (m - a') = (lam - μ) * ((q - p) / (m - a')) := by ring
      rw [e, mul_comm K]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have : (q - p) / (m - a') ≤ 2 * C / (m - a') := div_le_div_of_nonneg_right hqp hma.le
      have : 0 ≤ 2 * C / (b' - m) := div_nonneg (by linarith) hbm.le
      linarith
    · have hb := concave_left_slope_bound hcy hny hmb h2 h1 hb'I hμ hl hr hq
      refine hb.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_))
      rw [abs_of_nonpos (by linarith : lam - μ ≤ 0), neg_sub]
      have e : (μ - lam) * (q - r) / (b' - m) = (μ - lam) * ((q - r) / (b' - m)) := by ring
      rw [e, mul_comm K]
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      have : (q - r) / (b' - m) ≤ 2 * C / (b' - m) := div_le_div_of_nonneg_right hqr hbm.le
      have : 0 ≤ 2 * C / (m - a') := div_nonneg (by linarith) hma.le
      linarith
  -- now the upper semicontinuity
  intro c hc
  set S : EReal := ⨆ lam ∈ I, v lam x
  obtain ⟨c', hSc', hc'c⟩ := EReal.exists_between_coe_real hc
  -- `S` is finite
  have hvm : v m x ≤ S := le_iSup₂ (f := fun lam _ => v lam x) m hmI
  have hmx : v m x ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hC₂.self_of_nhds.1
  have hSbot : S ≠ ⊥ := ne_bot_of_le_ne_bot hmx hvm
  have hStop : S ≠ ⊤ := ne_top_of_lt hSc'
  set s : ℝ := S.toReal
  have hS : S = (s : EReal) := (EReal.coe_toReal hStop hSbot).symm
  have hsc' : s < c' := by
    have h' : S < c' := hSc'
    rw [hS] at h'; exact EReal.coe_lt_coe_iff.mp h'
  set ε : ℝ := c' - s
  have hε : 0 < ε := by simp only [ε]; linarith
  set h : ℝ := ε / (4 * K)
  have hh : 0 < h := div_pos hε (by linarith)
  have hKh : K * h = ε / 4 := by simp only [h]; field_simp
  -- grid members are eventually below `s + ε/2`
  have hgridR : ∀ k ∈ Finset.range (⌊(b - m) / h⌋₊ + 1),
      ∀ᶠ y in 𝓝 x, v (m + k * h) y < ((s + ε / 2 : ℝ) : EReal) := by
    intro k hk
    have hmem : m + k * h ∈ I := by
      have := grid_right_mem hh (by linarith [hmI.2] : m ≤ b) hk
      exact ⟨by linarith [this.1, hmI.1], this.2⟩
    have hle : v (m + k * h) x ≤ (s : EReal) := hS ▸ le_iSup₂ (f := fun lam _ => v lam x) _ hmem
    exact husc _ hmem _ (hle.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith)))
  have hgridL : ∀ k ∈ Finset.range (⌊(m - a) / h⌋₊ + 1),
      ∀ᶠ y in 𝓝 x, v (m - k * h) y < ((s + ε / 2 : ℝ) : EReal) := by
    intro k hk
    have hmem : m - k * h ∈ I := by
      have := grid_left_mem hh (by linarith [hmI.1] : a ≤ m) hk
      exact ⟨this.1, by linarith [this.2, hmI.2]⟩
    have hle : v (m - k * h) x ≤ (s : EReal) := hS ▸ le_iSup₂ (f := fun lam _ => v lam x) _ hmem
    exact husc _ hmem _ (hle.trans_lt (EReal.coe_lt_coe_iff.mpr (by linarith)))
  have hR := (Filter.eventually_all_finset _).mpr hgridR
  have hL := (Filter.eventually_all_finset _).mpr hgridL
  filter_upwards [hR, hL, hslope] with y hyR hyL hys
  have hbound : ∀ lam ∈ I, v lam y ≤ ((s + 3 * ε / 4 : ℝ) : EReal) := by
    intro lam hl
    rcases le_total m lam with hml | hlm
    · obtain ⟨k, hk, hk1, hk2⟩ := exists_grid_right hh ⟨hml, hl.2⟩
      have hmem : m + k * h ∈ I := by
        have := grid_right_mem hh (by linarith [hmI.2] : m ≤ b) hk
        exact ⟨by linarith [this.1, hmI.1], this.2⟩
      have h1 := hys _ hmem lam hl (Or.inl ⟨by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)], hk1⟩)
      have h2 : K * |lam - (m + k * h)| ≤ ε / 4 := by
        rw [abs_of_nonneg (by linarith)]
        calc K * (lam - (m + k * h)) ≤ K * h := mul_le_mul_of_nonneg_left hk2.le hKpos.le
          _ = ε / 4 := hKh
      calc v lam y ≤ v (m + k * h) y + ((K * |lam - (m + k * h)| : ℝ) : EReal) := h1
        _ ≤ ((s + ε / 2 : ℝ) : EReal) + ((ε / 4 : ℝ) : EReal) :=
          add_le_add (hyR k hk).le (EReal.coe_le_coe_iff.mpr h2)
        _ = ((s + 3 * ε / 4 : ℝ) : EReal) := by rw [← EReal.coe_add]; ring_nf
    · obtain ⟨k, hk, hk1, hk2⟩ := exists_grid_left hh ⟨hl.1, hlm⟩
      have hmem : m - k * h ∈ I := by
        have := grid_left_mem hh (by linarith [hmI.1] : a ≤ m) hk
        exact ⟨this.1, by linarith [this.2, hmI.2]⟩
      have h1 := hys _ hmem lam hl
        (Or.inr ⟨hk1, by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]⟩)
      have h2 : K * |lam - (m - k * h)| ≤ ε / 4 := by
        rw [abs_of_nonpos (by linarith), neg_sub]
        calc K * ((m - k * h) - lam) ≤ K * h := mul_le_mul_of_nonneg_left hk2.le hKpos.le
          _ = ε / 4 := hKh
      calc v lam y ≤ v (m - k * h) y + ((K * |lam - (m - k * h)| : ℝ) : EReal) := h1
        _ ≤ ((s + ε / 2 : ℝ) : EReal) + ((ε / 4 : ℝ) : EReal) :=
          add_le_add (hyL k hk).le (EReal.coe_le_coe_iff.mpr h2)
        _ = ((s + 3 * ε / 4 : ℝ) : EReal) := by rw [← EReal.coe_add]; ring_nf
  calc (⨆ lam ∈ I, v lam y) ≤ ((s + 3 * ε / 4 : ℝ) : EReal) := iSup₂_le hbound
    _ < (c' : EReal) := EReal.coe_lt_coe_iff.mpr (by simp only [ε]; linarith)
    _ < c := hc'c

/-- **WN21 Lemma 3.2 on a set.**  If on `U` the family `v_λ`, `λ ∈ [a, b]`, is concave, never
`⊤`, upper semicontinuous at every point of `U`, and `v_λ` is locally bounded near every point
of `U` for `λ ∈ [a', b']`, `a ≤ a' < b' ≤ b`, then `sup_{λ ∈ [a, b]} v_λ` is upper
semicontinuous at every point of the open set `U`. -/
theorem upperSemicontinuousOn_iSup_concave {v : ℝ → X → EReal} {a b a' b' : ℝ} {U : Set X}
    (hU : IsOpen U) (haa : a ≤ a') (hab' : a' < b') (hbb : b' ≤ b)
    (hconc : ∀ y ∈ U, IsConcaveFamilyAt v (Icc a b) y)
    (hne : ∀ y ∈ U, ∀ lam ∈ Icc a b, v lam y ≠ ⊤)
    (husc : ∀ lam ∈ Icc a b, ∀ x ∈ U, UpperSemicontinuousAt (v lam) x)
    (hbdd : ∀ lam ∈ Icc a' b', ∀ x ∈ U, ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      ((-C : ℝ) : EReal) ≤ v lam y ∧ v lam y ≤ (C : EReal)) :
    ∀ x ∈ U, UpperSemicontinuousAt (fun y => ⨆ lam ∈ Icc a b, v lam y) x := by
  intro x hx
  exact upperSemicontinuousAt_iSup_concave haa hab' hbb
    (eventually_of_mem (hU.mem_nhds hx) hconc) (eventually_of_mem (hU.mem_nhds hx) hne)
    (fun lam hl => husc lam hl x hx) (fun lam hl => hbdd lam hl x hx)

/-- **WN21 Lemma 3.2** (`tok-wn:legendre-usc`): a concave family `v_λ`, `λ ∈ [a, b]`, of upper
semicontinuous functions with values in `[-∞, ∞)`, such that `v_λ` is locally bounded for
`λ ∈ [a', b']`, `a ≤ a' < b' ≤ b`, has an upper semicontinuous supremum
`sup_{λ ∈ [a, b]} v_λ`. -/
theorem upperSemicontinuous_iSup_concave {v : ℝ → X → EReal} {a b a' b' : ℝ}
    (haa : a ≤ a') (hab' : a' < b') (hbb : b' ≤ b)
    (hconc : ∀ y, IsConcaveFamilyAt v (Icc a b) y)
    (hne : ∀ y, ∀ lam ∈ Icc a b, v lam y ≠ ⊤)
    (husc : ∀ lam ∈ Icc a b, UpperSemicontinuous (v lam))
    (hbdd : ∀ lam ∈ Icc a' b', ∀ x, ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      ((-C : ℝ) : EReal) ≤ v lam y ∧ v lam y ≤ (C : EReal)) :
    UpperSemicontinuous (fun y => ⨆ lam ∈ Icc a b, v lam y) := by
  intro x
  exact upperSemicontinuousOn_iSup_concave isOpen_univ haa hab' hbb (fun y _ => hconc y)
    (fun y _ => hne y) (fun lam hl x _ => husc lam hl x) (fun lam hl x _ => hbdd lam hl x)
    x (mem_univ x)

end SGPT.Okounkov.TranscendentalWN
