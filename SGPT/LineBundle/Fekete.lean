import Mathlib.Data.EReal.Inv
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Fekete's lemma for eventually finite superadditive sequences in `[-∞, ∞)`

Source: the uses of Fekete's lemma in `def:testcurve:L1134` (the jumping numbers of a
filtration: `τ(𝓕) = lim_k τ_k(𝓕)/k = sup_k τ_k(𝓕)/k`) and `ex:RWN`.

A sequence `a : ℕ → EReal` which is superadditive on positive indices, bounded above by a
linear function and finite (bounded below by a linear function) from some index on satisfies
`a k / k → sup_{k > 0} a k / k`. The values `a k = -∞` are allowed for finitely many `k`; this
is the situation of the section ring of a big line bundle, whose low degrees may have no
sections.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.LineBundle

open Filter Set
open scoped Topology

/-- Iterating superadditivity: `a (q m + r) ≥ q a(m) + a(r)` when `a m = α` is finite. -/
theorem EReal.superadditive_iterate {a : ℕ → EReal}
    (hsuper : ∀ m k : ℕ, 0 < m → 0 < k → a m + a k ≤ a (m + k)) {m : ℕ} (hm : 0 < m)
    {α : ℝ} (hα : a m = α) {r : ℕ} (hr : 0 < r) :
    ∀ q : ℕ, (((q : ℝ) * α : ℝ) : EReal) + a r ≤ a (q * m + r) := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : a m + a (q * m + r) ≤ a (m + (q * m + r)) := hsuper m _ hm (by positivity)
    have h2 : m + (q * m + r) = (q + 1) * m + r := by ring
    rw [h2] at h1
    calc (((((q + 1 : ℕ) : ℝ) * α : ℝ)) : EReal) + a r
        = (α : EReal) + ((((q : ℝ) * α : ℝ) : EReal) + a r) := by
          rw [← add_assoc, ← EReal.coe_add]
          congr 2
          push_cast
          ring
      _ ≤ a m + a (q * m + r) := by rw [hα]; exact add_le_add le_rfl ih
      _ ≤ a ((q + 1) * m + r) := h1

/-- **Fekete's lemma** for superadditive sequences with values in `[-∞, ∞)` which are finite
from some index on: if `a (m + k) ≥ a m + a k` for `m, k > 0`, `a k ≤ C k` for `k > 0`,
`a k ≥ -C k` whenever `a k ≠ -∞`, and `a k ≠ -∞` for `k ≥ k₀`, then
`a k / k → sup_{k > 0} a k / k`. -/
theorem EReal.tendsto_div_iSup_of_superadditive (a : ℕ → EReal) (C : ℝ) (k₀ : ℕ)
    (hsuper : ∀ m k : ℕ, 0 < m → 0 < k → a m + a k ≤ a (m + k))
    (hup : ∀ k : ℕ, 0 < k → a k ≤ ((C * k : ℝ) : EReal))
    (hlow : ∀ k : ℕ, 0 < k → a k ≠ ⊥ → (((-C) * k : ℝ) : EReal) ≤ a k)
    (hfin : ∀ k : ℕ, k₀ ≤ k → a k ≠ ⊥) (hk₀ : 0 < k₀) :
    Tendsto (fun k : ℕ => a k / ((k : ℝ) : EReal)) atTop
      (𝓝 (⨆ (k : ℕ) (_ : 0 < k), a k / ((k : ℝ) : EReal))) := by
  set s : EReal := ⨆ (k : ℕ) (_ : 0 < k), a k / ((k : ℝ) : EReal) with hs
  have hkpos : ∀ k : ℕ, 0 < k → (0 : EReal) < ((k : ℝ) : EReal) := fun k hk =>
    EReal.coe_pos.mpr (by exact_mod_cast hk)
  have hkne : ∀ k : ℕ, ((k : ℝ) : EReal) ≠ ⊤ := fun k => EReal.coe_ne_top _
  rw [tendsto_order]
  constructor
  · intro x hx
    -- choose an index `m` with `a m / m > x`
    obtain ⟨m, hm'⟩ := lt_iSup_iff.mp hx
    obtain ⟨hm, hxm⟩ := lt_iSup_iff.mp hm'
    have hm_bot : a m ≠ ⊥ := by
      intro h
      rw [h, EReal.bot_div_of_pos_ne_top (hkpos m hm) (hkne m)] at hxm
      exact not_lt_bot hxm
    have hm_top : a m ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hup m hm)
    set α : ℝ := (a m).toReal
    have hα : a m = α := (EReal.coe_toReal hm_top hm_bot).symm
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hxm' : x < ((α / m : ℝ) : EReal) := by rw [EReal.coe_div, ← hα]; exact hxm
    obtain ⟨x', hxx', hx'm⟩ := EReal.lt_iff_exists_real_btwn.mp hxm'
    have hx'm : x' < α / m := EReal.coe_lt_coe_iff.mp hx'm
    -- the shifted constant `β = α + C m ≥ 0`
    set β : ℝ := α + C * m
    have hβ : 0 ≤ β := by
      have h := hlow m hm hm_bot
      rw [hα] at h
      have h' : -C * m ≤ α := EReal.coe_le_coe_iff.mp h
      simp only [β]
      linarith
    have hlim : Tendsto (fun j : ℕ => α / m - β * (k₀ + m) / m / (j : ℝ)) atTop
        (𝓝 (α / m - 0)) :=
      tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [sub_zero] at hlim
    filter_upwards [hlim.eventually (lt_mem_nhds hx'm), eventually_ge_atTop (k₀ + 1)]
      with j hj hjk
    refine lt_of_lt_of_le hxx' (le_trans (EReal.coe_le_coe_iff.mpr hj.le) ?_)
    -- decompose `j = q m + r` with `k₀ ≤ r < k₀ + m`
    set q : ℕ := (j - k₀) / m
    set r : ℕ := k₀ + (j - k₀) % m
    have hjr : q * m + r = j := by
      have h1 := Nat.div_add_mod (j - k₀) m
      have h2 : q * m = m * ((j - k₀) / m) := mul_comm _ _
      simp only [r]
      omega
    have hr0 : 0 < r := by simp only [r]; omega
    have hrk : r ≤ k₀ + m := by
      have := Nat.mod_lt (j - k₀) hm
      simp only [r]
      omega
    have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hit := EReal.superadditive_iterate hsuper hm hα hr0 q
    rw [hjr] at hit
    have hr_low : (((-C) * r : ℝ) : EReal) ≤ a r := hlow r hr0 (hfin r (by simp only [r]; omega))
    have hsum : ((((q : ℝ) * α + (-C) * r : ℝ)) : EReal) ≤ a j := by
      rw [EReal.coe_add]
      exact le_trans (add_le_add le_rfl hr_low) hit
    have hdiv := EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hjpos.le) hsum
    rw [← EReal.coe_div] at hdiv
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hdiv
    -- real arithmetic
    have hqm : (q : ℝ) * m = j - r := by
      have : ((q * m + r : ℕ) : ℝ) = j := by exact_mod_cast hjr
      push_cast at this
      linarith
    have hrR : (r : ℝ) ≤ k₀ + m := by exact_mod_cast hrk
    have hkey : ((q : ℝ) * α + (-C) * r) / j = α / m - β * r / m / j := by
      have hq : (q : ℝ) = (j - r) / m := by field_simp; linarith
      rw [hq]
      simp only [β]
      field_simp
      ring
    rw [hkey]
    have : β * r / m / j ≤ β * (k₀ + m) / m / j := by
      apply div_le_div_of_nonneg_right _ hjpos.le
      apply div_le_div_of_nonneg_right _ hmR.le
      exact mul_le_mul_of_nonneg_left hrR hβ
    linarith
  · intro x hx
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact lt_of_le_of_lt (le_iSup₂ (f := fun k (_ : 0 < k) => a k / ((k : ℝ) : EReal)) k hk) hx

/-- The supremum in Fekete's lemma is at most the slope `C` of the linear upper bound. -/
theorem EReal.iSup_div_le_of_le (a : ℕ → EReal) (C : ℝ)
    (hup : ∀ k : ℕ, 0 < k → a k ≤ ((C * k : ℝ) : EReal)) :
    (⨆ (k : ℕ) (_ : 0 < k), a k / ((k : ℝ) : EReal)) ≤ (C : EReal) := by
  refine iSup₂_le fun k hk => ?_
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc a k / ((k : ℝ) : EReal) ≤ ((C * k : ℝ) : EReal) / ((k : ℝ) : EReal) :=
        EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr hkR.le) (hup k hk)
    _ = (C : EReal) := by rw [← EReal.coe_div, mul_div_assoc, div_self hkR.ne', mul_one]

/-- The supremum in Fekete's lemma is finite from below once one term is finite. -/
theorem EReal.iSup_div_ne_bot (a : ℕ → EReal) {k : ℕ} (hk : 0 < k) (hak : a k ≠ ⊥) :
    (⨆ (k : ℕ) (_ : 0 < k), a k / ((k : ℝ) : EReal)) ≠ ⊥ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hne : a k / ((k : ℝ) : EReal) ≠ ⊥ := by
    by_cases htop : a k = ⊤
    · rw [htop, EReal.top_div_of_pos_ne_top (EReal.coe_pos.mpr hkR) (EReal.coe_ne_top _)]
      exact top_ne_bot
    · rw [← EReal.coe_toReal htop hak, ← EReal.coe_div]
      exact EReal.coe_ne_bot _
  intro h
  apply hne
  have hle := le_iSup₂ (f := fun k (_ : 0 < k) => a k / ((k : ℝ) : EReal)) k hk
  rw [h] at hle
  exact le_bot_iff.mp hle

end SGPT.LineBundle
