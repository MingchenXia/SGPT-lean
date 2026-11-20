import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.Interval.Set.Basic

/-!
# A limit of normalized infima

Source: `chapter_NApotential.tex`, `prop:psiandPhi` (the limit
`σ(v)(Ψ) = lim_k k⁻¹ σ(v)(𝓘(kΨ))`). Blueprint `claude-na-gaga.tex`, node
`claude-na-gaga:limit`.

Let `a_k(τ) ∈ [0, ∞]` (`τ < M ≤ 0`) be increasing in `τ`, with `a_k(τ)/k ≤ p(τ)` and
`a_k(τ)/k → p(τ)` for every `τ`, and let `b_k` satisfy, for `k ≥ 1`,

`b_k/k ≤ a_k(τ)/k - τ` for every `τ`,   and   `b_k/k + 1/k ≥ inf_τ (a_k(τ)/k - τ)`.

Then `b_k/k → inf_{τ < M} (p(τ) - τ)` (`tendsto_div_of_bounds`). The exchange of the limit with
the infimum over the non-compact range of `τ` uses the monotonicity in `τ` (a finite grid of mesh
`h` loses at most `h`) and the term `-τ` (which is large for `τ ≪ 0`).
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.NAGaga

open Set Filter
open scoped Topology ENNReal

/-- **The limit of the normalized infima.** -/
theorem tendsto_div_of_bounds {M : ℝ} (hM : M ≤ 0) (a : ℕ → Iio M → ℝ≥0∞)
    (p : Iio M → ℝ≥0∞) (b : ℕ → ℝ≥0∞)
    (hmono : ∀ k : ℕ, 0 < k → ∀ τ τ' : Iio M, τ ≤ τ' → a k τ ≤ a k τ')
    (hlim : ∀ τ, Tendsto (fun k : ℕ => a k τ / k) atTop (𝓝 (p τ)))
    (hle : ∀ k : ℕ, 0 < k → ∀ τ, a k τ / k ≤ p τ)
    (hup : ∀ k : ℕ, 0 < k → ∀ τ : Iio M, b k / k ≤ a k τ / k + ENNReal.ofReal (-τ.1))
    (hlow : ∀ k : ℕ, 0 < k → ∀ c : ℝ≥0∞,
      (∀ τ : Iio M, c ≤ a k τ / k + ENNReal.ofReal (-τ.1)) → c ≤ b k / k + 1 / k) :
    Tendsto (fun k : ℕ => b k / k) atTop
      (𝓝 (⨅ τ : Iio M, p τ + ENNReal.ofReal (-τ.1))) := by
  set L := ⨅ τ : Iio M, p τ + ENNReal.ofReal (-τ.1) with hL
  have hbL : ∀ k : ℕ, 0 < k → b k / k ≤ L := fun k hk =>
    le_iInf fun τ => (hup k hk τ).trans (add_le_add (hle k hk τ) le_rfl)
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · -- lower bound
    obtain ⟨c₁, hcc₁, hc₁L⟩ := exists_between hc
    obtain ⟨c₂, hc₁c₂, hc₂L⟩ := exists_between hc₁L
    have hc₂top : c₂ ≠ ⊤ := ne_top_of_lt hc₂L
    have hc₁top : c₁ ≠ ⊤ := ne_top_of_lt hc₁c₂
    have hctop : c ≠ ⊤ := ne_top_of_lt hcc₁
    set h : ℝ := c₂.toReal - c₁.toReal with hh
    have hlt : c₁.toReal < c₂.toReal := (ENNReal.toReal_lt_toReal hc₁top hc₂top).mpr hc₁c₂
    have hhpos : 0 < h := by rw [hh]; linarith
    have hc₂eq : c₂ = c₁ + ENNReal.ofReal h := by
      rw [← ENNReal.ofReal_toReal hc₁top, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hhpos.le,
        hh, add_sub_cancel, ENNReal.ofReal_toReal hc₂top]
    set R : ℝ := c₂.toReal + 1 with hR
    set N : ℕ := ⌈R / h⌉₊ + 1 with hN
    have hNh : R ≤ N * h := by
      have h1 : R / h ≤ ⌈R / h⌉₊ := Nat.le_ceil _
      have h2 : (⌈R / h⌉₊ : ℝ) ≤ N := by rw [hN]; push_cast; linarith
      have := (div_le_iff₀ hhpos).mp (h1.trans h2)
      linarith
    -- the grid `τ_j = M - (j+1) h`, `j < N`
    let τg : Fin N → Iio M := fun j => ⟨M - ((j : ℝ) + 1) * h, by
      change M - ((j : ℝ) + 1) * h < M
      have : 0 < ((j : ℝ) + 1) * h := mul_pos (by positivity) hhpos
      linarith⟩
    have hgrid : ∀ j : Fin N, ∀ᶠ k : ℕ in atTop,
        c₂ < a k (τg j) / k + ENNReal.ofReal (-(τg j).1) := by
      intro j
      have hT := (hlim (τg j)).add (tendsto_const_nhds (x := ENNReal.ofReal (-(τg j).1)))
      exact hT.eventually (lt_mem_nhds (lt_of_lt_of_le hc₂L (iInf_le _ (τg j))))
    have hall : ∀ᶠ k : ℕ in atTop, ∀ j : Fin N,
        c₂ < a k (τg j) / k + ENNReal.ofReal (-(τg j).1) :=
      Filter.eventually_all.2 hgrid
    have hsmall : ∀ᶠ k : ℕ in atTop, 1 / (k : ℝ≥0∞) < c₁ - c := by
      have h0 : Tendsto (fun k : ℕ => 1 / (k : ℝ≥0∞)) atTop (𝓝 0) := by
        simpa only [one_div] using ENNReal.tendsto_inv_nat_nhds_zero
      exact h0.eventually (gt_mem_nhds (tsub_pos_of_lt hcc₁))
    filter_upwards [hall, hsmall, eventually_gt_atTop 0] with k hk hk1 hk0
    have hgood : ∀ τ : Iio M, c₁ ≤ a k τ / k + ENNReal.ofReal (-τ.1) := by
      intro τ
      by_cases hτ : τ.1 ≤ M - N * h
      · -- far away: the term `-τ` dominates
        have h1 : R ≤ -τ.1 := by linarith
        have h2 : c₁ ≤ ENNReal.ofReal (-τ.1) := by
          refine le_trans hc₁c₂.le ?_
          rw [← ENNReal.ofReal_toReal hc₂top]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        exact h2.trans le_add_self
      · -- inside: compare with the grid point below `τ`
        rw [not_le] at hτ
        have hτM : τ.1 < M := τ.2
        set x : ℝ := (M - τ.1) / h with hx
        have hx0 : 0 < x := div_pos (by linarith) hhpos
        set m := ⌈x⌉₊ with hm
        have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
          rw [hm]; exact (Nat.ceil_pos.mpr hx0).ne')
        have hmN : m ≤ N := by
          rw [hm, Nat.ceil_le, hx, div_le_iff₀ hhpos]; linarith
        have hjN : m - 1 < N := by omega
        set j : Fin N := ⟨m - 1, hjN⟩ with hj
        have hjcast : ((j : ℕ) : ℝ) + 1 = m := by
          rw [hj]; push_cast [Nat.cast_sub hm1]; ring
        have hle1 : (τg j).1 ≤ τ.1 := by
          change M - (((j : ℕ) : ℝ) + 1) * h ≤ τ.1
          rw [hjcast]
          have : x ≤ m := Nat.le_ceil x
          rw [hx, div_le_iff₀ hhpos] at this
          linarith
        have hle2 : -(τg j).1 ≤ -τ.1 + h := by
          change -(M - (((j : ℕ) : ℝ) + 1) * h) ≤ -τ.1 + h
          rw [hjcast]
          have : (m : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
          rw [hx] at this
          have h3 : ((m : ℝ) - 1) * h < M - τ.1 := by
            have := (lt_div_iff₀ hhpos).mp (show (m : ℝ) - 1 < (M - τ.1) / h by linarith)
            linarith
          nlinarith
        have hamono : a k (τg j) ≤ a k τ := hmono k hk0 _ _ hle1
        have hstep : c₁ + ENNReal.ofReal h < a k τ / k + ENNReal.ofReal (-τ.1) + ENNReal.ofReal h := by
          rw [← hc₂eq]
          calc c₂ < a k (τg j) / k + ENNReal.ofReal (-(τg j).1) := hk j
            _ ≤ a k τ / k + (ENNReal.ofReal (-τ.1) + ENNReal.ofReal h) := by
                gcongr
                exact (ENNReal.ofReal_le_ofReal hle2).trans ENNReal.ofReal_add_le
            _ = a k τ / k + ENNReal.ofReal (-τ.1) + ENNReal.ofReal h := by rw [add_assoc]
        exact ((ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).mp hstep).le
    have hb := hlow k hk0 c₁ hgood
    by_contra hcon
    rw [not_lt] at hcon
    have : b k / k + 1 / k < c₁ := by
      calc b k / k + 1 / k ≤ c + 1 / k := add_le_add hcon le_rfl
        _ < c + (c₁ - c) := ENNReal.add_lt_add_left hctop hk1
        _ = c₁ := add_tsub_cancel_of_le hcc₁.le
    exact absurd hb (not_le.mpr this)
  · -- upper bound
    filter_upwards [eventually_gt_atTop 0] with k hk
    exact lt_of_le_of_lt (hbL k hk) hc

end SGPT.NAPotential.NAGaga
