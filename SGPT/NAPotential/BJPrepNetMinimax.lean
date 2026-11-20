import Mathlib.Analysis.Convex.Slope
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Directed
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Exchanging an infimum over a monotone net with a Legendre-type supremum

The convex-analysis step of `prop:anpreinf` (`chapter_NApotential.tex`): for a decreasing net
`Γ_i ↓ Γ` of non-Archimedean metrics and a divisorial valuation `t ord_E`,

`inf_i sup_{τ < Γ_{i,max}} (τ - t ν(Γ_{i,τ}, E)) ≤ sup_{τ < Γ_max} (τ - t ν(Γ_τ, E))`

as soon as `ν(Γ_τ, E) = sup_i ν(Γ_{i,τ}, E)` for `τ < Γ_max` (`thm:Lelongcont`) and
`Γ_max = inf_i Γ_{i,max}`.  The book quotes `prop:Legendretranssup`; we give a direct argument:
the slice Lelong numbers are nonnegative and increase in `τ`, so a finite grid of mesh `δ/2` on
`[min(R, Γ_max - δ/4), Γ_max - δ/4]` controls the whole supremum, and finitely many members of
a directed net can be dominated by one.

## Main result

* `exists_index_legendre_le`.
-/

set_option autoImplicit false

namespace SGPT.NAPotential.BJPrep

open Set

/-- **Monotone-net Legendre exchange.**  Let `(m_i)` be antitone with infimum `m₀`, let
`f_i ≥ 0` be increasing on `(-∞, m_i)` and increasing in `i` on `(-∞, m₀)`, and let `F` be their
supremum on `(-∞, m₀)` (in the sense of `hlim`).  If `τ - t F(τ) ≤ R` for `τ < m₀`, then for every
`δ > 0` some member satisfies `τ - t f_i(τ) ≤ R + δ` for all `τ < m_i`. -/
theorem exists_index_legendre_le {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {m : I → ℝ} {m₀ : ℝ} {f : I → ℝ → ℝ} {F : ℝ → ℝ} {t R : ℝ} (ht : 0 < t)
    (hm₀ : ∀ i, m₀ ≤ m i) (hmanti : ∀ i j, i ≤ j → m j ≤ m i)
    (hmlim : ∀ ε > 0, ∃ i, m i ≤ m₀ + ε)
    (hmono : ∀ i, MonotoneOn (f i) (Iio (m i)))
    (hnonneg : ∀ i τ, 0 ≤ f i τ)
    (hfanti : ∀ i j, i ≤ j → ∀ τ < m₀, f i τ ≤ f j τ)
    (hlim : ∀ τ < m₀, ∀ ε > 0, ∃ i, F τ ≤ f i τ + ε)
    (hR : ∀ τ < m₀, τ - t * F τ ≤ R) {δ : ℝ} (hδ : 0 < δ) :
    ∃ i, ∀ τ < m i, τ - t * f i τ ≤ R + δ := by
  classical
  set h : ℝ := δ / 2 with hh_def
  have hh : 0 < h := by rw [hh_def]; linarith
  set B : ℝ := m₀ - h / 2 with hB_def
  have hBm : B < m₀ := by rw [hB_def]; linarith
  set A : ℝ := min R B with hA_def
  have hAB : A ≤ B := min_le_right _ _
  have hAR : A ≤ R := min_le_left _ _
  let g : ℕ → ℝ := fun k => min (A + k * h) B
  have hgB : ∀ k, g k ≤ B := fun k => min_le_right _ _
  have hgm : ∀ k, g k < m₀ := fun k => (hgB k).trans_lt hBm
  set N : ℕ := ⌈(B - A) / h⌉₊ with hN_def
  -- one member per grid point
  have hpt : ∀ k : ℕ, ∃ i, g k - t * f i (g k) ≤ R + h := by
    intro k
    obtain ⟨i, hi⟩ := hlim (g k) (hgm k) (h / t) (div_pos hh ht)
    refine ⟨i, ?_⟩
    have h1 := hR (g k) (hgm k)
    have h2 : t * F (g k) ≤ t * f i (g k) + h := by
      have := mul_le_mul_of_nonneg_left hi ht.le
      rwa [mul_add, mul_div_cancel₀ h ht.ne'] at this
    linarith
  choose ik hik using hpt
  obtain ⟨im, him⟩ := hmlim (h / 2) (by linarith)
  obtain ⟨i₁, hi₁⟩ := Finset.exists_le (insert im ((Finset.range (N + 1)).image ik))
  have him₁ : im ≤ i₁ := hi₁ im (Finset.mem_insert_self _ _)
  have hik₁ : ∀ k, k ≤ N → ik k ≤ i₁ := fun k hk =>
    hi₁ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr
      (Nat.lt_succ_of_le hk), rfl⟩))
  have hm₁ : m i₁ ≤ m₀ + h / 2 := (hmanti im i₁ him₁).trans him
  refine ⟨i₁, fun τ hτ => ?_⟩
  by_cases hτA : τ < A
  · have : τ - t * f i₁ τ ≤ τ := by
      have := mul_nonneg ht.le (hnonneg i₁ τ); linarith
    linarith
  push Not at hτA
  -- the grid point below `τ`
  set q : ℕ := ⌊(τ - A) / h⌋₊ with hq_def
  have hq_le : (q : ℝ) * h ≤ τ - A := by
    have h1 : (q : ℝ) ≤ (τ - A) / h := Nat.floor_le (div_nonneg (sub_nonneg.mpr hτA) hh.le)
    calc (q : ℝ) * h ≤ (τ - A) / h * h := mul_le_mul_of_nonneg_right h1 hh.le
      _ = τ - A := div_mul_cancel₀ _ hh.ne'
  have hq_lt : τ - A < ((q : ℝ) + 1) * h := by
    have h1 : (τ - A) / h < (q : ℝ) + 1 := Nat.lt_floor_add_one _
    calc τ - A = (τ - A) / h * h := (div_mul_cancel₀ _ hh.ne').symm
      _ < ((q : ℝ) + 1) * h := mul_lt_mul_of_pos_right h1 hh
  set k₀ : ℕ := min q N with hk₀_def
  have hk₀N : k₀ ≤ N := min_le_right _ _
  have hk₀q : k₀ ≤ q := min_le_left _ _
  have hgτ : g k₀ ≤ τ := by
    have : A + (k₀ : ℝ) * h ≤ τ := by
      have : (k₀ : ℝ) * h ≤ (q : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk₀q) hh.le
      linarith
    exact (min_le_left _ _).trans this
  have hτB : τ - B < h := by
    have : τ < m₀ + h / 2 := hτ.trans_le hm₁
    rw [hB_def]; linarith
  have hgap : τ - g k₀ ≤ h := by
    rcases min_cases (A + (k₀ : ℝ) * h) B with ⟨hmin, hle⟩ | ⟨hmin, _⟩
    · change τ - min (A + (k₀ : ℝ) * h) B ≤ h
      rw [hmin]
      rcases eq_or_lt_of_le hk₀q with hkq | hkq
      · rw [hkq]; nlinarith
      · -- `k₀ = N < q`, so `A + N h ≥ B ≥ A + k₀ h`, i.e. the grid point is `B`
        have hk₀ : k₀ = N := by
          rcases le_total q N with hqN | hqN
          · have : k₀ = q := by rw [hk₀_def]; exact min_eq_left hqN
            omega
          · rw [hk₀_def]; exact min_eq_right hqN
        have hNB : B ≤ A + (N : ℝ) * h := by
          have h1 : (B - A) / h ≤ (N : ℝ) := Nat.le_ceil _
          have h2 : B - A ≤ (N : ℝ) * h := by
            calc B - A = (B - A) / h * h := (div_mul_cancel₀ _ hh.ne').symm
              _ ≤ (N : ℝ) * h := mul_le_mul_of_nonneg_right h1 hh.le
          linarith
        rw [hk₀] at hle ⊢
        have : A + (N : ℝ) * h = B := le_antisymm hle hNB
        rw [this]; linarith
    · change τ - min (A + (k₀ : ℝ) * h) B ≤ h
      rw [hmin]; linarith
  -- compare with the grid point
  have hgk : g k₀ - t * f i₁ (g k₀) ≤ R + h := by
    have h1 := hik k₀
    have h2 : f (ik k₀) (g k₀) ≤ f i₁ (g k₀) := hfanti _ _ (hik₁ k₀ hk₀N) _ (hgm k₀)
    nlinarith
  have hmon : f i₁ (g k₀) ≤ f i₁ τ :=
    hmono i₁ (show g k₀ ∈ Iio (m i₁) from (hgm k₀).trans_le (hm₀ i₁)) hτ hgτ
  have : t * f i₁ (g k₀) ≤ t * f i₁ τ := mul_le_mul_of_nonneg_left hmon ht.le
  have hδh : R + δ = R + h + h := by rw [hh_def]; ring
  linarith

end SGPT.NAPotential.BJPrep
