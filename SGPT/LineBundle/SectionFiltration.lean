import SGPT.LineBundle.BigLineBundle
import SGPT.LineBundle.Fekete
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Filtrations of the section ring

Source `def:testcurve:L1134` (chapter *Test curves*): filtrations of the section ring
`R(X, L) = ⊕_k H⁰(X, L^k)` of a big line bundle, their jumping numbers
`τ_k(𝓕) = sup {λ ∈ ℝ : 𝓕^λ_k ≠ 0}`, and the limit
`τ(𝓕) = lim_k τ_k(𝓕)/k = sup_k τ_k(𝓕)/k` given by Fekete's lemma, together with the remark
following the definition (`τ(𝓕) ≤ C`, hence finite). Also the first claim of `ex:RWN`:
`𝓕^{kτ}_k ≠ 0` when `kτ ≤ τ_k(𝓕)`.

## Formal setting

`X` is a scheme over `ℂ` (structure morphism `f`), `L : X.Modules` a line bundle with atlas
`a`, `H⁰(X, L^k) = SectionSpace f L k` and the section product is `SectionSpace.mul f a`
(`SGPT.LineBundle.SectionRing`). A graded linear subspace `𝓕^λ = ⊕_k 𝓕^λ_k` of `R(X, L)` is
recorded by its graded pieces `𝓕^λ_k ⊆ H⁰(X, L^k)`; intersections of graded subspaces are
taken degreewise. The definition does not use bigness; the bigness of `L` enters the
existence of the limit `τ(𝓕)` (through nonzero sections in all large degrees).

## Main definitions

* `SGPT.LineBundle.SectionFiltration f a`: a filtration on `R(X, L)` (decreasing,
  left-continuous, multiplicative, linearly bounded).
* `SectionFiltration.jump 𝓕 k = τ_k(𝓕) ∈ [-∞, ∞]` and
  `SectionFiltration.slope 𝓕 = τ(𝓕) = sup_{k > 0} τ_k(𝓕)/k`.

## Main results

* `SectionFiltration.piece_ne_bot_iff`: `𝓕^λ_k ≠ 0 ↔ λ ≤ τ_k(𝓕)` (the supremum is attained,
  by left-continuity and finite dimensionality).
* `SectionFiltration.jump_add_le`: `τ_{k+k'}(𝓕) ≥ τ_k(𝓕) + τ_{k'}(𝓕)`.
* `SectionFiltration.tendsto_jump_div_slope`, `IsBig.tendsto_jump_div_slope`: Fekete's lemma
  `τ_k(𝓕)/k → τ(𝓕)`.
* `SectionFiltration.slope_le_bound`, `SectionFiltration.slope_ne_bot`: `τ(𝓕)` is finite,
  `τ(𝓕) ≤ C`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes Filter Set
open scoped Topology

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) {L : X.Modules} (a : LineBundleAtlas L)

/-- Source `def:testcurve:L1134`. A *filtration* on the section ring `R(X, L)` is a family
`(𝓕^μ)_{μ ∈ ℝ}` of graded linear subspaces `𝓕^μ = ⊕_k 𝓕^μ_k`, `𝓕^μ_k ⊆ H⁰(X, L^k)`, which is

* decreasing in `μ`;
* left-continuous: `𝓕^μ = ⋂_{μ' < μ} 𝓕^{μ'}`;
* multiplicative: `𝓕^μ_k · 𝓕^{μ'}_{k'} ⊆ 𝓕^{μ+μ'}_{k+k'}` for all `μ, μ' ∈ ℝ`, `k, k' ∈ ℕ`;
* linearly bounded: there is an integer `C > 0` with `𝓕^{Cm}_m = 0` and
  `𝓕^{-Cm}_m = H⁰(X, L^m)` for all `m ∈ ℤ_{>0}`. -/
structure SectionFiltration where
  /-- The graded piece `𝓕^μ_k ⊆ H⁰(X, L^k)`. -/
  piece : ℝ → ∀ k : ℕ, Submodule ℂ (SectionSpace f L k)
  antitone_piece : ∀ k : ℕ, Antitone fun μ : ℝ => piece μ k
  leftContinuous : ∀ (μ : ℝ) (k : ℕ), piece μ k = ⨅ (μ' : ℝ) (_ : μ' < μ), piece μ' k
  mul_mem : ∀ (μ μ' : ℝ) (k k' : ℕ) (s : SectionSpace f L k) (t : SectionSpace f L k'),
    s ∈ piece μ k → t ∈ piece μ' k' → SectionSpace.mul f a k k' s t ∈ piece (μ + μ') (k + k')
  linearlyBounded : ∃ C : ℕ, 0 < C ∧ ∀ m : ℕ, 0 < m →
    piece ((C : ℝ) * m) m = ⊥ ∧ piece (-((C : ℝ) * m)) m = ⊤

namespace SectionFiltration

variable {f a} (F : SectionFiltration f a)

/-- The jumping number `τ_k(𝓕) = sup {μ ∈ ℝ : 𝓕^μ_k ≠ 0} ∈ [-∞, ∞]` (equal to `-∞` when
`H⁰(X, L^k) = 0`). -/
def jump (k : ℕ) : EReal := ⨆ (μ : ℝ) (_ : F.piece μ k ≠ ⊥), (μ : EReal)

/-- `τ(𝓕) = sup_{k ∈ ℤ_{>0}} τ_k(𝓕)/k`; by Fekete's lemma it is also the limit of
`τ_k(𝓕)/k` (`tendsto_jump_div_slope`). -/
def slope : EReal := ⨆ (k : ℕ) (_ : 0 < k), F.jump k / ((k : ℝ) : EReal)

/-- A choice of the integer `C` of the linear boundedness condition. -/
def bound : ℕ := F.linearlyBounded.choose

theorem bound_pos : 0 < F.bound := F.linearlyBounded.choose_spec.1

theorem piece_bound_eq_bot {m : ℕ} (hm : 0 < m) : F.piece ((F.bound : ℝ) * m) m = ⊥ :=
  (F.linearlyBounded.choose_spec.2 m hm).1

theorem piece_neg_bound_eq_top {m : ℕ} (hm : 0 < m) : F.piece (-((F.bound : ℝ) * m)) m = ⊤ :=
  (F.linearlyBounded.choose_spec.2 m hm).2

theorem piece_anti {μ μ' : ℝ} (h : μ ≤ μ') (k : ℕ) : F.piece μ' k ≤ F.piece μ k :=
  F.antitone_piece k h

theorem piece_eq_bot_of_le {m : ℕ} (hm : 0 < m) {μ : ℝ} (hμ : (F.bound : ℝ) * m ≤ μ) :
    F.piece μ m = ⊥ :=
  le_bot_iff.mp ((F.piece_anti hμ m).trans (F.piece_bound_eq_bot hm).le)

theorem piece_eq_top_of_le {m : ℕ} (hm : 0 < m) {μ : ℝ} (hμ : μ ≤ -((F.bound : ℝ) * m)) :
    F.piece μ m = ⊤ :=
  top_le_iff.mp ((F.piece_neg_bound_eq_top hm).symm.le.trans (F.piece_anti hμ m))

theorem le_jump {μ : ℝ} {k : ℕ} (h : F.piece μ k ≠ ⊥) : (μ : EReal) ≤ F.jump k :=
  le_iSup₂ (f := fun (μ : ℝ) (_ : F.piece μ k ≠ ⊥) => (μ : EReal)) μ h

theorem piece_ne_bot_of_lt_jump {μ : ℝ} {k : ℕ} (h : (μ : EReal) < F.jump k) :
    F.piece μ k ≠ ⊥ := by
  obtain ⟨μ', hμ'⟩ := lt_iSup_iff.mp h
  obtain ⟨hne, hlt⟩ := lt_iSup_iff.mp hμ'
  intro hbot
  apply hne
  exact le_bot_iff.mp ((F.piece_anti (EReal.coe_lt_coe_iff.mp hlt).le k).trans hbot.le)

/-- `τ_k(𝓕) ≤ C k` in positive degree. -/
theorem jump_le_bound {k : ℕ} (hk : 0 < k) : F.jump k ≤ (((F.bound : ℝ) * k : ℝ) : EReal) := by
  refine iSup₂_le fun μ hμ => EReal.coe_le_coe_iff.mpr ?_
  by_contra h
  exact hμ (F.piece_eq_bot_of_le hk (not_le.mp h).le)

/-- `τ_k(𝓕) ≥ -C k` when `H⁰(X, L^k) ≠ 0`, `k > 0`. -/
theorem neg_bound_le_jump {k : ℕ} (hk : 0 < k) [Nontrivial (SectionSpace f L k)] :
    ((-((F.bound : ℝ) * k) : ℝ) : EReal) ≤ F.jump k := by
  apply F.le_jump
  rw [F.piece_neg_bound_eq_top hk]
  exact top_ne_bot

/-- `τ_k(𝓕) = -∞` exactly when `H⁰(X, L^k) = 0` (for `k > 0`). -/
theorem jump_eq_bot_iff {k : ℕ} (hk : 0 < k) :
    F.jump k = ⊥ ↔ ¬ Nontrivial (SectionSpace f L k) := by
  constructor
  · intro h hn
    have := F.neg_bound_le_jump hk
    rw [h, le_bot_iff] at this
    exact EReal.coe_ne_bot _ this
  · intro hn
    have : Subsingleton (SectionSpace f L k) := not_nontrivial_iff_subsingleton.mp hn
    exact le_bot_iff.mp (iSup₂_le fun μ hμ => absurd (Subsingleton.elim _ _) hμ)

/-- In positive degree with `H⁰(X, L^k) ≠ 0`, the jumping number is a real number. -/
theorem jump_eq_coe {k : ℕ} (hk : 0 < k) [Nontrivial (SectionSpace f L k)] :
    F.jump k = ((F.jump k).toReal : EReal) :=
  (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (F.jump_le_bound hk))
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (F.neg_bound_le_jump hk))).symm

/-- The supremum defining `τ_k(𝓕)` is attained: if `τ_k(𝓕) = τ` is finite, then
`𝓕^τ_k ≠ 0`. This uses left-continuity and `dim H⁰(X, L^k) < ∞`. -/
theorem piece_ne_bot_of_jump_eq {k : ℕ} [FiniteDimensional ℂ (SectionSpace f L k)] {τ : ℝ}
    (hτ : F.jump k = τ) : F.piece τ k ≠ ⊥ := by
  have hlt : ∀ μ : ℝ, μ < τ → F.piece μ k ≠ ⊥ := fun μ hμ =>
    F.piece_ne_bot_of_lt_jump (by rw [hτ]; exact EReal.coe_lt_coe_iff.mpr hμ)
  -- a degree of minimal dimension among the pieces below `τ`
  let g : ℝ → ℕ := fun μ => Module.finrank ℂ (F.piece μ k)
  have hne : (g '' Iio τ).Nonempty := ⟨g (τ - 1), τ - 1, by simp, rfl⟩
  obtain ⟨μ₀, hμ₀, hgμ₀⟩ := Nat.sInf_mem hne
  have hmin : ∀ μ : ℝ, μ < τ → g μ₀ ≤ g μ := fun μ hμ => by
    rw [hgμ₀]
    exact Nat.sInf_le ⟨μ, hμ, rfl⟩
  have hle : ∀ μ : ℝ, μ < τ → F.piece μ₀ k ≤ F.piece μ k := by
    intro μ hμ
    rcases le_total μ μ₀ with h | h
    · exact F.piece_anti h k
    · have hsub : F.piece μ k ≤ F.piece μ₀ k := F.piece_anti h k
      exact (Submodule.eq_of_le_of_finrank_le hsub (hmin μ hμ)).symm.le
  rw [F.leftContinuous τ k]
  intro hbot
  apply hlt μ₀ hμ₀
  rw [eq_bot_iff, ← hbot]
  exact le_iInf₂ fun μ hμ => hle μ hμ

/-- `𝓕^μ_k ≠ 0 ↔ μ ≤ τ_k(𝓕)`. In particular (source `ex:RWN`) `𝓕^{kτ}_k ≠ 0` whenever
`kτ ≤ τ_k(𝓕)`. -/
theorem piece_ne_bot_iff {k : ℕ} [FiniteDimensional ℂ (SectionSpace f L k)] (μ : ℝ) :
    F.piece μ k ≠ ⊥ ↔ (μ : EReal) ≤ F.jump k := by
  refine ⟨F.le_jump, fun h => ?_⟩
  rcases h.lt_or_eq with h | h
  · exact F.piece_ne_bot_of_lt_jump h
  · exact F.piece_ne_bot_of_jump_eq h.symm

/-- Superadditivity of the jumping numbers: `τ_k(𝓕) + τ_{k'}(𝓕) ≤ τ_{k+k'}(𝓕)` (products of
nonzero sections are nonzero on an integral scheme). -/
theorem jump_add_le [IsIntegral X] (k k' : ℕ) : F.jump k + F.jump k' ≤ F.jump (k + k') := by
  apply EReal.add_le_of_forall_lt
  intro x hx y hy
  obtain ⟨μ, hμ⟩ := lt_iSup_iff.mp hx
  obtain ⟨hμne, hxμ⟩ := lt_iSup_iff.mp hμ
  obtain ⟨μ', hμ'⟩ := lt_iSup_iff.mp hy
  obtain ⟨hμ'ne, hyμ'⟩ := lt_iSup_iff.mp hμ'
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμne
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ'ne
  have hst := F.mul_mem μ μ' k k' s t hs ht
  have hne : F.piece (μ + μ') (k + k') ≠ ⊥ := fun hbot => by
    rw [hbot, Submodule.mem_bot] at hst
    exact SectionSpace.mul_ne_zero f a hs0 ht0 hst
  calc x + y ≤ (μ : EReal) + (μ' : EReal) := add_le_add hxμ.le hyμ'.le
    _ = ((μ + μ' : ℝ) : EReal) := (EReal.coe_add μ μ').symm
    _ ≤ F.jump (k + k') := F.le_jump hne

/-- The remark after `def:testcurve:L1134`: `τ(𝓕) ≤ C`. -/
theorem slope_le_bound : F.slope ≤ ((F.bound : ℝ) : EReal) :=
  EReal.iSup_div_le_of_le F.jump (F.bound : ℝ) fun _ hk => F.jump_le_bound hk

/-- If `H⁰(X, L^k) ≠ 0` for some `k > 0`, then `τ(𝓕) > -∞`. -/
theorem slope_ne_bot {k : ℕ} (hk : 0 < k) [Nontrivial (SectionSpace f L k)] : F.slope ≠ ⊥ :=
  EReal.iSup_div_ne_bot F.jump hk
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (F.neg_bound_le_jump hk))

theorem slope_ne_top : F.slope ≠ ⊤ :=
  ne_top_of_le_ne_top (EReal.coe_ne_top _) F.slope_le_bound

/-- Source `def:testcurve:L1134` (Fekete's lemma): if `L` has nonzero sections in all large
degrees (e.g. `L` big, `IsBig.tendsto_jump_div_slope`), then
`τ(𝓕) = lim_{k → ∞} τ_k(𝓕)/k = sup_{k > 0} τ_k(𝓕)/k`. -/
theorem tendsto_jump_div_slope [IsIntegral X]
    (hne : ∀ᶠ k : ℕ in atTop, Nontrivial (SectionSpace f L k)) :
    Tendsto (fun k : ℕ => F.jump k / ((k : ℝ) : EReal)) atTop (𝓝 F.slope) := by
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp hne
  refine EReal.tendsto_div_iSup_of_superadditive F.jump (F.bound : ℝ) (k₁ + 1)
    (fun m k _ _ => F.jump_add_le m k) (fun k hk => F.jump_le_bound hk) ?_ ?_ (by omega)
  · intro k hk hbot
    have : Nontrivial (SectionSpace f L k) := by
      by_contra hn
      exact hbot ((F.jump_eq_bot_iff hk).mpr hn)
    have h := F.neg_bound_le_jump hk
    rwa [← neg_mul] at h
  · intro k hk hbot
    have := hk₁ k (by omega)
    exact ((F.jump_eq_bot_iff (by omega)).mp hbot) this

end SectionFiltration

variable {f a}

/-- For a big line bundle `L`, the limit `τ(𝓕) = lim_k τ_k(𝓕)/k = sup_k τ_k(𝓕)/k` exists
and is a real number `≤ C` (source `def:testcurve:L1134` and the remark following it). -/
theorem IsBig.tendsto_jump_div_slope [IsIntegral X] {n : ℕ} (hL : IsBig f L n)
    (F : SectionFiltration f a) :
    Tendsto (fun k : ℕ => F.jump k / ((k : ℝ) : EReal)) atTop (𝓝 F.slope) ∧
      F.slope ≠ ⊥ ∧ F.slope ≤ ((F.bound : ℝ) : EReal) := by
  refine ⟨F.tendsto_jump_div_slope hL.eventually_nontrivial, ?_, F.slope_le_bound⟩
  obtain ⟨k, hk⟩ := (hL.eventually_nontrivial.and (eventually_ge_atTop 1)).exists
  have := hk.1
  exact F.slope_ne_bot (k := k) (by omega)

end SGPT.LineBundle
