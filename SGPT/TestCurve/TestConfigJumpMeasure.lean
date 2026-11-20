import SGPT.LineBundle.SectionFiltration
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Successive minima and jumping measures of a filtration

Infrastructure for `rmk:NApotential:L862` (chapter *Non-Archimedean pluripotential theory*):
*"When `{θ}` is a Hodge class and `Γ` is induced by a test configuration as in `ex:RWN` and
`rmk:PhongSturm`, our Duistermaat–Heckman measure coincides with the more traditional definition
of [BHJ17, Section 3.2]."*

The Duistermaat–Heckman measure of an ample test configuration `(𝓧, 𝓛)` [BHJ17, §3.2] is the
weak limit of the rescaled weight measures `(1/k)_* μ_{H⁰(𝓧₀, k𝓛₀)}`; by [BHJ17, Lemma 2.? (L201),
Prop. 5.? (DHlimit)] the weights of `H⁰(𝓧₀, k𝓛₀)` are, with multiplicities, the successive
minima `λ^{(k)}_1 ≥ … ≥ λ^{(k)}_{N_k}` of the induced filtration on `H⁰(X, L^k)`,
`λ_j = max {λ : dim 𝓕^λ_k ≥ j}`. This file defines these successive minima for a filtration of
`R(X, L)` in the sense of `def:testcurve:L1134` and the jumping measures
`ν_k = ∑_j δ_{λ^{(k)}_j / k}`, and proves the tail formula
`ν_k [τ, ∞) = dim 𝓕^{kτ}_k`.

## Main definitions

* `SectionFiltration.pieceDim F μ k = dim 𝓕^μ_k`.
* `SectionFiltration.succMin F k j`: the `(j+1)`-st successive minimum
  `λ^{(k)}_{j+1} = sup {μ : dim 𝓕^μ_k > j}`.
* `SectionFiltration.jumpMeasure F k = ∑_{j < N_k} δ_{λ^{(k)}_{j+1}/k}` (unnormalized), and
  `SectionFiltration.bhjWeightMeasure F k = N_k⁻¹ ν_k`, the rescaled weight measure of
  [BHJ17, Def. 2.? (`defi:weight`), Prop. 5.? (`prop:DHlimit`)].

## Main results

* `SectionFiltration.lt_pieceDim_iff`: `j < dim 𝓕^μ_k ↔ μ ≤ λ^{(k)}_{j+1}` (`j < N_k`).
* `SectionFiltration.jumpMeasure_Ici`: `ν_k [τ, ∞) = dim 𝓕^{kτ}_k` (`k > 0`), and
  `jumpMeasure_univ`: `ν_k(ℝ) = N_k`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SGPT.LineBundle.SectionFiltration

open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes MeasureTheory Set Module

variable {X : Scheme} {f : X ⟶ Spec (.of ℂ)} {L : X.Modules} {a : LineBundleAtlas L}
variable (F : SectionFiltration f a)

/-- `dim 𝓕^μ_k`. -/
def pieceDim (μ : ℝ) (k : ℕ) : ℕ := finrank ℂ (F.piece μ k)

/-- The `(j+1)`-st successive minimum `λ^{(k)}_{j+1} = sup {μ : dim 𝓕^μ_k > j}`
([BHJ17, §1.1]). -/
def succMin (k j : ℕ) : ℝ := sSup {μ : ℝ | j < F.pieceDim μ k}

theorem pieceDim_anti {μ μ' : ℝ} (h : μ ≤ μ') (k : ℕ) [FiniteDimensional ℂ (SectionSpace f L k)] :
    F.pieceDim μ' k ≤ F.pieceDim μ k :=
  Submodule.finrank_mono (F.piece_anti h k)

/-- The pieces are locally constant from the left: for every `σ` there is `μ₀ < σ` with
`𝓕^μ_k = 𝓕^σ_k` for `μ ∈ [μ₀, σ)` (left-continuity and finite dimension). -/
theorem exists_piece_eq_left (k : ℕ) [FiniteDimensional ℂ (SectionSpace f L k)] (σ : ℝ) :
    ∃ μ₀ < σ, ∀ μ ∈ Ico μ₀ σ, F.piece μ k = F.piece σ k := by
  classical
  let g : ℝ → ℕ := fun μ => F.pieceDim μ k
  have hne : (g '' Iio σ).Nonempty := ⟨g (σ - 1), σ - 1, by simp, rfl⟩
  obtain ⟨μ₀, hμ₀, hgμ₀⟩ := Nat.sInf_mem hne
  have hmin : ∀ μ : ℝ, μ < σ → g μ₀ ≤ g μ := fun μ hμ => by
    rw [hgμ₀]
    exact Nat.sInf_le ⟨μ, hμ, rfl⟩
  have heq : ∀ μ ∈ Ico μ₀ σ, F.piece μ k = F.piece μ₀ k := fun μ hμ =>
    Submodule.eq_of_le_of_finrank_le (F.piece_anti hμ.1 k) (hmin μ hμ.2)
  have hσ : F.piece σ k = F.piece μ₀ k := by
    apply le_antisymm (F.piece_anti (le_of_lt hμ₀) k)
    rw [F.leftContinuous σ k]
    refine le_iInf₂ fun μ hμ => ?_
    rcases le_total μ μ₀ with h | h
    · exact F.piece_anti h k
    · exact (heq μ ⟨h, hμ⟩).symm.le
  exact ⟨μ₀, hμ₀, fun μ hμ => (heq μ hμ).trans hσ.symm⟩

/-- `j < dim 𝓕^μ_k ↔ μ ≤ λ^{(k)}_{j+1}` for `j < N_k = dim H⁰(X, L^k)`, `k > 0`. -/
theorem lt_pieceDim_iff {k : ℕ} (hk : 0 < k) [FiniteDimensional ℂ (SectionSpace f L k)] {j : ℕ}
    (hj : j < finrank ℂ (SectionSpace f L k)) (μ : ℝ) :
    j < F.pieceDim μ k ↔ μ ≤ F.succMin k j := by
  set S := {μ : ℝ | j < F.pieceDim μ k} with hS
  have hbdd : BddAbove S := by
    refine ⟨(F.bound : ℝ) * k, fun μ hμ => ?_⟩
    by_contra h
    have hb := F.piece_eq_bot_of_le hk (le_of_lt (lt_of_not_ge h))
    have : F.pieceDim μ k = 0 := by
      unfold pieceDim
      rw [hb, finrank_bot]
    change j < F.pieceDim μ k at hμ
    omega
  have hSne : S.Nonempty := by
    refine ⟨-((F.bound : ℝ) * k), ?_⟩
    change j < F.pieceDim _ k
    unfold pieceDim
    rw [F.piece_neg_bound_eq_top hk, finrank_top]
    exact hj
  constructor
  · intro h
    exact le_csSup hbdd h
  · intro h
    rcases h.lt_or_eq with h | h
    · obtain ⟨μ', hμ'S, hμ'⟩ := exists_lt_of_lt_csSup hSne h
      exact lt_of_lt_of_le hμ'S (F.pieceDim_anti hμ'.le k)
    · -- the supremum is attained
      obtain ⟨μ₀, hμ₀, hconst⟩ := F.exists_piece_eq_left k (F.succMin k j)
      obtain ⟨μ', hμ'S, hμ'⟩ := exists_lt_of_lt_csSup hSne hμ₀
      have hμ'le : μ' ≤ F.succMin k j := le_csSup hbdd hμ'S
      rcases hμ'le.lt_or_eq with hlt | heq
      · have := hconst μ' ⟨hμ'.le, hlt⟩
        change j < F.pieceDim μ' k at hμ'S
        unfold pieceDim at hμ'S ⊢
        rw [h, ← this]
        exact hμ'S
      · rw [h, ← heq]
        exact hμ'S

/-- The jumping measure `ν_k = ∑_{j < N_k} δ_{λ^{(k)}_{j+1}/k}` of the filtration in degree
`k` (the rescaled weight measure of [BHJ17, Prop. 5.? (`prop:DHlimit`)] times `N_k`). -/
def jumpMeasure (k : ℕ) : Measure ℝ :=
  ∑ j ∈ Finset.range (finrank ℂ (SectionSpace f L k)), Measure.dirac (F.succMin k j / k)

/-- The probability measure `N_k⁻¹ ∑_j δ_{λ^{(k)}_j / k}` of [BHJ17, (5.2) (`equ:num`)]. -/
def bhjWeightMeasure (k : ℕ) : Measure ℝ :=
  ((finrank ℂ (SectionSpace f L k) : ENNReal))⁻¹ • F.jumpMeasure k

theorem jumpMeasure_univ (k : ℕ) :
    F.jumpMeasure k univ = finrank ℂ (SectionSpace f L k) := by
  simp [jumpMeasure]

/-- **Tail formula**: `ν_k [τ, ∞) = dim 𝓕^{kτ}_k` for `k > 0`. -/
theorem jumpMeasure_Ici {k : ℕ} (hk : 0 < k) [FiniteDimensional ℂ (SectionSpace f L k)]
    (τ : ℝ) : F.jumpMeasure k (Ici τ) = F.pieceDim ((k : ℝ) * τ) k := by
  classical
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  set N := finrank ℂ (SectionSpace f L k)
  have hterm : ∀ j ∈ Finset.range N, Measure.dirac (F.succMin k j / k) (Ici τ) =
      if j < F.pieceDim ((k : ℝ) * τ) k then 1 else 0 := by
    intro j hj
    rw [Measure.dirac_apply' _ measurableSet_Ici, Set.indicator_apply]
    have hiff : F.succMin k j / k ∈ Ici τ ↔ j < F.pieceDim ((k : ℝ) * τ) k := by
      rw [Set.mem_Ici, le_div_iff₀ hkpos, F.lt_pieceDim_iff hk (Finset.mem_range.mp hj),
        mul_comm]
    by_cases h : j < F.pieceDim ((k : ℝ) * τ) k
    · rw [if_pos (hiff.mpr h), if_pos h]; rfl
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  rw [jumpMeasure, Measure.coe_finsetSum, Finset.sum_apply, Finset.sum_congr rfl hterm,
    Finset.sum_boole]
  have hle : F.pieceDim ((k : ℝ) * τ) k ≤ N := Submodule.finrank_le _
  have hfilt : (Finset.range N).filter (fun j => j < F.pieceDim ((k : ℝ) * τ) k) =
      Finset.range (F.pieceDim ((k : ℝ) * τ) k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [hfilt, Finset.card_range]

end SGPT.LineBundle.SectionFiltration
