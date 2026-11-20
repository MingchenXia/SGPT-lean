import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Order.Interval.Set.Infinite

/-!
# Weak convergence of finite measures on `ℝ` from their upper tails

Auxiliary measure theory for `prop:contDH` (`chapter_NApotential.tex`, blueprint chapter
`claude-na-dh2`, node `claude-na-dh2:weak-tails`).

Let `μᵢ, μ` be finite Borel measures on `ℝ` and `a ∈ ℝ`. If the total masses converge and
`μᵢ([t, ∞)) → μ([t, ∞))` for every `t ≠ a`, then `μᵢ ⇀ μ` weakly.

The proof applies the portmanteau criterion of Mathlib for π-systems
(`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`) to the normalized measures and the
π-system of half-open intervals `[p, q)` with `p, q ≠ a`; these contain arbitrarily small
neighbourhoods of every point.

## Main result

* `SGPT.NAPotential.DH.tendsto_of_tendsto_mass_of_tendsto_Ici`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.DH

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

/-- The π-system of half-open intervals `[p, q)` whose endpoints avoid `a`. -/
def icoAvoiding (a : ℝ) : Set (Set ℝ) := {s | ∃ p q : ℝ, p ≠ a ∧ q ≠ a ∧ s = Ico p q}

theorem isPiSystem_icoAvoiding (a : ℝ) : IsPiSystem (icoAvoiding a) := by
  rintro _ ⟨p, q, hp, hq, rfl⟩ _ ⟨p', q', hp', hq', rfl⟩ _
  refine ⟨max p p', min q q', ?_, ?_, Ico_inter_Ico⟩
  · rcases max_choice p p' with h | h <;> rw [h] <;> assumption
  · rcases min_choice q q' with h | h <;> rw [h] <;> assumption

/-- An open interval contains a point different from `a`. -/
theorem exists_mem_Ioo_ne {x y : ℝ} (hxy : x < y) (a : ℝ) : ∃ p ∈ Ioo x y, p ≠ a := by
  obtain ⟨p, hp, hpa⟩ := ((Ioo_infinite hxy).sdiff (finite_singleton a)).nonempty
  exact ⟨p, hp, hpa⟩

/-- The intervals `[p, q)`, `p, q ≠ a`, contain arbitrarily small neighbourhoods of every point. -/
theorem icoAvoiding_nhds (a : ℝ) (u : Set ℝ) (hu : IsOpen u) (x : ℝ) (hx : x ∈ u) :
    ∃ s ∈ icoAvoiding a, s ∈ 𝓝 x ∧ s ⊆ u := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hx
  obtain ⟨p, ⟨hp1, hp2⟩, hpa⟩ := exists_mem_Ioo_ne (show x - ε < x by linarith) a
  obtain ⟨q, ⟨hq1, hq2⟩, hqa⟩ := exists_mem_Ioo_ne (show x < x + ε by linarith) a
  refine ⟨Ico p q, ⟨p, q, hpa, hqa, rfl⟩, Ico_mem_nhds hp2 hq1, fun y hy => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
  exact ⟨by linarith [hy.2], by linarith [hy.1]⟩

/-- `μ([p, q)) = μ([p, ∞)) - μ([q, ∞))` for a finite measure and `p < q`. -/
theorem finiteMeasure_Ico_eq_sub (ν : FiniteMeasure ℝ) {p q : ℝ} (hpq : p ≤ q) :
    ν (Ico p q) = ν (Ici p) - ν (Ici q) := by
  rw [← Ici_sdiff_Ici]
  apply ENNReal.coe_injective
  rw [ENNReal.coe_sub, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact measure_sdiff (Ici_subset_Ici.mpr hpq) measurableSet_Ici.nullMeasurableSet
    (measure_ne_top _ _)

/-- **Weak convergence from upper tails.** Let `μᵢ, μ` be finite Borel measures on `ℝ` and
`a ∈ ℝ`. If `μᵢ(ℝ) → μ(ℝ)` and `μᵢ([t, ∞)) → μ([t, ∞))` for every `t ≠ a`, then `μᵢ ⇀ μ`. -/
theorem tendsto_of_tendsto_mass_of_tendsto_Ici {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (a : ℝ) (hmass : Tendsto (fun i => (μs i).mass) atTop (𝓝 μ.mass))
    (htail : ∀ t, t ≠ a → Tendsto (fun i => μs i (Ici t)) atTop (𝓝 (μ (Ici t)))) :
    Tendsto μs atTop (𝓝 μ) := by
  by_cases hμ : μ = 0
  · subst hμ
    exact FiniteMeasure.tendsto_zero_of_tendsto_zero_mass (by simpa using hmass)
  rw [← FiniteMeasure.tendsto_normalize_iff_tendsto hμ]
  refine ⟨?_, hmass⟩
  have hIco : ∀ p q : ℝ, p ≠ a → q ≠ a →
      Tendsto (fun i => μs i (Ico p q)) atTop (𝓝 (μ (Ico p q))) := by
    intro p q hp hq
    rcases le_or_gt q p with hqp | hpq
    · have h0 : ∀ ν : FiniteMeasure ℝ, ν (Ico p q) = 0 := fun ν => by
        rw [Ico_eq_empty_of_le hqp]
        simp
      simp only [h0]
      exact tendsto_const_nhds
    · simp only [finiteMeasure_Ico_eq_sub _ hpq.le]
      exact (htail p hp).sub (htail q hq)
  have haux : {(0 : ℝ≥0)}ᶜ ∈ 𝓝 μ.mass :=
    isOpen_compl_singleton.mem_nhds (μ.mass_nonzero_iff.mpr hμ)
  have hne : ∀ᶠ i in atTop, μs i ≠ 0 := by
    simp_rw [← FiniteMeasure.mass_nonzero_iff]
    exact hmass haux
  have hinv : Tendsto (fun i => (μs i).mass⁻¹) atTop (𝓝 μ.mass⁻¹) :=
    (continuousOn_inv₀.continuousAt haux).tendsto.comp hmass
  apply IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem (isPiSystem_icoAvoiding a)
  · rintro _ ⟨p, q, -, -, rfl⟩
    exact measurableSet_Ico
  · exact icoAvoiding_nhds a
  · rintro _ ⟨p, q, hp, hq, rfl⟩
    rw [μ.normalize_eq_of_nonzero hμ]
    refine (hinv.mul (hIco p q hp hq)).congr' ?_
    filter_upwards [hne] with i hi
    rw [(μs i).normalize_eq_of_nonzero hi]

end SGPT.NAPotential.DH
