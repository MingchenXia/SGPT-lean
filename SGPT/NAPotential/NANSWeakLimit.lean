import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # Weak convergence on `ℝ` from the convergence of tails

A measure-theoretic step of `rmk:NApotential:L862` (comparison of the book's Duistermaat–Heckman
measure with the weak limit of the weight measures of [BHJ17, §3.2]): finite measures `μ_k` on
`ℝ` converge weakly to a nonzero finite measure `μ` as soon as their total masses converge and
their upper tails `μ_k (a, ∞)`, `μ_k [a, ∞)` converge to those of `μ` for all `a` outside a
countable set.  Proof: the open intervals with endpoints in the co-countable (hence dense) set
form a π-system containing arbitrarily small neighbourhoods of every point, on which the
normalized measures converge; Mathlib's `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`
and `FiniteMeasure.tendsto_normalize_iff_tendsto` conclude.  Blueprint `claude-na-ns`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.NAPotential.NANS

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

/-- The atoms of a finite measure on `ℝ` form a countable set. -/
theorem countable_atoms (μ : Measure ℝ) [IsFiniteMeasure μ] :
    {a : ℝ | μ {a} ≠ 0}ᶜᶜ.Countable := by
  rw [compl_compl]
  have h := Measure.countable_meas_pos_of_disjoint_iUnion₀ (μ := μ) (As := fun a : ℝ => {a})
    (fun _ => (measurableSet_singleton _).nullMeasurableSet)
    (fun a b hab => (Set.disjoint_singleton.mpr hab).aedisjoint)
  simpa only [pos_iff_ne_zero] using h

/-- The measure of an open interval from the two tails. -/
theorem measure_Ioo_eq_sub (μ : Measure ℝ) [IsFiniteMeasure μ] {a b : ℝ} (hab : a < b) :
    μ (Ioo a b) = μ (Ioi a) - μ (Ici b) := by
  have hsub : Ici b ⊆ Ioi a := fun x hx => lt_of_lt_of_le hab hx
  have hdiff : Ioi a \ Ici b = Ioo a b := by
    ext x
    simp
  rw [← hdiff, measure_sdiff hsub measurableSet_Ici.nullMeasurableSet (measure_ne_top μ _)]

/-- **Weak convergence from tails.** Let `μ_k`, `μ` be finite measures on `ℝ`, `μ ≠ 0`, and
`D ⊆ ℝ` with countable complement.  If `μ_k(ℝ) → μ(ℝ)` and `μ_k(a, ∞) → μ(a, ∞)`,
`μ_k[a, ∞) → μ[a, ∞)` for every `a ∈ D`, then `μ_k → μ` weakly. -/
theorem tendsto_of_tendsto_tails {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} (hμ : μ ≠ 0)
    {D : Set ℝ} (hD : Dᶜ.Countable)
    (hIoi : ∀ a ∈ D, Tendsto (fun k => (μs k : Measure ℝ) (Ioi a)) atTop
      (𝓝 ((μ : Measure ℝ) (Ioi a))))
    (hIci : ∀ a ∈ D, Tendsto (fun k => (μs k : Measure ℝ) (Ici a)) atTop
      (𝓝 ((μ : Measure ℝ) (Ici a))))
    (hmass : Tendsto (fun k => (μs k : Measure ℝ) univ) atTop (𝓝 ((μ : Measure ℝ) univ))) :
    Tendsto μs atTop (𝓝 μ) := by
  have hDdense : Dense D := by
    have := Set.Countable.dense_compl ℝ hD
    rwa [compl_compl] at this
  -- convergence of the masses in `ℝ≥0`
  have hmassNN : Tendsto (fun k => (μs k).mass) atTop (𝓝 μ.mass) := by
    have h : Tendsto (fun k => ((μs k).mass : ℝ≥0∞)) atTop (𝓝 (μ.mass : ℝ≥0∞)) := by
      simpa only [FiniteMeasure.ennreal_mass] using hmass
    exact ENNReal.tendsto_coe.mp h
  have hmass0 : μ.mass ≠ 0 := by
    intro h0
    exact hμ ((FiniteMeasure.mass_zero_iff μ).mp h0)
  have hev : ∀ᶠ k in atTop, μs k ≠ 0 := by
    have := hmassNN.eventually (eventually_ne_nhds hmass0)
    filter_upwards [this] with k hk h0
    exact hk ((FiniteMeasure.mass_zero_iff (μs k)).mpr h0)
  -- convergence on open intervals with endpoints in `D`
  have hIoo : ∀ a ∈ D, ∀ b ∈ D, Tendsto (fun k => μs k (Ioo a b)) atTop (𝓝 (μ (Ioo a b))) := by
    intro a ha b hb
    rcases lt_or_ge a b with hab | hab
    · have hE : Tendsto (fun k => (μs k : Measure ℝ) (Ioo a b)) atTop
          (𝓝 ((μ : Measure ℝ) (Ioo a b))) := by
        simp_rw [measure_Ioo_eq_sub _ hab]
        exact ENNReal.Tendsto.sub (hIoi a ha) (hIci b hb)
          (Or.inl (measure_ne_top (μ : Measure ℝ) _))
      have h : Tendsto (fun k => ((μs k (Ioo a b) : ℝ≥0) : ℝ≥0∞)) atTop
          (𝓝 ((μ (Ioo a b) : ℝ≥0) : ℝ≥0∞)) := by
        simpa only [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hE
      exact ENNReal.tendsto_coe.mp h
    · rw [Ioo_eq_empty (not_lt.mpr hab)]
      simp only [FiniteMeasure.coeFn_def, measure_empty, ENNReal.toNNReal_zero]
      exact tendsto_const_nhds
  rw [← FiniteMeasure.tendsto_normalize_iff_tendsto hμ]
  refine ⟨?_, hmassNN⟩
  let S : Set (Set ℝ) := {s | ∃ a ∈ D, ∃ b ∈ D, s = Ioo a b}
  have hS : IsPiSystem S := by
    rintro s ⟨a, ha, b, hb, rfl⟩ t ⟨c, hc, d, hd, rfl⟩ -
    refine ⟨max a c, ?_, min b d, ?_, Ioo_inter_Ioo⟩
    · rcases max_choice a c with h | h <;> rw [h] <;> assumption
    · rcases min_choice b d with h | h <;> rw [h] <;> assumption
  apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, -, b, -, rfl⟩
    exact measurableSet_Ioo
  · intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hx
    obtain ⟨a, haD, ha⟩ := hDdense.exists_between (show x - ε < x by linarith)
    obtain ⟨b, hbD, hb⟩ := hDdense.exists_between (show x < x + ε by linarith)
    refine ⟨Ioo a b, ⟨a, haD, b, hbD, rfl⟩, Ioo_mem_nhds ha.2 hb.1, ?_⟩
    intro y hy
    apply hball
    rw [Real.ball_eq_Ioo]
    exact ⟨lt_trans ha.1 hy.1, lt_trans hy.2 hb.2⟩
  · rintro s ⟨a, ha, b, hb, rfl⟩
    have hlim := ((hmassNN.inv₀ hmass0).mul (hIoo a ha b hb))
    rw [← μ.normalize_eq_of_nonzero hμ] at hlim
    refine hlim.congr' ?_
    filter_upwards [hev] with k hk
    rw [(μs k).normalize_eq_of_nonzero hk]

/-- `μ(t, ∞) = sup_j μ[t + ε_j, ∞)` for `ε_j = δ / (j + 2) ↓ 0`, `δ > 0`. -/
theorem measure_Ioi_eq_iSup (μ : Measure ℝ) (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    μ (Ioi t) = ⨆ j : ℕ, μ (Ici (t + δ / (j + 2))) := by
  have hmono : Monotone fun j : ℕ => Ici (t + δ / ((j : ℝ) + 2)) := by
    intro i j hij
    apply Ici_subset_Ici.mpr
    have hi : (0 : ℝ) < (i : ℝ) + 2 := by positivity
    have hij' : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hij 2
    have := div_le_div_of_nonneg_left hδ.le hi hij'
    linarith
  have hU : (⋃ j : ℕ, Ici (t + δ / ((j : ℝ) + 2))) = Ioi t := by
    ext x
    simp only [mem_iUnion, mem_Ici, mem_Ioi]
    constructor
    · rintro ⟨j, hj⟩
      have : 0 < δ / ((j : ℝ) + 2) := by positivity
      linarith
    · intro hx
      obtain ⟨j, hj⟩ := exists_nat_gt (δ / (x - t))
      refine ⟨j, ?_⟩
      have hxt : 0 < x - t := by linarith
      have hj2 : δ / (x - t) < (j : ℝ) + 2 := by linarith
      have : δ / ((j : ℝ) + 2) < x - t := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hxt] at hj2
        linarith
      linarith
  rw [← hU, hmono.measure_iUnion]

/-- **Tails from the sandwich.** Let `μ` be a finite measure on `ℝ`, `T ∈ ℝ`, and `g t k`,
`h t k ∈ [0, ∞]` (closed and open tails of `μ_k` at `t`) with `h t ≤ g t`, `g t' ≤ h t` for
`t < t'`, and the sandwich `μ[τ, ∞) ≤ liminf_k g τ' ≤ limsup_k g τ' ≤ μ[τ', ∞)` for
`τ' < τ < T`.  Then at every non-atom `t < T` of `μ`, `g t k → μ[t, ∞)` and `h t k → μ(t, ∞)`. -/
theorem tendsto_tails_of_sandwich (μ : Measure ℝ) [IsFiniteMeasure μ] {T : ℝ}
    {g h : ℝ → ℕ → ℝ≥0∞} (hhg : ∀ t k, h t k ≤ g t k) (hgh : ∀ t t', t < t' → ∀ k, g t' k ≤ h t k)
    (hS : ∀ τ' τ, τ' < τ → τ < T →
      μ (Ici τ) ≤ liminf (g τ') atTop ∧ limsup (g τ') atTop ≤ μ (Ici τ'))
    {t : ℝ} (ht : t < T) (hat : μ {t} = 0) :
    Tendsto (g t) atTop (𝓝 (μ (Ici t))) ∧ Tendsto (h t) atTop (𝓝 (μ (Ioi t))) := by
  have hIci : μ (Ici t) = μ (Ioi t) := by
    apply le_antisymm
    · calc μ (Ici t) = μ ({t} ∪ Ioi t) := by rw [Set.singleton_union, Set.Ioi_insert]
        _ ≤ μ {t} + μ (Ioi t) := measure_union_le _ _
        _ = μ (Ioi t) := by rw [hat, zero_add]
    · exact measure_mono Ioi_subset_Ici_self
  have hδ : 0 < T - t := by linarith
  have hεpos : ∀ j : ℕ, 0 < (T - t) / ((j : ℝ) + 2) := fun j => by positivity
  have hεlt : ∀ j : ℕ, t + (T - t) / ((j : ℝ) + 2) < T := by
    intro j
    have h2 : (T - t) / ((j : ℝ) + 2) ≤ (T - t) / 2 :=
      div_le_div_of_nonneg_left hδ.le two_pos (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)
    linarith
  have hεsucc : ∀ j : ℕ, (T - t) / (((j + 1 : ℕ) : ℝ) + 2) < (T - t) / ((j : ℝ) + 2) := by
    intro j
    apply div_lt_div_of_pos_left hδ (by positivity)
    push_cast
    linarith
  have hsup := measure_Ioi_eq_iSup μ t hδ
  have hlowg : μ (Ioi t) ≤ liminf (g t) atTop := by
    rw [hsup]
    exact iSup_le fun j => (hS t _ (by linarith [hεpos j]) (hεlt j)).1
  have hupg : limsup (g t) atTop ≤ μ (Ici t) := (hS t _ (by linarith [hεpos 0]) (hεlt 0)).2
  refine ⟨tendsto_of_le_liminf_of_limsup_le (by rw [hIci]; exact hlowg) hupg, ?_⟩
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · rw [hsup]
    refine iSup_le fun j => ?_
    calc μ (Ici (t + (T - t) / ((j : ℝ) + 2)))
        ≤ liminf (g (t + (T - t) / (((j + 1 : ℕ) : ℝ) + 2))) atTop :=
          (hS _ _ (by linarith [hεsucc j]) (hεlt j)).1
      _ ≤ liminf (h t) atTop :=
          liminf_le_liminf (Eventually.of_forall fun k => hgh t _ (by linarith [hεpos (j + 1)]) k)
  · calc limsup (h t) atTop ≤ limsup (g t) atTop :=
          limsup_le_limsup (Eventually.of_forall fun k => hhg t k)
      _ ≤ μ (Ici t) := hupg
      _ = μ (Ioi t) := hIci

end SGPT.NAPotential.NANS

end
