import SGPT.PSH.HermitianBalayageCovering
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Regular

/-!
# The geometric zero-mass step in coefficient freezing

Uniform finite overlap turns local estimates proportional to the radius
into zero mass on a compact set. The comparison measure is evaluated on
an internally constructed compact buffer. In particular no finiteness of
an ambient open ball is required.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianBalayage

open Set Metric MeasureTheory Classical
open scoped ENNReal NNReal BigOperators

section Multiplicity

variable {X ι : Type*} [MeasurableSpace X]

/-- A finite family of measurable sets with multiplicity at most `N`
has sum of measures at most `N` times the measure of their common buffer. -/
theorem sum_measure_le_mul_of_multiplicity (ν : Measure X) (S : Finset ι)
    (B : ι → Set X) {L : Set X} (hL : MeasurableSet L)
    (hB : ∀ i ∈ S, MeasurableSet (B i)) (hBL : ∀ i ∈ S, B i ⊆ L)
    {N : ℕ} (hmult : ∀ x, (S.filter (fun i => x ∈ B i)).card ≤ N) :
    ∑ i ∈ S, ν (B i) ≤ N * ν L := by
  have hfun (x : X) :
      ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ≥0∞)) x ≤
        L.indicator (fun _ => (N : ℝ≥0∞)) x := by
    by_cases hx : x ∈ L
    · rw [indicator_of_mem hx]
      simpa only [Set.indicator, Finset.sum_boole] using
        (Nat.cast_le.mpr (hmult x) :
          ((S.filter (fun i => x ∈ B i)).card : ℝ≥0∞) ≤ N)
    · rw [indicator_of_notMem hx]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro i hi
      exact indicator_of_notMem (fun h => hx (hBL i hi h)) _
  calc
    ∑ i ∈ S, ν (B i) = ∫⁻ x, ∑ i ∈ S, (B i).indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν := by
      rw [lintegral_finsetSum S (fun i hi => measurable_const.indicator (hB i hi))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_indicator_const (hB i hi), one_mul]
    _ ≤ ∫⁻ x, L.indicator (fun _ => (N : ℝ≥0∞)) x ∂ν := lintegral_mono hfun
    _ = N * ν L := lintegral_indicator_const hL _

end Multiplicity

section CompactMass

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- A genuine local `O(r)` comparison of positive measures forces zero
mass on a compact set. Centers, finite coverings, bounded overlap and a
finite compact buffer are all supplied by the proof. -/
theorem measure_compact_eq_zero_of_buffered_local_radius_bound
    (μ ν : Measure E) {K : Set E} (hK : IsCompact K)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hμbuffer : μ (cthickening δ K) ≠ ⊤)
    (hνbuffer : ν (cthickening δ K) ≠ ⊤)
    (hlocal : ∀ a ∈ K, ∀ r : ℝ, 0 < r → r < δ →
      (μ (ball a (r / 4))).toReal ≤ C * r * (ν (ball a r)).toReal) :
    μ K = 0 := by
  obtain ⟨N, hN⟩ := exists_finite_ball_cover_bounded_overlap (E := E)
  let L := cthickening δ K
  have hL : IsCompact L := hK.cthickening
  have hLfin : ν L ≠ ⊤ := hνbuffer
  have hballL {a : E} (ha : a ∈ K) {r : ℝ} (hr : r < δ) : ball a r ⊆ L := by
    intro x hx
    exact mem_cthickening_of_dist_le x a δ K ha (le_of_lt ((mem_ball.mp hx).trans hr))
  have hbound {r : ℝ} (hr : 0 < r) (hrδ : r < δ) :
      (μ K).toReal ≤ C * r * ((N : ℝ) * (ν L).toReal) := by
    obtain ⟨S, hSK, hcover, hmult⟩ := hN K hK r hr
    have hμfin (a : E) (ha : a ∈ S) : μ (ball a (r / 4)) ≠ ⊤ :=
      ne_top_of_le_ne_top hμbuffer (measure_mono
        ((ball_subset_ball (by linarith : r / 4 ≤ r)).trans (hballL (hSK ha) hrδ)))
    have hνfin (a : E) (ha : a ∈ S) : ν (ball a r) ≠ ⊤ :=
      ne_top_of_le_ne_top hLfin (measure_mono (hballL (hSK ha) hrδ))
    have hcoverμ : μ K ≤ ∑ a ∈ S, μ (ball a (r / 4)) :=
      (measure_mono (show K ⊆ ⋃ a ∈ S, ball a (r / 4) by
        simpa only [subset_def, mem_iUnion, exists_prop] using hcover)).trans
        (measure_biUnion_finset_le S _)
    have hcoverR := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr (fun a ha => hμfin a ha)) hcoverμ
    rw [ENNReal.toReal_sum (fun a ha => hμfin a ha)] at hcoverR
    have hsumν := sum_measure_le_mul_of_multiplicity ν S (fun a => ball a r)
      hL.isClosed.measurableSet (fun _ _ => isOpen_ball.measurableSet)
      (fun a ha => hballL (hSK ha) hrδ) hmult
    have hsumνR := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hLfin) hsumν
    rw [ENNReal.toReal_sum (fun a ha => hνfin a ha), ENNReal.toReal_mul,
      ENNReal.toReal_natCast] at hsumνR
    calc
      (μ K).toReal ≤ ∑ a ∈ S, (μ (ball a (r / 4))).toReal := hcoverR
      _ ≤ ∑ a ∈ S, C * r * (ν (ball a r)).toReal :=
        Finset.sum_le_sum (fun a ha => hlocal a (hSK ha) r hr hrδ)
      _ = C * r * ∑ a ∈ S, (ν (ball a r)).toReal := by rw [Finset.mul_sum]
      _ ≤ C * r * ((N : ℝ) * (ν L).toReal) :=
        mul_le_mul_of_nonneg_left hsumνR (mul_nonneg hC hr.le)
  have hzero : (μ K).toReal ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let M := C * ((N : ℝ) * (ν L).toReal)
    have hM : 0 ≤ M := mul_nonneg hC (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg)
    let r := min (δ / 2) (ε / (M + 1))
    have hr : 0 < r := lt_min (by positivity) (div_pos hε (by positivity))
    have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
    have hrε : r ≤ ε / (M + 1) := min_le_right _ _
    have hprod : r * M ≤ ε := by
      have hh := (le_div_iff₀ (by positivity : 0 < M + 1)).mp hrε
      nlinarith
    have hb := hbound hr hrδ
    change (μ K).toReal ≤ 0 + ε
    calc
      (μ K).toReal ≤ r * M := by dsimp [M]; nlinarith [hb]
      _ ≤ ε := hprod
      _ = 0 + ε := by ring
  have heq : (μ K).toReal = 0 := le_antisymm hzero ENNReal.toReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff _).mp heq).resolve_right
    (ne_top_of_le_ne_top hμbuffer (measure_mono (self_subset_cthickening K)))

/-- The chart-domain form of the geometric zero-mass step. Finiteness is
needed only on compact subsets of the actual open coordinate domain;
the proof chooses its buffer inside that domain. -/
theorem measure_compact_eq_zero_of_local_radius_bound
    (μ ν : Measure E) {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hμ : ∀ L : Set E, IsCompact L → L ⊆ Ω → μ L ≠ ⊤)
    (hν : ∀ L : Set E, IsCompact L → L ⊆ Ω → ν L ≠ ⊤)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hlocal : ∀ a ∈ K, ∀ r : ℝ, 0 < r → r < δ →
      (μ (ball a (r / 4))).toReal ≤ C * r * (ν (ball a r)).toReal) :
    μ K = 0 := by
  obtain ⟨ε, hε, hεΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let ρ := min ε (δ / 2)
  have hρ : 0 < ρ := lt_min hε (by positivity)
  have hbuffer : cthickening ρ K ⊆ Ω :=
    (cthickening_mono (min_le_left _ _) K).trans hεΩ
  apply measure_compact_eq_zero_of_buffered_local_radius_bound μ ν hK hρ hC
    (hμ _ hK.cthickening hbuffer) (hν _ hK.cthickening hbuffer)
  intro a ha r hr hrρ
  exact hlocal a ha r hr (hrρ.trans ((min_le_right _ _).trans_lt (by linarith)))

end CompactMass

end SGPT.PSH.HermitianBalayage
