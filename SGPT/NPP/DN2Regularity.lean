import SGPT.NPP.DN2SecondOrder
import SGPT.Envelopes.LapClassKahlerClass

/-!
# From the quadratic smoothing bound to the bounded metric Laplacian (FPT, "Regularity")

Lane DN2, `thm:DNT23_C11bar`; FPT `thm:big-metric-laplacian-rooftop`, "Regularity": if on every
compact subset of an open `U` the corrected smoothing satisfies `0 ≤ H_u(x, r) - u(x) ≤ M r²` for
small `r`, then `u` is continuous on `U` (a uniform limit of the continuous `H_u(·, r)`), and the
generator identity `(Ψ_u(·, r) - u)/r² → a Δ_ω u` bounds the distributional Laplacian:
`|∫ u Δ_ω χ ω^N| ≤ ((K + |M|)/a) ∫ χ ω^N` for `χ ≥ 0` supported in the compact set.  This is the
book's `C^{1,1̄}_ω(U)` (`HasBoundedMetricLaplacianOn`).

## Main results

* `continuous_smoothing`: `x ↦ Ψ_g(x, t)` is continuous.
* `hasBoundedMetricLaplacianOn_of_quadratic`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace SGPT.NPP.DN2

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open KahlerLaplacianChart SGPT.Envelopes.LapClass

variable {N : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel N) Y]
  [IsComplexManifold N Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The smoothing of an integrable function is continuous in the base point. -/
theorem continuous_smoothing {wY : KahlerBackground N Y} {r₀ : ℝ} {Ψ : (Y → ℝ) → Y → ℝ → ℝ}
    (hJ : IsJointSmoothing wY r₀ Ψ) {g : Y → ℝ} (hg : Integrable g (kahlerVolume wY)) {t : ℝ}
    (ht : 0 < t) (htr : t < r₀) : Continuous (fun y => Ψ g y t) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  set e := complexChartAt (n := N) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  have hc : ContinuousOn (fun z => Ψ g (e.val.symm z) t) e.val.target := by
    have h := (hJ.contDiffOn g hg e).continuousOn.comp (continuous_id.prodMk
      continuous_const).continuousOn (fun z hz => ⟨hz, ht, htr⟩)
    exact h
  have h1 : ContinuousAt (fun z => Ψ g (e.val.symm z) t) (e.val x) :=
    hc.continuousAt (e.val.open_target.mem_nhds hz)
  have he : ContinuousAt e.val x := e.val.continuousOn.continuousAt (e.val.open_source.mem_nhds hx)
  have := h1.comp he
  refine this.congr ?_
  filter_upwards [e.val.open_source.mem_nhds hx] with y hy
  simp [e.val.left_inv hy]

/-- **Regularity from the quadratic smoothing bound** (FPT, "Regularity"). -/
theorem hasBoundedMetricLaplacianOn_of_quadratic {wY : KahlerBackground N Y} {r₀ : ℝ}
    {Ψ : (Y → ℝ) → Y → ℝ → ℝ} (hJ : IsJointSmoothing wY r₀ Ψ) {u : Y → EReal}
    (hint : Integrable (fun y => (u y).toReal) (kahlerVolume wY)) {K : ℝ} (hK : 0 ≤ K)
    {U : Set Y} (hU : IsOpen U)
    (hge : ∀ (x : Y) (t : ℝ), 0 < t → t < r₀ → u x ≤ ((correctedSmoothing Ψ u K x t : ℝ) : EReal))
    (hfin : ∀ x ∈ U, u x = ((u x).toReal : EReal))
    (hquad : ∀ Kc ⊆ U, IsCompact Kc → ∃ M r₁ : ℝ, 0 < r₁ ∧ ∀ y ∈ Kc, ∀ r : ℝ, 0 < r → r < r₁ →
      correctedSmoothing Ψ u K y r ≤ (u y).toReal + M * r ^ 2) :
    HasBoundedMetricLaplacianOn wY U (fun y => (u y).toReal) := by
  have hr₀ := hJ.r₀_pos
  set g : Y → ℝ := fun y => (u y).toReal with hgdef
  have hlow : ∀ y ∈ U, ∀ t : ℝ, 0 < t → t < r₀ → g y ≤ correctedSmoothing Ψ u K y t := by
    intro y hy t ht htr
    have := hge y t ht htr
    rw [hfin y hy, EReal.coe_le_coe_iff] at this
    exact this
  have hHcont : ∀ t : ℝ, 0 < t → t < r₀ → Continuous (fun y => correctedSmoothing Ψ u K y t) :=
    fun t ht htr => (continuous_smoothing hJ hint ht htr).add continuous_const
  haveI : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (ComplexModel N) Y
  refine ⟨?_, ?_⟩
  · -- continuity: a uniform limit of continuous functions on compact neighbourhoods
    intro x hx
    obtain ⟨Kc, hKc, hKcU, hKcc⟩ := local_compact_nhds (hU.mem_nhds hx)
    obtain ⟨M, r₁, hr₁, hM⟩ := hquad Kc hKcU hKcc
    set ρ : ℕ → ℝ := fun k => min r₁ (r₀ / 2) / ((k : ℝ) + 2) with hρ
    have hρpos : ∀ k, 0 < ρ k := fun k => by
      rw [hρ]; have : 0 < min r₁ (r₀ / 2) := lt_min hr₁ (by linarith)
      positivity
    have hρlt : ∀ k, ρ k < min r₁ (r₀ / 2) := fun k => by
      rw [hρ, div_lt_iff₀ (by positivity)]
      have : 0 < min r₁ (r₀ / 2) := lt_min hr₁ (by linarith)
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    have hρr₁ : ∀ k, ρ k < r₁ := fun k => (hρlt k).trans_le (min_le_left _ _)
    have hρr₀ : ∀ k, ρ k < r₀ := fun k => (hρlt k).trans_le ((min_le_right _ _).trans
      (by linarith))
    have hρlim : Tendsto ρ atTop (𝓝 0) := by
      rw [hρ]
      exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hconv : TendstoUniformlyOn (fun k y => correctedSmoothing Ψ u K y (ρ k)) g atTop Kc := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hsq : Tendsto (fun k => |M| * ρ k ^ 2) atTop (𝓝 0) := by
        have := (hρlim.pow 2).const_mul |M|
        simpa using this
      filter_upwards [hsq.eventually (gt_mem_nhds hε)] with k hk y hy
      rw [Real.dist_eq]
      have h1 := hlow y (hKcU hy) (ρ k) (hρpos k) (hρr₀ k)
      have h2 := hM y hy (ρ k) (hρpos k) (hρr₁ k)
      have h3 : M * ρ k ^ 2 ≤ |M| * ρ k ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg _)
      rw [abs_lt]; constructor <;> linarith
    have hgc : ContinuousOn g Kc := hconv.continuousOn
      (Frequently.of_forall fun k => (hHcont (ρ k) (hρpos k) (hρr₀ k)).continuousOn)
    exact ((hgc.continuousAt hKc).continuousWithinAt)
  · -- the Laplacian bound
    intro Kc hKcU hKcc
    obtain ⟨M, r₁, hr₁, hM⟩ := hquad Kc hKcU hKcc
    obtain ⟨a, ha, hgen⟩ := hJ.generator
    refine ⟨(K + |M|) / a, fun χ hχ hχ0 hχK => ?_⟩
    have hχc : Continuous χ := YauUniformEstimate.continuous_of_chartSmooth hχ
    obtain ⟨Cχ, hCχ⟩ := (isCompact_univ.image hχc).isBounded.exists_norm_le
    have hχint : Integrable χ (kahlerVolume wY) := integral_continuous hχc _
    have hlim := hgen g hint χ hχ
    set I : ℝ → ℝ := fun t => ∫ y, (Ψ g y t - g y) / t ^ 2 * χ y ∂(kahlerVolume wY) with hI
    have hbounds : ∀ᶠ t in 𝓝[>] (0 : ℝ), -K * ∫ y, χ y ∂(kahlerVolume wY) ≤ I t ∧
        I t ≤ (|M| - K) * ∫ y, χ y ∂(kahlerVolume wY) := by
      have hmem : Ioo (0 : ℝ) (min r₁ r₀) ∈ 𝓝[>] (0 : ℝ) :=
        Ioo_mem_nhdsGT (lt_min hr₁ hr₀)
      filter_upwards [hmem] with t ht
      have htpos : 0 < t := ht.1
      have htr₁ : t < r₁ := ht.2.trans_le (min_le_left _ _)
      have htr₀ : t < r₀ := ht.2.trans_le (min_le_right _ _)
      have ht2 : 0 < t ^ 2 := by positivity
      have hΨc := continuous_smoothing hJ hint htpos htr₀
      have hΨint : Integrable (fun y => Ψ g y t) (kahlerVolume wY) := integral_continuous hΨc _
      have hfint : Integrable (fun y => (Ψ g y t - g y) / t ^ 2 * χ y) (kahlerVolume wY) :=
        ((hΨint.sub hint).div_const (t ^ 2)).mul_bdd hχc.aestronglyMeasurable
          (ae_of_all _ fun y => hCχ _ ⟨y, mem_univ _, rfl⟩)
      -- pointwise bounds
      have hpt : ∀ y, -K * χ y ≤ (Ψ g y t - g y) / t ^ 2 * χ y ∧
          (Ψ g y t - g y) / t ^ 2 * χ y ≤ (|M| - K) * χ y := by
        intro y
        by_cases hy : y ∈ Kc
        · have h1 := hlow y (hKcU hy) t htpos htr₀
          have h2 := hM y hy t htpos htr₁
          simp only [correctedSmoothing] at h1 h2
          have hlo : -K ≤ (Ψ g y t - g y) / t ^ 2 := by
            rw [le_div_iff₀ ht2]; linarith
          have hhi : (Ψ g y t - g y) / t ^ 2 ≤ |M| - K := by
            rw [div_le_iff₀ ht2]
            have : M * t ^ 2 ≤ |M| * t ^ 2 :=
              mul_le_mul_of_nonneg_right (le_abs_self M) ht2.le
            linarith
          exact ⟨mul_le_mul_of_nonneg_right hlo (hχ0 y),
            mul_le_mul_of_nonneg_right hhi (hχ0 y)⟩
        · have h0 : χ y = 0 := image_eq_zero_of_notMem_tsupport fun h => hy (hχK h)
          simp [h0]
      constructor
      · rw [← integral_const_mul]
        exact integral_mono (hχint.const_mul _) hfint fun y => (hpt y).1
      · rw [← integral_const_mul]
        exact integral_mono hfint (hχint.const_mul _) fun y => (hpt y).2
    have hlo := ge_of_tendsto hlim (hbounds.mono fun t ht => ht.1)
    have hhi := le_of_tendsto hlim (hbounds.mono fun t ht => ht.2)
    have hχ0int : 0 ≤ ∫ y, χ y ∂(kahlerVolume wY) := integral_nonneg hχ0
    rw [abs_le]
    constructor
    · rw [div_mul_eq_mul_div, neg_le, le_div_iff₀ ha]
      have : |M| * ∫ y, χ y ∂(kahlerVolume wY) ≥ 0 := mul_nonneg (abs_nonneg _) hχ0int
      nlinarith
    · rw [div_mul_eq_mul_div, le_div_iff₀ ha]
      have : K * ∫ y, χ y ∂(kahlerVolume wY) ≥ 0 := mul_nonneg hK hχ0int
      nlinarith

end SGPT.NPP.DN2
