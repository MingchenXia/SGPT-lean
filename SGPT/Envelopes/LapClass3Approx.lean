import SGPT.Analysis.CZConvexCauchy
import SGPT.Envelopes.LapClass3Energy
import SGPT.Envelopes.LapClassSmoothing

/-!
# Smooth approximations with `L²`-Cauchy Laplacians

Lane CZ-LP (`claude-cz-lp`, node `czlp:approx`).  Let `f` be continuous with bounded `ω`-Laplacian
on a compact complex manifold with a Kähler form `ω` (the book's `C^{1,1̄}(X)`,
`LapClass.HasBoundedMetricLaplacian`).

* `exists_smooth_abs_laplacian_le`: **two-sided smoothing.**  `f` is a uniform limit of chart-smooth
  `g` with `|Δ_ω g| ≤ K` for one `K` (the resolvent `g = (1 - sΔ_ω)⁻¹φ` of a smooth `φ ≈ f`; the
  duality estimate of LAP-CLASS's `sub_le_of_resolvent`, applied to `f` and `-f`).
* `exists_lapCauchy_approx`: **strong approximation.**  There are chart-smooth `v_k` with
  `|v_k - f| ≤ 1/(k+1)`, `|Δ_ω v_k| ≤ K` and `‖Δ_ω v_{k+1} - Δ_ω v_k‖²_{L²(ωⁿ)} ≤ 4⁻ᵏ`: convex
  combinations of tails of the two-sided smoothings (`exists_cauchySeq_mem_convexHull`, the
  elementary half of Mazur's lemma in `L²(ωⁿ)`) and a fast subsequence.

Together with the `L²` identity of `LapClass3Energy`, the complex Hessians of the `v_k` are then
Cauchy in `L²` in every chart (`LapClass3Density`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace SGPT.Envelopes.LapClass3

open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.KahlerLaplacianStokes
open SGPT.Foundations.Analysis.Pending.IntegrationCurrent
open SGPT.Foundations.Analysis.Pending.KahlerLaplacianChart
open SGPT.Envelopes.LapClass SGPT.Analysis.CZLp

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
theorem laplacianLE_neg_of_laplacianGE (w : KahlerBackground n M) {f : M → ℝ} {S : ℝ}
    (h : LaplacianGE w f (-S)) : LaplacianLE w (fun x => -f x) S := by
  intro χ hχ hχ0
  have h1 := h χ hχ hχ0
  have h3 : ∫ y, -f y * laplacian w.form.val χ y ∂(kahlerVolume w) =
      -∫ y, f y * laplacian w.form.val χ y ∂(kahlerVolume w) := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      show -f y * laplacian w.form.val χ y = -(f y * laplacian w.form.val χ y)
      ring)
  rw [h3]
  linarith

/-- **Two-sided smoothing** of a function with bounded `ω`-Laplacian. -/
theorem exists_smooth_abs_laplacian_le (w : KahlerBackground n M) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → ∃ g : M → ℝ, ChartSmooth (n := n) g ∧
      (∀ y, |g y - f y| ≤ η) ∧ ∀ y, |laplacian w.form.val g y| ≤ K := by
  obtain ⟨hfc, S, hLE, hGE⟩ := hf
  have hLE' := laplacianLE_neg_of_laplacianGE w hGE
  refine ⟨|S| + 1, by positivity, fun η hη => ?_⟩
  set η' : ℝ := min (η / 2) (1 / 2) with hη'
  have hη'0 : 0 < η' := lt_min (by positivity) (by norm_num)
  have hη'1 : η' ≤ 1 / 2 := min_le_right _ _
  have hη'η : η' ≤ η / 2 := min_le_left _ _
  set s : ℝ := min 1 (η' / (|S| + 1)) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hsS : s * (|S| + 1) ≤ η' := by
    have h1 : s ≤ η' / (|S| + 1) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at h1
  obtain ⟨φ, hφ, hφf⟩ := SGPT.Envelopes.DNTReg.exists_chartSmooth_abs_sub_lt (N := n) hfc
    (mul_pos hη'0 hs0)
  obtain ⟨g, hg, hgeq⟩ := exists_resolvent w hs0 hφ
  have hup : ∀ y, g y - φ y ≤ s * S + 2 * (η' * s) := fun y =>
    sub_le_of_resolvent w hfc hLE hφ hg hs0 (fun x => (hφf x).le) hgeq y
  have hnφ : ChartSmooth (n := n) (fun x => -φ x) := fun e => (hφ e).neg
  have hng : ChartSmooth (n := n) (fun x => -g x) := fun e => (hg e).neg
  have hngeq : ∀ y, -g y - s * laplacian w.form.val (fun x => -g x) y = -φ y := fun y => by
    have h1 := laplacian_const_mul w.form.val hg (-1) y
    simp only [neg_one_mul] at h1
    rw [h1]
    linarith [hgeq y]
  have hdown : ∀ y, -g y - -φ y ≤ s * S + 2 * (η' * s) := fun y =>
    sub_le_of_resolvent w hfc.neg hLE' hnφ hng hs0
      (fun x => by
        show |-φ x - -f x| ≤ η' * s
        rw [show -φ x - -f x = -(φ x - f x) by ring, abs_neg]; exact (hφf x).le)
      hngeq y
  have hgφ : ∀ y, |g y - φ y| ≤ s * (|S| + 1) := fun y => by
    have h1 := hup y
    have h2 := hdown y
    have h3 : s * S ≤ s * |S| := mul_le_mul_of_nonneg_left (le_abs_self S) hs0.le
    have h4 : s * -S ≤ s * |S| := mul_le_mul_of_nonneg_left (neg_le_abs S) hs0.le
    have h5 : 2 * (η' * s) ≤ s := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith
  refine ⟨g, hg, fun y => ?_, fun y => ?_⟩
  · have h1 := hgφ y
    have h2 := (hφf y).le
    have h3 : η' * s ≤ η' := by
      have : s ≤ 1 := min_le_left _ _
      nlinarith
    calc |g y - f y| = |(g y - φ y) + (φ y - f y)| := by ring_nf
      _ ≤ |g y - φ y| + |φ y - f y| := abs_add_le _ _
      _ ≤ η := by linarith
  · have hΔ : laplacian w.form.val g y = (g y - φ y) / s := by
      rw [eq_div_iff hs0.ne']; linarith [hgeq y]
    rw [hΔ, abs_div, abs_of_pos hs0, div_le_iff₀ hs0]
    have := hgφ y
    linarith

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem continuous_laplacian' (w : KahlerBackground n M) {u : M → ℝ}
    (hu : ChartSmooth (n := n) u) : Continuous (laplacian w.form.val u) :=
  continuous_laplacian_of_chartSmooth w.isKahler.1 hu

omit [MeasurableSpace M] [BorelSpace M] [CompactSpace M] in
theorem chartSmooth_two_of (u : M → ℝ) (hu : ChartSmooth (n := n) u) :
    ∀ e : ComplexChart n M, ContDiffOn ℝ 2 (fun z => u (e.val.symm z)) e.val.target := fun e =>
  (hu e).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

theorem norm_toLp_sq (μ : Measure M) [IsFiniteMeasure μ] (g : C(M, ℝ)) :
    ‖ContinuousMap.toLp (E := ℝ) 2 μ ℝ g‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, ContinuousMap.inner_toLp]
  simp only [RCLike.conj_to_real, pow_two]

/-- **Strong smooth approximation** of a function with bounded `ω`-Laplacian: uniform convergence,
uniformly bounded Laplacians, and Laplacians forming a fast Cauchy sequence in `L²(ωⁿ)`. -/
theorem exists_lapCauchy_approx (w : KahlerBackground n M) {f : M → ℝ}
    (hf : HasBoundedMetricLaplacian w f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ v : ℕ → M → ℝ, (∀ k, ChartSmooth (n := n) (v k)) ∧
      (∀ k x, |laplacian w.form.val (v k) x| ≤ K) ∧ (∀ k x, |v k x - f x| ≤ 1 / ((k : ℝ) + 1)) ∧
      ∀ k, ∫ x, (laplacian w.form.val (v (k + 1)) x - laplacian w.form.val (v k) x) ^ 2
        ∂(kahlerVolume w) ≤ (1 / 4 : ℝ) ^ k := by
  classical
  obtain ⟨K, hK0, hsm⟩ := exists_smooth_abs_laplacian_le w hf
  choose u hu huf huK using fun j : ℕ => hsm (1 / ((j : ℝ) + 1)) (by positivity)
  set μ := kahlerVolume w with hμ
  let T := ContinuousMap.toLp (E := ℝ) 2 μ ℝ
  let D : ℕ → C(M, ℝ) := fun j => ⟨laplacian w.form.val (u j), continuous_laplacian' w (hu j)⟩
  set a : ℕ → MeasureTheory.Lp ℝ 2 μ := fun j => T (D j) with ha
  have hDn : ∀ j, ‖D j‖ ≤ K := fun j =>
    (ContinuousMap.norm_le _ hK0).mpr fun x => by
      rw [Real.norm_eq_abs]; exact huK j x
  have hab : ∀ j, ‖a j‖ ≤ ‖T‖ * K := fun j =>
    (T.le_opNorm (D j)).trans (mul_le_mul_of_nonneg_left (hDn j) (norm_nonneg _))
  obtain ⟨b, hbS, hbC⟩ := exists_cauchySeq_mem_convexHull a hab
  -- each `b m` is the image of a convex combination of the `u j`, `j ≥ m`
  have hcomb : ∀ m : ℕ, ∃ v : M → ℝ, ChartSmooth (n := n) v ∧
      (∀ x, |laplacian w.form.val v x| ≤ K) ∧ (∀ x, |v x - f x| ≤ 1 / ((m : ℝ) + 1)) ∧
      ∃ hv : Continuous (laplacian w.form.val v), T ⟨_, hv⟩ = b m := by
    intro m
    have hmem := hbS m
    rw [convexHull_eq] at hmem
    obtain ⟨ι, t, c, z, hc0, hc1, hz, hcm⟩ := hmem
    have hzj : ∀ i ∈ t, ∃ j : ℕ, m ≤ j ∧ a j = z i := fun i hi => by
      obtain ⟨j, hj, hjz⟩ := hz i hi
      exact ⟨j, hj, hjz⟩
    choose! J hJm hJz using hzj
    set v : M → ℝ := fun x => ∑ i ∈ t, c i * u (J i) x with hvdef
    have hv : ChartSmooth (n := n) v := fun e =>
      ContDiffOn.sum fun i _ => contDiffOn_const.mul (hu (J i) e)
    have hΔv : ∀ x, laplacian w.form.val v x = ∑ i ∈ t, c i * laplacian w.form.val (u (J i)) x := by
      intro x
      rw [hvdef, laplacian_sum w.form.val t (f := fun i x => c i * u (J i) x)
        (fun i _ e => chartSmooth_two_of (fun x => c i * u (J i) x)
          (fun e => contDiffOn_const.mul (hu (J i) e)) e) x]
      exact Finset.sum_congr rfl fun i _ => laplacian_const_mul w.form.val (hu (J i)) (c i) x
    refine ⟨v, hv, fun x => ?_, fun x => ?_, continuous_laplacian' w hv, ?_⟩
    · rw [hΔv]
      calc |∑ i ∈ t, c i * laplacian w.form.val (u (J i)) x|
          ≤ ∑ i ∈ t, |c i * laplacian w.form.val (u (J i)) x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ t, c i * K := Finset.sum_le_sum fun i hi => by
            rw [abs_mul, abs_of_nonneg (hc0 i hi)]
            exact mul_le_mul_of_nonneg_left (huK _ x) (hc0 i hi)
        _ = K := by rw [← Finset.sum_mul, hc1, one_mul]
    · have : v x - f x = ∑ i ∈ t, c i * (u (J i) x - f x) := by
        simp only [hvdef, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hc1, one_mul]
      rw [this]
      calc |∑ i ∈ t, c i * (u (J i) x - f x)| ≤ ∑ i ∈ t, |c i * (u (J i) x - f x)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ t, c i * (1 / ((m : ℝ) + 1)) := Finset.sum_le_sum fun i hi => by
            rw [abs_mul, abs_of_nonneg (hc0 i hi)]
            refine mul_le_mul_of_nonneg_left ((huf (J i) x).trans ?_) (hc0 i hi)
            exact one_div_le_one_div_of_le (by positivity)
              (by exact_mod_cast Nat.succ_le_succ (hJm i hi))
        _ = 1 / ((m : ℝ) + 1) := by rw [← Finset.sum_mul, hc1, one_mul]
    · rw [← hcm, Finset.centerMass_eq_of_sum_1 _ _ hc1]
      have : (⟨laplacian w.form.val v, continuous_laplacian' w hv⟩ : C(M, ℝ)) =
          ∑ i ∈ t, c i • D (J i) := by
        ext x
        rw [ContinuousMap.coe_mk, hΔv, ContinuousMap.coe_sum, Finset.sum_apply]
        exact Finset.sum_congr rfl fun i _ => by simp [D]
      rw [this, map_sum]
      exact Finset.sum_congr rfl fun i hi => by rw [map_smul, ← hJz i hi]
  choose v' hv' hv'K hv'f hv'c hv'b using hcomb
  -- a fast subsequence
  have hfast : ∀ k : ℕ, ∃ N, ∀ p ≥ N, ∀ q ≥ N, dist (b p) (b q) < (1 / 2 : ℝ) ^ k := fun k =>
    Metric.cauchySeq_iff.mp hbC _ (by positivity)
  choose N hN using hfast
  set φ : ℕ → ℕ := fun k => (∑ i ∈ Finset.range (k + 1), N i) + k with hφ
  have hφN : ∀ k, N k ≤ φ k := fun k =>
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)).trans
      (Nat.le_add_right _ _)
  have hφmono : ∀ k, φ k ≤ φ (k + 1) := fun k => by
    simp only [hφ, Finset.sum_range_succ]
    omega
  have hφk : ∀ k, k ≤ φ k := fun k => Nat.le_add_left _ _
  refine ⟨K, hK0, fun k => v' (φ k), fun k => hv' _, fun k x => hv'K _ x, fun k x => ?_,
    fun k => ?_⟩
  · refine (hv'f _ x).trans (one_div_le_one_div_of_le (by positivity) ?_)
    exact_mod_cast Nat.succ_le_succ (hφk k)
  · have hd := hN k (φ (k + 1)) ((hφN k).trans (hφmono k)) (φ k) (hφN k)
    rw [dist_eq_norm, ← hv'b, ← hv'b, ← map_sub] at hd
    have hsq := norm_toLp_sq μ (⟨_, hv'c (φ (k + 1))⟩ - ⟨_, hv'c (φ k)⟩)
    simp only [ContinuousMap.sub_apply, ContinuousMap.coe_mk] at hsq
    rw [← hsq]
    calc ‖T (⟨_, hv'c (φ (k + 1))⟩ - ⟨_, hv'c (φ k)⟩)‖ ^ 2 ≤ ((1 / 2 : ℝ) ^ k) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hd.le 2
      _ = (1 / 4 : ℝ) ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

end SGPT.Envelopes.LapClass3
