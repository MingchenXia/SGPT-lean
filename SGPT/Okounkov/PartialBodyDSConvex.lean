import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.MetricSpace.HausdorffDistance
import SGPT.Okounkov.TranscendentalMainStatement

/-!
# Hausdorff convergence of convex bodies from volume convergence

Convex-geometry input of `thm:pobmain` (4) (blueprint chapter `claude-pob-ds`, node
`claude-pob-ds:volume-hausdorff`).

The book proves `thm:pobmain` (4) by reducing to monotone sequences of bodies and using the
Blaschke selection theorem and the continuity of the volume on `𝒦ₙ` (`thm:Blaschke`,
`thm:contvol`: "every Hausdorff cluster point is a monotone limit with the same volume").
Here a single elementary estimate replaces both:

* `exists_measure_add_le_of_far` (the volume gap): if a convex set `L ⊆ B̄(a, R)` contains the
  ball `B(a, r)`, `K ⊆ L` and `x ∈ L` is at distance `≥ ε` from `K`, then `L` contains a ball
  of radius `t r` (`t = min 1 (ε / (r + |R| + 1))`) around `x + t (a - x)`, disjoint from `K`,
  so `μ K + c ≤ μ L` with `c = μ(B(0, t r)) > 0` depending only on `r`, `R`, `ε`;
* `tendsto_hausdorffDist_of_tendsto_measure`: for a convex set `A` of positive finite measure
  and sets `K_i ⊆ L_i`, `A ⊆ L_i` with `L_i` convex and uniformly bounded, `μ L_i → μ A` and
  `μ K_i → μ A` imply `d_Haus(K_i, A) → 0` (no monotonicity, no subsequences);
* `volume_euclideanImage`, `convex_euclideanImage`: the transfer to the Euclidean copy of
  `ℝⁿ = Fin n → ℝ` on which the Hausdorff metric of the book is measured.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Okounkov.PartialBody

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A convex set containing `B(a, r)` and `x` contains `B(x + t (a - x), t r)` for
`t ∈ (0, 1]`. -/
theorem ball_subset_of_convex {L : Set V} (hL : Convex ℝ L) {a x : V} {r t : ℝ}
    (hball : ball a r ⊆ L) (hx : x ∈ L) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ball (x + t • (a - x)) (t * r) ⊆ L := by
  intro y hy
  set z : V := a + t⁻¹ • (y - (x + t • (a - x))) with hz
  have hzmem : z ∈ L := by
    refine hball ?_
    rw [mem_ball, dist_eq_norm, hz, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht0)]
    rw [mem_ball, dist_eq_norm] at hy
    calc t⁻¹ * ‖y - (x + t • (a - x))‖ < t⁻¹ * (t * r) := by gcongr
      _ = r := by field_simp
  have hyeq : y = (1 - t) • x + t • z := by
    rw [hz, smul_add, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
    module
  rw [hyeq]
  exact hL hx hzmem (by linarith) ht0.le (by ring)

/-- Points of the ball `B(x + t (a - x), t r)` are at distance `< t (r + ‖a - x‖)` from `x`. -/
theorem dist_lt_of_mem_ball_shift {a x y : V} {r t : ℝ} (ht0 : 0 ≤ t)
    (hy : y ∈ ball (x + t • (a - x)) (t * r)) : dist y x < t * (r + ‖a - x‖) := by
  rw [mem_ball] at hy
  calc dist y x ≤ dist y (x + t • (a - x)) + dist (x + t • (a - x)) x := dist_triangle _ _ _
    _ < t * r + t * ‖a - x‖ := by
        refine add_lt_add_of_lt_of_le hy (le_of_eq ?_)
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    _ = t * (r + ‖a - x‖) := by ring

variable [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (μ : Measure V)
  [μ.IsAddHaarMeasure]

/-- **The volume gap.** Given `a`, `r > 0`, `R` and `ε > 0`, there is `c > 0` such that for every
convex `L` with `B(a, r) ⊆ L ⊆ B̄(a, R)`, every `K ⊆ L` and every `x ∈ L` with `dist x y ≥ ε`
for all `y ∈ K`, `μ K + c ≤ μ L`. -/
theorem exists_measure_add_le_of_far (a : V) {r : ℝ} (hr : 0 < r) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∀ L K : Set V, Convex ℝ L → ball a r ⊆ L → L ⊆ closedBall a R →
      K ⊆ L → ∀ x ∈ L, (∀ y ∈ K, ε ≤ dist x y) → μ K + c ≤ μ L := by
  set t : ℝ := min 1 (ε / (r + |R| + 1)) with ht
  have hden : 0 < r + |R| + 1 := by positivity
  have ht0 : 0 < t := lt_min one_pos (div_pos hε hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htε : t * (r + |R|) < ε := by
    have h := min_le_right 1 (ε / (r + |R| + 1))
    rw [← ht, le_div_iff₀ hden] at h
    nlinarith
  refine ⟨μ (ball (0 : V) (t * r)), measure_ball_pos μ 0 (mul_pos ht0 hr),
    measure_ball_lt_top.ne, fun L K hL hball hLR hKL x hx hfar => ?_⟩
  set B := ball (x + t • (a - x)) (t * r) with hB
  have hBL : B ⊆ L := ball_subset_of_convex hL hball hx ht0 ht1
  have hdisj : Disjoint K B := by
    rw [Set.disjoint_left]
    intro y hyK hyB
    have h1 := dist_lt_of_mem_ball_shift ht0.le hyB
    have hax : ‖a - x‖ ≤ |R| := by
      have hxR := hLR hx
      rw [mem_closedBall, dist_eq_norm] at hxR
      rw [norm_sub_rev]
      exact hxR.trans (le_abs_self R)
    have h2 : t * (r + ‖a - x‖) ≤ t * (r + |R|) := by gcongr
    have h3 := hfar y hyK
    rw [dist_comm] at h3
    linarith
  have hμB : μ B = μ (ball (0 : V) (t * r)) := Measure.addHaar_ball_center μ _ _
  calc μ K + μ (ball (0 : V) (t * r)) = μ (K ∪ B) := by
        rw [measure_union hdisj measurableSet_ball, hμB]
    _ ≤ μ L := measure_mono (union_subset hKL hBL)

/-- A convex set of positive measure has nonempty interior. -/
theorem interior_nonempty_of_convex_of_measure_pos {A : Set V} (hA : Convex ℝ A)
    (hpos : 0 < μ A) : (interior A).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hsub : A ⊆ frontier A := by
    intro x hx
    rw [frontier, h, sdiff_empty]
    exact subset_closure hx
  have h0 := measure_mono_null hsub (hA.addHaar_frontier μ)
  exact hpos.ne' h0

/-- **Hausdorff convergence from volume convergence.** Let `A` be convex with
`0 < μ A < ∞`, and let `K_i ⊆ L_i` and `A ⊆ L_i`, with `L_i` convex and contained in a fixed
bounded set. If `μ L_i → μ A` and `μ K_i → μ A`, then `d_Haus(K_i, A) → 0`. -/
theorem tendsto_hausdorffDist_of_tendsto_measure {ι : Type*} {l : Filter ι} {A B : Set V}
    {K L : ι → Set V} (hA : Convex ℝ A) (hA0 : 0 < μ A) (hAfin : μ A ≠ ⊤)
    (hB : Bornology.IsBounded B) (hL : ∀ i, Convex ℝ (L i)) (hKL : ∀ i, K i ⊆ L i)
    (hAL : ∀ i, A ⊆ L i) (hLB : ∀ i, L i ⊆ B)
    (hμL : Tendsto (fun i => μ (L i)) l (𝓝 (μ A)))
    (hμK : Tendsto (fun i => μ (K i)) l (𝓝 (μ A))) :
    Tendsto (fun i => hausdorffDist (K i) A) l (𝓝 0) := by
  obtain ⟨a, ha⟩ := interior_nonempty_of_convex_of_measure_pos μ hA hA0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  have hballA : ball a r ⊆ A := hball.trans interior_subset
  obtain ⟨R, hR⟩ := hB.subset_closedBall a
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨c, hc, hctop, hgap⟩ := exists_measure_add_le_of_far μ a hr R (half_pos hε)
  have hc2 : c / 2 ≠ 0 := (ENNReal.half_pos hc.ne').ne'
  have hc2top : c / 2 ≠ ⊤ := ENNReal.div_ne_top hctop two_ne_zero
  have hL' : ∀ᶠ i in l, μ (L i) < μ A + c / 2 :=
    hμL.eventually_lt_const (ENNReal.lt_add_right hAfin hc2)
  have hK' : ∀ᶠ i in l, μ A - c / 2 < μ (K i) :=
    hμK.eventually_const_lt (ENNReal.sub_lt_self hAfin hA0.ne' hc2)
  filter_upwards [hL', hK'] with i hLi hKi
  have hKi' : μ A < μ (K i) + c / 2 := ENNReal.lt_add_of_sub_lt_right (Or.inl hAfin) hKi
  have hcc : c / 2 + c / 2 = c := ENNReal.add_halves c
  have hle : hausdorffDist (K i) A ≤ ε / 2 := by
    refine hausdorffDist_le_of_mem_dist (half_pos hε).le (fun x hx => ?_) (fun x hx => ?_)
    · by_contra hno
      push Not at hno
      have h := hgap (L i) A (hL i) (hballA.trans (hAL i)) ((hLB i).trans hR) (hAL i) x
        (hKL i hx) fun y hy => (hno y hy).le
      have : μ A + c / 2 < μ A + c :=
        ENNReal.add_lt_add_left hAfin (ENNReal.half_lt_self hc.ne' hctop)
      exact absurd (h.trans_lt hLi) (not_lt.mpr this.le)
    · by_contra hno
      push Not at hno
      have h := hgap (L i) (K i) (hL i) (hballA.trans (hAL i)) ((hLB i).trans hR) (hKL i) x
        (hAL i hx) fun y hy => (hno y hy).le
      have : μ A + c / 2 < μ (K i) + c :=
        calc μ A + c / 2 < μ (K i) + c / 2 + c / 2 := ENNReal.add_lt_add_right hc2top hKi'
          _ = μ (K i) + c := by rw [add_assoc, hcc]
      exact absurd (h.trans_lt hLi) (not_lt.mpr this.le)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hausdorffDist_nonneg]
  exact hle.trans_lt (half_lt_self hε)

end General

/-! ### The Euclidean copy of `ℝⁿ` -/

section Euclidean

variable {k : ℕ}

/-- The Euclidean copy of a set has the same Lebesgue measure. -/
theorem volume_euclideanImage (S : Set (Fin k → ℝ)) :
    volume (TranscendentalMain.euclideanImage S) = volume S := by
  have h :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k)).measure_preimage_equiv S
  convert h using 2
  ext x
  simp only [TranscendentalMain.euclideanImage, mem_image, mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨_, hx, by simp⟩

/-- The Euclidean copy of a convex set is convex. -/
theorem convex_euclideanImage {S : Set (Fin k → ℝ)} (hS : Convex ℝ S) :
    Convex ℝ (TranscendentalMain.euclideanImage S) :=
  hS.linear_image ((EuclideanSpace.equiv (Fin k) ℝ).symm.toLinearEquiv.toLinearMap)

/-- The Euclidean copy of a bounded set is bounded. -/
theorem isBounded_euclideanImage {S : Set (Fin k → ℝ)} (hS : Bornology.IsBounded S) :
    Bornology.IsBounded (TranscendentalMain.euclideanImage S) :=
  ((EuclideanSpace.equiv (Fin k) ℝ).symm.lipschitz).isBounded_image hS

/-- The Euclidean copy of a compact set is compact. -/
theorem isCompact_euclideanImage {S : Set (Fin k → ℝ)} (hS : IsCompact S) :
    IsCompact (TranscendentalMain.euclideanImage S) :=
  hS.image (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous

end Euclidean

end SGPT.Okounkov.PartialBody
