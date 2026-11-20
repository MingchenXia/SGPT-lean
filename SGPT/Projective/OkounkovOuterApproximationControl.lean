import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Genuine uniform upper point bounds from actual compact outer approximations.
Blueprint: okounkov-outer-approximation-control.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Okounkov.OuterApproximationControl
open Set Filter Metric
open scoped Topology

/-- A true iterated compact Hausdorff approximation controls every actual included raw point. -/
theorem eventually_near_of_compact_outer_limits
    {E : Type*} [PseudoMetricSpace E]
    {K : Set E} (hKc : IsCompact K) (hKne : K.Nonempty)
    (F : ℕ → Set E) (hFc : ∀ i, IsCompact (F i)) (hFne : ∀ i, (F i).Nonempty)
    (hF : Tendsto (fun i => hausdorffDist (F i) K) atTop (𝓝 0))
    (P : ℕ → ℕ → Set E)
    (hP : ∀ i, ∀ᶠ k : ℕ in atTop, (P i k).Nonempty ∧ Bornology.IsBounded (P i k))
    (hlim : ∀ i, Tendsto (fun k => hausdorffDist (P i k) (F i)) atTop (𝓝 0))
    (Q : ℕ → Set E) (hQP : ∀ i, ∀ᶠ k : ℕ in atTop, Q k ⊆ P i k) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k : ℕ in atTop, ∀ x∈Q k,
      ∃ z∈K, dist x z ≤ η := by
  intro η hη
  obtain ⟨i,hi⟩ := ((tendsto_order.mp hF).2 (η/2) (by linarith)).exists
  have hfinF : hausdorffEDist (F i) K ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (hFne i) hKne (hFc i).isBounded hKc.isBounded
  filter_upwards [hP i,hQP i,(tendsto_order.mp (hlim i)).2 (η/2) (by linarith)] with k hk hsub hdist x hx
  have hfinP : hausdorffEDist (P i k) (F i) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded hk.1 (hFne i) hk.2 (hFc i).isBounded
  obtain ⟨y,hy,hxy⟩ := exists_dist_lt_of_hausdorffDist_lt (hsub hx) hdist hfinP
  obtain ⟨z,hz,hyz⟩ := exists_dist_lt_of_hausdorffDist_lt hy hi hfinF
  exact ⟨z,hz,(dist_triangle x y z).trans (by linarith)⟩
end SGPT.Okounkov.OuterApproximationControl
