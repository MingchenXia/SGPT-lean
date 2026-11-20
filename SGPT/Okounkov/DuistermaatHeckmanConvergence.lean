import SGPT.Okounkov.LegendreNets
import SGPT.Okounkov.IncreasingLegendre
import SGPT.Okounkov.DuistermaatHeckman

noncomputable section

namespace SGPT.Okounkov.TestCurve

open Set Filter Metric MeasureTheory
open scoped Topology

variable {n : ℕ} {Δ : ConvexBody (EuclideanSpace ℝ (Fin n))}
  (K : SGPT.Okounkov.TestCurve Δ)
  {D : ℕ → ConvexBody (EuclideanSpace ℝ (Fin n))}
  (L : ∀ i, SGPT.Okounkov.TestCurve (D i))

/-- Actual original decreasing ambient bodies contain their genuine Hausdorff limit. -/
theorem base_subset_of_decreasing_limit
    (hD : Tendsto D atTop (𝓝 Δ))
    (hDmono : ∀ i j, i ≤ j → (D j : Set (EuclideanSpace ℝ (Fin n))) ⊆ D i)
    (i : ℕ) : (Δ : Set (EuclideanSpace ℝ (Fin n))) ⊆ D i := by
  apply (SGPT.AlmostSemigroup.Hyperspace.isCompact_bodies_subset (D i).isCompact).isClosed.mem_of_tendsto hD
  filter_upwards [eventually_ge_atTop i] with j hij
  exact hDmono i j hij

/-- Exact source lma:DHmconv: genuine original decreasing source curves have the original weak distribution limit. -/
theorem tendsto_duistermaatHeckman_of_decreasing
    (hD : Tendsto D atTop (𝓝 Δ))
    (hDmono : ∀ i j, i ≤ j → (D j : Set (EuclideanSpace ℝ (Fin n))) ⊆ D i)
    (hmono : ∀ i j, i ≤ j → (L j).Compare (L i))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 K.max))
    (hb : ∀ t : Iio K.max, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (K.body t))) :
    Tendsto (fun i ↦ (L i).finiteDuistermaatHeckman) atTop (𝓝 K.finiteDuistermaatHeckman) := by
  apply K.tendsto_duistermaatHeckman_of_interior_convergence L hD
  intro x _hx
  have hΔ := base_subset_of_decreasing_limit hD hDmono
  have ht := K.tendsto_transform_of_decreasing L hΔ hmono hm hb x
  have heq (i : ℕ) : (L i).toTestFunction.valueAt x =
      (L i).transform ⟨x, hΔ i x.property⟩ := by
    classical
    have hxDi : (x : EuclideanSpace ℝ (Fin n)) ∈ D i := hΔ i x.property
    rw [TestFunction.valueAt, dif_pos hxDi]
    rfl
  simpa only [heq] using ht

/-- Exact source lma:DHmconv2: genuine original increasing source curves have the original weak distribution limit. -/
theorem tendsto_duistermaatHeckman_of_increasing
    (hD : Tendsto D atTop (𝓝 Δ))
    (hmono : ∀ i j, i ≤ j → (L i).Compare (L j))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 K.max))
    (hb : ∀ t : Iio K.max, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (K.body t))) :
    Tendsto (fun i ↦ (L i).finiteDuistermaatHeckman) atTop (𝓝 K.finiteDuistermaatHeckman) := by
  apply K.tendsto_duistermaatHeckman_of_interior_convergence L hD
  exact K.tendsto_transform_of_increasing L hD hmono hm hb

/-- The genuinely constructed original increasing limit curve has the actual weak source distribution limit. -/
theorem tendsto_duistermaatHeckman_ofIncreasingLimits {m : ℝ}
    (B : Iio m → ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hD : Tendsto D atTop (𝓝 Δ))
    (hmono : ∀ i j, i ≤ j → (L i).Compare (L j))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 m))
    (hb : ∀ t : Iio m, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (B t))) :
    Tendsto (fun i ↦ (L i).finiteDuistermaatHeckman) atTop
      (𝓝 (ofIncreasingLimits L B hD hmono hm hb).finiteDuistermaatHeckman) := by
  exact (ofIncreasingLimits L B hD hmono hm hb).tendsto_duistermaatHeckman_of_increasing L
    hD hmono hm hb

end SGPT.Okounkov.TestCurve
