import SGPT.Okounkov.LegendreEnergy
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section

namespace SGPT.Okounkov.TestCurve

open Set Filter Metric
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Δ Δ' : ConvexBody V}

/-- Actual original comparison transports each genuine supremum witness. -/
theorem transform_le_of_compare (K : SGPT.Okounkov.TestCurve Δ)
    (L : SGPT.Okounkov.TestCurve Δ') (hKL : K.Compare L)
    (hΔ : (Δ : Set V) ⊆ Δ') (x : Δ) :
    K.transform x ≤ L.transform ⟨x, hΔ x.property⟩ := by
  obtain ⟨hm, hb⟩ := hKL
  apply sSup_le
  rintro _ ⟨t, hx, rfl⟩
  exact L.le_transform_of_mem ⟨x, hΔ x.property⟩
    ⟨t, lt_of_lt_of_le t.property hm⟩ (hb t hx)

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {D : I → ConvexBody V} (K : SGPT.Okounkov.TestCurve Δ)
  (L : ∀ i, SGPT.Okounkov.TestCurve (D i))

/-- Actual decreasing original cutoffs dominate their true original limit. -/
theorem cutoff_le_of_decreasing
    (hmono : ∀ i j, i ≤ j → (L j).Compare (L i))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 K.max)) (i : I) : K.max ≤ (L i).max := by
  apply le_of_tendsto hm
  filter_upwards [eventually_ge_atTop i] with j hij
  exact (hmono i j hij).choose

/-- Actual source level limits lie in every original earlier level through genuine compact-carrier closedness. -/
theorem body_subset_of_decreasing_limit
    (hmono : ∀ i j, i ≤ j → (L j).Compare (L i))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 K.max))
    (hb : ∀ t : Iio K.max, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (K.body t)))
    (t : Iio K.max) (i : I) :
    (K.body t : Set V) ⊆ (L i).bodyAt (t : ℝ) := by
  have ht (j : I) : (t : ℝ) < (L j).max :=
    t.property.trans_le (K.cutoff_le_of_decreasing L hmono hm j)
  apply (SGPT.AlmostSemigroup.Hyperspace.isCompact_bodies_subset
    ((L i).bodyAt (t : ℝ)).isCompact).isClosed.mem_of_tendsto (hb t)
  filter_upwards [eventually_ge_atTop i] with j hij
  rw [bodyAt, dif_pos (ht j), bodyAt, dif_pos (ht i)]
  exact (hmono i j hij).choose_spec ⟨t, ht j⟩

/-- Genuine source target levels and supremum witnesses bound every original transform below. -/
theorem transform_le_of_decreasing_limit
    (hΔ : ∀ i, (Δ : Set V) ⊆ D i)
    (hmono : ∀ i j, i ≤ j → (L j).Compare (L i))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 K.max))
    (hb : ∀ t : Iio K.max, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (K.body t)))
    (x : Δ) (i : I) : K.transform x ≤ (L i).transform ⟨x, hΔ i x.property⟩ := by
  apply sSup_le
  rintro _ ⟨t, hx, rfl⟩
  have ht : (t : ℝ) < (L i).max :=
    t.property.trans_le (K.cutoff_le_of_decreasing L hmono hm i)
  have hmem := K.body_subset_of_decreasing_limit L hmono hm hb t i hx
  rw [bodyAt, dif_pos ht] at hmem
  exact (L i).le_transform_of_mem ⟨x, hΔ i x.property⟩ ⟨t, ht⟩ hmem

/-- Exact source prop:decnetLegend, including original bottom boundary values and the original directed net. -/
theorem tendsto_transform_of_decreasing
    (hΔ : ∀ i, (Δ : Set V) ⊆ D i)
    (hmono : ∀ i j, i ≤ j → (L j).Compare (L i))
    (hm : Tendsto (fun i ↦ (L i).max) atTop (𝓝 K.max))
    (hb : ∀ t : Iio K.max, Tendsto (fun i ↦ (L i).bodyAt (t : ℝ)) atTop (𝓝 (K.body t)))
    (x : Δ) : Tendsto (fun i ↦ (L i).transform ⟨x, hΔ i x.property⟩) atTop
      (𝓝 (K.transform x)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun i ↦ ha.trans_le
      (K.transform_le_of_decreasing_limit L hΔ hmono hm hb x i))
  · intro b hbgt
    cases b using EReal.rec with
    | bot => exact False.elim (not_lt_bot hbgt)
    | top => exact Eventually.of_forall (fun i ↦ (L i).transform_lt_top ⟨x, hΔ i x.property⟩)
    | coe s =>
      by_cases hms : K.max < s
      · filter_upwards [(tendsto_order.mp hm).2 s hms] with i hi
        exact ((L i).transform_le_max ⟨x, hΔ i x.property⟩).trans_lt (EReal.coe_lt_coe hi)
      · obtain ⟨r, hxr, hrs⟩ := EReal.exists_between_coe_real hbgt
        have hrm : r < K.max := (EReal.coe_lt_coe_iff.mp hrs).trans_le (le_of_not_gt hms)
        let t : Iio K.max := ⟨r, hrm⟩
        have hxnot : (x : V) ∉ K.body t := fun hx ↦
          not_le_of_gt hxr (K.le_transform_of_mem x t hx)
        have hne : infDist (x : V) (K.body t : Set V) ≠ 0 :=
          fun hz ↦ hxnot (((K.body t).isCompact.isClosed.mem_iff_infDist_zero
            (K.body t).nonempty).mpr hz)
        have hpos : 0 < infDist (x : V) (K.body t : Set V) :=
          lt_of_le_of_ne infDist_nonneg hne.symm
        have hdist := ((Metric.lipschitz_infDist_set (x : V)).continuous.comp
          SGPT.AlmostSemigroup.Hyperspace.isometry_carrierMap.continuous).tendsto (K.body t)
          |>.comp (hb t)
        filter_upwards [hdist.eventually (isOpen_Ioi.mem_nhds hpos)] with i hi
        have ht : r < (L i).max :=
          hrm.trans_le (K.cutoff_le_of_decreasing L hmono hm i)
        change 0 < infDist (x : V) ((L i).bodyAt r : Set V) at hi
        rw [bodyAt, dif_pos ht] at hi
        have hlt : (L i).transform ⟨x, hΔ i x.property⟩ < (r : EReal) := by
          apply lt_of_not_ge
          intro hge
          have hmem := ((L i).mem_body_iff_le_transform ⟨x, hΔ i x.property⟩ ⟨r, ht⟩).mpr hge
          exact hi.ne' (infDist_zero_of_mem hmem)
        exact hlt.trans hrs

end SGPT.Okounkov.TestCurve
