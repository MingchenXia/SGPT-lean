import SGPT.Foundations.Analysis.Pending.AnalyticBoundedMultiplierChartTransfer
import SGPT.Foundations.Analysis.FirstPass.HolomorphicMaps

set_option autoImplicit false

/-! # Actual analytic coefficients persist on neighborhoods and preferred charts -/

open Set Filter
open scoped Topology ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.AnalyticCoefficientLocalization

open FirstPass

noncomputable section

/-- A genuine logarithmic germ supplies a whole actual neighborhood on
which the coefficient and the finite family are unchanged. -/
theorem exists_open_same_coefficient_types
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : E → EReal} {c : ℝ} {N : ℕ} {g : Fin N → E → ℂ} {x : E}
    (htype : LogarithmicTypeAt P c g x) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∀ z ∈ V, LogarithmicTypeAt P c g z := by
  obtain ⟨hc, ⟨D, hD, hxD, hgD⟩, b, ⟨C, hC, hb⟩, heq⟩ := htype
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ D ∧ |b y| ≤ C ∧
      P y = (c : EReal) * generatorLog g y + (b y : EReal) := by
    filter_upwards [hD.mem_nhds hxD, hb, heq] with y hy hby hey
    exact ⟨hy, hby, hey⟩
  obtain ⟨V, hVsub, hV, hxV⟩ := _root_.mem_nhds_iff.mp hnear
  refine ⟨V, hV, hxV, ?_⟩
  intro z hz
  refine ⟨hc, ⟨V, hV, hz, fun i => (hgD i).mono fun y hy => (hVsub hy).1⟩,
    b, ⟨C, hC, ?_⟩, ?_⟩
  · filter_upwards [hV.mem_nhds hz] with y hy
    exact (hVsub hy).2.1
  · filter_upwards [hV.mem_nhds hz] with y hy
    exact (hVsub hy).2.2

/-- Actual identity coordinate maps transport the same local coefficient
to every preferred chart on an internally chosen source neighborhood. -/
theorem exists_open_preferred_chart_same_coefficient_types
    {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
    {P : M → EReal} (e : ComplexChart n M) {x : M} (hx : x ∈ e.val.source)
    {c : ℝ} {g : Fin N → ComplexModel n → ℂ}
    (htype : LogarithmicTypeAt (chartFunction P e) c g (e.val x)) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ U ⊆ e.val.source ∧
      ∀ y ∈ U, ∃ f : Fin N → ComplexModel n → ℂ,
        LogarithmicTypeAt (chartFunction P (complexChartAt (n := n) y)) c f
          ((complexChartAt (n := n) y).val y) := by
  obtain ⟨V, hV, hxV, hVtypes⟩ := exists_open_same_coefficient_types htype
  refine ⟨e.val.source ∩ e.val ⁻¹' V,
    e.val.continuousOn.isOpen_inter_preimage e.val.open_source hV,
    ⟨hx, hxV⟩, inter_subset_left, ?_⟩
  intro y hy
  let d := complexChartAt (n := n) y
  let F := HolomorphicMaps.coordinateMap (id : M → M) d e
  have hyd : y ∈ d.val.source := mem_complexChartAt_source y
  have hdomain : d.val y ∈ HolomorphicMaps.coordinateDomain (id : M → M) d e :=
    HolomorphicMaps.mem_coordinateDomain hyd hy.1
  have hD := HolomorphicMaps.coordinateDomain_isOpen (contMDiff_id (I := 𝓘(ℂ, ComplexModel n))) d e
  have hFc : ContDiffOn ℂ ∞ F (HolomorphicMaps.coordinateDomain (id : M → M) d e) :=
    HolomorphicMaps.coordinateMap_contDiffOn contMDiff_id d e
  have hFcont : ContinuousAt F (d.val y) :=
    (HolomorphicMaps.coordinateMap_contDiffAt contMDiff_id d e hdomain).continuousAt
  have hFval : F (d.val y) = e.val y :=
    HolomorphicMaps.coordinateMap_at hyd
  have hlocal : LogarithmicTypeAt (chartFunction P e) c g (F (d.val y)) := by
    rw [hFval]
    exact hVtypes (e.val y) hy.2
  obtain ⟨hc, ⟨W, hW, hFW, hgW⟩, b, hb, heq⟩ := hlocal
  refine ⟨fun i z => g i (F z), hc,
    ⟨HolomorphicMaps.coordinateDomain (id : M → M) d e ∩ F ⁻¹' W,
      hFc.continuousOn.isOpen_inter_preimage hD hW, ⟨hdomain, hFW⟩, ?_⟩,
    fun z => b (F z), hb.comp_continuousAt hFcont, ?_⟩
  · intro i
    exact (hgW i).comp ((hFc.differentiableOn (by simp)).mono inter_subset_left)
      (fun z hz => hz.2)
  · filter_upwards [hD.mem_nhds hdomain, hFcont.eventually heq] with z hz hey
    have hcoord : chartFunction P d z = chartFunction P e (F z) := by
      change P (d.val.symm z) = P (e.val.symm (e.val (d.val.symm z)))
      have hsource : d.val.symm z ∈ e.val.source := hz.2
      rw [e.val.left_inv hsource]
    rw [hcoord, hey]
    rfl

end

end SGPT.Foundations.Analysis.Pending.AnalyticCoefficientLocalization
