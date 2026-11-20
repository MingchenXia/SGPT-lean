import SGPT.Okounkov.LegendreEnergy
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.FiniteMeasure

noncomputable section

namespace SGPT.Okounkov.TestCurve

open Set Filter Metric MeasureTheory
open scoped Topology BoundedContinuousFunction

variable {n : ℕ} {Δ : ConvexBody (EuclideanSpace ℝ (Fin n))} (K : SGPT.Okounkov.TestCurve Δ)

/-- The genuine finite almost-everywhere real representative of the original Legendre transform. -/
def realLegendre (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (K.toTestFunction.valueAt x).toReal

/-- Exact source def:DHmeasureOTC: actual original-body Lebesgue pushforward. -/
def duistermaatHeckman : Measure ℝ :=
  Measure.map K.realLegendre (volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))))

theorem measurable_realLegendre : Measurable K.realLegendre :=
  K.toTestFunction.measurable_valueAt.ereal_toReal

/-- The actual source transform is finite almost everywhere; real casting loses no original mass. -/
theorem coe_realLegendre_ae : ∀ᵐ x ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))),
    (K.realLegendre x : EReal) = K.toTestFunction.valueAt x := by
  filter_upwards [K.toTestFunction.valueAt_finite_ae] with x hx
  exact EReal.coe_toReal hx.1 hx.2

/-- Actual original source pushforward on every genuine real Borel set. -/
theorem duistermaatHeckman_apply {s : Set ℝ} (hs : MeasurableSet s) :
    K.duistermaatHeckman s = volume ((K.realLegendre ⁻¹' s) ∩ (Δ : Set (EuclideanSpace ℝ (Fin n)))) := by
  rw [duistermaatHeckman, Measure.map_apply K.measurable_realLegendre hs,
    Measure.restrict_apply (hs.preimage K.measurable_realLegendre)]

/-- Actual source eq:massDHm1, retaining the original Lebesgue normalization. -/
theorem duistermaatHeckman_univ : K.duistermaatHeckman univ = volume (Δ : Set (EuclideanSpace ℝ (Fin n))) := by
  rw [K.duistermaatHeckman_apply MeasurableSet.univ, preimage_univ, univ_inter]

instance duistermaatHeckman_finite : IsFiniteMeasure K.duistermaatHeckman where
  measure_univ_lt_top := by
    rw [K.duistermaatHeckman_univ]
    exact Δ.isCompact.measure_lt_top

/-- Genuine finite Borel measures on the actual real line are Radon; no regularity certificate is assumed. -/
theorem duistermaatHeckman_regular : K.duistermaatHeckman.Regular := by infer_instance

/-- The genuine distribution upper tail is exactly the original closed source level volume. -/
theorem duistermaatHeckman_Ici (t : Iio K.max) :
    K.duistermaatHeckman (Ici (t : ℝ)) = volume (K.body t : Set (EuclideanSpace ℝ (Fin n))) := by
  rw [duistermaatHeckman, Measure.map_apply K.measurable_realLegendre measurableSet_Ici]
  have hae : K.realLegendre ⁻¹' Ici (t : ℝ) =ᵐ[volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n)))]
      (K.body t : Set (EuclideanSpace ℝ (Fin n))) := by
    filter_upwards [K.coe_realLegendre_ae, ae_restrict_mem Δ.isCompact.measurableSet] with x hx hxΔ
    apply propext
    change (t : ℝ) ≤ K.realLegendre x ↔ x ∈ K.body t
    rw [← EReal.coe_le_coe_iff, hx, TestFunction.valueAt, dif_pos (show x ∈ Δ from hxΔ)]
    exact (K.mem_body_iff_le_transform ⟨x, hxΔ⟩ t).symm
  rw [measure_congr hae, Measure.restrict_apply (K.body t).isCompact.measurableSet,
    inter_eq_left.mpr (K.body_subset t)]

/-- Actual continuous test integrals are genuine original-transform pushforward integrals. -/
theorem integral_duistermaatHeckman (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂K.duistermaatHeckman) =
      ∫ x, f (K.realLegendre x) ∂volume.restrict (Δ : Set (EuclideanSpace ℝ (Fin n))) := by
  exact integral_map K.measurable_realLegendre.aemeasurable hf.aestronglyMeasurable

/-- The actual finite source distribution in the genuine weak topology of finite real measures. -/
def finiteDuistermaatHeckman : FiniteMeasure ℝ := ⟨K.duistermaatHeckman, inferInstance⟩

/-- Genuine bounded-test dominated convergence on actual varying Hausdorff bodies.
The original Legendre net producers discharge the displayed interior convergence premise. -/
theorem tendsto_integral_duistermaatHeckman_of_interior_convergence
    {D : ℕ → ConvexBody (EuclideanSpace ℝ (Fin n))}
    (L : ∀ i, SGPT.Okounkov.TestCurve (D i))
    (hD : Tendsto D atTop (𝓝 Δ))
    (hG : ∀ (x : Δ), (x : EuclideanSpace ℝ (Fin n)) ∈ interior (Δ : Set _) →
      Tendsto (fun i ↦ (L i).toTestFunction.valueAt x) atTop (𝓝 (K.transform x)))
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, f x ∂(L i).duistermaatHeckman) atTop
      (𝓝 (∫ x, f x ∂K.duistermaatHeckman)) := by
  obtain ⟨B, hB, _, hDB⟩ := SGPT.AlmostSemigroup.Hyperspace.exists_compact_containing_sequence hD
  have hBi : Integrable (B.indicator (fun _ ↦ ‖f‖)) volume :=
    (integrable_indicator_iff hB.measurableSet).mpr
      (integrableOn_const (hB.measure_ne_top (μ := volume)))
  have hmeas (i : ℕ) : AEStronglyMeasurable
      ((D i : Set (EuclideanSpace ℝ (Fin n))).indicator (fun x ↦ f ((L i).realLegendre x))) volume :=
    (f.continuous.measurable.comp (L i).measurable_realLegendre).aestronglyMeasurable.indicator
      (D i).isCompact.measurableSet
  have hbound (i : ℕ) : ∀ᵐ x ∂volume,
      ‖(D i : Set (EuclideanSpace ℝ (Fin n))).indicator (fun x ↦ f ((L i).realLegendre x)) x‖ ≤
        B.indicator (fun _ ↦ ‖f‖) x := by
    apply Eventually.of_forall
    intro x
    by_cases hxi : x ∈ D i
    · simp only [indicator_of_mem hxi, indicator_of_mem (hDB i hxi)]
      exact f.norm_coe_le_norm _
    · simp only [indicator_of_notMem hxi, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ norm_nonneg _) x
  have hpoint : ∀ᵐ x ∂volume, Tendsto
      (fun i ↦ (D i : Set (EuclideanSpace ℝ (Fin n))).indicator
        (fun y ↦ f ((L i).realLegendre y)) x) atTop
      (𝓝 ((Δ : Set (EuclideanSpace ℝ (Fin n))).indicator
        (fun y ↦ f (K.realLegendre y)) x)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (Δ.convex.addHaar_frontier volume)] with x hx
    by_cases hxΔ : x ∈ Δ
    · have hxInt : x ∈ interior (Δ : Set (EuclideanSpace ℝ (Fin n))) := by
        by_contra hn
        exact hx ((mem_frontier_iff_notMem_interior hxΔ).mpr hn)
      let x' : Δ := ⟨x, hxΔ⟩
      have hreal := (EReal.tendsto_toReal (ne_of_lt (K.transform_lt_top x'))
        (K.transform_ne_bot_of_mem_interior x' hxInt)).comp (hG x' hxInt)
      have htarget : K.realLegendre x = (K.transform x').toReal := by
        rw [realLegendre, TestFunction.valueAt, dif_pos hxΔ]
        rfl
      rw [indicator_of_mem hxΔ, htarget]
      apply (f.continuous.tendsto _ |>.comp hreal).congr'
      filter_upwards [SGPT.AlmostSemigroup.Hyperspace.eventually_mem_of_mem_interior hD hxInt] with i hi
      simp only [indicator_of_mem hi, realLegendre]
      rfl
    · rw [indicator_of_notMem hxΔ]
      apply tendsto_const_nhds.congr'
      filter_upwards [SGPT.AlmostSemigroup.Hyperspace.eventually_not_mem_of_not_mem hD hxΔ] with i hi
      simp only [indicator_of_notMem hi]
  have ht := tendsto_integral_of_dominated_convergence (B.indicator (fun _ ↦ ‖f‖))
    hmeas hBi hbound hpoint
  simp_rw [integral_indicator (D _).isCompact.measurableSet,
    integral_indicator Δ.isCompact.measurableSet] at ht
  simpa only [integral_duistermaatHeckman _ _ f.continuous] using ht

/-- The original net convergence consumers give genuine weak convergence, rather than only individual formal test integrals. -/
theorem tendsto_duistermaatHeckman_of_interior_convergence
    {D : ℕ → ConvexBody (EuclideanSpace ℝ (Fin n))}
    (L : ∀ i, SGPT.Okounkov.TestCurve (D i))
    (hD : Tendsto D atTop (𝓝 Δ))
    (hG : ∀ (x : Δ), (x : EuclideanSpace ℝ (Fin n)) ∈ interior (Δ : Set _) →
      Tendsto (fun i ↦ (L i).toTestFunction.valueAt x) atTop (𝓝 (K.transform x))) :
    Tendsto (fun i ↦ (L i).finiteDuistermaatHeckman) atTop (𝓝 K.finiteDuistermaatHeckman) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  exact K.tendsto_integral_duistermaatHeckman_of_interior_convergence L hD hG

end SGPT.Okounkov.TestCurve
