import SGPT.Foundations.Analysis.Pending.ActualHolomorphicGraphDivision
import SGPT.Foundations.Analysis.Pending.HolomorphicZeroSetNull

set_option autoImplicit false

/-! # Actual transverse graph nullity from primitive holomorphic germs

The natural primitive condition produces a nontrivial graph restriction,
then a genuine small-ball Haar-null common-zero set.  No current or
analytic stratification theorem is assumed or asserted.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicGraphNullity

/-- Actual primitive germs force genuine local transverse common-zero nullity on a graph. -/
theorem exists_ball_graph_common_zero_null {m N : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin m) × ℂ → ℂ)
    (hf : ∀ i, ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin m) × ℂ),
      DifferentiableAt ℂ (f i) x)
    (hprimitive : ∀ q : HolGerm (EuclideanSpace ℂ (Fin m) × ℂ),
      (∀ i, q ∣ HolGerm.mk (f i) (hf i)) → IsUnit q)
    (k : EuclideanSpace ℂ (Fin m) → ℂ)
    (hk : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin m)), DifferentiableAt ℂ k z)
    (hk0 : k 0 = 0) :
    ∃ δ : ℝ, 0 < δ ∧
      volume {z : EuclideanSpace ℂ (Fin m) |
        z ∈ ball 0 δ ∧ ∀ i, f i (z, k z) = 0} = 0 := by
  classical
  have hZ : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℂ (Fin m) × ℂ),
      DifferentiableAt ℂ (0 : EuclideanSpace ℂ (Fin m) × ℂ → ℂ) x :=
    eventually_differentiableAt_zero
  obtain ⟨hd, -, -, hnu⟩ :=
    ActualHolomorphicGraphDivision.exists_graph_germ_divisibility_iff hZ hk hk0
  have hdata : ∀ i, ∃ hr : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin m)),
      DifferentiableAt ℂ (fun z => f i (z, k z)) z,
      HolGerm.mk (fun x : EuclideanSpace ℂ (Fin m) × ℂ => x.2 - k x.1) hd ∣
        HolGerm.mk (f i) (hf i) ↔ HolGerm.mk (fun z => f i (z, k z)) hr = 0 := by
    intro i
    obtain ⟨hdi, hr, hi, _⟩ :=
      ActualHolomorphicGraphDivision.exists_graph_germ_divisibility_iff (hf i) hk hk0
    exact ⟨hr, hi⟩
  choose hr hiff using hdata
  have hsome : ∃ i, HolGerm.mk (fun z => f i (z, k z)) (hr i) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    exact hnu (hprimitive _ fun i => (hiff i).mpr (hnone i))
  obtain ⟨i, hi⟩ := hsome
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hr i)
  have hg : DifferentiableOn ℂ (fun z => f i (z, k z)) (ball 0 δ) :=
    fun z hz => (hball z hz).differentiableWithinAt
  have hnot : ¬ ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin m)), f i (z, k z) = 0 := by
    intro he
    apply hi
    rw [← HolGerm.mk_zero]
    exact HolGerm.mk_eq_mk_iff.mpr he
  have hfreq : ∃ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin m)), f i (z, k z) ≠ 0 :=
    Filter.not_eventually.mp hnot
  obtain ⟨z, hzne, hzball⟩ := (hfreq.and_eventually (ball_mem_nhds _ hδ)).exists
  have hnull := HolomorphicZeroSetNull.measure_ball_inter_preimage_zero_eq_zero
    volume hg hzball hzne
  refine ⟨δ, hδ, measure_mono_null ?_ hnull⟩
  intro z hz
  exact ⟨hz.1, hz.2 i⟩

end SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicGraphNullity
