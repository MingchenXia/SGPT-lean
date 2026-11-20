import SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicGraphNullity
import SGPT.Foundations.Analysis.Pending.DivisorSingularProjection

set_option autoImplicit false

/-! # Actual transverse nullity on a given holomorphic graph

The natural all-centre primitive germ property supplies local nullity;
an actual countable neighbourhood cover gives the full graph projection.
Uniform primitive remainders of an analytic ideal remain separate.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicGraphProjection

/-- Actual translated holomorphic germs have no common nonunit divisor. -/
def IsPrimitiveAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {N : ℕ}
    (f : Fin N → E → ℂ) (x : E) : Prop :=
  ∃ hf : ∀ i, ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℂ (fun y => f i (y + x)) y,
    ∀ q : HolGerm E, (∀ i, q ∣ HolGerm.mk (fun y => f i (y + x)) (hf i)) → IsUnit q

/-- A given holomorphic graph has actual null transverse common zeros
when the genuine family is primitive at every graph centre. -/
theorem volume_graph_common_zero_eq_zero {m N : ℕ}
    (f : Fin N → EuclideanSpace ℂ (Fin m) × ℂ → ℂ)
    {W : Set (EuclideanSpace ℂ (Fin m))} (hW : IsOpen W)
    {k : EuclideanSpace ℂ (Fin m) → ℂ} (hk : DifferentiableOn ℂ k W)
    (hprimitive : ∀ w ∈ W, IsPrimitiveAt f (w, k w)) :
    volume {w : EuclideanSpace ℂ (Fin m) | w ∈ W ∧ ∀ i, f i (w, k w) = 0} = 0 := by
  classical
  let T : Set (EuclideanSpace ℂ (Fin m)) := {w | w ∈ W ∧ ∀ i, f i (w, k w) = 0}
  have hlocal : ∀ w ∈ T, ∃ V ∈ 𝓝 w, volume (id '' (V ∩ T)) = 0 := by
    intro w hw
    obtain ⟨hF, hp⟩ := hprimitive w hw.1
    let F : Fin N → EuclideanSpace ℂ (Fin m) × ℂ → ℂ := fun i x => f i (x + (w, k w))
    let K : EuclideanSpace ℂ (Fin m) → ℂ := fun z => k (z + w) - k w
    have hshift : Tendsto (fun z : EuclideanSpace ℂ (Fin m) => z + w)
        (𝓝 0) (𝓝 w) := by
      have hc : Continuous (fun z : EuclideanSpace ℂ (Fin m) => z + w) :=
        continuous_id.add continuous_const
      simpa only [zero_add] using hc.tendsto (0 : EuclideanSpace ℂ (Fin m))
    have hK : ∀ᶠ z in 𝓝 (0 : EuclideanSpace ℂ (Fin m)), DifferentiableAt ℂ K z := by
      filter_upwards [hshift.eventually (hW.mem_nhds hw.1)] with z hz
      exact (((hk (z + w) hz).differentiableAt (hW.mem_nhds hz)).comp z
        (differentiableAt_id.add_const w)).sub_const (k w)
    obtain ⟨δ, hδ, hnull⟩ :=
      ActualPrimitiveHolomorphicGraphNullity.exists_ball_graph_common_zero_null F hF hp K hK
        (by simp [K])
    let A : Set (EuclideanSpace ℂ (Fin m)) :=
      {z | z ∈ ball 0 δ ∧ ∀ i, F i (z, K z) = 0}
    have hsub : ball w δ ∩ T ⊆ (fun y => -w + y) ⁻¹' A := by
      intro y hy
      refine ⟨?_, ?_⟩
      · simpa [mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm] using hy.1
      · intro i
        simpa [F, K, add_assoc] using hy.2.2 i
    refine ⟨ball w δ, ball_mem_nhds w hδ, ?_⟩
    rw [image_id]
    apply measure_mono_null hsub
    rw [measure_preimage_add]
    exact hnull
  simpa [T] using DivisorSingularProjection.measure_image_null_of_local volume id hlocal

end SGPT.Foundations.Analysis.Pending.ActualPrimitiveHolomorphicGraphProjection
