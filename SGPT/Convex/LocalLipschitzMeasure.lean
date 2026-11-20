import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique

namespace SGPT.Convex
open Set Filter Topology MeasureTheory
open scoped MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F] in
/-- One genuine countable open Lipschitz cover of the original open domain. -/
theorem exists_countable_lipschitzOn_cover {g : E → F} {U : Set E}
    (hU : IsOpen U) (hg : LocallyLipschitzOn U g) :
    ∃ (K : U → NNReal) (V : U → Set E) (r : Set U), r.Countable ∧
      (∀ i, IsOpen (V i) ∧ LipschitzOnWith (K i) g (V i)) ∧
        U ⊆ ⋃ i ∈ r, V i := by
  classical
  have hloc (x : U) : ∃ (K : NNReal) (V : Set E),
      IsOpen V ∧ (x : E) ∈ V ∧ LipschitzOnWith K g V := by
    obtain ⟨K, t, ht, hKt⟩ := hg x.property
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds x.property)] at ht
    obtain ⟨V, hVt, hVo, hxV⟩ := mem_nhds_iff.mp ht
    exact ⟨K, V, hVo, hxV, hKt.mono hVt⟩
  choose K V hVo hxV hKV using hloc
  have hcover : U ⊆ ⋃ x : U, V x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨r, hr, hrcov⟩ :=
    (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover V hVo hcover
  exact ⟨K, V, r, hr, fun i ↦ ⟨hVo i, hKV i⟩, hrcov⟩

variable {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Refactored existing Rademacher globalization through the one actual
cover, now for every genuine finite-dimensional target. -/
theorem ae_differentiableAt_of_locallyLipschitzOn_open [FiniteDimensional ℝ F]
    {g : E → F} {U : Set E} (hU : IsOpen U) (hg : LocallyLipschitzOn U g) :
    ∀ᵐ x ∂μ, x ∈ U → DifferentiableAt ℝ g x := by
  obtain ⟨K, V, r, hr, hV, hcover⟩ := exists_countable_lipschitzOn_cover hU hg
  have hae : ∀ i ∈ r, ∀ᵐ x ∂μ, x ∈ V i → DifferentiableAt ℝ g x := by
    intro i _
    filter_upwards [(hV i).2.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx hxV
    exact (hx hxV).differentiableAt ((hV i).1.mem_nhds hxV)
  filter_upwards [(ae_ball_iff hr).mpr hae] with x hx hxU
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hxU)
  obtain ⟨hir, hxi⟩ := mem_iUnion.mp hxi
  exact hx i hir hxi

/-- Actual finite-dimensional Haar-null Lipschitz images via genuine
Hausdorff control and mutual actual Haar absolute continuity. -/
theorem addHaar_image_eq_zero_of_lipschitzOnWith {g : E → E} {S : Set E}
    {K : NNReal} (hg : LipschitzOnWith K g S) (hS : μ S = 0) : μ (g '' S) = 0 := by
  let H : Measure E := μH[Module.finrank ℝ E]
  have hH : H S = 0 := (Measure.absolutelyContinuous_isAddHaarMeasure H μ) hS
  have hbound := hg.hausdorffMeasure_image_le
    (d := (Module.finrank ℝ E : ℝ)) (by positivity)
  change H (g '' S) ≤ (K : ENNReal) ^ (Module.finrank ℝ E : ℝ) * H S at hbound
  rw [hH, mul_zero] at hbound
  have hHi : H (g '' S) = 0 := le_antisymm hbound bot_le
  exact (Measure.absolutelyContinuous_isAddHaarMeasure μ H) hHi

/-- The same genuine countable cover globalizes actual local null-image
control without any null-image or cover premise. -/
theorem addHaar_image_eq_zero_of_locallyLipschitzOn_open {g : E → E}
    {U S : Set E} (hU : IsOpen U) (hg : LocallyLipschitzOn U g)
    (hSU : S ⊆ U) (hS : μ S = 0) : μ (g '' S) = 0 := by
  obtain ⟨K, V, r, hr, hV, hcover⟩ := exists_countable_lipschitzOn_cover hU hg
  have hnull : ∀ i ∈ r, μ (g '' (S ∩ V i)) = 0 := by
    intro i _
    exact addHaar_image_eq_zero_of_lipschitzOnWith ((hV i).2.mono inter_subset_right)
      (measure_mono_null inter_subset_left hS)
  have hzero : μ (⋃ i ∈ r, g '' (S ∩ V i)) = 0 :=
    (measure_biUnion_null_iff hr).mpr hnull
  apply measure_mono_null _ hzero
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover (hSU hx))
  obtain ⟨hir, hxi⟩ := mem_iUnion.mp hxi
  exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hir, mem_image_of_mem g ⟨hx, hxi⟩⟩⟩

end SGPT.Convex
