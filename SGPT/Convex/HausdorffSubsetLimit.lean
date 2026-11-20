import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

/-! Eventual inclusion passes to the actual Hausdorff limits of nonempty sets.
Blueprint: hausdorff-subset-limit.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Convex
open Set Filter
open scoped Topology

variable {I E : Type*} [MetricSpace E] {l : Filter I} [NeBot l]
  {A B : Set E} {a b : I → Set E}

theorem subset_of_tendsto_hausdorffDist
    (hA : Bornology.IsBounded A) (hB : Bornology.IsBounded B) (hBc : IsClosed B)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hgood : ∀ᶠ i in l, (a i).Nonempty ∧ (b i).Nonempty ∧
      Bornology.IsBounded (a i) ∧ Bornology.IsBounded (b i))
    (hsub : ∀ᶠ i in l, a i ⊆ b i)
    (ha : Tendsto (fun i => Metric.hausdorffDist (a i) A) l (𝓝 0))
    (hb : Tendsto (fun i => Metric.hausdorffDist (b i) B) l (𝓝 0)) : A ⊆ B := by
  intro x hx
  have hbound : ∀ᶠ i in l, Metric.infDist x B ≤
      Metric.hausdorffDist (a i) A + Metric.hausdorffDist (b i) B := by
    filter_upwards [hgood,hsub] with i hi hs
    have hfa := Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hAn hi.1 hA hi.2.2.1
    have hfb := Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded hi.2.1 hBn hi.2.2.2 hB
    calc
      Metric.infDist x B ≤ Metric.infDist x (b i) + Metric.hausdorffDist (b i) B :=
        Metric.infDist_le_infDist_add_hausdorffDist hfb
      _ ≤ Metric.infDist x (a i) + Metric.hausdorffDist (b i) B :=
        add_le_add (Metric.infDist_le_infDist_of_subset hs hi.1) le_rfl
      _ ≤ Metric.hausdorffDist A (a i) + Metric.hausdorffDist (b i) B :=
        add_le_add (Metric.infDist_le_hausdorffDist_of_mem hx hfa) le_rfl
      _ = _ := by rw [Metric.hausdorffDist_comm (s := A) (t := a i)]
  have hlim : Tendsto (fun i => Metric.hausdorffDist (a i) A +
      Metric.hausdorffDist (b i) B) l (𝓝 0) := by simpa using ha.add hb
  exact (hBc.mem_iff_infDist_zero hBn).mpr
    (le_antisymm (ge_of_tendsto hlim hbound) Metric.infDist_nonneg)

theorem subset_of_tendsto_hausdorffDist_of_isCompact
    (hA : IsCompact A) (hB : IsCompact B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hgood : ∀ᶠ i in l, IsCompact (a i) ∧ IsCompact (b i) ∧
      (a i).Nonempty ∧ (b i).Nonempty)
    (hsub : ∀ᶠ i in l, a i ⊆ b i)
    (ha : Tendsto (fun i => Metric.hausdorffDist (a i) A) l (𝓝 0))
    (hb : Tendsto (fun i => Metric.hausdorffDist (b i) B) l (𝓝 0)) : A ⊆ B := by
  apply subset_of_tendsto_hausdorffDist hA.isBounded hB.isBounded hB.isClosed hAn hBn
    _ hsub ha hb
  filter_upwards [hgood] with i hi
  exact ⟨hi.2.2.1,hi.2.2.2,hi.1.isBounded,hi.2.1.isBounded⟩

end SGPT.Convex
