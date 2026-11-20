import SGPT.AlmostSemigroup.Hyperspace
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace SGPT.AlmostSemigroup.ConvexIntersection
open Set Filter MeasureTheory
open scoped Topology
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Genuine positive-weight combinations of an actual common interior point prove exact closure-intersection equality. -/
theorem closure_iInter_eq_of_nonempty_interior {I : Type*} (D : I → Set V)
    (hD : ∀ i, Convex ℝ (D i)) (hint : (interior (⋂ i, D i)).Nonempty) :
    closure (⋂ i, D i) = ⋂ i, closure (D i) := by
  apply subset_antisymm
  · intro y hy
    exact mem_iInter.mpr (fun i ↦ closure_mono (iInter_subset D i) hy)
  · intro y hy
    obtain ⟨x, hx⟩ := hint
    let a (j : ℕ) : ℝ := 1 / (j + 1 : ℝ)
    have ha : Tendsto a atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun j ↦ a j • x + (1 - a j) • y) atTop (𝓝 y) := by
      have h := (ha.smul (tendsto_const_nhds (x := x))).add
        (((tendsto_const_nhds (x := (1 : ℝ))).sub ha).smul (tendsto_const_nhds (x := y)))
      simpa only [zero_smul, sub_zero, one_smul, zero_add] using h
    apply mem_closure_of_tendsto ht
    apply Eventually.of_forall
    intro j
    apply mem_iInter.mpr
    intro i
    have hxi : x ∈ interior (D i) := interior_mono (iInter_subset D i) hx
    have hai : 0 < a j := by dsimp [a]; positivity
    have ha1 : a j ≤ 1 := by
      dsimp [a]
      apply (div_le_one (by positivity : (0 : ℝ) < j + 1)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) j]
    exact interior_subset ((hD i).combo_interior_closure_mem_interior hxi
      (mem_iInter.mp hy i) hai (by linarith) (by ring))

variable [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]

/-- Positive actual Haar volume forces an ordinary interior point of the actual convex carrier, without measurability or interior certificates. -/
theorem interior_nonempty_of_measure_pos (μ : Measure V) [μ.IsAddHaarMeasure]
    {D : Set V} (hD : Convex ℝ D) (hpos : 0 < μ D) : (interior D).Nonempty := by
  by_contra hne
  have hempty : interior D = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  have hsub : D ⊆ frontier D := by
    rw [frontier, hempty, sdiff_empty]
    exact subset_closure
  exact (ne_of_gt hpos) (measure_mono_null hsub (hD.addHaar_frontier μ))

/-- Exact SGPT lma:intconvexset, strengthened to an arbitrary family: its genuine positive-volume intersection has the actual closure-intersection equality. -/
theorem closure_iInter_eq_of_measure_pos {I : Type*} (D : I → Set V)
    (hD : ∀ i, Convex ℝ (D i)) (μ : Measure V) [μ.IsAddHaarMeasure]
    (hpos : 0 < μ (⋂ i, D i)) : closure (⋂ i, D i) = ⋂ i, closure (D i) :=
  closure_iInter_eq_of_nonempty_interior D hD
    (interior_nonempty_of_measure_pos μ (convex_iInter hD) hpos)

/-- Exact source Euclidean Lebesgue specialization, including zero-dimensional carriers. -/
theorem euclidean_closure_iInter_eq {n : ℕ} {I : Type*}
    (D : I → Set (EuclideanSpace ℝ (Fin n))) (hD : ∀ i, Convex ℝ (D i))
    (hpos : 0 < volume (⋂ i, D i)) : closure (⋂ i, D i) = ⋂ i, closure (D i) :=
  closure_iInter_eq_of_measure_pos D hD volume hpos

end SGPT.AlmostSemigroup.ConvexIntersection
