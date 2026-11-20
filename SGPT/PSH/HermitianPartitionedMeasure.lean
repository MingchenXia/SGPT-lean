import SGPT.PSH.HermitianMixedGlobalCurrent
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Finite measures from the actual partitioned Hermitian products

Each local top-degree current is the actual signed background expansion,
with positivity produced from the original bounded Hermitian tuple. The
smooth partition has compact support inside each coordinate patch. This
proves finite global mass directly, before any identification of products
on overlaps or independence of the chosen partition is asserted.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianGlobalProducts

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open Hermitian

section WeightedTrace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [MeasurableSpace M] [BorelSpace M]

/-- The literal nonnegative density times the transported actual trace. -/
def CoordinatePatch.weightedTraceMeasure (P : CoordinatePatch n M)
    (T : LocalProductCurrent n P.domain 0) (hT : IsPositive T) (χ : M → ℝ) : Measure M :=
  (P.pushTraceMeasure T hT).withDensity (fun x => ENNReal.ofReal (χ x))

/-- Compactly supported weights inside an active coordinate patch give
finite mass, even if its unweighted zero extension has infinite boundary mass. -/
theorem CoordinatePatch.weightedTraceMeasure_isFiniteMeasure
    (P : CoordinatePatch n M) (T : LocalProductCurrent n P.domain 0) (hT : IsPositive T)
    (χ : M → ℝ) (hχc : IsCompact (tsupport χ))
    (hχs : tsupport χ ⊆ P.source) (hχle : ∀ x, χ x ≤ 1) :
    IsFiniteMeasure (P.weightedTraceMeasure T hT χ) := by
  let μ := P.pushTraceMeasure T hT
  have hfinite : μ (tsupport χ) < ⊤ := hχc.measure_lt_top_of_nhdsWithin
    (fun x hx => (P.pushTraceMeasure_finiteAtNhds T hT (hχs hx)).inf_of_left)
  have hs : Function.support (fun x => ENNReal.ofReal (χ x)) ⊆ tsupport χ := by
    intro x hx
    apply subset_tsupport χ
    intro hzero
    exact hx (by
      change ENNReal.ofReal (χ x) = 0
      rw [hzero, ENNReal.ofReal_zero])
  have hL : ∫⁻ x, ENNReal.ofReal (χ x) ∂μ < ⊤ := by
    calc
      ∫⁻ x, ENNReal.ofReal (χ x) ∂μ =
          ∫⁻ x in tsupport χ, ENNReal.ofReal (χ x) ∂μ :=
        (setLIntegral_eq_of_support_subset hs).symm
      _ ≤ ∫⁻ _x in tsupport χ, (1 : ℝ≥0∞) ∂μ :=
        lintegral_mono (fun x => ENNReal.ofReal_le_one.mpr (hχle x))
      _ = μ (tsupport χ) := by simp
      _ < ⊤ := hfinite
  exact isFiniteMeasure_withDensity hL.ne

end WeightedTrace

namespace MixedCurrentPartition

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] {omega : Background (m + 1) M}

omit [MeasurableSpace M] [BorelSpace M] in
/-- Each manufactured partition coefficient lies in the unit interval. -/
theorem weight_le_one (D : MixedCurrentPartition omega) (j : Fin D.count) (x : M) :
    D.weight j x ≤ 1 := by
  rw [← D.sum_one x]
  exact Finset.single_le_sum (fun k _ => D.nonneg k x) (Finset.mem_univ j)

/-- The actual global positive measure given by the finite supported sum
of the original positive local Hermitian top-degree currents. -/
def topMeasure (D : MixedCurrentPartition omega) (u : Fin (m + 1) → M → EReal)
    (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) : Measure M :=
  Measure.sum (fun j : Fin D.count => (D.patch j).geometry.weightedTraceMeasure
    ((D.patch j).current u) ((D.patch j).current_isPositive u hu hb) (D.weight j))

/-- Finite total mass is internally proved from actual current positivity,
compact weight supports and the ordinary chart geometry; no mass bound or
overlap equality is an assumption. -/
theorem topMeasure_isFiniteMeasure [CompactSpace M] (D : MixedCurrentPartition omega)
    (u : Fin (m + 1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal)) :
    IsFiniteMeasure (D.topMeasure u hu hb) := by
  have hfin (j : Fin D.count) : IsFiniteMeasure
      ((D.patch j).geometry.weightedTraceMeasure ((D.patch j).current u)
        ((D.patch j).current_isPositive u hu hb) (D.weight j)) :=
    (D.patch j).geometry.weightedTraceMeasure_isFiniteMeasure _ _ _
      (isClosed_tsupport (D.weight j)).isCompact (D.supported j) (D.weight_le_one j)
  let := hfin
  unfold topMeasure
  infer_instance

end MixedCurrentPartition

end SGPT.PSH.HermitianGlobalProducts
