import SGPT.Foundations.Analysis.Pending.ChartPartitionRelativeSupports
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

set_option autoImplicit false

/-! # The genuine bounded Borel multiplier on an actual whole chart

The complete mathematical statements and entire proofs precede this file.
-/

noncomputable section
open Set TopologicalSpace MeasureTheory
namespace SGPT.Foundations.Analysis.Pending.BorelChartZeroExtension
open FirstPass
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

def chartBorelWeight (e : ComplexChart n M) (f : M → ℝ) : ComplexModel n → ℝ :=
  e.val.target.indicator (fun z => f (e.val.symm z))

omit [IsComplexManifold n M] in
theorem measurable_chartBorelWeight (e : ComplexChart n M) (f : M → ℝ)
    (hf : Measurable f) : Measurable (chartBorelWeight e f) := by
  classical
  have ht : Measurable (fun z : e.val.target => f (e.val.symm z)) :=
    hf.comp e.val.continuousOn_symm.domRestrict.measurable
  apply measurable_of_restrict_of_restrict_compl e.val.open_target.measurableSet
  · have heq : e.val.target.domRestrict (chartBorelWeight e f) =
        (fun z : e.val.target => f (e.val.symm z)) := by
      funext z
      exact indicator_of_mem z.property (fun y : ComplexModel n => f (e.val.symm y))
    rw [heq]
    exact ht
  · have heq : (e.val.target)ᶜ.domRestrict (chartBorelWeight e f) =
        (fun _ : ((e.val.target)ᶜ : Set (ComplexModel n)) => (0 : ℝ)) := by
      funext z
      exact indicator_of_notMem z.property (fun y : ComplexModel n => f (e.val.symm y))
    rw [heq]
    exact measurable_const

omit [MeasurableSpace M] [BorelSpace M] [IsComplexManifold n M] in
theorem chartBorelWeight_bound (e : ComplexChart n M) (f : M → ℝ)
    (hb : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    ∃ C : ℝ, ∀ z, |chartBorelWeight e f z| ≤ C := by
  classical
  obtain ⟨C, hC⟩ := hb
  refine ⟨max C 0, fun z => ?_⟩
  by_cases hz : z ∈ e.val.target
  · rw [chartBorelWeight, indicator_of_mem hz]
    exact (hC _).trans (le_max_left _ _)
  · rw [chartBorelWeight, indicator_of_notMem hz, abs_zero]
    exact le_max_right _ _

end SGPT.Foundations.Analysis.Pending.BorelChartZeroExtension
