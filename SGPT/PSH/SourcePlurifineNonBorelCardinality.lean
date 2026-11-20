import SGPT.PSH.SourcePlurifineNonBorelKernel
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated

/-! The genuine Boolean product has more subsets than Borel subsets. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.PSH.SourceNonBorelDraft
open Set Filter MeasureTheory Metric TopologicalSpace Cardinal
open scoped Cardinal
local notation "Bits" => ℕ → Bool

lemma exists_nonmeasurable_bits : ∃ A : Set Bits, ¬ MeasurableSet A := by
  by_contra hno
  have hall : ∀ A : Set Bits, MeasurableSet A := by simpa only [not_exists, not_not] using hno
  have hgen := MeasurableSpace.cardinal_measurableSet_le_continuum
    ((Cardinal.le_aleph0_iff_set_countable.mpr
      (MeasurableSpace.countable_countableGeneratingSet (α := Bits))).trans aleph0_le_continuum)
  rw [MeasurableSpace.generateFrom_countableGeneratingSet] at hgen
  have heq : {A : Set Bits | MeasurableSet A} = Set.univ := Set.eq_univ_iff_forall.mpr hall
  rw [heq, Cardinal.mk_univ] at hgen
  have hbits : Cardinal.mk Bits = 𝔠 := by
    simp [Cardinal.two_power_aleph0]
  have hc : 𝔠 < Cardinal.mk (Set Bits) := by
    simpa only [Cardinal.mk_set, hbits] using Cardinal.cantor (Cardinal.mk Bits)
  exact (not_lt_of_ge hgen) hc

end SGPT.PSH.SourceNonBorelDraft
