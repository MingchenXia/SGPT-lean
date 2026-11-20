import SGPT.PSH.HermitianComparisonGlobalReadback

/-!
# Canonical global strict one-factor comparison with a constant competitor

The signed strict-set factor sum is identified with the original canonical
mixed measures. Actual local comparison and native global cutoff
cancellation then give the global inequality. All positivity, coordinate
transport and correction readers are produced from the genuine bounded
Hermitian class inputs.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonGlobalOneFactor

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open Hermitian HermitianGlobalProducts

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]
  {omega : Background (m + 1) M}

/-- Actual canonical distinguished-factor comparison on the original open
strict sublevel set. The same geometric partition works for every genuine
bounded tuple and distinguished potential. -/
theorem canonical_strict_onefactor_const (C : CompactPartition omega)
    (u : Fin m → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    {a : M → EReal} (ha : IsHermitianPSH omega a)
    (hab : ∃ c d : ℝ, ∀ x, (c : EReal) ≤ a x ∧ a x ≤ (d : EReal))
    (c : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (hgap : ∀ x, max (c - (a x).toReal) 0 ≤ δ) :
    (globalMixedMeasure omega (Fin.cons (fun _ => (c : EReal)) u)
        (fun i => Fin.cases
          (HermitianBoundedMass.isFormPSH_const omega.isTypeOneOne omega.isSemipositive c) hu i)
        (fun i => Fin.cases ⟨c, c, fun _ => ⟨le_rfl, le_rfl⟩⟩ hb i)
        {x | a x < (c : EReal)}).toReal -
      (globalMixedMeasure omega (Fin.cons a u) (fun i => Fin.cases ha hu i)
        (fun i => Fin.cases hab hb i) {x | a x < (c : EReal)}).toReal ≤
      torsionDifference C u hu hb a (fun _ => (c : EReal)) := by
  have hc : IsHermitianPSH omega (fun _ => (c : EReal)) :=
    HermitianBoundedMass.isFormPSH_const omega.isTypeOneOne omega.isSemipositive c
  have hcb : ∃ e f : ℝ, ∀ x : M,
      (e : EReal) ≤ (fun _ : M => (c : EReal)) x ∧
        (fun _ : M => (c : EReal)) x ≤ (f : EReal) :=
    ⟨c, c, fun _ => ⟨le_rfl, le_rfl⟩⟩
  have hE : IsOpen {x | a x < (c : EReal)} :=
    ha.quasiPshPotential.1.upperSemicontinuous.isOpen_preimage (c : EReal)
  rw [← strictDifference_eq_globalMixedMeasure_sub C u hu hb ha hc hab hcb hE]
  exact strict_onefactor_const C u hu hb ha hab c hδ hgap

end SGPT.PSH.HermitianComparisonGlobalOneFactor
