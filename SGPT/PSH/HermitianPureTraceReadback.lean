import SGPT.PSH.HermitianZeroSlotsMeasure
import SGPT.PSH.HermitianComparisonPureTraces

/-!
# Actual local lower traces are controlled by canonical global pure traces

The original lower current is completed by genuine zero slots. Its native
measure reads back from the same canonical global mixed measure. A literal
coordinate-set inclusion gives the mass inequality, and the internally
manufactured binary permutation identifies a lower pure trace. Constants
in this local-to-global step are exactly one.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianPureTraceReadback

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorCollar LocalBedfordTaylorForms
open Hermitian HermitianGlobalProducts HermitianComparisonTraceDomination HermitianComparisonPureTraces

/-- Degree transport preserves the actual unit current. -/
theorem cast_oneCurrentOf {n a b : ℕ} {U : Opens (ComplexModel n)}
    (hab : a = b) (ha : a = n) (hb : b = n) :
    castLPC hab (oneCurrentOf (U := U) ha) = oneCurrentOf (U := U) hb := by
  cases hab
  rfl

/-- Degree transport preserves the actual unit-base background expansion. -/
theorem cast_backgroundExpansion_unit {n k a b : ℕ} {U : Opens (ComplexModel n)}
    (hab : a = b) (ha : a + k = n) (hb : b + k = n)
    (v : Fin k → ComplexModel n → ℝ)
    {σ : ComplexModel n → RealForm n 2} (hσ : ContDiffOn ℝ ∞ σ U) :
    castLPC hab (HermitianProducts.backgroundExpansion k a v hσ (oneCurrentOf (U := U) ha)) =
      HermitianProducts.backgroundExpansion k b v hσ (oneCurrentOf (U := U) hb) := by
  cases hab
  rfl

variable {m p l : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

theorem binaryFamily_isHermitianPSH {u : M → EReal} (hu : IsHermitianPSH omega u)
    (v : Fin p → M → EReal) (hvalues : ∀ i, v i = u ∨ v i = fun _ => 0) :
    ∀ i, IsHermitianPSH omega (v i) := by
  intro i
  rcases hvalues i with hi | hi
  · rw [hi]
    exact hu
  · rw [hi]
    exact HermitianExtremal.isHermitianPSH_zero omega

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
theorem binaryFamily_bounded {u : M → EReal}
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (v : Fin p → M → EReal) (hvalues : ∀ i, v i = u ∨ v i = fun _ => 0) :
    ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal) := by
  intro i
  rcases hvalues i with hi | hi
  · rw [hi]
    exact hb
  · rw [hi]
    exact ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
theorem completeWithZeros_binary {u : M → EReal} (hpl : p + l = m + 1)
    (v : Fin p → M → EReal) (hvalues : ∀ i, v i = u ∨ v i = fun _ => 0) :
    ∀ i, completeWithZeros hpl v i = u ∨ completeWithZeros hpl v i = fun _ => 0 := by
  have h (i : Fin (p + l)) :
      Fin.append v (fun _ : Fin l => fun _ : M => (0 : EReal)) i = u ∨
        Fin.append v (fun _ : Fin l => fun _ : M => (0 : EReal)) i = fun _ => 0 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hvalues j
    · exact Or.inr (Fin.append_right _ _ _)
  exact fun i => h (Fin.cast hpl.symm i)

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
theorem completeWithZeros_eq_zero_outside (hpl : p + l = m + 1)
    (v : Fin p → M → EReal) :
    ∀ i, p ≤ i.val → completeWithZeros hpl v i = fun _ => 0 := by
  have h (j : Fin (p + l)) : p ≤ j.val →
      Fin.append v (fun _ : Fin l => fun _ : M => (0 : EReal)) j = fun _ => 0 := by
    refine Fin.addCases (fun a ha => ?_) (fun b _ => ?_) j
    · have hlt := a.isLt
      change p ≤ a.val at ha
      omega
    · exact Fin.append_right _ _ _
  intro i hi
  exact h (Fin.cast hpl.symm i) hi

/-- The native positive measure of the original lower current wedged with
its actual Hermitian power. -/
def lowerTraceMeasure (P : BackgroundPatch omega) (hp : p ≤ m + 1)
    (v : Fin p → M → EReal) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hvb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal)) :
    Measure (ComplexModel (m + 1)) :=
  powerTraceMeasure (P.currentOfDegree p (m + 1 - p) (by omega) v)
    (P.currentOfDegree_isPositive p (m + 1 - p) (by omega) v hv hvb)
    ((omega.form.smooth P.geometry.chart).mono P.geometry.domain_le_target)
    (fun z hz => ⟨omega.isTypeOneOne P.geometry.chart z (P.geometry.domain_le_target hz),
      omega.isSemipositive P.geometry.chart z (P.geometry.domain_le_target hz)⟩)

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Literal inverse-chart inclusion controls the original local trace mass
by the same canonical full mixed measure with appended zero potentials.
This statement also applies to sets without measurability assumptions. -/
theorem lowerTraceMass_le_completed_global
    (P : BackgroundPatch omega) (hp : p ≤ m + 1)
    (v : Fin p → M → EReal) (hv : ∀ i, IsHermitianPSH omega (v i))
    (hvb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ v i x ∧ v i x ≤ (b : EReal))
    (A : Set (ComplexModel (m + 1))) (E : Set M)
    (hA : A ⊆ P.geometry.domain) (hAE : ∀ z ∈ A, P.geometry.chart.val.symm z ∈ E) :
    (lowerTraceMeasure P hp v hv hvb A).toReal ≤
      (globalMixedMeasure omega (completeWithZeros (by omega : p + (m + 1 - p) = m + 1) v)
        (completeWithZeros_isHermitianPSH (by omega) v hv)
        (completeWithZeros_bounded (by omega) v hvb) E).toReal := by
  let hpl : p + (m + 1 - p) = m + 1 := by omega
  let μ := lowerTraceMeasure P hp v hv hvb
  let ν := globalMixedMeasure omega (completeWithZeros hpl v)
    (completeWithZeros_isHermitianPSH hpl v hv) (completeWithZeros_bounded hpl v hvb)
  have hread : ν.restrict P.geometry.source = P.geometry.pushMeasure μ :=
    globalMixedMeasure_completeWithZeros_restrict_patch hpl v hv hvb P
  have hle : μ A ≤ ν E := by
    calc
      μ A ≤ P.geometry.pushMeasure μ E := by
        rw [P.geometry.pushMeasure_apply]
        exact measure_mono (fun z hz => ⟨hA hz, hAE z hz⟩)
      _ = ν (E ∩ (P.geometry.source : Set M)) := by
        rw [← hread, Measure.restrict_apply' P.geometry.source.isOpen.measurableSet]
      _ ≤ ν E := measure_mono inter_subset_left
  let := globalMixedMeasure_isFiniteMeasure (completeWithZeros hpl v)
    (completeWithZeros_isHermitianPSH hpl v hv) (completeWithZeros_bounded hpl v hvb)
  exact ENNReal.toReal_mono (measure_ne_top ν E) hle

/-- Every actual local lower binary trace is controlled by the finite sum
of canonical global pure trace masses, with coefficient one. Class membership,
real bounds, zero slots and binary sorting are all produced internally. -/
theorem lower_binary_traceMass_le_pureTrace_sum
    (P : BackgroundPatch omega) (hp : p < m + 1)
    {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (v : Fin p → M → EReal) (hvalues : ∀ i, v i = u ∨ v i = fun _ => 0)
    (A : Set (ComplexModel (m + 1))) (E : Set M)
    (hA : A ⊆ P.geometry.domain) (hAE : ∀ z ∈ A, P.geometry.chart.val.symm z ∈ E) :
    (lowerTraceMeasure P hp.le v (binaryFamily_isHermitianPSH hu v hvalues)
      (binaryFamily_bounded hb v hvalues) A).toReal ≤
      ∑ k ∈ Finset.range (m + 1), pureTraceMass omega hu hb E k := by
  let hv := binaryFamily_isHermitianPSH hu v hvalues
  let hvb := binaryFamily_bounded hb v hvalues
  let hpl : p + (m + 1 - p) = m + 1 := by omega
  exact (lowerTraceMass_le_completed_global P hp.le v hv hvb A E hA hAE).trans
    (lower_binary_mass_le_pureTrace_sum hu hb (completeWithZeros hpl v)
      (completeWithZeros_isHermitianPSH hpl v hv) (completeWithZeros_bounded hpl v hvb)
      hp (completeWithZeros_binary hpl v hvalues) (completeWithZeros_eq_zero_outside hpl v) E)

end SGPT.PSH.HermitianPureTraceReadback
