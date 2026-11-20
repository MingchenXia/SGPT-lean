import SGPT.PSH.HermitianComparisonPureStep
import SGPT.PSH.HermitianComparisonTorsionGeometry
import SGPT.PSH.HermitianComparisonPureBudget
import SGPT.PSH.HermitianComparisonGlobalTorsion

/-!
# The actual uniform pure-trace recurrence

The compact partition, derivative constants and fixed-form trace dominator
are all chosen before the potential. The genuine canonical one-factor
comparison is then bounded by a finite sum of canonical lower pure traces.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparison

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianGlobalProducts HermitianComparisonPureTraces
  HermitianComparisonGlobalOneFactor HermitianComparisonTorsionGeometry
  HermitianComparisonPureBudget
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- Geometry supplies the uniform error coefficient before every bounded
Hermitian potential. The recurrence concerns the literal canonical mixed
measures and internally instantiates all local-to-global analytical bounds. -/
theorem exists_uniform_pure_recurrence (omega : Background (m + 1) M) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (u : M → EReal) (hu : IsHermitianPSH omega u)
        (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
        (c δ : ℝ), 0 ≤ δ → (∀ x, max (c - (u x).toReal) 0 ≤ δ) →
        ∀ k, k < m + 1 →
          pureTraceMass omega hu hb {x | u x < (c : EReal)} k ≤
            pureTraceMass omega hu hb {x | u x < (c : EReal)} (k + 1) +
              δ * B * ∑ j ∈ Finset.range (m + 1),
                pureTraceMass omega hu hb {x | u x < (c : EReal)} j := by
  classical
  let C : CompactPartition omega := Classical.choice (nonempty_compactPartition omega)
  obtain ⟨A, hA, hdom⟩ := exists_uniform_trace_dominator C
  obtain ⟨b, hbpos, hbound⟩ := exists_torsionDifference_setBudget_bound C
  let L : ℝ := (4 : ℝ) ^ m * (A : ℝ) ^ (m + 1)
  let B : ℝ := (∑ i, b i) * L
  have hL : 0 ≤ L := by positivity
  have hB : 0 ≤ B := mul_nonneg (Finset.sum_nonneg (fun i _ => hbpos i)) hL
  refine ⟨B, hB, ?_⟩
  intro u hu hb c δ hδ hgap k hk
  let old := pureTuple m k u
  let hold := pureTuple_isHermitianPSH (N := m) hu k
  let hbold := pureTuple_bounded (N := m) hb k
  let E : Set M := {x | u x < (c : EReal)}
  let S : ℝ := ∑ j ∈ Finset.range (m + 1), pureTraceMass omega hu hb E j
  have hvalues : ∀ i, old i = u ∨ old i = fun _ => 0 := by
    intro i
    dsimp only [old, pureTuple]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hbudget (i : Fin C.outer.count) :
      patchProperBudget (C.patch i) old hold hbold
        (comparisonSublevel (C.patch i) u c ∩ tsupport (C.weight i)) ≤ L * S := by
    exact properCorrectedTraceBudget_le_pureTrace_sum (C.patch i) hu hb old hold hbold hvalues
      (comparisonSublevel (C.patch i) u c ∩ tsupport (C.weight i)) E
      (fun z hz => hz.1.1) (fun z hz => hz.1.2) A hA
      (fun z hz => (hdom i z hz).1) (fun z hz => (hdom i z hz).2)
  have htor : torsionDifference C old hold hbold u (fun _ => (c : EReal)) ≤ δ * B * S := by
    calc
      _ ≤ |torsionDifference C old hold hbold u (fun _ => (c : EReal))| := le_abs_self _
      _ ≤ ∑ i, b i * δ * patchProperBudget (C.patch i) old hold hbold
          (comparisonSublevel (C.patch i) u c ∩ tsupport (C.weight i)) :=
        hbound old hold hbold hu hb c hδ hgap
      _ ≤ ∑ i, b i * δ * (L * S) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hbudget i) (mul_nonneg (hbpos i) hδ)
      _ = (∑ i, b i) * (δ * (L * S)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = δ * B * S := by dsimp only [B]; ring
  exact (pureTraceMass_le_succ_add_torsion C hu hb c hδ hgap k hk).trans
    (add_le_add (le_refl _) htor)

end SGPT.PSH.HermitianComparison
