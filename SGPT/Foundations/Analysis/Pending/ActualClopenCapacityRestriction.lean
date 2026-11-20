import SGPT.Foundations.Analysis.Pending.OpensRestrictionMeasure
import SGPT.Foundations.Analysis.Pending.ThetaCapacity

set_option autoImplicit false

/-! # Actual capacity control on compact clopen submanifolds

Every genuine restricted capacity competitor glues to zero on the
open complement. Actual diagonal measure restriction then controls its
mass by the actual ambient capacity. Empty submanifolds are handled
before invoking the nonempty restricted-measure producer.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.ActualClopenCapacityRestriction

open FirstPass FirstPass.PositiveClasses OpensRestriction OpensRestrictionMeasure
  ThetaCapacity DiagonalMass

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]


/-- Actual clopen gluing of every restricted competitor and genuine measure
restriction produce ambient control of the restricted capacity. -/
theorem thetaCapacity_restrict_le (omega : KahlerBackground n M)
    (U : Opens M) (hU : IsClopen (U : Set M)) {S : Set M} (hS : MeasurableSet S) :
    let _ : CompactSpace U := compactSpace_of_isClopen hU
    thetaCapacity (restrictKahler U omega).form (fun _ => 0) (Subtype.val ⁻¹' S) ≤
      thetaCapacity omega.form (fun _ => 0) S := by
  classical
  let _ : CompactSpace U := compactSpace_of_isClopen hU
  change thetaCapacity (restrictKahler U omega).form (fun _ => 0) (Subtype.val ⁻¹' S) ≤
    thetaCapacity omega.form (fun _ => 0) S
  cases isEmpty_or_nonempty U with
  | inl hE =>
      let _ := hE
      have hpre : (Subtype.val : U → M) ⁻¹' S = ∅ :=
        eq_empty_of_forall_notMem fun y _ => isEmptyElim y
      rw [hpre, thetaCapacity_empty]
      exact bot_le
  | inr hN =>
      let _ := hN
      apply thetaCapacity_le_of_forall
      intro f hf hf0 hflb
      have hzero := (LocalPotentials.isThetaPshPotential_zero_iff omega.form).mpr omega.isSemipositive
      let g : M → EReal := (U : Set M).piecewise (extendBot f) (fun _ => 0)
      have hres : (fun y : U => g y) = f := by
        funext y
        simp only [g, Set.piecewise_eq_of_mem (U : Set M) (extendBot f) (fun _ => 0) y.2,
          extendBot_val]
      have hg : IsThetaPshPotential omega.form.val g := by
        refine ⟨thetaPlurisubharmonic_piecewise hU ?_ hzero.1,
          locallyNondegenerate_piecewise hU ?_ hzero.2⟩
        · change ThetaPlurisubharmonic (restrictForm U omega.form).val
            (fun y : U => extendBot f y)
          simpa only [extendBot_val, restrictKahler_form] using hf.1
        · simpa only [extendBot_val] using hf.2
      have hg0 : g ≤ (fun _ => 0) := by
        intro x
        by_cases hx : x ∈ (U : Set M)
        · change (U : Set M).piecewise (extendBot f) (fun _ => 0) x ≤ 0
          rw [Set.piecewise_eq_of_mem _ _ _ hx]
          exact (extendBot_val f ⟨x, hx⟩) ▸ hf0 ⟨x, hx⟩
        · simp only [g, Set.piecewise_eq_of_notMem _ _ _ hx]
          exact le_rfl
      have hglb : ∀ x, (0 : EReal) ≤ g x + 1 := by
        intro x
        by_cases hx : x ∈ (U : Set M)
        · change (0 : EReal) ≤ (U : Set M).piecewise (extendBot f) (fun _ => 0) x + 1
          rw [Set.piecewise_eq_of_mem _ _ _ hx]
          exact (extendBot_val f ⟨x, hx⟩) ▸ hflb ⟨x, hx⟩
        · simp only [g, Set.piecewise_eq_of_notMem _ _ _ hx, zero_add]
          exact zero_le_one
      have hm : diagonalPotentialMeasure (restrictKahler U omega).form f hf
          (Subtype.val ⁻¹' S) = diagonalPotentialMeasure omega.form g hg (S ∩ U) := by
        have hh := diagonalPotentialMeasure_restrict_apply (U := U) hg hS
        simpa only [restrictKahler_form, hres] using hh
      rw [hm]
      exact (measure_mono inter_subset_left).trans
        (diagonalPotentialMeasure_le_thetaCapacity hg hg0 hglb S)

end
end SGPT.Foundations.Analysis.Pending.ActualClopenCapacityRestriction
