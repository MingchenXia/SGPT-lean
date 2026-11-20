import SGPT.Foundations.Analysis.Pending.ActualClopenCapacityRestriction
import SGPT.Foundations.Analysis.Pending.ActualConnectedCapacityUpperBound

set_option autoImplicit false

/-! # Genuine capacity convergence bounds every component

Actual clopen restricted capacity control gives the true connected
upper bound on each component. Compactness chooses a finite component
open cover; their actual eventual bounds yield one ambient real bound.
No connectedness, nonempty or caller uniform-bound field is used.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology BigOperators

namespace SGPT.Foundations.Analysis.Pending.ActualCapacityUpperBound

open FirstPass FirstPass.PositiveClasses OpensRestriction OpensRestrictionMeasure ThetaCapacity

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]


/-- Genuine capacity convergence internally gives one eventual everywhere
upper bound, including empty and disconnected compact complex ambients. -/
theorem exists_eventual_upper_bound (omega : KahlerBackground n M)
    {α : ClosedRealOneOneForm n M} {I : Type*} {F : Filter I}
    {u : I → M → EReal} {v : M → EReal}
    (hu : ∀ j, IsThetaPshPotential α.val (u j)) (hv : IsThetaPshPotential α.val v)
    (hcap : ∀ a : ℝ, 0 < a → Tendsto (fun j => thetaCapacity omega.form (fun _ => 0)
      {x | u j x ≠ ⊥ ∧ v x ≠ ⊥ ∧ a < |(u j x).toReal - (v x).toReal|}) F (𝓝 0)) :
    ∃ H : ℝ, ∀ᶠ j in F, ∀ x, u j x ≤ (H : EReal) := by
  classical
  let _ : LocallyConnectedSpace M := OpensRestrictionMeasure.locallyConnectedSpace n M
  have hcomponent (x : M) : ∃ H : ℝ, ∀ᶠ j in F,
      ∀ y ∈ (componentOpens x : Set M), u j y ≤ (H : EReal) := by
    let U := componentOpens x
    have hU : IsClopen (U : Set M) := isClopen_componentOpens x
    let _ : CompactSpace U := compactSpace_of_isClopen hU
    let huU : ∀ j, IsThetaPshPotential (restrictForm U α).val (fun y : U => u j y) :=
      fun j => isThetaPshPotential_restrict (hu j)
    let hvU : IsThetaPshPotential (restrictForm U α).val (fun y : U => v y) :=
      isThetaPshPotential_restrict hv
    have hcapU : ∀ a : ℝ, 0 < a → Tendsto (fun j =>
        thetaCapacity (restrictKahler U omega).form (fun _ => 0)
          {y : U | u j y ≠ ⊥ ∧ v y ≠ ⊥ ∧ a < |(u j y).toReal - (v y).toReal|})
        F (𝓝 0) := by
      intro a ha
      have hmeas (j : I) : MeasurableSet
          {y : M | u j y ≠ ⊥ ∧ v y ≠ ⊥ ∧ a < |(u j y).toReal - (v y).toReal|} := by
        have hum : Measurable (u j) := (hu j).1.quasiPlurisubharmonic.upperSemicontinuous.measurable
        have hvm : Measurable v := hv.1.quasiPlurisubharmonic.upperSemicontinuous.measurable
        have hgap : Measurable (fun y => |(u j y).toReal - (v y).toReal|) := by
          simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hum.ereal_toReal.sub hvm.ereal_toReal).norm
        exact (measurableSet_eq_fun hum measurable_const).compl.inter
          ((measurableSet_eq_fun hvm measurable_const).compl.inter
            (measurableSet_lt measurable_const hgap))
      have hle (j : I) : thetaCapacity (restrictKahler U omega).form (fun _ => 0)
          {y : U | u j y ≠ ⊥ ∧ v y ≠ ⊥ ∧ a < |(u j y).toReal - (v y).toReal|} ≤
          thetaCapacity omega.form (fun _ => 0)
            {y : M | u j y ≠ ⊥ ∧ v y ≠ ⊥ ∧ a < |(u j y).toReal - (v y).toReal|} := by
        have hh := ActualClopenCapacityRestriction.thetaCapacity_restrict_le
          (n := n) (M := M) omega U hU
          (S := {y : M | u j y ≠ ⊥ ∧ v y ≠ ⊥ ∧ a < |(u j y).toReal - (v y).toReal|})
          (hmeas j)
        change thetaCapacity (restrictKahler U omega).form (fun _ => 0)
          ((Subtype.val : U → M) ⁻¹'
            {y : M | u j y ≠ ⊥ ∧ v y ≠ ⊥ ∧ a < |(u j y).toReal - (v y).toReal|}) ≤ _ at hh
        exact hh
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hcap a ha)
        (fun _ => bot_le) hle
    obtain ⟨H, hH⟩ := ActualConnectedCapacityUpperBound.exists_eventual_upper_bound
      (n := n) (M := U) (α := restrictForm U α) (I := I) (F := F)
      (u := fun j (y : U) => u j y) (v := fun y : U => v y)
      (restrictKahler U omega) huU hvU hcapU
    exact ⟨H, hH.mono fun j hj y hy => hj ⟨y, hy⟩⟩
  choose H hH using hcomponent
  have hcover : (univ : Set M) ⊆ ⋃ x : M, (componentOpens x : Set M) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_componentOpens x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (componentOpens x : Set M))
    (fun x => (componentOpens x).isOpen) hcover
  have hAll : ∀ᶠ j in F, ∀ x ∈ s, ∀ y ∈ (componentOpens x : Set M), u j y ≤ (H x : EReal) :=
    (eventually_all_finset s).mpr fun x _ => hH x
  refine ⟨∑ x ∈ s, |H x|, hAll.mono fun j hj y => ?_⟩
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ y))
  obtain ⟨hxS, hy⟩ := mem_iUnion.mp hx
  exact (hj x hxS y hy).trans (EReal.coe_le_coe_iff.mpr
    ((le_abs_self (H x)).trans (Finset.single_le_sum (fun z _ => abs_nonneg (H z)) hxS)))

end
end SGPT.Foundations.Analysis.Pending.ActualCapacityUpperBound
