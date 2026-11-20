import SGPT.Foundations.Analysis.Pending.ActualBoundedMixedCapacityDomination
import SGPT.Foundations.Analysis.Pending.TraceFreeLimit
import SGPT.Foundations.Analysis.Pending.GlobalMaxLocality
import SGPT.Foundations.Analysis.Pending.GlobalSlotComparison

set_option autoImplicit false

/-! # Actual unbounded mixed measures do not charge capacity-zero sets

Independent background enlargement and bounded maximum truncation give the
capacity-null ingredient for the original quasicontinuous-weight argument.
No global boundedness, Connected, Nonempty, n>0 or Big premise is imposed.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.ActualMixedCapacityZeroNull

open FirstPass FirstPass.PositiveClasses GlobalNonPluripolar ThetaCapacity
  GlobalMaxLocality GlobalSlotComparison

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M]

/-- Arbitrary capacity-zero sets are null for the actual mixed product of
genuine potentials in independent arbitrary closed backgrounds. -/
theorem globalMixedMeasure_eq_zero_of_capacity_eq_zero (omega : KahlerBackground n M)
    {θ : Fin n → ClosedRealOneOneForm n M} {u : Fin n → M → EReal}
    (hu : ∀ i, IsThetaPshPotential (θ i).val (u i)) {E : Set M}
    (hE : thetaCapacity omega.form (fun _ => 0) E = 0) :
    globalMixedMeasure θ u (fun i => (hu i).1) E = 0 := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · have he : E = ∅ := eq_empty_iff_forall_notMem.mpr fun x => isEmptyElim x
    simp only [he, measure_empty]
  choose A hA hα using fun i => KahlerDomination.exists_pos_isSemipositive_add_smul omega (θ i)
  let σ : Fin n → ClosedRealOneOneForm n M := fun i => A i • omega.form
  let α : Fin n → ClosedRealOneOneForm n M := fun i => θ i + σ i
  have hσ : ∀ i, (σ i).val.IsSemipositive := fun i =>
    KahlerDomination.isSemipositive_smul omega.isSemipositive (hA i).le
  have huα : ∀ i, IsThetaPshPotential (α i).val (u i) := fun i =>
    LocalPotentials.isThetaPshPotential_add_of_semipositive (hu i) (hσ i)
  have hmono : globalMixedMeasure θ u (fun i => (hu i).1) ≤
      globalMixedMeasure α u (fun i => (huα i).1) :=
    TraceFreeLimit.globalMixedMeasure_le_of_add_semipositive hσ hu (fun i => (huα i).1)
  let ν : Measure M := globalMixedMeasure α u (fun i => (huα i).1)
  choose C hC using fun i => (huα i).exists_global_upper_bound
  let S (k : ℕ) : Set M := {x | ∀ i, ((-(k : ℝ)) : EReal) < u i x}
  have hSk : ∀ k, ν (E ∩ S k) = 0 := by
    intro k
    let w : Fin n → M → EReal := fun _ _ => ((-(k : ℝ)) : EReal)
    have hw : ∀ i, IsThetaPshPotential (α i).val (w i) := by
      intro i
      have hz := (LocalPotentials.isThetaPshPotential_zero_iff (α i)).mpr (hα i)
      simpa only [w, zero_sub, EReal.coe_neg] using hz.sub_const (k : ℝ)
    have hm : ∀ i, IsThetaPshPotential (α i).val (fun x => max (u i x) (w i x)) :=
      fun i => IsThetaPshPotential.max (huα i) (hw i)
    let B : ℝ := (k : ℝ) + (∑ i, |C i|) + 1
    have hs : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hb : ∀ i x, ((-B : ℝ) : EReal) ≤ max (u i x) (w i x) ∧
        max (u i x) (w i x) ≤ (B : EReal) := by
      intro i x
      have hci : |C i| ≤ ∑ i, |C i| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ i)
      have hkB : -(k : ℝ) ≤ B := by dsimp [B]; linarith [Nat.cast_nonneg (α := ℝ) k]
      have hklo : -B ≤ -(k : ℝ) := by dsimp [B]; linarith
      have hCi : C i ≤ B := by dsimp [B]; linarith [le_abs_self (C i)]
      exact ⟨(EReal.coe_le_coe_iff.mpr hklo).trans (le_max_right _ _),
        max_le ((hC i x).trans (EReal.coe_le_coe_iff.mpr hCi)) (EReal.coe_le_coe_iff.mpr hkB)⟩
    obtain ⟨K, _hK, hdom⟩ :=
      ActualBoundedMixedCapacityDomination.exists_uniform_capacity_bound omega α B hB
    have hmE : globalMixedMeasure α (fun i x => max (u i x) (w i x))
        (fun i => (hm i).1) E = 0 := by
      apply le_antisymm _ zero_le
      simpa only [hE, mul_zero] using hdom _ hm hb E
    have hSm : MeasurableSet (S k) :=
      measurableSet_forall_lt (fun i => (huα i).1) (fun i => (hw i).1)
    have hloc := congrArg (fun μ : Measure M => μ E)
      (globalMixedMeasure_restrict_max_eq (fun i => (huα i).1)
        (fun i => (hw i).1) (fun i => (hm i).1))
    rw [Measure.restrict_apply' hSm, Measure.restrict_apply' hSm] at hloc
    exact hloc.symm.trans (measure_mono_null inter_subset_left hmE)
  have hbad : ν (⋃ k, E ∩ S k) = 0 := measure_iUnion_null hSk
  have hpole : ν (⋃ i, {x | u i x = ⊥}) = 0 :=
    measure_iUnion_null fun i => globalMixedMeasure_pole_null (fun i => (huα i).1) i
  have hcover : E ⊆ (⋃ k, E ∩ S k) ∪ (⋃ i, {x | u i x = ⊥}) := by
    intro x hx
    by_cases hp : ∃ i, u i x = ⊥
    · exact Or.inr (mem_iUnion.mpr hp)
    have hf : ∀ i, u i x ≠ ⊥ := fun i hi => hp ⟨i, hi⟩
    obtain ⟨k, hk⟩ := exists_nat_gt (∑ i, |(u i x).toReal|)
    have hxS : x ∈ S k := by
      intro i
      have hi : |(u i x).toReal| ≤ ∑ j, |(u j x).toReal| :=
        Finset.single_le_sum (fun j _ => abs_nonneg ((u j x).toReal)) (Finset.mem_univ i)
      have hr : -(k : ℝ) < (u i x).toReal := by linarith [neg_abs_le ((u i x).toReal)]
      rw [← EReal.coe_toReal ((huα i).1.quasiPlurisubharmonic.ne_top x) (hf i)]
      exact EReal.coe_lt_coe_iff.mpr hr
    exact Or.inl (mem_iUnion.mpr ⟨k, hx, hxS⟩)
  have hνE : ν E = 0 := le_antisymm ((measure_mono hcover).trans
    ((measure_union_le _ _).trans (by simp only [hbad, hpole, add_zero, le_refl]))) zero_le
  exact le_antisymm ((hmono E).trans hνE.le) zero_le

end
end SGPT.Foundations.Analysis.Pending.ActualMixedCapacityZeroNull
