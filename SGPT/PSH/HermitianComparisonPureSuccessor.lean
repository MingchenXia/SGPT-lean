import SGPT.PSH.HermitianComparisonPureTraces
import SGPT.PSH.HermitianGlobalProductConstants
import SGPT.PSH.HermitianConstantComparison
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Canonical distinguished-factor identities for the pure traces

The old tuple has its first `k` entries equal to the original bounded
potential and all other entries zero. Adding the same potential gives
the next pure trace; adding a constant gives the current pure trace.
These are equalities of the actual canonical measures on every set.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianComparisonPureTraces

open Set MeasureTheory TopologicalSpace
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open Hermitian HermitianGlobalProducts HermitianExtremalCurrentAlgebra HermitianExtremal
open scoped Topology

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]
  {omega : Background (m + 1) M}

theorem cons_isHermitianPSH {N : ℕ} {a : M → EReal} {v : Fin N → M → EReal}
    (ha : IsHermitianPSH omega a) (hv : ∀ i, IsHermitianPSH omega (v i)) :
    ∀ i, IsHermitianPSH omega (Fin.cons (α := fun _ : Fin (N + 1) => M → EReal) a v i) :=
  Fin.cases ha hv

omit [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M] in
theorem cons_bounded {N : ℕ} {a : M → EReal} {v : Fin N → M → EReal}
    (ha : ∃ b c : ℝ, ∀ x, (b : EReal) ≤ a x ∧ a x ≤ (c : EReal))
    (hv : ∀ i, ∃ b c : ℝ, ∀ x, (b : EReal) ≤ v i x ∧ v i x ≤ (c : EReal)) :
    ∀ i, ∃ b c : ℝ, ∀ x, (b : EReal) ≤ Fin.cons (α := fun _ : Fin (N + 1) => M → EReal) a v i x ∧ Fin.cons (α := fun _ : Fin (N + 1) => M → EReal) a v i x ≤ (c : EReal) :=
  Fin.cases ha hv

theorem cons_self_pureTuple {Z : Type*} (m k : ℕ) (a b : Z) :
    Fin.cons (α := fun _ : Fin (m + 1) => Z) a (fun i : Fin m => if i.val < k then a else b) =
      fun i : Fin (m + 1) => if i.val < k + 1 then a else b := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.cons_succ, Fin.val_succ, Nat.add_lt_add_iff_right]

theorem cons_zero_pureTuple_rotate {Z : Type*} (m k : ℕ) (hk : k ≤ m) (a b : Z) :
    (fun i => Fin.cons (α := fun _ : Fin (m + 1) => Z) b (fun j : Fin m => if j.val < k then a else b) (finRotate (m + 1) i)) =
      fun i : Fin (m + 1) => if i.val < k then a else b := by
  rw [← Fin.snoc_eq_cons_rotate]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, Fin.val_last, not_lt.mpr hk, if_false]
  · simp only [Fin.snoc_castSucc, Fin.val_castSucc]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- Adding the original potential to its old prefix tuple gives the next
actual canonical pure trace, with no ordering certificate supplied. -/
theorem cons_self_measure_eq_pureTraceMeasure_succ {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (k : ℕ) :
    globalMixedMeasure omega (Fin.cons (α := fun _ : Fin (m + 1) => M → EReal) u (pureTuple m k u))
      (cons_isHermitianPSH hu (pureTuple_isHermitianPSH hu k))
      (cons_bounded hb (pureTuple_bounded hb k)) = pureTraceMeasure omega hu hb (k + 1) := by
  apply globalMixedMeasure_congr_tuple
  exact cons_self_pureTuple m k u (fun _ : M => (0 : EReal))

/-- A zero distinguished factor rotates to the complementary zero slot;
the actual canonical measure is the same current pure trace. -/
theorem cons_zero_measure_eq_pureTraceMeasure {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (k : ℕ) (hk : k ≤ m) :
    globalMixedMeasure omega (Fin.cons (α := fun _ : Fin (m + 1) => M → EReal) (fun _ => (0 : EReal)) (pureTuple m k u))
      (cons_isHermitianPSH (isHermitianPSH_zero omega) (pureTuple_isHermitianPSH hu k))
      (cons_bounded ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩ (pureTuple_bounded hb k)) =
      pureTraceMeasure omega hu hb k := by
  have h := globalMixedMeasure_comp_perm
    (Fin.cons (α := fun _ : Fin (m + 1) => M → EReal) (fun _ => (0 : EReal)) (pureTuple m k u))
    (cons_isHermitianPSH (isHermitianPSH_zero omega) (pureTuple_isHermitianPSH hu k))
    (cons_bounded ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩ (pureTuple_bounded hb k))
    (finRotate (m + 1))
  exact h.symm.trans (globalMixedMeasure_congr_tuple _ _ _ _
    (cons_zero_pureTuple_rotate m k hk u (fun _ : M => (0 : EReal))))

/-- A finite constant distinguished factor gives exactly the same actual
pure trace as the zero distinguished factor. -/
theorem cons_const_measure_eq_pureTraceMeasure {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (k : ℕ) (hk : k ≤ m) (c : ℝ) :
    globalMixedMeasure omega (Fin.cons (α := fun _ : Fin (m + 1) => M → EReal) (fun _ => (c : EReal)) (pureTuple m k u))
      (cons_isHermitianPSH
        (HermitianBoundedMass.isFormPSH_const omega.isTypeOneOne omega.isSemipositive c)
        (pureTuple_isHermitianPSH hu k))
      (cons_bounded ⟨c, c, fun _ => ⟨le_rfl, le_rfl⟩⟩ (pureTuple_bounded hb k)) =
      pureTraceMeasure omega hu hb k := by
  let v := Fin.cons (α := fun _ : Fin (m + 1) => M → EReal) (fun _ : M => (0 : EReal)) (pureTuple m k u)
  let hv := cons_isHermitianPSH (N := m) (isHermitianPSH_zero omega) (pureTuple_isHermitianPSH hu k)
  let hvb := cons_bounded (N := m) ⟨0, 0, fun _ => ⟨le_rfl, le_rfl⟩⟩ (pureTuple_bounded hb k)
  let d : Fin (m + 1) → ℝ := Fin.cons (α := fun _ : Fin (m + 1) => ℝ) c (fun _ => 0)
  have hshift := globalMixedMeasure_add_constants v hv hvb d
  have heq : Fin.cons (α := fun _ : Fin (m + 1) => M → EReal) (fun _ => (c : EReal)) (pureTuple m k u) =
      fun i x => v i x + (d i : EReal) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · funext x
      exact (zero_add (c : EReal)).symm
    · funext x
      exact (add_zero (pureTuple m k u j x)).symm
  exact (globalMixedMeasure_congr_tuple _ _ _ _ heq).trans
    (hshift.trans (cons_zero_measure_eq_pureTraceMeasure hu hb k hk))

omit [BorelSpace M] in
theorem cons_self_mass_eq_pureTraceMass_succ {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (k : ℕ) (E : Set M) :
    (globalMixedMeasure omega (Fin.cons (α := fun _ : Fin (m + 1) => M → EReal) u (pureTuple m k u))
      (cons_isHermitianPSH hu (pureTuple_isHermitianPSH hu k))
      (cons_bounded hb (pureTuple_bounded hb k)) E).toReal = pureTraceMass omega hu hb E (k + 1) :=
  congrArg (fun ν : Measure M => (ν E).toReal) (cons_self_measure_eq_pureTraceMeasure_succ hu hb k)

theorem cons_const_mass_eq_pureTraceMass {u : M → EReal}
    (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal))
    (k : ℕ) (hk : k ≤ m) (c : ℝ) (E : Set M) :
    (globalMixedMeasure omega (Fin.cons (α := fun _ : Fin (m + 1) => M → EReal) (fun _ => (c : EReal)) (pureTuple m k u))
      (cons_isHermitianPSH
        (HermitianBoundedMass.isFormPSH_const omega.isTypeOneOne omega.isSemipositive c)
        (pureTuple_isHermitianPSH hu k))
      (cons_bounded ⟨c, c, fun _ => ⟨le_rfl, le_rfl⟩⟩ (pureTuple_bounded hb k)) E).toReal =
      pureTraceMass omega hu hb E k :=
  congrArg (fun ν : Measure M => (ν E).toReal) (cons_const_measure_eq_pureTraceMeasure hu hb k hk c)

end SGPT.PSH.HermitianComparisonPureTraces
