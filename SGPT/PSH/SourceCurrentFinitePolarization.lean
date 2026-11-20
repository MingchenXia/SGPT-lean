import SGPT.PSH.SourceCurrentMixedIVolumeAlgebra
import SGPT.Foundations.Analysis.Pending.PolarizationAlgebra
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
Static draft during the cache no-Lean freeze. Not compiled or adopted.

Finite polarization is derived for ACTUAL source mixed I-volumes. The
additive cone below is exactly the three original whole-current predicates;
it adds no realization or equality-to-goal certificate. Natural-number
multilinearity suffices: negative currents are never introduced.
-/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.VariableComplexAtlas

open Set Filter MeasureTheory
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending GlobalPositiveCurrentACRestriction CanonicalCurrentFrame
open scoped Topology BigOperators ENNReal

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

local notation "Cur" => GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m))

/-- The actual additive cone of original closed positive (1,1)-currents. -/
def sourcePositiveCurrentCone : AddSubmonoid Cur where
  carrier := {T | T.IsClosed (canonicalBasis (m + 1)) ∧
    T.IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧ IsFullPositive T}
  zero_mem' := by
    refine ⟨GlobalCurrent.isClosed_zero _, ?_, ?_⟩
    · intro e v w
      simp only [GlobalCurrent.coefficients_zero]
      rfl
    · intro e α hα
      simpa only [GlobalCurrent.inChart_zero, _root_.zero_apply] using
        (le_refl (0 : ℝ))
  add_mem' := by
    intro S T hS hT
    refine ⟨hS.1.add _ hT.1, hS.2.1.add _ hT.2.1, ?_⟩
    intro e α hα
    simpa only [GlobalCurrent.inChart_add, _root_.add_apply] using
      add_nonneg (hS.2.2 e α hα) (hT.2.2 e α hα)

local notation "Pos" => (sourcePositiveCurrentCone (m := m) (M := M))

private theorem sourcePositiveCurrent_coe_update (T : Fin (m + 1) → Pos)
    (a : Fin (m + 1)) (S : Pos) :
    (fun i => (Function.update T a S i).val) =
      Function.update (fun i => (T i).val) a S.val := by
  classical
  funext i
  by_cases hi : i = a
  · subst i; simp only [Function.update_self]
  · simp only [Function.update_of_ne hi]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [ConnectedSpace M]

/-- Realification of the genuine existing ORIGINAL-current quantity.
Its finite value is already established by sourceCurrentMixedIVolume_lt_top. -/
def sourcePositiveCurrentMixedReal (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → Pos) : ℝ :=
  (sourceCurrentMixedIVolume ω (fun i => (T i).val)
    (fun i => (T i).property.1) (fun i => (T i).property.2.1)
    (fun i => (T i).property.2.2)).toReal

private theorem sourcePositiveCurrentMixedReal_add_slot
    (ω : KahlerBackground (m + 1) M) (T : Fin (m + 1) → Pos)
    (a : Fin (m + 1)) (S : Pos) :
    sourcePositiveCurrentMixedReal ω (Function.update T a (T a + S)) =
      sourcePositiveCurrentMixedReal ω T +
        sourcePositiveCurrentMixedReal ω (Function.update T a S) := by
  classical
  obtain ⟨hAc, hA11, hAp, h⟩ := sourceCurrentMixedIVolume_add_slot ω
    (fun i => (T i).val) (fun i => (T i).property.1)
    (fun i => (T i).property.2.1) (fun i => (T i).property.2.2)
    a S.val S.property.1 S.property.2.1 S.property.2.2
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add
    (ne_of_lt (sourceCurrentMixedIVolume_lt_top ω _ _ _ _))
    (ne_of_lt (sourceCurrentMixedIVolume_lt_top ω _ _ _ _))] at hreal
  simpa only [sourcePositiveCurrentMixedReal, sourcePositiveCurrent_coe_update,
    AddSubmonoid.coe_add] using hreal

private theorem sourcePositiveCurrentMixedReal_update_add
    (ω : KahlerBackground (m + 1) M) (T : Fin (m + 1) → Pos)
    (a : Fin (m + 1)) (S U : Pos) :
    sourcePositiveCurrentMixedReal ω (Function.update T a (S + U)) =
      sourcePositiveCurrentMixedReal ω (Function.update T a S) +
        sourcePositiveCurrentMixedReal ω (Function.update T a U) := by
  classical
  simpa only [Function.update_self, Function.update_idem] using
    sourcePositiveCurrentMixedReal_add_slot ω (Function.update T a S) a U

private theorem sourcePositiveCurrentMixedReal_update_zero
    (ω : KahlerBackground (m + 1) M) (T : Fin (m + 1) → Pos)
    (a : Fin (m + 1)) :
    sourcePositiveCurrentMixedReal ω (Function.update T a 0) = 0 := by
  have h := sourcePositiveCurrentMixedReal_update_add ω T a 0 0
  simp only [zero_add] at h
  linarith

private theorem sourcePositiveCurrentMixedReal_update_nsmul
    (ω : KahlerBackground (m + 1) M) (T : Fin (m + 1) → Pos)
    (a : Fin (m + 1)) (c : ℕ) (S : Pos) :
    sourcePositiveCurrentMixedReal ω (Function.update T a (c • S)) =
      c • sourcePositiveCurrentMixedReal ω (Function.update T a S) := by
  induction c with
  | zero => simp only [zero_nsmul, sourcePositiveCurrentMixedReal_update_zero]
  | succ c ih =>
    rw [succ_nsmul, sourcePositiveCurrentMixedReal_update_add, ih, succ_nsmul]

/-- The actual positive-current mixed I-volume is a natural-number
multilinear map on the genuine additive cone. -/
def sourcePositiveCurrentMixedNatMultilinear (ω : KahlerBackground (m + 1) M) :
    MultilinearMap ℕ (fun _ : Fin (m + 1) => Pos) ℝ :=
  MultilinearMap.mk' (sourcePositiveCurrentMixedReal ω)
    (sourcePositiveCurrentMixedReal_update_add ω)
    (sourcePositiveCurrentMixedReal_update_nsmul ω)

theorem sourcePositiveCurrentMixedReal_perm (ω : KahlerBackground (m + 1) M)
    (T : Fin (m + 1) → Pos) (σ : Equiv.Perm (Fin (m + 1))) :
    sourcePositiveCurrentMixedReal ω (fun i => T (σ i)) =
      sourcePositiveCurrentMixedReal ω T := by
  exact congrArg ENNReal.toReal
    (sourceCurrentMixedIVolume_perm ω (fun i => (T i).val)
      (fun i => (T i).property.1) (fun i => (T i).property.2.1)
      (fun i => (T i).property.2.2) σ)

/-- The actual subset sum of positive currents expands into actual source
mixed I-volumes, with every dependent domain manufactured by the cone. -/
theorem sourcePositiveCurrentMixedReal_diagonal_sum
    (ω : KahlerBackground (m + 1) M) (T : Fin (m + 1) → Pos)
    (S : Finset (Fin (m + 1))) :
    sourcePositiveCurrentMixedReal ω (fun _ => ∑ j ∈ S, T j) =
      ∑ g : Fin (m + 1) → Fin (m + 1) with ∀ j, g j ∈ S,
        sourcePositiveCurrentMixedReal ω (fun i => T (g i)) := by
  classical
  have h := (sourcePositiveCurrentMixedNatMultilinear ω).map_sum_finset
    (fun _ (j : Fin (m + 1)) => T j) (fun _ => S)
  change sourcePositiveCurrentMixedReal ω (fun _ => ∑ j ∈ S, T j) =
    ∑ g ∈ Fintype.piFinset (fun _ : Fin (m + 1) => S),
      sourcePositiveCurrentMixedReal ω (fun i => T (g i)) at h
  convert h using 1
  apply Finset.sum_congr
  · ext g; simp [Fintype.mem_piFinset]
  · intro g _; rfl

/-- Actual whole-current mixed I-volume is recovered from the ORIGINAL
single-I-volume diagonal values of its finite subset sums. No equality
with NP mass or a geometric mixed-volume quantity is an input. -/
theorem factorial_mul_sourcePositiveCurrentMixedReal_eq_diagonal_polarization
    (ω : KahlerBackground (m + 1) M) (T : Fin (m + 1) → Pos) :
    ((m + 1).factorial : ℝ) * sourcePositiveCurrentMixedReal ω T =
      ∑ S : Finset (Fin (m + 1)), (-1 : ℝ) ^ (m + 1 - S.card) *
        sourcePositiveCurrentMixedReal ω (fun _ => ∑ j ∈ S, T j) := by
  classical
  let d : (Fin (m + 1) → Fin (m + 1)) → ℝ := fun g =>
    sourcePositiveCurrentMixedReal ω (fun i => T (g i))
  have hd (σ : Equiv.Perm (Fin (m + 1))) : d σ = d id :=
    sourcePositiveCurrentMixedReal_perm ω T σ
  have h := SGPT.Foundations.Analysis.Pending.PolarizationAlgebra.sum_powerset_signed_eq_factorial_mul d hd
  simp_rw [sourcePositiveCurrentMixedReal_diagonal_sum]
  simpa only [d, id_eq] using h.symm

end SGPT.PSH.VariableComplexAtlas
