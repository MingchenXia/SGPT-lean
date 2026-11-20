import SGPT.Projective.NativeCIPeriodAlgebra
import SGPT.Projective.NumEqNSQuadratic

/-! Actual original terminal base degree, literal original positive-power
recursion and literal Hodge tuples for whole complete intersections. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft

namespace WholeNativeCITower

/-- The actual zero-cut terminal is the SAME original curve, and its
degree is the original single-slot integral by actual identity pullback. -/
theorem terminal_degree_base (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel 1) X] [IsComplexManifold 1 X] [CompactSpace X]
    {P : Fin 0 → NativePositiveLine 1 X} (T : WholeNativeCITower 0 X P)
    (κ : KahlerBackground 1 X) (alpha : ClosedRealOneOneForm 1 X) :
    let : MeasurableSpace X := borel X
    let : BorelSpace X := ⟨rfl⟩
    degreeAlong (terminal 0 X T κ).background (terminal 0 X T κ).inclusion.contMDiff alpha =
      slotIntegral κ (Fin.cons alpha Fin.elim0) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  dsimp only
  rw [terminal]
  apply slotIntegral_eq_of_bottChernRel κ
  intro i
  fin_cases i
  exact ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
    (SmoothRealForm.pullback_id_geometricallyEq alpha.val)

/-- Literal product recursion for the powers of the SAME first cut and
the SAME actual restricted tail, with no period equality premise. -/
theorem powers_real_prod_succ (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 2)) X] [IsComplexManifold (k + 2) X]
    {P : Fin (k + 1) → NativePositiveLine (k + 2) X} (T : WholeNativeCITower (k + 1) X P) :
    let D := T.1
    let : ChartedSpace (ComplexModel (k + 1)) D.carrier := D.carrierCharts
    let : IsComplexManifold (k + 1) D.carrier := D.carrierComplex
    (∏ i, (powers (k + 1) T i : ℝ)) =
      (D.power : ℝ) * ∏ i, (powers k T.2 i : ℝ) := by
  dsimp only
  let D := T.1
  let : ChartedSpace (ComplexModel (k + 1)) D.carrier := D.carrierCharts
  let : IsComplexManifold (k + 1) D.carrier := D.carrierComplex
  simp only [Fin.prod_univ_succ, powers, Fin.cons_zero, Fin.cons_succ]

end WholeNativeCITower

variable {m : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel (m + 2)) X] [IsComplexManifold (m + 2) X]

/-- The original first Hodge tuple is literally the actual first test
form followed by the unchanged original background. -/
theorem oneSlot_eq_cons (κ : KahlerBackground (m + 2) X)
    (alpha : ClosedRealOneOneForm (m + 2) X) :
    oneSlot κ alpha = Fin.cons alpha (fun _ : Fin (m + 1) => κ.form) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [oneSlot]
  · simp [oneSlot]

/-- The original updated second Hodge slot is literally the SAME two
original test forms followed by the unchanged original background. -/
theorem update_oneSlot_eq_cons (κ : KahlerBackground (m + 2) X)
    (alpha theta : ClosedRealOneOneForm (m + 2) X) :
    Function.update (oneSlot κ alpha) 1 theta =
      Fin.cons alpha (Fin.cons theta (fun _ : Fin m => κ.form)) := by
  classical
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [oneSlot]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [oneSlot]
    · have h0 : j.succ.succ ≠ (0 : Fin (m + 2)) := by simp
      have h1 : j.succ.succ ≠ (1 : Fin (m + 2)) := by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_succ, Fin.val_one] at hv
        omega
      simp [oneSlot, Function.update_of_ne h1]

end SGPT.Projective.NumEq.CompleteIntersections
