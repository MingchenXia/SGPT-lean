import SGPT.Projective.NativeCICutIntrinsicPeriod

/-! The genuine original whole CI degree formula and numerical vanishing,
with all powers and all whole member subtypes chosen before the test form. -/
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

/-- The SAME actual whole terminal curve degree equals the literal chosen
power product times the SAME original ambient mixed Chern period. No
complete-intersection/cycle/current/degree certificate is a premise. -/
theorem terminal_degree_eq_power_product (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X] [CompactSpace X]
    {P : Fin k → NativePositiveLine (k + 1) X} (T : WholeNativeCITower k X P)
    (κ : KahlerBackground (k + 1) X) (alpha : ClosedRealOneOneForm (k + 1) X) :
    let : MeasurableSpace X := borel X
    let : BorelSpace X := ⟨rfl⟩
    degreeAlong (terminal k X T κ).background (terminal k X T κ).inclusion.contMDiff alpha =
      (∏ i, (powers k T i : ℝ)) * slotIntegral κ (Fin.cons alpha (fun i => (P i).curvature)) := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  dsimp only
  cases k with
  | zero =>
      have hempty : (fun i : Fin 0 => (P i).curvature) = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simpa only [Fin.prod_univ_zero, one_mul, hempty] using terminal_degree_base X T κ alpha
  | succ k =>
      let D := T.1
      let : ChartedSpace (ComplexModel (k + 1)) D.carrier := D.carrierCharts
      let : IsComplexManifold (k + 1) D.carrier := D.carrierComplex
      let : MeasurableSpace D.carrier := borel D.carrier
      let : BorelSpace D.carrier := ⟨rfl⟩
      have htail := terminal_degree_eq_power_product k D.carrier T.2 (D.restrictKahler κ)
        (ClosedRealOneOneForm.pullback D.inclusion.contMDiff alpha)
      have htuple :
          (Fin.cons (ClosedRealOneOneForm.pullback D.inclusion.contMDiff alpha)
            (fun i : Fin k => (D.restrictPositive (P i.succ)).curvature) :
              Fin (k + 1) → ClosedRealOneOneForm (k + 1) D.carrier) =
          fun i : Fin (k + 1) => ClosedRealOneOneForm.pullback D.inclusion.contMDiff
            ((Fin.cons alpha (fun j : Fin k => (P j.succ).curvature) :
              Fin (k + 1) → ClosedRealOneOneForm (k + 2) X) i) := by
        funext i
        refine Fin.cases rfl (fun _ => rfl) i
      have hP : (Fin.cons (P 0).curvature (fun i : Fin k => (P i.succ).curvature) :
          Fin (k + 1) → ClosedRealOneOneForm (k + 2) X) =
          fun i : Fin (k + 1) => (P i).curvature := by
        funext i
        refine Fin.cases rfl (fun _ => rfl) i
      rw [terminal_degree_succ, htail, htuple,
        D.slotIntegral_restrict_eq_power κ (Fin.cons alpha (fun i : Fin k => (P i.succ).curvature))
          (D.restrictKahler κ),
        slotIntegral_cons_snoc_cycle κ alpha (P 0).curvature,
        hP, powers_real_prod_succ]
      ring
termination_by k

end WholeNativeCITower

/-- Genuine original numerical triviality kills the original mixed period
with any fixed tuple of actual original positive native bundle curvatures.
The entire actual CI geometry is manufactured, not supplied as a premise. -/
theorem slotIntegral_positive_tuple_eq_zero_of_numericallyTrivial
    (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X] [CompactSpace X]
    (P : Fin k → NativePositiveLine (k + 1) X)
    (κ : KahlerBackground (k + 1) X) (alpha : ClosedRealOneOneForm (k + 1) X)
    (hnum : IsNumericallyTrivial alpha) :
    let : MeasurableSpace X := borel X
    let : BorelSpace X := ⟨rfl⟩
    slotIntegral κ (Fin.cons alpha (fun i => (P i).curvature)) = 0 := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  dsimp only
  obtain ⟨T⟩ := exists_wholeNativeCITower k X P
  have hdegree := WholeNativeCITower.terminal_degree_eq_power_product k X T κ alpha
  have hzero := WholeNativeCITower.terminal_degree_zero_of_numericallyTrivial k X T κ alpha hnum
  have hprod := WholeNativeCITower.powers_real_prod_pos k T
  exact (mul_eq_zero.mp (hdegree.symm.trans hzero)).resolve_left (ne_of_gt hprod)

end SGPT.Projective.NumEq.CompleteIntersections
