import SGPT.Projective.NativeCICutPeriod
import SGPT.Projective.NativeCITerminalCurve
import SGPT.Projective.NumEqCurveComponents

/-! Unconditional original tuple-order, positive-power and actual degree
functoriality adapters for the SAME whole native CI geometry. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections
open Set
open scoped Topology Manifold ContDiff BigOperators
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.NefMixedMass
open SGPT.Hodge.BDivChain.SourceMixedOrderDraft

/-- Original ambient mixed tensor symmetry puts the newly cut original
bundle after the SAME fixed first test slot. -/
theorem slotIntegral_cons_snoc_cycle {m : ℕ} {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (m + 2)) X] [IsComplexManifold (m + 2) X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (κ : KahlerBackground (m + 2) X) (alpha theta : ClosedRealOneOneForm (m + 2) X)
    (beta : Fin m → ClosedRealOneOneForm (m + 2) X) :
    slotIntegral κ (Fin.snoc (Fin.cons alpha beta) theta) =
      slotIntegral κ (Fin.cons alpha (Fin.cons theta beta)) := by
  classical
  rw [slotIntegral_snoc_eq_cons]
  let F : Fin (m + 2) → ClosedRealOneOneForm (m + 2) X := Fin.cons alpha (Fin.cons theta beta)
  have hfun : (fun i => F (Equiv.swap (0 : Fin (m + 2)) 1 i)) =
      Fin.cons theta (Fin.cons alpha beta) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [F]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [F]
      · have h0 : j.succ.succ ≠ (0 : Fin (m + 2)) := by simp
        have h1 : j.succ.succ ≠ (1 : Fin (m + 2)) := by
          intro h
          have hv := congrArg Fin.val h
          simp only [Fin.val_succ, Fin.val_one] at hv
          omega
        simp only [Equiv.swap_apply_of_ne_of_ne h0 h1, F, Fin.cons_succ]
  have h := slotIntegral_perm κ F (Equiv.swap 0 1)
  rw [hfun] at h
  exact h

/-- Degrees use the actual dimension-free pullback chain rule on the SAME
original form and SAME actual compact source curve. -/
theorem degreeAlong_comp_actual {n k : ℕ} {X Y C : Type}
    [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y] [IsComplexManifold k Y]
    [TopologicalSpace C] [ChartedSpace (ComplexModel 1) C] [IsComplexManifold 1 C] [CompactSpace C]
    (κC : KahlerBackground 1 C) {f : Y → X} {g : C → Y}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel 1) 𝓘(ℂ, ComplexModel k) ∞ g)
    (alpha : ClosedRealOneOneForm n X) :
    degreeAlong κC (hf.comp hg) alpha = degreeAlong κC hg (ClosedRealOneOneForm.pullback hf alpha) := by
  let : MeasurableSpace C := borel C
  let : BorelSpace C := ⟨rfl⟩
  change slotIntegral κC (fun _ => ClosedRealOneOneForm.pullback (hf.comp hg) alpha) =
    slotIntegral κC (fun _ => ClosedRealOneOneForm.pullback hg (ClosedRealOneOneForm.pullback hf alpha))
  exact slotIntegral_eq_of_bottChernRel κC _ _ (fun _ =>
    ClosedRealOneOneForm.bottChernRel_of_geometricallyEq
      (FormPullbackCompMixed.pullback_comp_geometricallyEq hf hg alpha.val))

namespace WholeNativeCITower

/-- The actual chosen positive power product cannot vanish. -/
theorem powers_prod_pos (k : ℕ) {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X]
    {P : Fin k → NativePositiveLine (k + 1) X} (T : WholeNativeCITower k X P) :
    0 < ∏ i, powers k T i := Finset.prod_pos (fun i _ => powers_pos k T i)

/-- The literal real product of actual chosen power integers is positive. -/
theorem powers_real_prod_pos (k : ℕ) {X : Type} [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X]
    {P : Fin k → NativePositiveLine (k + 1) X} (T : WholeNativeCITower k X P) :
    0 < ∏ i, (powers k T i : ℝ) :=
  Finset.prod_pos (fun i _ => by exact_mod_cast powers_pos k T i)

/-- The actual terminal degree factors through the SAME first original
cut and the SAME actual restricted tail; this is functoriality, without
assuming any degree/intersection identity for that cut. -/
theorem terminal_degree_succ (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 2)) X] [IsComplexManifold (k + 2) X] [CompactSpace X]
    {P : Fin (k + 1) → NativePositiveLine (k + 2) X} (T : WholeNativeCITower (k + 1) X P)
    (κ : KahlerBackground (k + 2) X) (alpha : ClosedRealOneOneForm (k + 2) X) :
    let D := T.1
    let : ChartedSpace (ComplexModel (k + 1)) D.carrier := D.carrierCharts
    let : IsComplexManifold (k + 1) D.carrier := D.carrierComplex
    degreeAlong (terminal (k + 1) X T κ).background (terminal (k + 1) X T κ).inclusion.contMDiff alpha =
      degreeAlong (terminal k D.carrier T.2 (D.restrictKahler κ)).background
        (terminal k D.carrier T.2 (D.restrictKahler κ)).inclusion.contMDiff
          (ClosedRealOneOneForm.pullback D.inclusion.contMDiff alpha) := by
  dsimp only
  rw [terminal]
  exact degreeAlong_comp_actual _ T.1.inclusion.contMDiff _ alpha

/-- The original numerical test condition already kills the actual degree
on the WHOLE manufactured terminal curve, including all its components. -/
theorem terminal_degree_zero_of_numericallyTrivial (k : ℕ) (X : Type) [TopologicalSpace X]
    [ChartedSpace (ComplexModel (k + 1)) X] [IsComplexManifold (k + 1) X] [CompactSpace X]
    {P : Fin k → NativePositiveLine (k + 1) X} (T : WholeNativeCITower k X P)
    (κ : KahlerBackground (k + 1) X) (alpha : ClosedRealOneOneForm (k + 1) X)
    (hnum : IsNumericallyTrivial alpha) :
    degreeAlong (terminal k X T κ).background (terminal k X T κ).inclusion.contMDiff alpha = 0 :=
  degreeAlong_eq_zero_of_isNumericallyTrivial_compactCurve alpha hnum _ _

end WholeNativeCITower
end SGPT.Projective.NumEq.CompleteIntersections
