import SGPT.PSH.HermitianGlobalMeasure
import SGPT.PSH.HermitianExtremalCurrentAlgebra

/-! The actual nonclosed mixed product retains the original invariance under
finite scalar translations of every bounded potential. -/

set_option autoImplicit false
noncomputable section

namespace SGPT.PSH.HermitianProducts

open Set Filter TopologicalSpace
open scoped Distributions ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorForms LocalBedfordTaylorCollar LocalBedfordTaylorSmoothCovariance

variable {n : ℕ} {U : Opens (ComplexModel n)}

/-- Every actual subset BT product is invariant under arbitrary finite
slotwise constants; the smooth residual is retained literally. -/
theorem backgroundExpansion_add_constants (p r : ℕ)
    (T : LocalProductCurrent n U (r+p)) (hT : IsPositive T) (hTc : IsClosedAny (r+p) T)
    (v : Fin p → ComplexModel n → ℝ) (hv : ∀ i, IsLocallyBoundedPshOn U (v i))
    (c : Fin p → ℝ) {σ : ComplexModel n → RealForm n 2}
    (hσ : ContDiffOn ℝ ∞ σ U) :
    backgroundExpansion p r (fun i z => v i z + c i) hσ T =
      backgroundExpansion p r v hσ T := by
  classical
  unfold backgroundExpansion
  apply Finset.sum_congr rfl
  intro s _
  dsimp only [backgroundExpansionTerm]
  rw [btProduct_add_const s.card (r+(p-s.card))
    (fun i => v (s.orderEmbOfFin rfl i)) (fun i => c (s.orderEmbOfFin rfl i))
    _ (isPositive_castLPC _ hT) (isClosedAny_castLPC _ hTc) (fun i => hv _)]

end SGPT.PSH.HermitianProducts

namespace SGPT.PSH.HermitianGlobalProducts

open Set MeasureTheory TopologicalSpace
open scoped Distributions ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending
open FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents LocalBedfordTaylorProducts
  LocalBedfordTaylorForms LocalBedfordTaylorCollar LocalBedfordTaylorSmoothCovariance
open Hermitian HermitianExtremalCurrentAlgebra

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m+1)) M] [IsComplexManifold (m+1) M]
  {omega : Background (m+1) M}

/-- Real boundedness gives the translated real representative exactly. -/
theorem BackgroundPatch.correctedReal_add_const (P : BackgroundPatch omega)
    {u : M → EReal} (hu : IsHermitianPSH omega u)
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (c : ℝ)
    (z : ComplexModel (m+1)) :
    P.correctedReal (fun x => u x + (c : EReal)) z = P.correctedReal u z + c := by
  obtain ⟨a, b, hab⟩ := hb
  have htop : u (P.geometry.chart.val.symm z) ≠ ⊤ := hu.ne_top _
  have hbot : u (P.geometry.chart.val.symm z) ≠ ⊥ :=
    ne_of_gt ((EReal.bot_lt_coe a).trans_le (hab _).1)
  unfold BackgroundPatch.correctedReal chartFunction
  rw [EReal.toReal_add htop hbot (EReal.coe_ne_top _) (EReal.coe_ne_bot _), EReal.toReal_coe]
  ring

/-- The literal genuine top-degree correction-patch current does not change
under finite slotwise translations of its original bounded potentials. -/
theorem BackgroundPatch.current_add_constants (P : BackgroundPatch omega)
    (u : Fin (m+1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (c : Fin (m+1) → ℝ) :
    P.current (fun i x => u i x + (c i : EReal)) = P.current u := by
  have heq : (fun i => P.correctedReal (fun x => u i x + (c i : EReal))) =
      (fun i z => P.correctedReal (u i) z + c i) := by
    funext i z
    exact P.correctedReal_add_const (hu i) (hb i) (c i) z
  unfold BackgroundPatch.current
  rw [heq]
  exact HermitianProducts.backgroundExpansion_add_constants _ _ _
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) _
    (fun i => P.correctedReal_isLocallyBoundedPshOn (hu i) (hb i)) c _

omit [TopologicalSpace M] in
/-- Finite real translation produces honest two-sided real bounds. -/
theorem boundedPotential_add_const {u : M → EReal}
    (hb : ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x ∧ u x ≤ (b : EReal)) (c : ℝ) :
    ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u x + (c : EReal) ∧ u x + (c : EReal) ≤ (b : EReal) := by
  obtain ⟨a, b, hab⟩ := hb
  refine ⟨a+c, b+c, fun x => ?_⟩
  rw [EReal.coe_add, EReal.coe_add]
  exact ⟨add_le_add (hab x).1 le_rfl, add_le_add (hab x).2 le_rfl⟩

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

omit [BorelSpace M] in
/-- The same canonical actual global mixed measure is obtained after finite
slotwise translations. Both translated class membership and real bounds are
produced internally, with no invariance certificate. -/
theorem globalMixedMeasure_add_constants
    (u : Fin (m+1) → M → EReal) (hu : ∀ i, IsHermitianPSH omega (u i))
    (hb : ∀ i, ∃ a b : ℝ, ∀ x, (a : EReal) ≤ u i x ∧ u i x ≤ (b : EReal))
    (c : Fin (m+1) → ℝ) :
    globalMixedMeasure omega (fun i x => u i x + (c i : EReal))
      (fun i => isFormPSH_add_const (hu i) (c i))
      (fun i => boundedPotential_add_const (hb i) (c i)) =
      globalMixedMeasure omega u hu hb := by
  classical
  let C : BackgroundFiniteCover omega := Classical.choice (nonempty_backgroundFiniteCover omega)
  change C.measure _ _ _ = C.measure u hu hb
  unfold BackgroundFiniteCover.measure glueTraceMeasure
  congr 1
  funext i
  apply congrArg (C.patch i).geometry.pushMeasure
  exact traceMeasure_congr ((C.patch i).current_add_constants u hu hb c) _ _

end SGPT.PSH.HermitianGlobalProducts
