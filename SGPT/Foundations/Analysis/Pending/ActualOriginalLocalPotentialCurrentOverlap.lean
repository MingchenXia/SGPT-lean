import SGPT.Foundations.Analysis.Pending.ActualWeakAnalyticCurrentPotentialAtlas
import SGPT.Foundations.Analysis.Pending.CurrentPairing
import SGPT.Foundations.Analysis.Pending.DDCOverlap

set_option autoImplicit false

/-! # Complete overlap readings of the original local potentials

The natural coefficient readings of the same actual signed global current
restore its entire real test functional. The original potentials, rather
than supplied current-parts identities, produce the overlap adjoint integrals.
-/

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.ActualOriginalLocalPotentialCurrentOverlap
open FirstPass CanonicalCurrentFrame ActualQuasiPshPotentialSmoothCompatibility
open _root_.SGPT.Foundations.Analysis.LocalCurrents

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem full_current_of_original_reading
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e : ComplexChart (m + 1) M) {Ω : Opens (ComplexModel (m + 1))}
    (hΩ : Ω ≤ chartTarget e) {u : ComplexModel (m + 1) → EReal}
    (hu : LocalQuasiPshPotentialOn u Ω)
    (hread : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(Ω, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ) :
    T.restrictChart e hΩ = toLocalCurrent (canonicalBasis (m + 1))
      (degreeTwo (Nat.succ_pos m)) (ddC (regularLocalQuasiPsh hu)) := by
  have hextract : fromLocalCurrent (canonicalBasis (m + 1))
      (degreeTwo (Nat.succ_pos m)) (T.restrictChart e hΩ) =
        ddC (regularLocalQuasiPsh hu) := by
    ext w φ
    exact (GlobalCurrent.coefficients_restrictChart (canonicalBasis (m + 1))
      T e hΩ w φ).trans (hread w φ)
  rw [← hextract, CurrentPairing.toLocalCurrent_fromLocalCurrent]

private theorem same_nested_test_inclusion
    {A B C D : Opens (ComplexModel (m + 1))} {q : ℕ}
    (hAB : A ≤ B) (hBD : B ≤ D) (hAC : A ≤ C) (hCD : C ≤ D)
    (η : TestForm A q) :
    (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm B q) : TestForm D q) =
      TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm C q) := by
  ext x
  simp only [testForm_inclusion_apply hBD, testForm_inclusion_apply hAB,
    testForm_inclusion_apply hCD, testForm_inclusion_apply hAC]

/-- The genuine original local readers restore every real complementary test
of the same signed global current, and internally produce its exact overlap
identity directly in the two original scalar-potential adjoint integrals. -/
theorem original_local_potential_full_overlap
    (T : GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)))
    (e f : ComplexChart (m + 1) M) {Ω P : Opens (ComplexModel (m + 1))}
    (hΩ : Ω ≤ chartTarget e) (hP : P ≤ chartTarget f)
    {u v : ComplexModel (m + 1) → EReal}
    (hu : LocalQuasiPshPotentialOn u Ω) (hv : LocalQuasiPshPotentialOn v P)
    (hreadu : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(Ω, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) e w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hu) w φ)
    (hreadv : ∀ (w : Fin 2 → ComplexModel (m + 1)) (φ : 𝓓(P, ℝ)),
      T.coefficients (canonicalBasis (m + 1)) f w (TestFunction.monoCLM ℝ φ) =
        ddC (regularLocalQuasiPsh hv) w φ) :
    T.restrictChart e hΩ = toLocalCurrent (canonicalBasis (m + 1))
      (degreeTwo (Nat.succ_pos m)) (ddC (regularLocalQuasiPsh hu)) ∧
    T.restrictChart f hP = toLocalCurrent (canonicalBasis (m + 1))
      (degreeTwo (Nat.succ_pos m)) (ddC (regularLocalQuasiPsh hv)) ∧
    ∀ (η : TestForm (Ω ⊓ overlapSource e f)
        (Module.finrank ℝ (ComplexModel (m + 1)) - (degreeTwo (Nat.succ_pos m)).val))
      (ζ : TestForm (P ⊓ overlapTarget e f)
        (Module.finrank ℝ (ComplexModel (m + 1)) - (degreeTwo (Nat.succ_pos m)).val)),
      (∀ x, x ∈ (chartTransition e f).source →
        ∀ w : Fin (Module.finrank ℝ (ComplexModel (m + 1)) -
          (degreeTwo (Nat.succ_pos m)).val) → ComplexModel (m + 1),
          η x w = ζ (chartTransition e f x)
            (fun i => chartTransitionDerivative e f x (w i))) →
      restrictLocalCurrent inf_le_left
          (toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
            (ddC (regularLocalQuasiPsh hu))) η =
        restrictLocalCurrent inf_le_left
          (toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
            (ddC (regularLocalQuasiPsh hv))) ζ ∧
      (∫ x, DDCOverlap.ddcAdjoint
          (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) η x *
          (u x).toReal ∂volume) =
        ∫ x, DDCOverlap.ddcAdjoint
          (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) ζ x *
          (v x).toReal ∂volume := by
  have hCu := full_current_of_original_reading T e hΩ hu hreadu
  have hCv := full_current_of_original_reading T f hP hv hreadv
  refine ⟨hCu, hCv, ?_⟩
  intro η ζ hrel
  have hrelated : OverlapTestRelated e f
      (TestFunction.monoCLM ℝ η : TestForm (overlapSource e f) _)
      (TestFunction.monoCLM ℝ ζ : TestForm (overlapTarget e f) _) := by
    intro x hx w
    rw [testForm_inclusion_apply inf_le_right, testForm_inclusion_apply inf_le_right]
    exact hrel x hx w
  have hcur : restrictLocalCurrent inf_le_left (T.restrictChart e hΩ) η =
      restrictLocalCurrent inf_le_left (T.restrictChart f hP) ζ := by
    change T.inChart e (TestFunction.monoCLM ℝ
        (TestFunction.monoCLM ℝ η : TestForm Ω _)) =
      T.inChart f (TestFunction.monoCLM ℝ
        (TestFunction.monoCLM ℝ ζ : TestForm P _))
    rw [same_nested_test_inclusion inf_le_left hΩ inf_le_right (overlapSource_le e f) η,
      same_nested_test_inclusion inf_le_left hP inf_le_right (overlapTarget_le e f) ζ]
    exact T.overlap e f _ _ hrelated
  rw [hCu, hCv] at hcur
  refine ⟨hcur, ?_⟩
  have hpairu : restrictLocalCurrent inf_le_left
      (toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
        (ddC (regularLocalQuasiPsh hu))) η =
      ∫ x, DDCOverlap.ddcAdjoint
        (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) η x *
        (u x).toReal ∂volume := by
    change wedgePairing _ (ddC (regularLocalQuasiPsh hu)) (TestFunction.monoCLM ℝ η) = _
    rw [DDCOverlap.wedgePairing_ddC, regularLocalQuasiPsh, regularDistribution_apply]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [DDCOverlap.ddcAdjoint_monoCLM_apply inf_le_left]
  have hpairv : restrictLocalCurrent inf_le_left
      (toLocalCurrent (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))
        (ddC (regularLocalQuasiPsh hv))) ζ =
      ∫ x, DDCOverlap.ddcAdjoint
        (currentPairingBasis (canonicalBasis (m + 1)) (degreeTwo (Nat.succ_pos m))) ζ x *
        (v x).toReal ∂volume := by
    change wedgePairing _ (ddC (regularLocalQuasiPsh hv)) (TestFunction.monoCLM ℝ ζ) = _
    rw [DDCOverlap.wedgePairing_ddC, regularLocalQuasiPsh, regularDistribution_apply]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [DDCOverlap.ddcAdjoint_monoCLM_apply inf_le_left]
  exact hpairu.symm.trans (hcur.trans hpairv)

end SGPT.Foundations.Analysis.Pending.ActualOriginalLocalPotentialCurrentOverlap
