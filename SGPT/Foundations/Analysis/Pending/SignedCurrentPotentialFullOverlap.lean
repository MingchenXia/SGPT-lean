import SGPT.Foundations.Analysis.Pending.FiniteGlobalScalarDdc

set_option autoImplicit false

/-! Entire original-current overlap pairings of ANY signed scalar distribution
potentials. Full pairings are recovered from the natural local ddC equations
by the actual original inverse-coefficient theorem. No regular/L1/quasi-PSH
representative or desired overlap certificate is supplied. -/

noncomputable section
open Set TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis.Pending.SignedCurrentPotentialFullOverlap
open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents
  LelongPoincareDivisor DDCOverlap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable (b : Module.Basis (Fin (Module.finrank ℝ (ComplexModel n))) ℝ (ComplexModel n))
  (hn : 0 < n)

private theorem full_current_of_potential
    (T : GlobalCurrent n M (degreeTwo hn)) (e : ComplexChart n M)
    {Ω : Opens (ComplexModel n)} (hΩ : Ω ≤ chartTarget e) (R : 𝓓'(Ω, ℝ))
    (hR : ddC R = restrictForm (T.coefficients b e) hΩ) :
    T.restrictChart e hΩ = toLocalCurrent b (degreeTwo hn) (ddC R) := by
  have hex : fromLocalCurrent b (degreeTwo hn) (T.restrictChart e hΩ) = ddC R := by
    ext v φ
    rw [GlobalCurrent.coefficients_restrictChart]
    exact (congrArg (fun A : DistributionForm Ω 2 => A v φ) hR).symm
  rw [← hex, CurrentPairing.toLocalCurrent_fromLocalCurrent]

private theorem same_nested_inclusion
    {A B C D : Opens (ComplexModel n)} {q : ℕ}
    (hAB : A ≤ B) (hBD : B ≤ D) (hAC : A ≤ C) (hCD : C ≤ D)
    (η : TestForm A q) :
    (TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm B q) : TestForm D q) =
      TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ η : TestForm C q) := by
  apply TestFunction.ext
  intro x
  rw [testForm_inclusion_apply hBD, testForm_inclusion_apply hAB,
    testForm_inclusion_apply hCD, testForm_inclusion_apply hAC]

private theorem adjoint_mono {Ω U : Opens (ComplexModel n)} {q : ℕ}
    (hU : U ≤ Ω) (B : Fin 2 ⊕ Fin q → ComplexModel n) (η : TestForm U q) :
    ddcAdjoint B (TestFunction.monoCLM ℝ η : TestForm Ω q) =
      (TestFunction.monoCLM ℝ (ddcAdjoint B η) : 𝓓(Ω, ℝ)) := by
  apply TestFunction.ext
  intro z
  rw [ddcAdjoint_monoCLM_apply hU, testFunction_inclusion_coe hU]

/-- Two natural arbitrary signed scalar potentials of the SAME original
current internally produce its full functional readings and all overlap
adjoint-test pairings; no L1/regular/quasi-PSH or cocycle assumption is present. -/
theorem original_signed_potential_full_overlap
    (T : GlobalCurrent n M (degreeTwo hn)) (e f : ComplexChart n M)
    {Ω P : Opens (ComplexModel n)} (hΩ : Ω ≤ chartTarget e) (hP : P ≤ chartTarget f)
    (R : 𝓓'(Ω, ℝ)) (S : 𝓓'(P, ℝ))
    (hR : ddC R = restrictForm (T.coefficients b e) hΩ)
    (hS : ddC S = restrictForm (T.coefficients b f) hP) :
    T.restrictChart e hΩ = toLocalCurrent b (degreeTwo hn) (ddC R) ∧
    T.restrictChart f hP = toLocalCurrent b (degreeTwo hn) (ddC S) ∧
    ∀ (η : TestForm (Ω ⊓ overlapSource e f)
        (Module.finrank ℝ (ComplexModel n) - 2))
      (ζ : TestForm (P ⊓ overlapTarget e f) (Module.finrank ℝ (ComplexModel n) - 2)),
      (∀ x ∈ (chartTransition e f).source,
        ∀ v : Fin (Module.finrank ℝ (ComplexModel n) - 2) → ComplexModel n,
          η x v = ζ (chartTransition e f x)
            (fun i => chartTransitionDerivative e f x (v i))) →
      R (TestFunction.monoCLM ℝ (ddcAdjoint (currentPairingBasis b (degreeTwo hn)) η)) =
        S (TestFunction.monoCLM ℝ (ddcAdjoint (currentPairingBasis b (degreeTwo hn)) ζ)) := by
  have hCR := full_current_of_potential b hn T e hΩ R hR
  have hCS := full_current_of_potential b hn T f hP S hS
  refine ⟨hCR, hCS, ?_⟩
  intro η ζ hrel
  have hrelated : OverlapTestRelated e f
      (TestFunction.monoCLM ℝ η : TestForm (overlapSource e f) _)
      (TestFunction.monoCLM ℝ ζ : TestForm (overlapTarget e f) _) := by
    intro x hx v
    rw [testForm_inclusion_apply inf_le_right, testForm_inclusion_apply inf_le_right]
    exact hrel x hx v
  have hcur : restrictLocalCurrent inf_le_left (T.restrictChart e hΩ) η =
      restrictLocalCurrent inf_le_left (T.restrictChart f hP) ζ := by
    change T.inChart e (TestFunction.monoCLM ℝ
        (TestFunction.monoCLM ℝ η : TestForm Ω _)) =
      T.inChart f (TestFunction.monoCLM ℝ
        (TestFunction.monoCLM ℝ ζ : TestForm P _))
    rw [same_nested_inclusion inf_le_left hΩ inf_le_right (overlapSource_le e f) η,
      same_nested_inclusion inf_le_left hP inf_le_right (overlapTarget_le e f) ζ]
    exact T.overlap e f _ _ hrelated
  rw [hCR, hCS] at hcur
  change wedgePairing (currentPairingBasis b (degreeTwo hn)) (ddC R)
      (TestFunction.monoCLM ℝ η) =
    wedgePairing (currentPairingBasis b (degreeTwo hn)) (ddC S)
      (TestFunction.monoCLM ℝ ζ) at hcur
  rw [wedgePairing_ddC, wedgePairing_ddC, adjoint_mono inf_le_left,
    adjoint_mono inf_le_left] at hcur
  exact hcur

end SGPT.Foundations.Analysis.Pending.SignedCurrentPotentialFullOverlap
