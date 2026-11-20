import SGPT.Foundations.Analysis.Pending.NaturalThetaPshGeometricCurrent
import SGPT.Foundations.Analysis.Pending.LelongPoincareDivisor

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent

open FirstPass _root_.SGPT.Foundations.Analysis.LocalCurrents LelongPoincareDivisor
  GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame NaturalThetaPshGeometricCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

/-- A genuine local potential identifies the literal restricted smooth coefficients. -/
theorem restrictForm_smoothFormDistribution_eq_ddC
    (θ : SmoothRealForm (m + 1) M 2) (e : ComplexChart (m + 1) M)
    {W : Opens (ComplexModel (m + 1))} (hW : W ≤ chartTarget e)
    (ρ : ComplexModel (m + 1) → ℝ) (hpot : IsSmoothLocalPotential θ e W ρ) :
    restrictForm ((smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ).coefficients (canonicalBasis (m + 1)) e) hW =
      ddC (regularDistribution (canonicalBasis (m + 1)).addHaar ρ
        (hpot.2.2.1.continuousOn.locallyIntegrableOn W.isOpen.measurableSet)) := by
  rw [coefficients_smoothGlobalCurrent]
  ext v φ
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  have hint : Integrable (fun x => (TestFunction.monoCLM ℝ φ : 𝓓(chartTarget e, ℝ)) x •
      θ.coeff e x) (canonicalBasis (m + 1)).addHaar :=
    TestFunction.integrable_bilin (ContinuousLinearMap.lsmul ℝ ℝ)
      (smoothForm_coeff_locallyIntegrable (canonicalBasis (m + 1)) θ e) _
  rw [restrictForm_apply, hv,
    ddC_regularDistribution_apply_of_contDiffOn hpot.2.2.1,
    smoothFormDistribution_apply, ← formEvaluationCLM_apply,
    ← (formEvaluationCLM _).integral_comp_comm hint]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [formEvaluationCLM_apply]
  rw [congrFun (testFunction_inclusion_coe hW φ) x]
  by_cases hx : x ∈ W
  · rw [hpot.2.2.2 hx]
    rfl
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))]
    simp

/-- Actual smooth local potentials give both global coefficient properties. -/
theorem smoothGlobalCurrent_closed_type_of_hasSmoothLocalPotentials
    (θ : SmoothRealForm (m + 1) M 2) (hθ : HasSmoothLocalPotentials θ) :
    (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ).IsClosed (canonicalBasis (m + 1)) ∧
    (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ).IsTypeOneOne
        (canonicalBasis (m + 1)) (Nat.succ_pos m) := by
  classical
  have hlocal (e : ComplexChart (m + 1) M) (z : chartTarget e) :
      ∃ (W : Opens (ComplexModel (m + 1))) (hW : W ≤ chartTarget e)
        (ρ : ComplexModel (m + 1) → ℝ) (hpot : IsSmoothLocalPotential θ e W ρ), z.val ∈ W := by
    obtain ⟨W, ρ, hzW, hpot⟩ := hθ e z.val z.property
    exact ⟨⟨W, hpot.1⟩, hpot.2.1, ρ, hpot, hzW⟩
  constructor
  · intro e
    choose W hW ρ hpot hzW using hlocal e
    unfold _root_.SGPT.Foundations.Analysis.LocalCurrents.IsClosed
    refine form_eq_of_forall_restrictForm_eq W hW
      (fun z hz => ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩) fun z => ?_
    rw [restrictForm_exteriorDerivative,
      restrictForm_smoothFormDistribution_eq_ddC θ e (hW z) (ρ z) (hpot z)]
    exact (Pending.LocalCurrents.ddC_isClosed _).trans (by ext v φ; rfl)
  · intro e v w
    choose W hW ρ hpot hzW using hlocal e
    refine eq_of_forall_restrict_eq W hW
      (fun z hz => ⟨⟨z, hz⟩, hzW ⟨z, hz⟩⟩) fun z => ?_
    rw [← restrictForm_apply', ← restrictForm_apply',
      restrictForm_smoothFormDistribution_eq_ddC θ e (hW z) (ρ z) (hpot z)]
    exact Pending.LocalCurrents.ddC_isOneOne _ v w

/-- A genuine theta potential supplies a closed positive actual current of type `(1,1)`. -/
theorem thetaPotentialCurrent_closed_type_positive
    (θ : SmoothRealForm (m + 1) M 2) (u : M → EReal) (hu : IsThetaPshPotential θ u) :
    (thetaPotentialCurrent θ u hu).IsClosed (canonicalBasis (m + 1)) ∧
    (thetaPotentialCurrent θ u hu).IsTypeOneOne (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
    ∀ (e : ComplexChart (m + 1) M) (α : TestForm (chartTarget e) (2 * m)),
      (∀ x, α x ∈ StronglyPositiveForms.spCone m) →
        0 ≤ (thetaPotentialCurrent θ u hu).inChart e
          (CanonicalComplementaryCurrentTests.castTestDegree
            (by rw [complexModel_real_finrank]; omega :
              2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) α) := by
  obtain ⟨hc, ht⟩ := smoothGlobalCurrent_closed_type_of_hasSmoothLocalPotentials
    θ hu.1.hasSmoothLocalPotentials
  refine ⟨hc.add _ (globalDDC_isClosed (canonicalBasis (m + 1)) (Nat.succ_pos m)
    u hu.quasiPshPotential), ht.add _ (globalDDC_isTypeOneOne (canonicalBasis (m + 1))
    (Nat.succ_pos m) u hu.quasiPshPotential), ?_⟩
  exact thetaPotentialCurrent_full_positive θ u hu

end SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
