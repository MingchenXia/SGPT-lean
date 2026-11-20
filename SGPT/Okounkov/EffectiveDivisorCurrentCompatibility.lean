import SGPT.Okounkov.EffectiveDivisorPotentialCompatibility
import SGPT.Okounkov.CurrentFlagValuation

set_option autoImplicit false
noncomputable section
universe u
namespace SGPT.Okounkov

open Set Filter
open scoped Manifold ContDiff NNReal ENNReal Distributions
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.FirstPass.IEnvelope
open SGPT.Foundations.Analysis.FirstPass.BlowupSequences
open SGPT.Foundations.Analysis.Pending
open GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame
open NaturalThetaPshGeometricCurrent NaturalThetaPshClosedCurrent
open GlobalPositiveCurrentACRestriction LelongPoincareDivisor

/-- The complete original current of the actual effective Cartier divisor,
using its produced genuine metric; the next theorem removes metric choice. -/
def effectiveDivisorIntegrationCurrent {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1))
    (D : EffectiveDivisor (m + 1) F.carrier) :
    GlobalCurrent (m + 1) F.carrier (degreeTwo (Nat.succ_pos m)) :=
  integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m)
    (Classical.choose (DivisorMetric.exists_divisorMetric D))

/-- Actual unchanged whole-current metric independence, including every
divisor-supported distribution coefficient of the same original ideal. -/
theorem effectiveDivisorIntegrationCurrent_eq_of_metric {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (D : EffectiveDivisor (m + 1) F.carrier)
    (ED : MeteredEffectiveQDivisor (m + 1) F.carrier)
    (hED : DivisorMetric.IsDivisorMetric D ED) :
    effectiveDivisorIntegrationCurrent F D =
      integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) ED := by
  exact ActualDivisorCurrentMetricIndependence.integrationCurrent_eq_of_isDivisorMetric
    (canonicalBasis (m + 1)) D _ ED
      (Classical.choose_spec (DivisorMetric.exists_divisorMetric D)).2 hED

/-- The genuine metric theta representation equals the actual complete
integration current, by its original whole chart coefficient identities. -/
theorem thetaPotentialCurrent_effectiveDivisorMetric_eq {m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel (m + 1)) M]
    [IsComplexManifold (m + 1) M]
    (D : EffectiveDivisor (m + 1) M) (ED : MeteredEffectiveQDivisor (m + 1) M)
    (hED : DivisorMetric.IsDivisorMetric D ED) :
    thetaPotentialCurrent ED.curvature.val ED.weight
        (isThetaPshPotential_effectiveDivisorMetric D ED hED) =
      integrationCurrent (canonicalBasis (m + 1)) (Nat.succ_pos m) ED := by
  apply globalCurrent_ext (canonicalBasis (m + 1))
  intro e
  simp only [thetaPotentialCurrent, GlobalCurrent.coefficients_add,
    coefficients_smoothGlobalCurrent, globalDDC_coefficients, coefficients_integrationCurrent]
  exact add_comm _ _

/-- Original effective divisor data produce actual full positivity,
closedness and type of its literal complete integration current. -/
theorem effectiveDivisorIntegrationCurrent_closed_type_positive {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (D : EffectiveDivisor (m + 1) F.carrier) :
    (effectiveDivisorIntegrationCurrent F D).IsClosed (canonicalBasis (m + 1)) ∧
    (effectiveDivisorIntegrationCurrent F D).IsTypeOneOne
      (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
    IsFullPositive (effectiveDivisorIntegrationCurrent F D) := by
  obtain ⟨ED, _hEDsup, hED⟩ := DivisorMetric.exists_divisorMetric D
  have hu := isThetaPshPotential_effectiveDivisorMetric D ED hED
  have heq : effectiveDivisorIntegrationCurrent F D =
      thetaPotentialCurrent ED.curvature.val ED.weight hu :=
    (effectiveDivisorIntegrationCurrent_eq_of_metric F D ED hED).trans
      (thetaPotentialCurrent_effectiveDivisorMetric_eq D ED hED).symm
  rw [heq]
  exact thetaPotentialCurrent_closed_type_positive ED.curvature.val ED.weight hu

/-- Actual independent Cartier division/restriction supplies the whole
integer vector of the original complete divisor integration current. -/
theorem exists_currentFlagValuation_effectiveDivisor_eq_integer_vector {m : ℕ}
    (F : OriginalFlagGeometry.{u} (m + 1)) (D : EffectiveDivisor (m + 1) F.carrier) :
    ∃ ν : Fin (m + 1) → ℕ, OriginalCartierFlagValuation (m + 1) F D ν ∧
      currentFlagValuation F (effectiveDivisorIntegrationCurrent F D)
        (effectiveDivisorIntegrationCurrent_closed_type_positive F D).1
        (effectiveDivisorIntegrationCurrent_closed_type_positive F D).2.1
        (effectiveDivisorIntegrationCurrent_closed_type_positive F D).2.2 =
      (fun i => (ν i : ℝ≥0)) := by
  obtain ⟨ν, hν⟩ := exists_originalCartierFlagValuation (m + 1) F D
  obtain ⟨ED, _hEDsup, hED⟩ := DivisorMetric.exists_divisorMetric D
  have hu := isThetaPshPotential_effectiveDivisorMetric D ED hED
  have hread : effectiveDivisorIntegrationCurrent F D =
      thetaPotentialCurrent ED.curvature.val ED.weight hu :=
    (effectiveDivisorIntegrationCurrent_eq_of_metric F D ED hED).trans
      (thetaPotentialCurrent_effectiveDivisorMetric_eq D ED hED).symm
  have hνP := originalPotentialFlagValuation_of_originalCartierFlagValuation
    (m + 1) F D ED hED ν hν
  refine ⟨ν, hν, ?_⟩
  rw [currentFlagValuation_eq_potentialFlagValuation F _ _ _ _ hu hread]
  exact originalPotentialFlagValuation_eq_of_iEquivalent (m + 1) F ED.weight ED.weight
    (potentialFlagValuation F hu) (fun i => (ν i : ℝ≥0))
      (potentialFlagValuation_spec F hu) hνP (IEquivalentOnManifold.refl ED.weight)

end SGPT.Okounkov
