import SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalMixedZero
import SGPT.Foundations.Analysis.Pending.RelativePreceqClasses

set_option autoImplicit false

/-! # Actual homogeneous mixed strip equation for full singularity-order endpoint classes -/

open Set

namespace SGPT.Foundations.Analysis.Pending.SingularPerronPreceqMixedZero

open FirstPass FirstPass.PositiveClasses MixedNonPluripolar RelativePreceqClasses
  SingularPerronNonpluripolarZero SingularPerronCanonicalMixedZero FiniteGeodesicMaximality

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Genuine singularity-order full-mass endpoints internally produce the actual canonical diagonal mixed homogeneous strip equation, without pointwise endpoint normalization. -/
theorem mixedTruncationLimitMeasure_erealModel_of_relativeFullMassPreceq_eq_zero
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}
    (hu₀ : RelativeFullMassPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFullMassPreceq θ φ u₁ hφ)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e W ρ) :
    mixedTruncationLimitMeasure (modelStripOpens W hρ.1)
      (fun _ => erealModelChartFunction (finiteGeodesic θ.val u₀ u₁) e ρ)
      (fun _ => (isBoundaryMaximalPshOn_erealModel_of_subgeodesic
        (finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hu₀ hu₁)
        e hρ).2.1) = 0 :=
  mixedTruncationLimitMeasure_erealModel_of_subgeodesic_eq_zero
    (finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hu₀ hu₁) e hρ

/-- Genuine singularity-order finite energy supplies all actual full-mass and subgeodesic producers needed for the actual mixed homogeneous strip equation. -/
theorem mixedTruncationLimitMeasure_erealModel_of_relativeFiniteEnergyPreceq_eq_zero
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ u₀ u₁ : M → EReal} {hφ : IsModelPotential θ φ}
    (hu₀ : RelativeFiniteEnergyPreceq θ φ u₀ hφ)
    (hu₁ : RelativeFiniteEnergyPreceq θ φ u₁ hφ)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e W ρ) :
    mixedTruncationLimitMeasure (modelStripOpens W hρ.1)
      (fun _ => erealModelChartFunction (finiteGeodesic θ.val u₀ u₁) e ρ)
      (fun _ => (isBoundaryMaximalPshOn_erealModel_of_subgeodesic
        (finiteGeodesic_isSubgeodesicFrom_of_relativeFullMassPreceq omega hu₀.1 hu₁.1)
        e hρ).2.1) = 0 :=
  mixedTruncationLimitMeasure_erealModel_of_relativeFullMassPreceq_eq_zero
    omega θ hu₀.1 hu₁.1 e hρ

end

end SGPT.Foundations.Analysis.Pending.SingularPerronPreceqMixedZero
