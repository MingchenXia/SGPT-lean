import SGPT.Foundations.Analysis.Pending.SingularPerronNonpluripolarZero
import SGPT.Foundations.Analysis.Pending.FiniteGeodesicsFullMassAnyDim
import SGPT.Foundations.Analysis.Pending.SubgeodesicChartPotential

set_option autoImplicit false

/-! # Actual canonical diagonal mixed vanishing from singular Perron endpoints -/

open Set TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalMixedZero

open FirstPass FirstPass.PositiveClasses FiniteGeodesicMaximality
  SingularPerronBoundaryMaximality SingularPerronNonpluripolarZero
  SingularMaximalNonpluripolarZero MongeAmpere MixedNonPluripolar

noncomputable section

/-- The genuine scalar/diagonal mixed identification gives actual mixed NP vanishing from actual ordinary maximality. -/
theorem mixedTruncationLimitMeasure_eq_zero_of_boundaryMaximal
    {d : ℕ} (hd : 0 < d) {Ω : Opens (ComplexModel d)} {u : ComplexModel d → EReal}
    (hu : IsBoundaryMaximalPshOn (Ω : Set (ComplexModel d)) u) :
    mixedTruncationLimitMeasure Ω (fun _ => u) (fun _ => hu.2.1) = 0 := by
  rw [mixedTruncationLimitMeasure_diagonal hd hu.2.1]
  exact truncationLimitMeasure_eq_zero_of_boundaryMaximal hd hu

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] [CompactSpace M]

/-- Genuine fixed-local-potential transport supplies actual model-strip ordinary maximality without an additional strip PSH input. -/
theorem isBoundaryMaximalPshOn_erealModel_of_subgeodesic
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) :
    IsBoundaryMaximalPshOn (modelStripOpens W hρ.1 : Set (ComplexModel (n + 1)))
      (erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ) :=
  isBoundaryMaximalPshOn_erealModel_finiteGeodesic hsub e hρ
    (SubgeodesicChartPotential.plurisubharmonicOn_subgeodesicChartFunction hsub.2.2.1 e hρ)

/-- The actual scalar NP strip equation is internally produced on any actual local-potential chart. -/
theorem truncationLimitMeasure_erealModel_of_subgeodesic_eq_zero
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) :
    truncationLimitMeasure (modelStripOpens W hρ.1)
      (erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (isBoundaryMaximalPshOn_erealModel_of_subgeodesic hsub e hρ).2.1 = 0 :=
  truncationLimitMeasure_eq_zero_of_boundaryMaximal (Nat.succ_pos n)
    (isBoundaryMaximalPshOn_erealModel_of_subgeodesic hsub e hρ)

/-- The actual canonical diagonal mixed NP strip equation follows from internally produced ordinary maximality. -/
theorem mixedTruncationLimitMeasure_erealModel_of_subgeodesic_eq_zero
    {θ : SmoothRealForm n M 2} {u₀ u₁ : M → EReal}
    (hsub : IsSubgeodesicFrom θ (finiteGeodesic θ u₀ u₁) u₀ u₁)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ e W ρ) :
    mixedTruncationLimitMeasure (modelStripOpens W hρ.1)
      (fun _ => erealModelChartFunction (finiteGeodesic θ u₀ u₁) e ρ)
      (fun _ => (isBoundaryMaximalPshOn_erealModel_of_subgeodesic hsub e hρ).2.1) = 0 :=
  mixedTruncationLimitMeasure_eq_zero_of_boundaryMaximal (Nat.succ_pos n)
    (isBoundaryMaximalPshOn_erealModel_of_subgeodesic hsub e hρ)

variable [MeasurableSpace M] [BorelSpace M] [ConnectedSpace M]

/-- Actual relative full-mass endpoints internally supply both the actual Perron subgeodesic and its actual diagonal mixed homogeneous strip equation. -/
theorem mixedTruncationLimitMeasure_erealModel_of_relativeFullMass_eq_zero
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ u₀ u₁ : M → EReal} (hφ : IsModelPotential θ φ)
    (hu₀ : RelativeFullMass θ φ u₀ hφ) (hu₁ : RelativeFullMass θ φ u₁ hφ)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e W ρ) :
    mixedTruncationLimitMeasure (modelStripOpens W hρ.1)
      (fun _ => erealModelChartFunction (finiteGeodesic θ.val u₀ u₁) e ρ)
      (fun _ => (isBoundaryMaximalPshOn_erealModel_of_subgeodesic
        (FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass
          omega θ φ u₀ u₁ hφ hu₀ hu₁) e hρ).2.1) = 0 :=
  mixedTruncationLimitMeasure_erealModel_of_subgeodesic_eq_zero
    (FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeFullMass
      omega θ φ u₀ u₁ hφ hu₀ hu₁) e hρ

/-- Actual arbitrary singular relative finite-energy endpoints give the canonical diagonal mixed strip equation with no target subgeodesic or PSH input. -/
theorem mixedTruncationLimitMeasure_erealModel_of_relativeFiniteEnergy_eq_zero
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {φ u₀ u₁ : M → EReal} (hφ : IsModelPotential θ φ)
    (hu₀ : RelativeFiniteEnergy θ φ u₀ hφ) (hu₁ : RelativeFiniteEnergy θ φ u₁ hφ)
    (e : ComplexChart n M) {W : Set (ComplexModel n)} {ρ : ComplexModel n → ℝ}
    (hρ : IsSmoothLocalPotential θ.val e W ρ) :
    mixedTruncationLimitMeasure (modelStripOpens W hρ.1)
      (fun _ => erealModelChartFunction (finiteGeodesic θ.val u₀ u₁) e ρ)
      (fun _ => (isBoundaryMaximalPshOn_erealModel_of_subgeodesic
        (FiniteGeodesicsFullMassAnyDim.finiteGeodesic_isSubgeodesicFrom_of_relativeFiniteEnergy
          omega θ φ u₀ u₁ hφ hu₀ hu₁) e hρ).2.1) = 0 :=
  mixedTruncationLimitMeasure_erealModel_of_relativeFullMass_eq_zero
    omega θ hφ hu₀.fullMass hu₁.fullMass e hρ

end

end SGPT.Foundations.Analysis.Pending.SingularPerronCanonicalMixedZero
