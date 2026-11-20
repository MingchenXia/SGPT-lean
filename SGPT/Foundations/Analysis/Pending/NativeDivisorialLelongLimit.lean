import SGPT.Foundations.Analysis.Pending.PositiveNativeDivisorialLelongLimit
import SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence

set_option autoImplicit false

/-! # Actual native generic Lelong limits, including zero original mass -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.NativeDivisorialLelongLimit

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus DiagonalMass
  DemaillyApproximantDivisorialLelong ThetaPshL1Topology
  SingularCanonicalSingularityDistance SingularPositiveCommonBackgroundExistence
  SingularNativeBackgroundIndependence

noncomputable section

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
  [BorelSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]
  [CompactSpace Y] [ConnectedSpace Y]

/-- Actual positive enlargement and native transport internally remove all
original mass hypotheses; the literal raw Lelong reader is unchanged. -/
theorem tendsto_divisorialLelongNumber_of_native
    (omega : KahlerBackground (m + 1) Y) (θ : ClosedRealOneOneForm (m + 1) Y)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ)) {I : Type*} (F : Filter I)
    (w : I → ThetaPshL1 θ.val) (u : ThetaPshL1 θ.val)
    (hlim : Tendsto w F (@nhds (ThetaPshL1 θ.val)
      (singularityPseudoMetricSpace omega θ hbig).toUniformSpace.toTopologicalSpace u))
    (E : Set Y) :
    Tendsto (fun i => divisorialLelongNumber m (w i).val E) F
      (𝓝 (divisorialLelongNumber m u.val E)) := by
  let γ := θ + omega.form
  have hγ : IsBigClass (RealBottChern.ofRepresentative γ) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential
        omega θ u.property zero_lt_one
  let W : I → ThetaPshL1 γ.val := fun i =>
    ⟨(w i).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
      (w i).property omega.isSemipositive⟩
  let U : ThetaPshL1 γ.val :=
    ⟨u.val, LocalPotentials.isThetaPshPotential_add_of_semipositive
      u.property omega.isSemipositive⟩
  have hUpos : 0 < diagonalPotentialMass γ U.val U.property := by
    simpa only [HasPositivePotentialMass, one_smul] using
      hasPositivePotentialMass_add_smul omega u.property zero_lt_one
  have hWlim : Tendsto W F (@nhds (ThetaPshL1 γ.val)
      (singularityPseudoMetricSpace omega γ hγ).toUniformSpace.toTopologicalSpace U) :=
    (tendsto_native_iff_add_kahler omega θ hbig F w u).mp hlim
  exact PositiveNativeDivisorialLelongLimit.tendsto_divisorialLelongNumber_of_native_positive
    omega γ hγ F W U hUpos hWlim E

end
end SGPT.Foundations.Analysis.Pending.NativeDivisorialLelongLimit
