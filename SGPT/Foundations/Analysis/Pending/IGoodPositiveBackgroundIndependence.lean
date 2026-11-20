import SGPT.Foundations.Analysis.Pending.PositiveMassAnalyticCurrentSequences
import SGPT.Foundations.Analysis.Pending.PositiveNativeIGoodSequenceClosure
import SGPT.Foundations.Analysis.Pending.IGoodBackgroundDescent
import SGPT.Foundations.Analysis.Pending.SingularNativeBackgroundIndependence
import SGPT.Foundations.Analysis.Pending.SingularPositiveCommonBackgroundExistence
import SGPT.Foundations.Analysis.Pending.BoucksomMassBigness
import SGPT.Foundations.Analysis.Pending.DimZeroKahler

set_option autoImplicit false

/-! # Actual I-goodness in every positive admissible closed background -/

open Set Filter MeasureTheory
open scoped Topology

namespace SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence

open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.IEnvelope
  FirstPass.QuasiEquisingularApproximation DiagonalMass
  ThetaPshL1Topology SingularCanonicalSingularityDistance
  PositiveMassAnalyticCurrentSequences PositiveNativeIGoodSequenceClosure
  IGoodBackgroundDescent SingularNativeBackgroundIndependence
  SingularPositiveCommonBackgroundExistence

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [CompactSpace M] [ConnectedSpace M]

/-- Actual analytic approximation and native background transport produce
the Kähler-enlargement equivalence without an input bigness witness. -/
theorem iGoodWith_iff_add_kahler
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hpos : HasPositivePotentialMass θ u hu) :
    let hU : IsThetaPshPotential (θ + omega.form).val u :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hu omega.isSemipositive
    IGoodWith θ u hu ↔ IGoodWith (θ + omega.form) u hU := by
  let hU : IsThetaPshPotential (θ + omega.form).val u :=
    LocalPotentials.isThetaPshPotential_add_of_semipositive hu omega.isSemipositive
  change IGoodWith θ u hu ↔ IGoodWith (θ + omega.form) u hU
  have hbig : IsBigClass (RealBottChern.ofRepresentative θ) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact DimZeroKahler.isBigClass_of_dim_zero hn omega θ
    · exact BoucksomMassBigness.isBigClass_of_diagonalPotentialMass_pos hn omega θ hu hpos
  have hlarge : IsBigClass (RealBottChern.ofRepresentative (θ + omega.form)) := by
    simpa only [one_smul] using
      PositiveCurrentAssembly.isBigClass_add_smul_of_isThetaPshPotential omega θ hu zero_lt_one
  have hposU : HasPositivePotentialMass (θ + omega.form) u hU := by
    simpa only [one_smul] using hasPositivePotentialMass_add_smul omega hu zero_lt_one
  constructor
  · intro hgood
    obtain ⟨A, hA, hlim⟩ :=
      exists_analytic_current_sequence_native_of_iGoodWith omega θ hbig hu hgood
    let V : ℕ → ThetaPshL1 (θ + omega.form).val := fun j =>
      ⟨(A j).val, LocalPotentials.isThetaPshPotential_add_of_semipositive
        (A j).property omega.isSemipositive⟩
    let U : ThetaPshL1 (θ + omega.form).val := ⟨u, hU⟩
    have hlimV : Tendsto V atTop (@nhds (ThetaPshL1 (θ + omega.form).val)
        (singularityPseudoMetricSpace omega (θ + omega.form) hlarge).toUniformSpace.toTopologicalSpace U) :=
      (tendsto_native_iff_add_kahler omega θ hbig atTop A ⟨u, hu⟩).mp hlim
    exact iGoodWith_of_analytic_native_sequence_positive_limit
      omega (θ + omega.form) hlarge V U hposU (fun j => (hA j).1) hlimV
  · intro hgood
    have hsemi : ((θ + omega.form) - θ).val.IsSemipositive := by
      have he : (θ + omega.form) - θ = omega.form := by abel
      rw [he]
      exact omega.isSemipositive
    exact iGoodWith_of_semipositive_background_enlargement omega hu hU hsemi hpos hgood

/-- Compact actual Kähler domination internally selects the common form;
I-goodness then descends to every original positive admissible background. -/
theorem iGoodWith_iff_positive_common_potential
    (omega : KahlerBackground n M) (θ σ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hv : IsThetaPshPotential σ.val u)
    (hpos : HasPositivePotentialMass θ u hu)
    (hposV : HasPositivePotentialMass σ u hv) :
    IGoodWith θ u hu ↔ IGoodWith σ u hv := by
  have forward (θ σ : ClosedRealOneOneForm n M)
      (hu : IsThetaPshPotential θ.val u) (hv : IsThetaPshPotential σ.val u)
      (hpos : HasPositivePotentialMass θ u hu)
      (hposV : HasPositivePotentialMass σ u hv)
      (hgood : IGoodWith θ u hu) : IGoodWith σ u hv := by
    obtain ⟨C, hC, hK⟩ := KahlerDomination.exists_pos_isKahler_add_smul omega (σ - θ)
    let κ : KahlerBackground n M := ⟨σ - θ + C • omega.form, hK⟩
    have hlarge : IsThetaPshPotential (θ + κ.form).val u :=
      LocalPotentials.isThetaPshPotential_add_of_semipositive hu κ.isSemipositive
    have hlargeGood : IGoodWith (θ + κ.form) u hlarge :=
      (iGoodWith_iff_add_kahler κ θ hu hpos).mp hgood
    have hform : (θ + κ.form) - σ = C • omega.form := by
      dsimp only [κ]
      module
    have hsemi : ((θ + κ.form) - σ).val.IsSemipositive := by
      rw [hform]
      exact KahlerDomination.isSemipositive_smul omega.isSemipositive hC.le
    exact iGoodWith_of_semipositive_background_enlargement omega hv hlarge hsemi hposV hlargeGood
  exact ⟨forward θ σ hu hv hpos hposV, forward σ θ hv hu hposV hpos⟩

end

end SGPT.Foundations.Analysis.Pending.IGoodPositiveBackgroundIndependence
