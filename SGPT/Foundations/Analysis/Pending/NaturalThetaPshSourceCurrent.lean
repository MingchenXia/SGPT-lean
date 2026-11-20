import SGPT.Foundations.Analysis.Pending.NaturalThetaPshClosedCurrent
import SGPT.Foundations.Analysis.Pending.GlobalQuasiPshVolumeIntegrability
import SGPT.Foundations.Analysis.Pending.KahlerVolumeSmoothPositive

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold

namespace SGPT.Foundations.Analysis.Pending.NaturalThetaPshSourceCurrent

open FirstPass FirstPass.PositiveClasses _root_.SGPT.Foundations.Analysis.LocalCurrents
  GlobalCurrents GlobalCurrentPotentials CanonicalCurrentFrame
  CanonicalSmoothCurrentDensity CanonicalComplementaryCurrentTests ConstantFormProducts
  TopDegreeDensity StronglyPositiveForms NaturalThetaPshGeometricCurrent
  NaturalThetaPshClosedCurrent GlobalQuasiPshVolumeIntegrability KahlerVolumeSmoothPositive
  IntegrationCurrent

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (m + 1)) M] [IsComplexManifold (m + 1) M]

private theorem smoothGlobalCurrent_smul_closedForm (c : ℝ)
    (θ : ClosedRealOneOneForm (m + 1) M) :
    smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) (c • θ).val =
        c • smoothGlobalCurrent (canonicalBasis (m + 1))
          (k := degreeTwo (Nat.succ_pos m)) θ.val := by
  apply GlobalCurrent.ext
  intro e η
  rw [smoothGlobalCurrent_apply_eq_integral_topDensity, GlobalCurrent.inChart_smul]
  change (∫ x, topDensity (wedgeTo _ ((c • θ).val.coeff e x) (η x))) =
    c * (smoothGlobalCurrent (canonicalBasis (m + 1))
      (k := degreeTwo (Nat.succ_pos m)) θ.val).inChart e η
  rw [smoothGlobalCurrent_apply_eq_integral_topDensity, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ClosedRealOneOneForm.coeff_smul, wedgeTo_smul_left]
  simp only [topDensity, ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- The actual global current for the source normalization `D = 2π ddᶜ`. -/
def sourceDCurrent (α : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
    (hu : IsGlobalQuasiPshPotential (n := m + 1) u) :
    GlobalCurrent (m + 1) M (degreeTwo (Nat.succ_pos m)) :=
  smoothGlobalCurrent (canonicalBasis (m + 1)) α.val +
    (2 * Real.pi) • globalDDC (canonicalBasis (m + 1)) (Nat.succ_pos m) u hu

/-- Source rescaling gives literal equality in the genuine compatible current space. -/
theorem sourceDCurrent_scaled_theta_eq
    (θ : ClosedRealOneOneForm (m + 1) M) (u : M → EReal)
    (hu : IsThetaPshPotential θ.val u) :
    sourceDCurrent ((2 * Real.pi) • θ) u hu.quasiPshPotential =
      (2 * Real.pi) • thetaPotentialCurrent θ.val u hu := by
  unfold sourceDCurrent thetaPotentialCurrent
  rw [smoothGlobalCurrent_smul_closedForm, smul_add]

variable [MeasurableSpace M] [BorelSpace M] [CompactSpace M]

/-- The actual source conditions use genuine regularity, genuine volume, and full tests. -/
def IsSourceDPshPotential (omega : KahlerBackground (m + 1) M)
    (α : ClosedRealOneOneForm (m + 1) M) (u : M → EReal) : Prop :=
  ∃ hu : IsGlobalQuasiPshPotential (n := m + 1) u,
    Integrable (fun x => (u x).toReal) (kahlerVolume omega) ∧
    ∀ (e : ComplexChart (m + 1) M) (η : TestForm (chartTarget e) (2 * m)),
      (∀ x, η x ∈ spCone m) →
        0 ≤ (sourceDCurrent α u hu).inChart e
          (castTestDegree (by rw [complexModel_real_finrank]; omega :
            2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) η)

/-- Genuine theta-PSH supplies all the original source current conditions internally. -/
theorem genuine_theta_source_current_interpretation
    (omega : KahlerBackground (m + 1) M) (θ : ClosedRealOneOneForm (m + 1) M)
    (u : M → EReal) (hu : IsThetaPshPotential θ.val u) :
    UpperSemicontinuous u ∧
    Integrable (fun x => (u x).toReal) (kahlerVolume omega) ∧
    (thetaPotentialCurrent θ.val u hu).IsClosed (canonicalBasis (m + 1)) ∧
    (thetaPotentialCurrent θ.val u hu).IsTypeOneOne
      (canonicalBasis (m + 1)) (Nat.succ_pos m) ∧
    (∀ (e : ComplexChart (m + 1) M) (η : TestForm (chartTarget e) (2 * m)),
      (∀ x, η x ∈ spCone m) →
        0 ≤ (thetaPotentialCurrent θ.val u hu).inChart e
          (castTestDegree (by rw [complexModel_real_finrank]; omega :
            2 * m = Module.finrank ℝ (ComplexModel (m + 1)) - 2) η)) ∧
    IsSourceDPshPotential omega ((2 * Real.pi) • θ) u ∧
    (sourceDCurrent ((2 * Real.pi) • θ) u hu.quasiPshPotential).IsClosed
      (canonicalBasis (m + 1)) ∧
    (sourceDCurrent ((2 * Real.pi) • θ) u hu.quasiPshPotential).IsTypeOneOne
      (canonicalBasis (m + 1)) (Nat.succ_pos m) := by
  have hint := integrable_toReal_of_genuine_thetaPsh (kahlerVolume omega)
    (isSmoothPositiveVolume_kahlerVolume omega) θ.val u hu
  obtain ⟨hc, ht, hp⟩ := thetaPotentialCurrent_closed_type_positive θ.val u hu
  refine ⟨hu.quasiPshPotential.1.upperSemicontinuous, hint, hc, ht, hp, ?_, ?_, ?_⟩
  · refine ⟨hu.quasiPshPotential, hint, ?_⟩
    intro e η hη
    rw [sourceDCurrent_scaled_theta_eq]
    change 0 ≤ (2 * Real.pi) * (thetaPotentialCurrent θ.val u hu).inChart e _
    exact mul_nonneg (by positivity) (hp e η hη)
  · rw [sourceDCurrent_scaled_theta_eq]
    exact hc.smul _ _
  · rw [sourceDCurrent_scaled_theta_eq]
    exact ht.smul _ _

end SGPT.Foundations.Analysis.Pending.NaturalThetaPshSourceCurrent
