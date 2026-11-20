import SGPT.Bergman.SourceNativeDegreeChern
import SGPT.Foundations.Analysis.Pending.KahlerDomination

/-!
# Actual auxiliary native positivity after the manufactured original bound

Original C is given FIRST, then an actual integer threshold chooses the
native auxiliary metric. That same threshold works before every semipositive
native S and degree. All Chern coefficients are the true physical native ones.
Blueprint: work/sgpt-resume-20261114/bert-e2-aux-curvature/blueprint/bert-e2-aux-curvature.tex.
-/
set_option autoImplicit false
noncomputable section
namespace SGPT.Trace.BertiniAuxiliaryCurvatureChoice
open Set Filter Bundle
open scoped Topology Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric
open HermitianHolomorphicLineBundle

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [CompactSpace X]

theorem exists_actual_native_auxiliary_curvature_threshold (omega : KahlerBackground n X)
    (G E : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
    (hKah : (sourceNativeFirstChernForm G hG).val.IsKahler) (C κ : ℝ) :
    ∃ a₀ : ℕ, 0 < a₀ ∧ ∀ a : ℕ, a₀ ≤ a →
      ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target → ∀ v : ComplexModel n,
        (C + κ) * omega.form.val.coeff c z ![v, Complex.I • v] ≤
          (sourceNativeFirstChernForm (twistedPower G E a)
            (sourceNativeTwistedPower_smooth G E hG hE a)).val.coeff c z ![v, Complex.I • v] := by
  let omegaG : KahlerBackground n X := ⟨sourceNativeFirstChernForm G hG, hKah⟩
  obtain ⟨A, hA, hsemi⟩ := KahlerDomination.exists_pos_isSemipositive_add_smul omegaG
    (sourceNativeFirstChernForm E hE - (C + κ) • omega.form)
  obtain ⟨a₀, ha₀⟩ := exists_nat_gt A
  have ha₀pos : 0 < a₀ := by exact_mod_cast hA.trans ha₀
  refine ⟨a₀, ha₀pos, ?_⟩
  intro a ha c z hz v
  have hAa : A ≤ (a : ℝ) := ha₀.le.trans (by exact_mod_cast ha)
  have h := KahlerDomination.isSemipositive_add_smul_mono omegaG.isSemipositive hAa hsemi c z hz v
  simp only [sub_eq_add_neg, ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_neg,
    ClosedRealOneOneForm.coeff_smul, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at h
  rw [sourceNativeTwistedPower_chern_coeff G E hG hE c hz a]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  dsimp only [omegaG] at h
  linarith

theorem exists_actual_native_auxiliary_for_all_semipositive_twists (omega : KahlerBackground n X)
    (G E : HermitianHolomorphicLineBundle.{0, 0} n X)
    (hG : IsSourceSmoothHermitianMetric G) (hE : IsSourceSmoothHermitianMetric E)
    (hKah : (sourceNativeFirstChernForm G hG).val.IsKahler) (C κ : ℝ) :
    ∃ a₀ : ℕ, 0 < a₀ ∧ ∀ a : ℕ, a₀ ≤ a →
      ∀ (S : HermitianHolomorphicLineBundle.{0, 0} n X) (hS : IsSourceSmoothHermitianMetric S),
      (sourceNativeFirstChernForm S hS).val.IsSemipositive → ∀ b : ℕ,
      ∀ (c : ComplexChart n X) (z : ComplexModel n), z ∈ c.val.target → ∀ v : ComplexModel n,
        (C + κ) * omega.form.val.coeff c z ![v, Complex.I • v] ≤
          (sourceNativeFirstChernForm (twistedPower S (twistedPower G E a) b)
            (sourceNativeTwistedPower_smooth S (twistedPower G E a) hS
              (sourceNativeTwistedPower_smooth G E hG hE a) b)).val.coeff c z ![v, Complex.I • v] := by
  obtain ⟨a₀, ha₀, hchoice⟩ := exists_actual_native_auxiliary_curvature_threshold omega G E hG hE hKah C κ
  refine ⟨a₀, ha₀, ?_⟩
  intro a ha S hS hSsemi b c z hz v
  have hbase := hchoice a ha c z hz v
  have hS0 := hSsemi c z hz v
  rw [sourceNativeTwistedPower_chern_coeff S (twistedPower G E a) hS
    (sourceNativeTwistedPower_smooth G E hG hE a) c hz b]
  simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact hbase.trans (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg b) hS0))

end SGPT.Trace.BertiniAuxiliaryCurvatureChoice
