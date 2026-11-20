import SGPT.Bergman.SiuUniformGenerationCorrection
import SGPT.Bergman.SiuUniformGenerationStep
import SGPT.Trace.ProductMultiplierRestriction

/-!
# Uniform multiplier generation in one literal positive power

The target is the actual recursively constructed positive power of `G`,
with its original physical metric.  One degree works for every potential
in a fixed multiple of its original Chern background.  This avoids any
unstated tensor-association equivalence in the Kodaira consumer.
Blueprint: `siu-kodaira-embedding.tex`, node `siu-kodaira:uniform-point-ideals`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace SGPT.Bergman.SiuKodaira

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal Manifold ContDiff
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric SGPT.Bergman.SiuUniformGeneration
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.SiuGen SGPT.NAPotential.NAGaga

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- The literal original positive power has its exact prescribed Chern form. -/
theorem positivePower_isOwnFirstChernForm
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    {θG : ClosedRealOneOneForm n X} (hθG : IsOwnFirstChernForm G θG) (j : ℕ) :
    IsOwnFirstChernForm (positivePower G j) (((j + 1 : ℕ) : ℝ) • θG) := by
  intro c e z hz he
  have h := sourceNativeFirstChernForm_isOwn (positivePower G j)
    (sourceNativePositivePower_smooth G hG j) c e z hz he
  rw [sourceNativePositivePower_chern_coeff G hG c hz j,
    sourceNativeFirstChernForm_geometricallyEq G hG hθG c hz] at h
  simpa only [ClosedRealOneOneForm.coeff_smul] using h

/-- One literal positive power works for all original potentials with the
specified fixed background.  The degree is chosen before the potential. -/
theorem exists_positivePower_productGeneration [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG)
    (hKah : θG.val.IsKahler) (ell : ℕ) :
    ∃ d : ℕ, 0 < d ∧ ∀ φ : X → EReal,
      IsThetaPshPotential ((ell : ℝ) • θG).val φ →
      IsProdGloballyGenerated (positivePower G (d - 1))
        (multiplierIdeal (n := n + 1) 1 (fun q : X × unitDisc => φ q.1)) := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  let omega : KahlerBackground n X := ⟨θG, hKah⟩
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  let D := fixedGeometry hμ G hG θG hθG hKah
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_siuPoleB hKah
  let K := exponent D (((n : ℝ) + 3) * B)
  have hKpos : 0 < K := exponent_pos D _
  have hK := goodPower_exponent D (((n : ℝ) + 3) * B) (K := K) le_rfl
  have hd : 1 ≤ ell + K := by omega
  refine ⟨ell + K, by omega, fun φ hφ => ?_⟩
  have hΦ := SGPT.Trace.ProductMultiplierRestriction.isThetaPshPotential_comp_fst
    (m := 1) (Y := unitDisc) ((ell : ℝ) • θG) hφ
  have hE := sourceNativePositivePower_smooth G hG (ell + K - 1)
  have hOwnE := positivePower_isOwnFirstChernForm G hG hθG (ell + K - 1)
  have hform : (((ell + K - 1 + 1 : ℕ) : ℝ) • θG) =
      (1 : ℝ) • ((ell : ℝ) • θG) + (K : ℝ) • θG := by
    rw [Nat.sub_add_cancel hd]
    push_cast
    module
  rw [hform] at hOwnE
  have hOwnE' : IsOwnFirstChernForm (positivePower G (ell + K - 1))
      (((1 : ℕ) : ℝ) • ((ell : ℝ) • θG) + (K : ℝ) • θG) := by
    simpa only [Nat.cast_one] using hOwnE
  have hcorr := hasProdCorrection_fixedCover D hG hE hθG hK (by norm_num : 0 < (1 : ℕ)) hOwnE' hΦ
  simpa only [Nat.cast_one] using isProdGloballyGenerated_of_fixedCover_correction hμ D hKah hB0 hBa
    (by norm_num : 0 < (1 : ℕ)) hΦ hcorr

end SGPT.Bergman.SiuKodaira
