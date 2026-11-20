import SGPT.Bergman.SiuUniformGenerationCorrection
import SGPT.Bergman.SiuUniformGenerationStep

/-!
# Siu's uniform generation with the original quantifier order

The actual fixed-cover correction and local generation step give one
exponent before any varying line bundle, potential or tensor degree is
introduced. The conclusion is the existing source statement itself.

Blueprint: `siu-uniform-source-main.tex`.
-/

set_option autoImplicit false

noncomputable section

namespace SGPT.Bergman.SiuUniformGeneration

open Set Filter Metric MeasureTheory Bundle
open scoped Topology ENNReal ContDiff Manifold
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open SGPT.Foundations.Analysis.Pending SGPT.Foundations.Analysis.Pending.ChartwiseGlobalL1
open SGPT.Foundations.Analysis.Pending.ProductComplexManifold
open scoped ProductComplexManifold
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.NativeHermitianMetric
open HermitianHolomorphicLineBundle
open SGPT.PSH.GlobalL2 SGPT.PSH.SiuL2 SGPT.NAPotential.NAGaga SGPT.NAPotential.SiuGen

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- One threshold chosen from the original positive bundle works for every
larger exponent and every original varying bundle, potential and degree. -/
theorem siuGlobalUniformGeneration_prod_of_le [CompactSpace X]
    (G : HermitianHolomorphicLineBundle.{0, 0} n X) (hG : IsSourceSmoothHermitianMetric G)
    (θG : ClosedRealOneOneForm n X) (hθG : IsOwnFirstChernForm G θG) (hKah : θG.val.IsKahler) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
    ∀ L : HermitianHolomorphicLineBundle.{0, 0} n X, IsSourceSmoothHermitianMetric L →
    ∀ θ : ClosedRealOneOneForm n X, IsOwnFirstChernForm L θ →
    ∀ Φ : X × unitDisc → EReal, IsThetaPshPotential
      (ClosedRealOneOneForm.pullback
        (contMDiff_fst (n := n) (m := 1) (X := X) (Y := unitDisc)) θ).val Φ →
    ∀ m : ℕ, 0 < m →
      IsProdGloballyGenerated (twistedPower L (positivePower G (k - 1)) m)
        (multiplierIdeal (n := n + 1) (m : ℝ) Φ) := by
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  let omega : KahlerBackground n X := ⟨θG, hKah⟩
  have hμ := KahlerVolumeSmoothPositive.isSmoothPositiveVolume_kahlerVolume omega
  let D := fixedGeometry hμ G hG θG hθG hKah
  obtain ⟨B, hB0, hBa⟩ := D.exists_uniform_siuPoleB hKah
  refine ⟨exponent D (((n : ℝ) + 3) * B), exponent_pos D _, ?_⟩
  intro k hk L hL θ hθ Φ hΦ m hm
  have hGood := goodPower_exponent D (((n : ℝ) + 3) * B) hk
  have hE := sourceNativeTwistedPower_smooth L (positivePower G (k - 1)) hL
    (sourceNativePositivePower_smooth G hG (k - 1)) m
  have hOwnE := twistedPower_isOwnFirstChernForm L G hL hG hθ hθG hGood.1 m
  have hcorr := hasProdCorrection_fixedCover D hG hE hθG hGood hm hOwnE hΦ
  exact isProdGloballyGenerated_of_fixedCover_correction hμ D hKah hB0 hBa hm hΦ hcorr

/-- The literal whole source `lma:Siu_global_uniform_generatedness`:
`∃ k` occurs before the varying line bundle, weight and tensor degree. -/
theorem siuGlobalUniformGeneration_prod [CompactSpace X] :
    SiuGlobalUniformGenerationStatement n X := by
  intro G hG θG hθG hKah
  obtain ⟨k₀, hk₀, h⟩ := siuGlobalUniformGeneration_prod_of_le G hG θG hθG hKah
  exact ⟨k₀, hk₀, h k₀ le_rfl⟩

end SGPT.Bergman.SiuUniformGeneration
