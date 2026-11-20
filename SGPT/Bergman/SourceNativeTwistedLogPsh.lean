import SGPT.Bergman.SourceNativeSectionLogPsh
import SGPT.Bergman.SourceNativeDegreeChern
import SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.Bergman.NativeHermitianMetric
open Bundle Set Filter
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.PolynomialH0Growth
open SGPT.Bergman.QuantizationDraft
open HermitianHolomorphicLineBundle
open scoped Topology Manifold ContDiff ENNReal

variable {n : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] [ConnectedSpace X]

/-- The TRUE entire original twisted section log is theta-PSH in its
actual degree Chern background; the whole native reader is produced. -/
theorem sourceTwistedSectionLogNormSq_isThetaPsh
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (k : ℕ) (s : twistedSections L T k) (hs : s ≠ 0) :
    IsThetaPshPotential
      ((k : ℝ) • sourceNativeFirstChernForm L hL + sourceNativeFirstChernForm T hT).val
      (sourceSectionLogNormSq (twistedPower L T k) s) :=
  ⟨sourceSectionLogNormSq_thetaPlurisubharmonic_of_isOwn (twistedPower L T k)
      (sourceNativeTwistedPower_smooth L T hL hT k) _
      (sourceNativeTwistedPower_isOwn L T hL hT k) s,
    sourceSectionLogNormSq_locallyNondegenerate (twistedPower L T k) s hs⟩

/-- Literal normalized original section potential (1/k)log|s|² is
theta-PSH in c1(L)+(1/k)c1(T), with actual physical degree data. All poles
are retained; no normalized-curvature or PSH certificate is supplied. -/
theorem sourceNormalizedTwistedSectionLogNormSq_isThetaPsh
    (L T : HermitianHolomorphicLineBundle.{0,0} n X)
    (hL : IsSourceSmoothHermitianMetric L) (hT : IsSourceSmoothHermitianMetric T)
    (k : ℕ) (hk : 0 < k) (s : twistedSections L T k) (hs : s ≠ 0) :
    IsThetaPshPotential
      (sourceNativeFirstChernForm L hL + (k : ℝ)⁻¹ • sourceNativeFirstChernForm T hT).val
      (fun x => (((k : ℝ)⁻¹ : ℝ) : EReal) * sourceSectionLogNormSq (twistedPower L T k) s x) := by
  have hkp : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hp := SGPT.Foundations.Analysis.Pending.RestrictedApproximantComparison.isThetaPshPotential_smul
    (sourceTwistedSectionLogNormSq_isThetaPsh L T hL hT k s hs) (inv_pos.mpr hkp)
  have hform : (k : ℝ)⁻¹ •
      ((k : ℝ) • sourceNativeFirstChernForm L hL + sourceNativeFirstChernForm T hT) =
      sourceNativeFirstChernForm L hL + (k : ℝ)⁻¹ • sourceNativeFirstChernForm T hT := by
    rw [smul_add, smul_smul, inv_mul_cancel₀ hkp.ne', one_smul]
  rwa [hform] at hp

end SGPT.Bergman.NativeHermitianMetric
