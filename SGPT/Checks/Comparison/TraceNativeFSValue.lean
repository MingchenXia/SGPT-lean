import SGPT.Checks.Comparison.TraceNativeAnalyticIdealOrder
import SGPT.Checks.Comparison.TraceGFGlobalAnalyticType

/-! The ORIGINAL physical FS value on the ACTUAL native image semi-valuation.
Blueprint: `trace-native-image-valuation.tex`. Native targets remain arbitrary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeImage

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ SGPT.NAPotential.BJ.GfIm SGPT.NAPotential.GAGAMult
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.GlobalAnalyticSingularities
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance traceNativeFSProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceNativeFSTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceNativeFSCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceNativeFSManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The original normalized physical maximum has its SAME positive rational
global ideal type under ANY actual native holomorphic restriction. -/
theorem normalized_sectionMaximum_nativeRestriction_has_global_actual_ideal_type
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {I : Type} [Fintype I] [Nonempty I] (s : I → bundlePowerGlobalSections L N)
    {k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
    [IsComplexManifold k V] (F : V → SchemeComplexPoint f)
    (hF : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ F) :
    HasAnalyticSingularitiesOfType (n := k)
      (fun y => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H (F y))
      ((K : ℚ)⁻¹) (GermIdeal.pullback (m := k) F (analytificationIdeal f n EX (sectionsIdeal a N s))) :=
  AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hF
    (normalized_sectionMaximum_has_global_actual_ideal_type f n EX H a N K hK s)

/-- **The ORIGINAL normalized physical FS value at the ACTUAL image of a
native analytic prime is exactly the SAME scaled ENTIRE pulled ideal order.**
All source poles/zero pulled families/non-dominant native targets are retained. -/
theorem potentialAn_sectionMaximum_nativeImagePoint_eq
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {I : Type} [Fintype I] [Nonempty I] (s : I → bundlePowerGlobalSections L N)
    (hs : ∀ j, s j ≠ 0)
    {m : ℕ} {Z : Type} [TopologicalSpace Z] [ChartedSpace (ComplexModel (m+1)) Z]
    [IsComplexManifold (m+1) Z] (G : Z → SchemeComplexPoint f)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel n) ∞ G) (z : Z)
    {E : Set Z} (Φ : DivisorFlattening (m := m) E z) (c : ℝ) (hc : 0 < c) :
    potentialAn n EX (fun x => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H x)
      (nativeImagePoint f n G hG z Φ c hc) =
      -((ENNReal.ofReal c * (originalStalkNormalOrder Φ
        (GermIdeal.pullback (m := m+1) G (analytificationIdeal f n EX (sectionsIdeal a N s))) : ℝ≥0∞) /
          K : ℝ≥0∞) : EReal) := by
  rw [SGPT.NAPotential.BJ.GfIm.RationalHull.potentialAn_sectionsMaxLog_all_narrow
    f n EX H a N s hs hK]
  rw [nativeImagePoint_idealVal_eq_originalStalkNormalOrder f n G hG z Φ EX c hc]

end SGPT.NAPotential.TraceComparison.NativeImage
