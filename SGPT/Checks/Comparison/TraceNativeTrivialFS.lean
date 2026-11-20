import SGPT.Checks.Comparison.TraceNativeTrivialIdeal
import SGPT.Checks.Comparison.TraceNativeTrivialType
import SGPT.Checks.Comparison.TraceGFGlobalAnalyticType
import SGPT.Checks.Comparison.TraceGFRationalHull
import SGPT.Foundations.Analysis.Pending.GlobalPotentialPullback
import SGPT.Foundations.Analysis.Pending.ThetaPshIdentityPrinciple

/-! The ORIGINAL physical FS value at its ACTUAL native trivial image.
Blueprint: `trace-native-trivial.tex`. All native target dimensions, including zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeTrivial

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ SGPT.NAPotential.BJ.GfIm
open SGPT.PSH.VariableComplexAtlas
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open SGPT.Foundations.Analysis.FirstPass.HolomorphicIdealSheaves
open scoped Topology Manifold ContDiff ENNReal Classical

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance traceTrivialFSProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance traceTrivialFSTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance traceTrivialFSCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance traceTrivialFSManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable {k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V]

/-- Under its LITERAL nontrivial restriction hypothesis, the original
physical section maximum has value ZERO at its ACTUAL native trivial image.
Actual target PSH, entire ideal nonvanishing and all dictionaries are internal. -/
theorem potentialAn_sectionMaximum_trivialPoint_eq_zero [ConnectedSpace V]
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {I : Type} [Fintype I] [Nonempty I] (s : I → bundlePowerGlobalSections L N) (hs : ∀ j, s j ≠ 0)
    (G : V → SchemeComplexPoint f)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ G)
    (hne : ∃ y, (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H (G y) ≠ ⊥)
    (z : V) :
    potentialAn n EX (fun x => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H x)
      (point f n G hG z) = 0 := by
  have hφ := SGPT.Okounkov.TranscendentalCore.isThetaPshPotential_nonneg_smul
    (isThetaPshPotential_sectionsMaxLog f n EX a N s H hs)
    (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) K))
  let β := ClosedRealOneOneForm.pullback hG (((K : ℝ)⁻¹) • (N : ℝ) • H.curvature a)
  have hV : IsThetaPshPotential β.val
      (fun y => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H (G y)) :=
    ThetaPshIdentityPrinciple.isThetaPshPotential_of_exists_ne_bot
      (GlobalPotentialPullback.thetaPlurisubharmonic_comp hG hφ.1) hne
  have htype := AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hG
    (normalized_sectionMaximum_has_global_actual_ideal_type f n EX H a N K hK s)
  have hnon := spanGerms_ne_bot_of_globalAnalyticType hV.2 htype z
  rw [RationalHull.potentialAn_sectionsMaxLog_all_narrow f n EX H a N s hs hK,
    point_idealVal_eq_if_analytic f n G hG z EX, if_neg hnon]
  simp

/-- An identically minus-infinite actual restriction gives the actual
original FS value minus infinity at the SAME native trivial image. -/
theorem potentialAn_sectionMaximum_trivialPoint_eq_bot
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) (N K : ℕ) (hK : 0 < K)
    {I : Type} [Fintype I] [Nonempty I] (s : I → bundlePowerGlobalSections L N) (hs : ∀ j, s j ≠ 0)
    (G : V → SchemeComplexPoint f)
    (hG : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ G)
    (hbot : ∀ y, (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H (G y) = ⊥)
    (z : V) :
    potentialAn n EX (fun x => (((K : ℝ)⁻¹ : ℝ) : EReal) * sectionsMaxLog f n EX a N s H x)
      (point f n G hG z) = ⊥ := by
  have htype := AnalyticTypeRestriction.hasAnalyticSingularitiesOfType_comp hG
    (normalized_sectionMaximum_has_global_actual_ideal_type f n EX H a N K hK s)
  have hzero := spanGerms_eq_bot_of_globalAnalyticType_eq_bot htype hbot z
  rw [RationalHull.potentialAn_sectionsMaxLog_all_narrow f n EX H a N s hs hK,
    point_idealVal_eq_if_analytic f n G hG z EX, if_pos hzero,
    ENNReal.top_div_of_ne_top (ENNReal.natCast_ne_top K)]
  simp

end SGPT.NAPotential.TraceComparison.NativeTrivial
