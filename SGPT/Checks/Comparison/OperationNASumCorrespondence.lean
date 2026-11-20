import SGPT.Checks.Comparison.OperationOriginalSumOnDivisorial
import SGPT.Checks.Comparison.OperationSumChernData
import SGPT.Checks.Comparison.OperationNativeDivisorialEquality
import SGPT.Checks.Comparison.SourceAnalytificationMap
import SGPT.Checks.Comparison.ThinApprox.BJNativePSHAdmission

/-! ORIGINAL actual sum correspondence on ALL original Berkovich points.
Primitive input data only, actual tensor/dictionary/PSH inputs produced.
Blueprint: operation-na-sum-correspondence.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.NativePicard
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (E : ClosedProjectiveEmbedding f)
  [IsProjective f] [IsIntegral X]
local instance sumComparisonProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance sumComparisonPointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance sumComparisonPointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance sumComparisonPointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M N : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M)
  (c : LineBundleAtlas N) (HN : SchemeLineBundleMetric f n E N)
  {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
  {θ σ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)
  (hσ : (atlasClosedFormToNative σ).val.GeometricallyEq (((q : ℝ)⁻¹) • HN.curvature c).val)

include b HM c HN hm hq hθ hσ

/-- SAME ORIGINAL sum has literal added original map values on EVERY
original point, with only the TWO original primitive rational Chern inputs.
Tensor target, every prime, native classes and all geometry are INTERNAL. -/
theorem naPotentialAnAt_sum (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    naPotentialAnAt n E (Γ.sum Δ) ω =
      fun v => naPotentialAnAt n E Γ ω v + naPotentialAnAt n E Δ ω v := by
  let bS := sumTensorAtlas b c m q
  let HS := sumTensorMetric f n E b HM c HN m q
  have hChern := sumTensor_geometricallyEq f n E b HM c HN hm hq hθ hσ
  have hΓ := (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Γ).2
  have hΔ := (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E c HN hq hσ ω Δ).2
  have hS := (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E bS HS
    (Nat.mul_pos hm hq) hChern ω (Γ.sum Δ)).2
  have hΓnative := SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.isNativePSH f hΓ
  have hΔnative := SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.isNativePSH f hΔ
  have hSnative := SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.isNativePSH f hS
  simp only [SGPT.NAPotential.BJ.SourceNet.naAnalytification_apply] at hΓnative hΔnative hSnative
  have hsumNative := nativePSH_add f hΓnative hΔnative
  apply nativePSH_eq_of_sourceDivisorial_eq f hSnative hsumNative
  intro v hv
  exact naPotentialAnAt_sum_on_sourceDivisorialSet f n E Γ Δ ω v hv

/-- CLOSED original source sum clause: exact SAME map value formula AND
actual ORIGINAL BJ PSH membership at the SUM of original rational classes.
No transported operation definition, output net or desired certificate. -/
theorem source_sum_correspondence (Γ : SourceNAPotential θ) (Δ : SourceNAPotential σ)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    (∀ v : BerkovichPoint f, naPotentialAnAt n E (Γ.sum Δ) ω v =
      (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Γ).1 v +
        (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E c HN hq hσ ω Δ).1 v) ∧
    IsModuleTopologyPSH.{0} f
      ((m : ℚ)⁻¹ • rationalPicardClass b + (q : ℚ)⁻¹ • rationalPicardClass c)
      (fun v =>
        (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Γ).1 v +
          (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E c HN hq hσ ω Δ).1 v) := by
  have heq := naPotentialAnAt_sum f n E b HM c HN hm hq hθ hσ Γ Δ ω
  refine ⟨fun v => congrFun heq v, ?_⟩
  have hChern := sumTensor_geometricallyEq f n E b HM c HN hm hq hθ hσ
  have hS := (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E
    (sumTensorAtlas b c m q) (sumTensorMetric f n E b HM c HN m q)
    (Nat.mul_pos hm hq) hChern ω (Γ.sum Δ)).2
  change IsModuleTopologyPSH.{0} f
    (((m * q : ℕ) : ℚ)⁻¹ • rationalPicardClass (sumTensorAtlas b c m q))
    (naPotentialAnAt n E (Γ.sum Δ) ω) at hS
  rw [sumTensor_rationalClass b c hm hq] at hS
  rwa [heq] at hS

end SGPT.NAPotential.OperationComparison
