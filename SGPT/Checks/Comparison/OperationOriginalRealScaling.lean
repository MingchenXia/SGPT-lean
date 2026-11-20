import SGPT.Checks.Comparison.OperationNAScaling
import SGPT.Checks.Comparison.OperationNativeRealScaling
import SGPT.Checks.Comparison.ThinApprox.BJNativePSHAdmission
import SGPT.Checks.Comparison.ThinApprox.SourceDXZ

/-! Original real rescaling correspondence with the EXISTING genuine
real numerical-class native BJ PSH target. No rationality/nef/PSH2 premise.
Blueprint: operation-real-class-scaling.tex. -/
set_option autoImplicit false
noncomputable section
namespace SGPT.NAPotential.OperationComparison
open AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass
open SGPT.PSH.VariableComplexAtlas SGPT.NAPotential.Berkovich
open SGPT.NAPotential.BJ.Printed SGPT.NAPotential.BJ.NativePicard
open SGPT.NAPotential.BJ
open SGPT.Foundations.Envelope

variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ) [SmoothOfRelativeDimension n f]
  (E : ClosedProjectiveEmbedding f) [IsProjective f] [IsIntegral X]
local instance opOriginalRealScaleProper : IsProper f := (SGPT.Foundations.Envelope.ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance opOriginalRealScalePointTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance opOriginalRealScalePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance opOriginalRealScalePointManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {M : X.Modules} (b : LineBundleAtlas M) (HM : SchemeLineBundleMetric f n E M) {m : ℕ}
  (hm : 0 < m) {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((m : ℝ)⁻¹) • HM.curvature b).val)


include b HM hm hθ

/-- SAME actual original scaled NA function is PSH for its genuine
scaled numerical REAL class, even for irrational scalars; all original
points, including trivial, are read through the existing point homeomorphism. -/
theorem naPotentialAnAt_positiveScale_isNativePSH
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    Variety.IsPSH f
      (c • NativePicard.numericalClass f ((m : ℚ)⁻¹ • rationalPicardClass b))
      (fun y => naPotentialAnAt n E (Γ.positiveScale hc) ω ((pointEquiv f).symm y)) := by
  have hF := (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Γ).2
  have hN := SGPT.NAPotential.ThinApprox.BJ.Printed.IsModuleTopologyPSH.isNativePSH f hF
  have hscaled := nativePSH_positiveScale f hN hc
  simpa only [naPotentialAnAt_positiveScale n E Γ hc ω,
    SGPT.NAPotential.BJ.SourceNet.naAnalytification_apply] using hscaled

/-- Source thm:NApotential:L1352 REAL-rescaling clause with ORIGINAL
primitive line/metric/Chern scope: actual full-point function equality AND
membership in the EXISTING actual BJ numerical REAL-class predicate.
No scaled-Q-line presentation or new predicate equivalence is asserted. -/
theorem source_positive_real_scaling
    (Γ : SourceNAPotential θ) {c : ℝ} (hc : 0 < c)
    (ω : SourceKahlerForm n (SchemeComplexPoint f)) :
    (∀ v : BerkovichPoint f, naPotentialAnAt n E (Γ.positiveScale hc) ω v =
      (c : EReal) *
        (SGPT.NAPotential.BJ.SourceNet.naAnalytification f n E b HM hm hθ ω Γ).1 v) ∧
    Variety.IsPSH f
      (c • NativePicard.numericalClass f ((m : ℚ)⁻¹ • rationalPicardClass b))
      (fun y => naPotentialAnAt n E (Γ.positiveScale hc) ω ((pointEquiv f).symm y)) :=
  ⟨fun v => naPotentialAnAt_positiveScale n E Γ hc ω v,
    naPotentialAnAt_positiveScale_isNativePSH f n E b HM hm hθ Γ hc ω⟩

end SGPT.NAPotential.OperationComparison
