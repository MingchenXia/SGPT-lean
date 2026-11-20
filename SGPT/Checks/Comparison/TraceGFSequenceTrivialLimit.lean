import SGPT.Checks.Comparison.TraceGFSequenceNativeMembers
import SGPT.Checks.Comparison.TraceResIntrinsicEquivalent

/-! The actual general native trivial trace limit, for the ACTUAL
original lifted GF sequence. Blueprint: trace-na-general-family.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison.NativeGFSequence

open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.NAPotential.BJ.NativePicard SGPT.NAPotential.BJ.Printed
open SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.NAPotential.TraceComparison.GFTwist
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong NATrace NativeImage
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {f : X ⟶ Spec (.of ℂ)} {r : ℕ}
  [SmoothOfRelativeDimension (r+1) f] [IsIntegral X] [IsProjective f]
  {EX : ClosedProjectiveEmbedding f}
local instance trivialLimitProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance trivialLimitTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance trivialLimitCharts : ChartedSpace (ComplexModel (r+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (r+1)
local instance trivialLimitManifold : IsComplexManifold (r+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (r+1)
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (r+1) EX L)
  {d : ℕ} (hd : 0 < d)
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (r+1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
  {Γ : SourceNAPotential θ} {κX : SourceKahlerForm (r+1) (SchemeComplexPoint f)}
  (S : NativeGFSequence f r EX θ ((d : ℚ)⁻¹ • rationalPicardClass a)
    (naPotentialAnAt (r+1) EX Γ κX) κX)

include H hd hθ S in
/-- At the SAME actual native trivial image, the GIVEN original curve's
full analytification equals its unchanged actual native trace maximum.
The original actual common infimum, cutoff convergence and primitive GF
member identities are internal; every native target dimension includes0. -/
theorem nativeTrivial_eq
    {k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
    [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    (hk : k ≤ r+1) (omegaX : KahlerBackground (r+1) (SchemeComplexPoint f))
    (omegaV : KahlerBackground k V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (r+1)) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) (z : V) :
    naPotentialAnAt (r+1) EX Γ κX (NativeTrivial.point f (r+1) ι hι z) =
      ((((TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd).component κV).val.max : ℝ) : EReal) := by
  obtain ⟨ha,hb,hInf⟩ := S.exists_common_decreasingInf_eq omegaX
  have hwCommon : TraceWellDefined ι S.commonGiven :=
    traceWellDefined_of_naOrder (Γ.transition_POrder_equivalent omegaX S.original_to_common_semipositive).1 hwd
  have hwInf : TraceWellDefined ι (SourceNAPotential.decreasingInf omegaX S.commonMember ha hb) := by
    simpa only [hInf] using hwCommon
  have hmemberCutoff (i : ℕ) : traceCutoff ι (S.commonMember i) κX =
      traceCutoff ι (S.member i) κX :=
    (traceCutoff_transition omegaX (S.member i) (S.member_to_common_semipositive i)
      (traceWellDefined_of_naOrder (S.original_le_member omegaX i) hwd) κX).symm
  have hgivenCutoff : traceCutoff ι S.commonGiven κX = traceCutoff ι Γ κX :=
    (traceCutoff_transition omegaX Γ S.original_to_common_semipositive hwd κX).symm
  have hreal : Tendsto (fun i => traceCutoff ι (S.member i) κX) atTop
      (𝓝 (traceCutoff ι Γ κX)) := by
    simpa only [hInf,hmemberCutoff,hgivenCutoff] using
      tendsto_traceCutoff_decreasingInf omegaX S.commonMember ha hb hwInf κX
  have hvalue (i : ℕ) :
      naPotentialAnAt (r+1) EX (S.member i) κX (NativeTrivial.point f (r+1) ι hι z) =
        ((traceCutoff ι (S.member i) κX : ℝ) : EReal) := by
    rw [S.member_nativeTrivial_eq a H hd hθ hk omegaX omegaV hι hvol hwd κV z i,
      TraceRes.naTraceRes_max hk omegaX omegaV hι hvol (S.member i)
        (traceWellDefined_of_naOrder (S.original_le_member omegaX i) hwd) κV κX]
  have hfirst : Tendsto (fun i => ((traceCutoff ι (S.member i) κX : ℝ) : EReal)) atTop
      (𝓝 (naPotentialAnAt (r+1) EX Γ κX (NativeTrivial.point f (r+1) ι hι z))) := by
    simpa only [hvalue] using S.tendsto (NativeTrivial.point f (r+1) ι hι z)
  calc
    _ = ((traceCutoff ι Γ κX : ℝ) : EReal) := tendsto_nhds_unique hfirst (EReal.tendsto_coe.mpr hreal)
    _ = _ := by rw [TraceRes.naTraceRes_max hk omegaX omegaV hι hvol Γ hwd κV κX]

end SGPT.NAPotential.TraceComparison.NativeGFSequence
