import SGPT.Checks.Comparison.TraceGFSequenceNativeMembers
import SGPT.Checks.Comparison.TraceResInfimum
import SGPT.Checks.Comparison.TraceResIntrinsicEquivalent

/-! The actual general native divisorial trace limit, for the ACTUAL
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
local instance nativeLimitProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance nativeLimitTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance nativeLimitCharts : ChartedSpace (ComplexModel (r+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (r+1)
local instance nativeLimitManifold : IsComplexManifold (r+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (r+1)
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
/-- The SAME ACTUAL original source curve and unchanged native trace
agree at the SAME ACTUAL native prime image. The actual common family,
original NA infimum, cutoff bound, member trace existence, primitive GF
identities, all transition invariances and full Legendre infimum are
produced internally from the original approximation. -/
theorem nativeDivisorial_eq
    {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel (m+1)) V]
    [IsComplexManifold (m+1) V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    (hk : m+1 ≤ r+1) (omegaX : KahlerBackground (r+1) (SchemeComplexPoint f))
    (omegaV : KahlerBackground (m+1) V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel (r+1)) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm (m+1) V) (p : PrimePresentation (m+1) V)
    {z : p.model} (hz : z ∈ p.divisor) (Φ : DivisorFlattening (m := m) p.divisor z)
    (c : ℝ) (hc : 0 < c) :
    BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV p c =
      naPotentialAnAt (r+1) EX Γ κX
        (nativeImagePoint f (r+1) (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc) := by
  obtain ⟨ha,hb,hInf⟩ := S.exists_common_decreasingInf_eq omegaX
  have hwCommon : TraceWellDefined ι S.commonGiven :=
    traceWellDefined_of_naOrder (Γ.transition_POrder_equivalent omegaX S.original_to_common_semipositive).1 hwd
  have hwInf : TraceWellDefined ι (SourceNAPotential.decreasingInf omegaX S.commonMember ha hb) := by
    simpa only [hInf] using hwCommon
  let T := traceResFamily hk omegaX omegaV hι hvol S.commonMember ha hb hwInf
  have hT (i : ℕ) : BJPrep.naDivisorialTransform (T i) κV p c =
      BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol (S.member i)
        (traceWellDefined_of_naOrder (S.original_le_member omegaX i) hwd)) κV p c := by
    change BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol
      (S.commonMember i) _) κV p c = _
    simpa only [commonMember] using
      (naTraceRes_divisorial_transition hk omegaX omegaV hι hvol (S.member i)
        (S.member_to_common_semipositive i)
        (traceWellDefined_of_naOrder (S.original_le_member omegaX i) hwd) κV p c).symm
  have hlimit :
      BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol
        S.commonGiven hwCommon) κV p c = ⨅ i, BJPrep.naDivisorialTransform (T i) κV p c := by
    simpa only [hInf] using
      naTraceRes_divisorial_decreasingInf hk omegaX omegaV hι hvol S.commonMember ha hb hwInf κV p hc
  calc
    _ = BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol
        S.commonGiven hwCommon) κV p c :=
      naTraceRes_divisorial_transition hk omegaX omegaV hι hvol Γ
        S.original_to_common_semipositive hwd κV p c
    _ = ⨅ i, BJPrep.naDivisorialTransform (T i) κV p c := hlimit
    _ = ⨅ i, naPotentialAnAt (r+1) EX (S.member i) κX
        (nativeImagePoint f (r+1) (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc) := by
      apply iInf_congr
      intro i
      exact (hT i).trans (S.member_nativeDivisorial_eq a H hd hθ hk omegaX omegaV hι hvol hwd κV p hz Φ c hc i)
    _ = _ := (tendsto_nhds_unique
      (S.tendsto (nativeImagePoint f (r+1) (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc))
      (tendsto_atTop_iInf (S.antitone _))).symm

end SGPT.NAPotential.TraceComparison.NativeGFSequence
