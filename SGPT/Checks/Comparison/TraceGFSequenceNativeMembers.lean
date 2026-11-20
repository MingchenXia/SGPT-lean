import SGPT.Checks.Comparison.TraceGFSequenceCommon
import SGPT.Checks.Comparison.TraceRationalGFCompatibility
import SGPT.Checks.Comparison.TraceCutoffDecreasingInf

/-! The SAME original native image reads EVERY actual GF approximation.
Blueprint: trace-na-general-family.tex. -/
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
local instance nativeMembersProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance nativeMembersTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance nativeMembersCharts : ChartedSpace (ComplexModel (r+1)) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f (r+1)
local instance nativeMembersManifold : IsComplexManifold (r+1) (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f (r+1)
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {L : X.Modules} (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f (r+1) EX L)
  {d : ℕ} (hd : 0 < d)
  {θ : AtlasClosedRealOneOneForm (ofFixedModel (r+1) (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
  {Γ : SourceNAPotential θ} {κX : SourceKahlerForm (r+1) (SchemeComplexPoint f)}
  (S : NativeGFSequence f r EX θ ((d : ℚ)⁻¹ • rationalPicardClass a)
    (naPotentialAnAt (r+1) EX Γ κX) κX)

include hd in
omit [IsIntegral X] in
/-- EVERY actual varying-class member is rational GF in its SAME literal
primitive tensor line bundle; its primitive Chern match is manufactured by
the original metric tensor calculation. -/
theorem member_primitive_GF (i : ℕ) :
    IsRationalGF f (((d * (S.epsilon i).den : ℕ) : ℚ)⁻¹ •
      rationalPicardClass (twistLineAtlas a S.atlas (S.epsilon i).den (d*(S.epsilon i).num.toNat)))
      (naPotentialAnAt (r+1) EX (S.member i) κX) := by
  rw [rationalPicardClass_twist a S.atlas hd (S.epsilon i) (S.positive i).le]
  exact S.member_GF i

include H hd hθ in
/-- The ORIGINAL native prime/point/flattening/image is IDENTICAL at
every index. Actual member trace existence, primitive tensor Chern class,
GF family and the full actual rational trace formula are all internal. -/
theorem member_nativeDivisorial_eq
    {m : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel (m+1)) V]
    [IsComplexManifold (m+1) V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    (hk : m+1 ≤ r+1) (omegaX : KahlerBackground (r+1) (SchemeComplexPoint f))
    (omegaV : KahlerBackground (m+1) V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel (m+1)) 𝓘(ℂ, ComplexModel (r+1)) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm (m+1) V) (p : PrimePresentation (m+1) V)
    {z : p.model} (hz : z ∈ p.divisor) (Φ : DivisorFlattening (m := m) p.divisor z)
    (c : ℝ) (hc : 0 < c) (i : ℕ) :
    BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol (S.member i)
      (traceWellDefined_of_naOrder (S.original_le_member omegaX i) hwd)) κV p c =
      naPotentialAnAt (r+1) EX (S.member i) κX
        (nativeImagePoint f (r+1) (ι ∘ p.projection) (hι.comp p.modification.1) z Φ c hc) := by
  exact naTraceRes_nativeDivisorial_eq_of_isRationalGF f (r+1) EX hk omegaX omegaV hι hvol
    (twistLineAtlas a S.atlas (S.epsilon i).den (d*(S.epsilon i).num.toNat))
    (twistLineMetric f (r+1) EX a H S.atlas S.metric (S.epsilon i).den (d*(S.epsilon i).num.toNat))
    (Nat.mul_pos hd (S.epsilon i).den_pos)
    (twistForm_geometricallyEq f (r+1) EX a H S.atlas S.metric hd hθ (S.epsilon i) (S.positive i).le)
    (S.member i) (traceWellDefined_of_naOrder (S.original_le_member omegaX i) hwd) κX κV
    (S.member_primitive_GF a hd i) p hz Φ c hc

include H hd hθ in
/-- The SAME actual native trivial image works at EVERY approximation
index, including native target dimension zero. -/
theorem member_nativeTrivial_eq
    {k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
    [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
    (hk : k ≤ r+1) (omegaX : KahlerBackground (r+1) (SchemeComplexPoint f))
    (omegaV : KahlerBackground k V) {ι : V → SchemeComplexPoint f}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel (r+1)) ∞ ι)
    (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι) (hwd : TraceWellDefined ι Γ)
    (κV : SourceKahlerForm k V) (z : V) (i : ℕ) :
    naPotentialAnAt (r+1) EX (S.member i) κX (NativeTrivial.point f (r+1) ι hι z) =
      ((((TraceRes.naTraceRes hk omegaX omegaV hι hvol (S.member i)
        (traceWellDefined_of_naOrder (S.original_le_member omegaX i) hwd)).component κV).val.max : ℝ) : EReal) := by
  exact naPotentialAnAt_nativeTrivial_eq_traceMax_of_isRationalGF f (r+1) EX hk omegaX omegaV hι hvol
    (twistLineAtlas a S.atlas (S.epsilon i).den (d*(S.epsilon i).num.toNat))
    (twistLineMetric f (r+1) EX a H S.atlas S.metric (S.epsilon i).den (d*(S.epsilon i).num.toNat))
    (Nat.mul_pos hd (S.epsilon i).den_pos)
    (twistForm_geometricallyEq f (r+1) EX a H S.atlas S.metric hd hθ (S.epsilon i) (S.positive i).le)
    (S.member i) (traceWellDefined_of_naOrder (S.original_le_member omegaX i) hwd) κX κV
    (S.member_primitive_GF a hd i) z

end SGPT.NAPotential.TraceComparison.NativeGFSequence
