import SGPT.Checks.Comparison.TraceNAGeneralCompatibility
import SGPT.Checks.Comparison.TraceNAGeneralTrivial
import SGPT.Checks.Comparison.TraceNativePrimeChoice
import SGPT.Checks.Comparison.TraceNativeDivisorReader

/-! The FIXED original ambient analytification has a canonical actual
native divisorial restriction: real weights, original direct geometric
quotient, and the trivial point. No canonical ambient POINT equality is
assumed. Blueprint: trace-native-divisor-readers.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.NAPotential.TraceComparison
open Set Filter AlgebraicGeometry CategoryTheory SGPT.Foundations.Schemes SGPT.Okounkov SGPT.Foundations.Envelope
open SGPT.NAPotential.Berkovich SGPT.PSH.VariableComplexAtlas SGPT.PSH.CompactPrimeOver
open SGPT.Foundations.Analysis SGPT.Foundations.Analysis.FirstPass SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.FirstPass.PositiveClasses
open FixedGermNormalOrder DemaillyApproximantDivisorialLelong NATrace NativeImage
open scoped Topology Manifold ContDiff ENNReal

variable {X : Scheme.{0}} {L : X.Modules} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsIntegral X] [IsProjective f]
  (EX : ClosedProjectiveEmbedding f)
local instance canonicalRestrictionProper : IsProper f := (ProjectiveFactorizationRingIso.of_isProjective f).isProper
local instance canonicalRestrictionTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance canonicalRestrictionCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance canonicalRestrictionManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n
variable [MeasurableSpace (SchemeComplexPoint f)] [BorelSpace (SchemeComplexPoint f)]
  [CompactSpace (SchemeComplexPoint f)] [ConnectedSpace (SchemeComplexPoint f)]
  {k : ℕ} {V : Type} [TopologicalSpace V] [ChartedSpace (ComplexModel k) V]
  [IsComplexManifold k V] [MeasurableSpace V] [BorelSpace V] [CompactSpace V] [ConnectedSpace V]
  (hk : k ≤ n) (omegaX : KahlerBackground n (SchemeComplexPoint f))
  (omegaV : KahlerBackground k V) {ι : V → SchemeComplexPoint f}
  (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
  (hvol : SGPT.Trace.RIsoB.PullbackKahlerVolumePos hι)
  (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n EX L) {d : ℕ} (hd : 0 < d)
  {θ : AtlasClosedRealOneOneForm (ofFixedModel n (SchemeComplexPoint f))}
  (hθ : (atlasClosedFormToNative θ).val.GeometricallyEq (((d : ℝ)⁻¹) • H.curvature a).val)
  (Γ : SourceNAPotential θ) (hwd : TraceWellDefined ι Γ)
  (κX : SourceKahlerForm n (SchemeComplexPoint f)) (κV : SourceKahlerForm k V)

include a H hd hθ in
/-- The actual chosen image of EVERY original prime presentation reads
the unchanged actual trace; includes the vacuous strict-prime dimension0. -/
theorem naTraceRes_primeImagePoint_eq (p : PrimePresentation k V) (c : ℝ) (hc : 0 < c) :
    BJPrep.naDivisorialTransform (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV p c =
      naPotentialAnAt n EX Γ κX (primeImagePoint f n ι hι p c hc) := by
  cases k with
  | zero => have h := p.dimension_pos; omega
  | succ m =>
    rw [primeImagePoint_succ]
    exact naTraceRes_nativeDivisorial_eq f n EX hk omegaX omegaV hι hvol a H hd hθ Γ hwd κX κV
      p (choosePrimeChartData p).mem (choosePrimeChartData p).flattening c hc

include hk omegaX omegaV hvol hwd κV a H hd hθ in
/-- Actual ambient values of the FIXED original Gamma descend under the
ORIGINAL single-common-resolution relation. No ambient point equality or
value certificate is supplied. -/
theorem ambientPrimeValue_eq_of_commonResolution
    (p q : PrimePresentation k V) (hpq : commonResolutionRelation p q)
    (c : ℝ) (hc : 0 < c) :
    naPotentialAnAt n EX Γ κX (primeImagePoint f n ι hι p c hc) =
      naPotentialAnAt n EX Γ κX (primeImagePoint f n ι hι q c hc) := by
  let Δ := TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd
  have hp : naPotentialAnAt n EX Γ κX (primeImagePoint f n ι hι p c hc) =
      directNAPrimeValue Δ κV (Quot.mk commonResolutionRelation p) c :=
    (naTraceRes_primeImagePoint_eq f n EX hk omegaX omegaV hι hvol a H hd hθ Γ hwd κX κV p c hc).symm.trans
      (directNAPrimeValue_mk Δ κV p c).symm
  have hq : naPotentialAnAt n EX Γ κX (primeImagePoint f n ι hι q c hc) =
      directNAPrimeValue Δ κV (Quot.mk commonResolutionRelation q) c :=
    (naTraceRes_primeImagePoint_eq f n EX hk omegaX omegaV hι hvol a H hd hθ Γ hwd κX κV q c hc).symm.trans
      (directNAPrimeValue_mk Δ κV q c).symm
  exact hp.trans ((congrArg (fun p => directNAPrimeValue Δ κV p c)
    ((direct_mk_eq_iff p q).mpr hpq)).trans hq.symm)

/-- The actual original ambient function restricted to actual native
divisorial classes, REAL positive weights and the trivial point. Its
quotient descent is PROVED internally from actual original Gamma/trace
geometry. There is no chosen family of matching values as an input. -/
def nativeDivisorialRestriction : NativeDivisorialPoint k V → EReal
  | none => naPotentialAnAt n EX Γ κX
      (NativeTrivial.point f n ι hι (Classical.choice (inferInstance : Nonempty V)))
  | some cp =>
      Quot.lift (fun p => naPotentialAnAt n EX Γ κX
        (primeImagePoint f n ι hι p cp.1.val cp.1.property))
        (fun p q hpq => ambientPrimeValue_eq_of_commonResolution f n EX hk omegaX omegaV hι hvol
          a H hd hθ Γ hwd κX κV p q hpq cp.1.val cp.1.property) cp.2

/-- Equality of ACTUAL FUNCTIONS on the original direct geometric
quotient, including the native trivial point. Original Gamma, original
trace and original ambient evaluation are retained literally. -/
theorem nativeDivisorialRestriction_eq_trace :
    nativeDivisorialRestriction f n EX hk omegaX omegaV hι hvol a H hd hθ Γ hwd κX κV =
      nativeDivisorialFunction (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV := by
  funext v
  cases v with
  | none =>
    exact naPotentialAnAt_nativeTrivial_eq_traceMax f n EX hk omegaX omegaV hι hvol a H hd hθ Γ hwd κX κV
      (Classical.choice (inferInstance : Nonempty V))
  | some cp =>
    rcases cp with ⟨c,p⟩
    refine Quot.inductionOn p fun p => ?_
    change naPotentialAnAt n EX Γ κX (primeImagePoint f n ι hι p c.val c.property) =
      directNAPrimeValue (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV
        (Quot.mk commonResolutionRelation p) c.val
    exact (naTraceRes_primeImagePoint_eq f n EX hk omegaX omegaV hι hvol a H hd hθ Γ hwd κX κV
      p c.val c.property).symm.trans
      (directNAPrimeValue_mk (TraceRes.naTraceRes hk omegaX omegaV hι hvol Γ hwd) κV p c.val).symm

end SGPT.NAPotential.TraceComparison
