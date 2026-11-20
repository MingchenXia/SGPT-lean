import SGPT.Projective.AlgebraicNativeSectionForward
import SGPT.Projective.OriginalSectionUnit

/-! Actual ordinary original section to its native holomorphic section,
with every original frame coefficient proved through the genuine tensor unit.
Blueprint: original-ordinary-native-section.tex. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
open CategoryTheory AlgebraicGeometry SGPT.Foundations.Schemes
open SGPT.Okounkov SGPT.NAPotential.GAGAMult
open SGPT.Projective.NumEq.AlgebraicCurveDegree
open SGPT.Bergman.TensorDictionaryDraft SGPT.Bergman.QuantizationDraft
open SGPT.Bergman.CompactHolomorphicSectionsDraft
open HermitianHolomorphicLineBundle
open SGPT.Foundations.Analysis.FirstPass
open scoped Topology Manifold ContDiff
variable {X : Scheme.{0}} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]
    (E : ClosedProjectiveEmbedding f) {L : X.Modules}
    (a : LineBundleAtlas L) (H : SchemeLineBundleMetric f n E L)
local instance ordinaryForwardTopology : TopologicalSpace (SchemeComplexPoint f) := schemeAnalyticPointTopology f
local instance ordinaryForwardCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) := schemeAnalyticTNChartedSpace f n
local instance ordinaryForwardManifold : IsComplexManifold n (SchemeComplexPoint f) := schemeAnalyticTN_isComplexManifold f n

/-- The fixed original ordinary section gives a true native section of the
SAME physical line. The original inverse left unitor is applied explicitly;
only native positivePower zero is definitionally the original native line. -/
def nativeSectionOfOriginalOrdinary (s : Γ(L,⊤)) :
    HolomorphicSections (n:=n) (schemeHermitianLineBundle f n E a H).Fiber :=
  nativeSectionOfAlgebraicPositivePower f n E a H 0 (originalSectionUnit s)

/-- EVERY original atlas coefficient of the produced native section is the
actual original ordinary coefficient. No reader equality is input. -/
theorem nativeSectionOfOriginalOrdinary_frame (s : Γ(L,⊤)) (i : a.I)
    (p : SchemeComplexPoint f) (hp : schemeComplexPointImage f p∈a.opens i) :
    sectionCoefficient (schemeHermitianLineBundle f n E a H).Fiber
      (schemeHermitianAtlasFrame f n E a H (a.frame i)).val
      (nativeSectionOfOriginalOrdinary f n E a H s) p =
    schemeOpenRegularFunction f n E (a.opens i)
      ((a.frame i).coefficients (𝟙 _) (L.val.map (a.opens i).leTop.op s)) p := by
  have h := nativeSectionOfAlgebraicPositivePower_frame f n E a H 0
    (originalSectionUnit s) i hp
  change _ = schemeOpenRegularFunction f n E (a.opens i)
    (algCoef (a.frame i) 1 (originalSectionUnit s)) p at h
  exact h.trans (congrArg (fun c => schemeOpenRegularFunction f n E (a.opens i) c p)
    (originalSectionUnit_coefficients s (a.frame i) (𝟙 _)))
end SGPT.Projective.NumEq.CompleteIntersections.AlgebraicNativeCI
